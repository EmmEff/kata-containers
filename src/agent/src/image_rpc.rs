// Copyright (c) 2021 Alibaba Cloud
// Copyright (c) 2021, 2023 IBM Corporation
// Copyright (c) 2022 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0
//

use std::collections::HashMap;
use std::env;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU16, Ordering};
use std::sync::Arc;

use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use base64::{engine::general_purpose, Engine as _};
use image_rs::image::ImageClient;
use image_rs::pull::PullClient;
use oci_distribution::secrets::RegistryAuth;
use protocols::image;
use rand::{thread_rng, RngCore};
use serde::{Deserialize, Serialize};
use sev::certs::snp::ecdsa::Signature;
use sev::firmware::{
    guest::{AttestationReport, Firmware},
    host::{CertTableEntry, CertType, TcbVersion},
};
use sevsnp::{
    serialize_report,
    sevsnp::{Attestation, CertificateChain, Report, SevProduct},
};
use tokio::sync::Mutex;
use ttrpc::{self, error::get_rpc_status as ttrpc_error};

use crate::rpc::{verify_cid, CONTAINER_BASE};
use crate::AGENT_CONFIG;

// A marker to merge container spec for images pulled inside guest.
const ANNO_K8S_IMAGE_NAME: &str = "io.kubernetes.cri.image-name";

// kata rootfs is readonly, use tmpfs before CC storage is implemented.
const KATA_CC_IMAGE_WORK_DIR: &str = "/run/image/";
const KATA_CC_PAUSE_BUNDLE: &str = "/pause_bundle";
const CONFIG_JSON: &str = "config.json";

#[rustfmt::skip]
lazy_static! {
    pub static ref IMAGE_SERVICE: Mutex<Option<ImageService>> = Mutex::new(None);
}

// Convenience function to obtain the scope logger.
fn sl() -> slog::Logger {
    slog_scope::logger().new(o!("subsystem" => "cgroups"))
}

#[derive(Debug, Serialize, Deserialize)]
struct RequestData {
    image: String,
    digest: String,
    hw_attest: String,
}

#[derive(Clone)]
pub struct ImageService {
    image_client: Arc<Mutex<ImageClient>>,
    images: Arc<Mutex<HashMap<String, String>>>,
    container_count: Arc<AtomicU16>,
}

impl ImageService {
    pub fn new() -> Self {
        env::set_var("CC_IMAGE_WORK_DIR", KATA_CC_IMAGE_WORK_DIR);

        let mut image_client = ImageClient::default();
        if !AGENT_CONFIG.image_policy_file.is_empty() {
            image_client.config.file_paths.policy_path = AGENT_CONFIG.image_policy_file.clone();
        }
        if !AGENT_CONFIG.simple_signing_sigstore_config.is_empty() {
            image_client.config.file_paths.sigstore_config =
                AGENT_CONFIG.simple_signing_sigstore_config.clone();
        }
        if !AGENT_CONFIG.image_registry_auth_file.is_empty() {
            image_client.config.file_paths.auth_file =
                AGENT_CONFIG.image_registry_auth_file.clone();
        }

        Self {
            image_client: Arc::new(Mutex::new(image_client)),
            images: Arc::new(Mutex::new(HashMap::new())),
            container_count: Arc::new(AtomicU16::new(0)),
        }
    }

    /// Get the singleton instance of image service.
    pub async fn singleton() -> Result<ImageService> {
        IMAGE_SERVICE
            .lock()
            .await
            .clone()
            .ok_or_else(|| anyhow!("image service is uninitialized"))
    }

    // pause image is packaged in rootfs for CC
    fn unpack_pause_image(cid: &str, target_subpath: &str) -> Result<String> {
        let cc_pause_bundle = Path::new(KATA_CC_PAUSE_BUNDLE);
        if !cc_pause_bundle.exists() {
            return Err(anyhow!("Pause image not present in rootfs"));
        }

        info!(sl(), "use guest pause image cid {:?}", cid);
        let pause_bundle = Path::new(CONTAINER_BASE).join(cid).join(target_subpath);
        let pause_rootfs = pause_bundle.join("rootfs");
        let pause_config = pause_bundle.join(CONFIG_JSON);
        let pause_binary = pause_rootfs.join("pause");
        fs::create_dir_all(&pause_rootfs)?;
        if !pause_config.exists() {
            fs::copy(
                cc_pause_bundle.join(CONFIG_JSON),
                pause_bundle.join(CONFIG_JSON),
            )?;
        }
        if !pause_binary.exists() {
            fs::copy(cc_pause_bundle.join("rootfs").join("pause"), pause_binary)?;
        }

        Ok(pause_rootfs.display().to_string())
    }

    /// Determines the container id (cid) to use for a given request.
    ///
    /// If the request specifies a non-empty id, use it; otherwise derive it from the image path.
    /// In either case, verify that the chosen id is valid.
    fn cid_from_request(&self, req: &image::PullImageRequest) -> Result<String> {
        let req_cid = req.container_id();
        let cid = if !req_cid.is_empty() {
            req_cid.to_string()
        } else if let Some(last) = req.image().rsplit('/').next() {
            // Support multiple containers with same image
            let index = self.container_count.fetch_add(1, Ordering::Relaxed);

            // ':' not valid for container id
            format!("{}_{}", last.replace(':', "_"), index)
        } else {
            return Err(anyhow!("Invalid image name. {}", req.image()));
        };
        verify_cid(&cid)?;
        Ok(cid)
    }

    /// Set proxy environment from AGENT_CONFIG
    fn set_proxy_env_vars() {
        let https_proxy = &AGENT_CONFIG.https_proxy;
        if !https_proxy.is_empty() {
            env::set_var("HTTPS_PROXY", https_proxy);
        }
        let no_proxy = &AGENT_CONFIG.no_proxy;
        if !no_proxy.is_empty() {
            env::set_var("NO_PROXY", no_proxy);
        }
    }

    /// init atestation agent and read config from AGENT_CONFIG
    async fn get_security_config(&self) -> Result<String> {
        let aa_kbc_params = &AGENT_CONFIG.aa_kbc_params;
        // If the attestation-agent is being used, then enable the authenticated credentials support
        info!(
            sl(),
            "image_client.config.auth set to: {}",
            !aa_kbc_params.is_empty()
        );
        self.image_client.lock().await.config.auth = !aa_kbc_params.is_empty();
        let decrypt_config = format!("provider:attestation-agent:{}", aa_kbc_params);

        // Read enable signature verification from the agent config and set it in the image_client
        let enable_signature_verification = &AGENT_CONFIG.enable_signature_verification;
        info!(
            sl(),
            "enable_signature_verification set to: {}", enable_signature_verification
        );
        self.image_client.lock().await.config.security_validate = *enable_signature_verification;
        Ok(decrypt_config)
    }

    /// Call image-rs to pull and unpack image.
    async fn common_image_pull(
        &self,
        image: &str,
        bundle_path: &Path,
        decrypt_config: &str,
        source_creds: Option<&str>,
        cid: &str,
    ) -> Result<()> {
        let res = self
            .image_client
            .lock()
            .await
            .pull_image(image, bundle_path, &source_creds, &Some(decrypt_config))
            .await;
        match res {
            Ok(image) => {
                info!(
                    sl(),
                    "pull and unpack image {:?}, cid: {:?}, with image-rs succeed. ", image, cid
                );
            }
            Err(e) => {
                error!(
                    sl(),
                    "pull and unpack image {:?}, cid: {:?}, with image-rs failed with {:?}. ",
                    image,
                    cid,
                    e.to_string()
                );
                return Err(e);
            }
        };
        self.add_image(String::from(image), String::from(cid)).await;
        Ok(())
    }

    /// Pull image when creating container and return the bundle path with rootfs.
    pub async fn pull_image_for_container(
        &self,
        image: &str,
        cid: &str,
        image_metadata: &HashMap<String, String>,
    ) -> Result<String> {
        info!(sl(), "image metadata: {:?}", image_metadata);
        Self::set_proxy_env_vars();
        let is_sandbox = if let Some(value) = image_metadata.get("io.kubernetes.cri.container-type")
        {
            value == "sandbox"
        } else if let Some(value) = image_metadata.get("io.kubernetes.cri-o.ContainerType") {
            value == "sandbox"
        } else {
            false
        };

        if is_sandbox {
            let mount_path = Self::unpack_pause_image(cid, "pause")?;
            self.add_image(String::from(image), String::from(cid)).await;
            return Ok(mount_path);
        }
        let bundle_path = Path::new(CONTAINER_BASE).join(cid).join("images");
        fs::create_dir_all(&bundle_path)?;
        info!(sl(), "pull image {:?}, bundle path {:?}", cid, bundle_path);

        let client = reqwest::blocking::Client::new();

        let reference: oci_distribution::Reference = image.parse().unwrap();

        let auth = RegistryAuth::Anonymous;

        let path = PathBuf::new();

        let mut reg_client = PullClient::new(reference.clone(), &path, &auth, 1).unwrap();

        let (_, digest, _) = reg_client.pull_manifest().await.unwrap();

        let b64_value = base64_encode_report(&get_report().unwrap()).unwrap();

        let req_data = RequestData {
            image: String::from(image),
            digest: String::from(digest),
            hw_attest: b64_value,
        };

        let json_data = serde_json::to_string(&req_data)?;

        // TODO: patch for your installation for now
        let url = format!("{}/endpoint", "http://10.43.99.132:8080");

        let _result = client.post(url).body(json_data).send()?;

        let decrypt_config = self.get_security_config().await?;

        let source_creds = None; // You need to determine how to obtain this.

        self.common_image_pull(image, &bundle_path, &decrypt_config, source_creds, cid)
            .await?;
        Ok(format! {"{}/rootfs",bundle_path.display()})
    }

    /// Pull image when recieving the PullImageRequest and return the image digest.
    async fn pull_image(&self, req: &image::PullImageRequest) -> Result<String> {
        Self::set_proxy_env_vars();
        let cid = self.cid_from_request(req)?;
        let image = req.image();
        if cid.starts_with("pause") {
            Self::unpack_pause_image(&cid, "")?;
            self.add_image(String::from(image), cid).await;
            return Ok(image.to_owned());
        }

        // Image layers will store at KATA_CC_IMAGE_WORK_DIR, generated bundles
        // with rootfs and config.json will store under CONTAINER_BASE/cid.
        let bundle_path = Path::new(CONTAINER_BASE).join(&cid);
        fs::create_dir_all(&bundle_path)?;

        let decrypt_config = self.get_security_config().await?;
        let source_creds = (!req.source_creds().is_empty()).then(|| req.source_creds());

        self.common_image_pull(
            image,
            &bundle_path,
            &decrypt_config,
            source_creds,
            cid.clone().as_str(),
        )
        .await?;
        Ok(image.to_owned())
    }

    async fn add_image(&self, image: String, cid: String) {
        self.images.lock().await.insert(image, cid);
    }

    // When being passed an image name through a container annotation, merge its
    // corresponding bundle OCI specification into the passed container creation one.
    pub async fn merge_bundle_oci(&self, container_oci: &mut oci::Spec) -> Result<()> {
        if let Some(image_name) = container_oci
            .annotations
            .get(&ANNO_K8S_IMAGE_NAME.to_string())
        {
            let images = self.images.lock().await;
            if let Some(container_id) = images.get(image_name) {
                let image_oci_config_path = Path::new(CONTAINER_BASE)
                    .join(container_id)
                    .join(CONFIG_JSON);
                debug!(
                    sl(),
                    "Image bundle config path: {:?}", image_oci_config_path
                );

                let image_oci =
                    oci::Spec::load(image_oci_config_path.to_str().ok_or_else(|| {
                        anyhow!(
                            "Invalid container image OCI config path {:?}",
                            image_oci_config_path
                        )
                    })?)
                    .context("load image bundle")?;

                if let Some(container_root) = container_oci.root.as_mut() {
                    if let Some(image_root) = image_oci.root.as_ref() {
                        let root_path = Path::new(CONTAINER_BASE)
                            .join(container_id)
                            .join(image_root.path.clone());
                        container_root.path =
                            String::from(root_path.to_str().ok_or_else(|| {
                                anyhow!("Invalid container image root path {:?}", root_path)
                            })?);
                    }
                }

                if let Some(container_process) = container_oci.process.as_mut() {
                    if let Some(image_process) = image_oci.process.as_ref() {
                        self.merge_oci_process(container_process, image_process);
                    }
                }
            }
        }

        Ok(())
    }

    // Partially merge an OCI process specification into another one.
    fn merge_oci_process(&self, target: &mut oci::Process, source: &oci::Process) {
        if target.args.is_empty() && !source.args.is_empty() {
            target.args.append(&mut source.args.clone());
        }

        if target.cwd == "/" && source.cwd != "/" {
            target.cwd = String::from(&source.cwd);
        }

        for source_env in &source.env {
            let variable_name: Vec<&str> = source_env.split('=').collect();
            if !target.env.iter().any(|i| i.contains(variable_name[0])) {
                target.env.push(source_env.to_string());
            }
        }
    }
}

struct SnpEvidence {
    attestation_report: AttestationReport,
    cert_chain: Option<Vec<CertTableEntry>>,
}

fn extract_tcb_version(tcb_version: &TcbVersion) -> u64 {
    (tcb_version.microcode as u64) << 56
        | (tcb_version.snp as u64) << 48
        | (tcb_version.tee as u64) << 8
        | (tcb_version.bootloader as u64)
}

// serialize signature to bytes
fn signature_to_bytes(signature: &Signature) -> Vec<u8> {
    let mut buf = Vec::with_capacity(512);

    let b: Vec<u8> = signature
        .r()
        .iter()
        .chain(signature.s().iter())
        .cloned()
        .collect();

    let _ = buf.write(&b);

    let mut padding: Vec<u8> = vec![0; 512 - b.len()];

    buf.append(&mut padding);

    buf
}

fn get_report() -> Result<Attestation> {
    let vmpl = Some(0);
    let data = Some(create_random_request());

    let snp_evidence = match request_hardware_report(data, vmpl) {
        Ok(value) => value,
        Err(_) => panic!("not working"),
    };

    let mut attestation = Attestation::default();

    attestation.report = Some(Report {
        family_id: snp_evidence.attestation_report.family_id.to_vec(),
        report_data: snp_evidence.attestation_report.report_data.to_vec(),
        measurement: snp_evidence.attestation_report.measurement.to_vec(),
        guest_svn: snp_evidence.attestation_report.guest_svn,
        policy: snp_evidence.attestation_report.policy.0,
        image_id: snp_evidence.attestation_report.image_id.to_vec(),
        vmpl: snp_evidence.attestation_report.vmpl,
        signature_algo: snp_evidence.attestation_report.sig_algo,
        current_tcb: extract_tcb_version(&snp_evidence.attestation_report.current_tcb),
        platform_info: snp_evidence.attestation_report.plat_info.0,
        signer_info: 0,
        host_data: snp_evidence.attestation_report.host_data.to_vec(),
        id_key_digest: snp_evidence.attestation_report.id_key_digest.to_vec(),
        version: snp_evidence.attestation_report.version,
        author_key_digest: snp_evidence.attestation_report.author_key_digest.to_vec(),
        report_id: snp_evidence.attestation_report.report_id.to_vec(),
        report_id_ma: snp_evidence.attestation_report.report_id_ma.to_vec(),
        reported_tcb: extract_tcb_version(&snp_evidence.attestation_report.reported_tcb),
        chip_id: snp_evidence.attestation_report.chip_id.to_vec(),
        committed_tcb: extract_tcb_version(&snp_evidence.attestation_report.committed_tcb),
        current_build: u32::from(snp_evidence.attestation_report.current_build),
        current_minor: u32::from(snp_evidence.attestation_report.current_minor),
        current_major: u32::from(snp_evidence.attestation_report.current_major),
        committed_build: u32::from(snp_evidence.attestation_report.committed_build),
        committed_minor: u32::from(snp_evidence.attestation_report.committed_minor),
        committed_major: u32::from(snp_evidence.attestation_report.committed_major),
        launch_tcb: extract_tcb_version(&snp_evidence.attestation_report.launch_tcb),
        signature: signature_to_bytes(&snp_evidence.attestation_report.signature),
    });

    // println!("{:0x}", snp_evidence.attestation_report.version);

    let mut certificate_chain = CertificateChain::default();

    match snp_evidence.cert_chain {
        Some(v) => {
            for cert in v.iter() {
                match cert.cert_type {
                    CertType::ARK => {
                        certificate_chain.ark_cert = cert.data().to_vec();
                    }
                    CertType::CRL => {}
                    CertType::ASK => {
                        certificate_chain.ask_cert = cert.data().to_vec();
                    }
                    CertType::Empty => {}
                    CertType::VCEK => {
                        certificate_chain.vcek_cert = cert.data().to_vec();
                    }
                    CertType::VLEK => {
                        certificate_chain.vlek_cert = cert.data().to_vec();
                    }
                    CertType::OTHER(_) => {}
                };
            }
        }
        None => {}
    };

    attestation.certificate_chain = Some(certificate_chain);

    let mut sev_product = SevProduct::default();

    // TODO: get these values from somewhere
    sev_product.name = 1; // MILAN
    sev_product.stepping = 0;
    // prod.machine_stepping = Some(121 as u32);

    attestation.product = Some(sev_product);

    Ok(attestation)
}

fn base64_encode_report(attestation: &Attestation) -> Result<String> {
    let b = serialize_report(attestation);
    let mut buf = String::new();
    general_purpose::STANDARD.encode_string(b, &mut buf);
    Ok(String::from(buf))
}

// Create 64 random bytes of data for attestation report request
pub fn create_random_request() -> [u8; 64] {
    let mut data = [0u8; 64];
    thread_rng().fill_bytes(&mut data);
    data
}

fn request_hardware_report(data: Option<[u8; 64]>, vmpl: Option<u32>) -> Result<SnpEvidence> {
    let mut fw = Firmware::open().context("unable to open /dev/sev-guest")?;

    let (report, certs) = fw
        .get_ext_report(None, data, vmpl)
        .context("Failed to get attestation report")?;

    Ok(SnpEvidence {
        attestation_report: report,
        cert_chain: certs,
    })
}

#[async_trait]
impl protocols::image_ttrpc_async::Image for ImageService {
    async fn pull_image(
        &self,
        _ctx: &ttrpc::r#async::TtrpcContext,
        req: image::PullImageRequest,
    ) -> ttrpc::Result<image::PullImageResponse> {
        match self.pull_image(&req).await {
            Ok(r) => {
                let mut resp = image::PullImageResponse::new();
                resp.image_ref = r;
                return Ok(resp);
            }
            Err(e) => {
                return Err(ttrpc_error(ttrpc::Code::INTERNAL, e.to_string()));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ImageService;
    use protocols::image;

    #[tokio::test]
    async fn test_cid_from_request() {
        struct Case {
            cid: &'static str,
            image: &'static str,
            result: Option<&'static str>,
        }

        let cases = [
            Case {
                cid: "",
                image: "",
                result: None,
            },
            Case {
                cid: "..",
                image: "",
                result: None,
            },
            Case {
                cid: "",
                image: "..",
                result: None,
            },
            Case {
                cid: "",
                image: "abc/..",
                result: None,
            },
            Case {
                cid: "",
                image: "abc/",
                result: None,
            },
            Case {
                cid: "",
                image: "../abc",
                result: Some("abc_4"),
            },
            Case {
                cid: "",
                image: "../9abc",
                result: Some("9abc_5"),
            },
            Case {
                cid: "some-string.1_2",
                image: "",
                result: Some("some-string.1_2"),
            },
            Case {
                cid: "0some-string.1_2",
                image: "",
                result: Some("0some-string.1_2"),
            },
            Case {
                cid: "a:b",
                image: "",
                result: None,
            },
            Case {
                cid: "",
                image: "prefix/a:b",
                result: Some("a_b_6"),
            },
            Case {
                cid: "",
                image: "/a/b/c/d:e",
                result: Some("d_e_7"),
            },
        ];

        let image_service = ImageService::new();
        for case in &cases {
            let mut req = image::PullImageRequest::new();
            req.set_image(case.image.to_string());
            req.set_container_id(case.cid.to_string());
            let ret = image_service.cid_from_request(&req);
            match (case.result, ret) {
                (Some(expected), Ok(actual)) => assert_eq!(expected, actual),
                (None, Err(_)) => (),
                (None, Ok(r)) => panic!("Expected an error, got {}", r),
                (Some(expected), Err(e)) => {
                    panic!("Expected {} but got an error ({})", expected, e)
                }
            }
        }
    }

    #[tokio::test]
    async fn test_merge_cwd() {
        #[derive(Debug)]
        struct TestData<'a> {
            container_process_cwd: &'a str,
            image_process_cwd: &'a str,
            expected: &'a str,
        }

        let tests = &[
            // Image cwd should override blank container cwd
            // TODO - how can we tell the user didn't specifically set it to `/` vs not setting at all? Is that scenario valid?
            TestData {
                container_process_cwd: "/",
                image_process_cwd: "/imageDir",
                expected: "/imageDir",
            },
            // Container cwd should override image cwd
            TestData {
                container_process_cwd: "/containerDir",
                image_process_cwd: "/imageDir",
                expected: "/containerDir",
            },
            // Container cwd should override blank image cwd
            TestData {
                container_process_cwd: "/containerDir",
                image_process_cwd: "/",
                expected: "/containerDir",
            },
        ];

        let image_service = ImageService::new();

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let mut container_process = oci::Process {
                cwd: d.container_process_cwd.to_string(),
                ..Default::default()
            };

            let image_process = oci::Process {
                cwd: d.image_process_cwd.to_string(),
                ..Default::default()
            };

            image_service.merge_oci_process(&mut container_process, &image_process);

            assert_eq!(d.expected, container_process.cwd, "{}", msg);
        }
    }

    #[tokio::test]
    async fn test_merge_env() {
        #[derive(Debug)]
        struct TestData {
            container_process_env: Vec<String>,
            image_process_env: Vec<String>,
            expected: Vec<String>,
        }

        let tests = &[
            // Test that the pods environment overrides the images
            TestData {
                container_process_env: vec!["ISPRODUCTION=true".to_string()],
                image_process_env: vec!["ISPRODUCTION=false".to_string()],
                expected: vec!["ISPRODUCTION=true".to_string()],
            },
            // Test that multiple environment variables can be overrided
            TestData {
                container_process_env: vec![
                    "ISPRODUCTION=true".to_string(),
                    "ISDEVELOPMENT=false".to_string(),
                ],
                image_process_env: vec![
                    "ISPRODUCTION=false".to_string(),
                    "ISDEVELOPMENT=true".to_string(),
                ],
                expected: vec![
                    "ISPRODUCTION=true".to_string(),
                    "ISDEVELOPMENT=false".to_string(),
                ],
            },
            // Test that when none of the variables match do not override them
            TestData {
                container_process_env: vec!["ANOTHERENV=TEST".to_string()],
                image_process_env: vec![
                    "ISPRODUCTION=false".to_string(),
                    "ISDEVELOPMENT=true".to_string(),
                ],
                expected: vec![
                    "ANOTHERENV=TEST".to_string(),
                    "ISPRODUCTION=false".to_string(),
                    "ISDEVELOPMENT=true".to_string(),
                ],
            },
            // Test a mix of both overriding and not
            TestData {
                container_process_env: vec![
                    "ANOTHERENV=TEST".to_string(),
                    "ISPRODUCTION=true".to_string(),
                ],
                image_process_env: vec![
                    "ISPRODUCTION=false".to_string(),
                    "ISDEVELOPMENT=true".to_string(),
                ],
                expected: vec![
                    "ANOTHERENV=TEST".to_string(),
                    "ISPRODUCTION=true".to_string(),
                    "ISDEVELOPMENT=true".to_string(),
                ],
            },
        ];

        let image_service = ImageService::new();

        for (i, d) in tests.iter().enumerate() {
            let msg = format!("test[{}]: {:?}", i, d);

            let mut container_process = oci::Process {
                env: d.container_process_env.clone(),
                ..Default::default()
            };

            let image_process = oci::Process {
                env: d.image_process_env.clone(),
                ..Default::default()
            };

            image_service.merge_oci_process(&mut container_process, &image_process);

            assert_eq!(d.expected, container_process.env, "{}", msg);
        }
    }
}
