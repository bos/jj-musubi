use std::fmt::Write as _;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;

use super::Service;
use super::config;
use super::xml_escape;

pub(super) fn user_and_instance() -> anyhow::Result<(String, String)> {
    let user = whoami::username().context("looking up this user's name")?;
    let instance = instance(&user, crate::socket::uid()?);
    Ok((user, instance))
}

/// How long SMF gives the stop method, signalling the daemon to exit, before it kills what's
/// left and puts the instance in maintenance.
pub(super) const STOP_TIMEOUT_SECONDS: u64 = 60;

/// The SMF service that each user's instance of `service` belongs to.
pub(super) fn service_name(service: Service) -> &'static str {
    match service {
        Service::Daemon => "site/musubi/daemon",
        Service::Hub => "site/musubi/hub",
    }
}

pub(super) fn service_fmri(service: Service) -> String {
    format!("svc:/{}", service_name(service))
}

pub(super) fn fmri_of(service: Service, instance: &str) -> String {
    format!("{}:{instance}", service_fmri(service))
}

pub(super) fn fmri(service: Service) -> anyhow::Result<String> {
    Ok(fmri_of(service, &user_and_instance()?.1))
}

pub(super) fn manifest_path(service: Service) -> anyhow::Result<PathBuf> {
    let name = match service {
        Service::Daemon => "smf-daemon.xml",
        Service::Hub => "smf-hub.xml",
    };
    Ok(config::state_dir()?.join(name))
}

/// The SMF instance named after `user`. An instance name starts with a letter, holds only
/// letters, digits, `-` and `_` (libuutil's `uu_check_name`), and is at most 119 bytes
/// (`SCF_LIMIT_MAX_NAME_LENGTH`), so a user name that isn't one gets `uid` and the user's id
/// instead.
pub(super) fn instance(user: &str, uid: u32) -> String {
    let mut chars = user.chars();
    let valid = user.len() <= 119
        && chars.next().is_some_and(|c| c.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_');
    if valid {
        user.to_owned()
    } else {
        format!("uid{uid}")
    }
}

/// Where svc.startd writes an instance's output, as `svcs -L` reports it: the FMRI without
/// `svc:/`, with `/` as `-`.
pub(super) fn log_path(fmri: &str) -> String {
    let name = fmri.strip_prefix("svc:/").unwrap_or(fmri).replace('/', "-");
    format!("/var/svc/log/{name}.log")
}

/// A word for an SMF method's command line. svc.startd expands `%` tokens, then runs the method
/// with `/sbin/sh -c "exec <method>"`, so the word is quoted for sh and its `%`s doubled.
pub(super) fn exec_quote(text: &str) -> String {
    crate::ui::sh_word(text).replace('%', "%%")
}

/// An SMF manifest for one user's instance of `service`. It is wait-style (`duration=child`):
/// svc.startd supervises `exe daemon` (or `exe hub`) and starts it again when it exits. It runs
/// as the user, in `dir` or else their home directory, once the machine reaches multi-user.
///
/// The methods and startd settings belong to the instance, not to the service every user's
/// instance shares, so one user's install never changes what another's runs. A new instance is
/// imported disabled, and `install` enables it only once importing and refreshing it have
/// succeeded, so a failed install starts nothing.
///
/// The start method has no timeout, since a wait-style start method is the daemon itself and
/// never returns.
pub(super) fn manifest(
    service: Service,
    instance: &str,
    user: &str,
    exe: &Path,
    dir: Option<&Path>,
    environment: &[(String, String)],
) -> String {
    let name = service_name(service);
    let exec = xml_escape(&format!(
        "{} {}",
        exec_quote(&exe.to_string_lossy()),
        service.command()
    ));
    let working = dir.map_or_else(
        || ":default".to_owned(),
        |dir| xml_escape(&dir.to_string_lossy()),
    );
    // The DTD requires at least one `envvar` in a `method_environment`, so leave it out when
    // there are none.
    let mut variables = String::new();
    if !environment.is_empty() {
        variables.push_str("\t\t\t\t<method_environment>\n");
        for (variable, value) in environment {
            writeln!(
                variables,
                "\t\t\t\t\t<envvar name=\"{}\" value=\"{}\"/>",
                xml_escape(variable),
                xml_escape(value)
            )
            .expect("writing to a String");
        }
        variables.push_str("\t\t\t\t</method_environment>\n");
    }
    let instance = xml_escape(instance);
    let user = xml_escape(user);
    let description = xml_escape(service.description());
    format!(
        r#"<?xml version="1.0"?>
<!DOCTYPE service_bundle SYSTEM "/usr/share/lib/xml/dtd/service_bundle.dtd.1">
<service_bundle type="manifest" name="musubi">
	<service name="{name}" type="service" version="1">
		<dependency name="multi-user" grouping="require_all" restart_on="none" type="service">
			<service_fmri value="svc:/milestone/multi-user:default"/>
		</dependency>
		<instance name="{instance}" enabled="false">
			<method_context working_directory="{working}">
				<method_credential user="{user}" group=":default"/>
{variables}			</method_context>
			<exec_method type="method" name="start" exec="{exec}" timeout_seconds="0"/>
			<exec_method type="method" name="stop" exec=":kill" timeout_seconds="{STOP_TIMEOUT_SECONDS}"/>
			<property_group name="startd" type="framework">
				<propval name="duration" type="astring" value="child"/>
			</property_group>
		</instance>
		<template>
			<common_name>
				<loctext xml:lang="C">{description}</loctext>
			</common_name>
		</template>
	</service>
</service_bundle>
"#
    )
}
