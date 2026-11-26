# syntax=docker/dockerfile:1
# The Antithesis workload's images (antithesis/README.md), built from the repository's root:
# `node` runs a hub or a machine, `driver` the driver. Both share the ssh keys made below, so
# build them together, as `docker compose build` in ../config does.

# Jobs for each compiling stage. BuildKit builds the stages at once, so scripts/build.sh gives
# each a share of the machine (AGENTS.md, "Checks").
ARG JOBS=4
ARG RUSTFLAGS_ANTITHESIS='["-Ccodegen-units=1", "-Cpasses=sancov-module", "-Cllvm-args=-sanitizer-coverage-level=3", "-Cllvm-args=-sanitizer-coverage-trace-pc-guard", "-Cllvm-args=-sanitizer-coverage-pc-table", "-Clink-args=-Wl,--build-id"]'

# musubi, instrumented for Antithesis, with its SDK assertions.
FROM rust:1-trixie AS build
ARG RUSTFLAGS_ANTITHESIS
ARG JOBS
WORKDIR /src
COPY . .
RUN --mount=type=cache,target=/usr/local/cargo/registry,id=musubi-registry \
    --mount=type=cache,target=/src/target,id=musubi-target \
    cargo build --release --locked -j "$JOBS" -p jj-musubi --features antithesis \
      --config 'build.target = "x86_64-unknown-linux-gnu"' \
      --config 'profile.release.debug = true' \
      --config "target.x86_64-unknown-linux-gnu.rustflags = ${RUSTFLAGS_ANTITHESIS}" \
 && mkdir -p /out /symbols \
 && cp target/x86_64-unknown-linux-gnu/release/musubi /out/ \
 && cp /out/musubi /symbols/ \
 && nm /symbols/musubi | grep -q 'T antithesis_load_libvoidstar' \
 && readelf -S /symbols/musubi | grep -q __sancov_guards \
 && test "$(readelf -S /symbols/musubi | grep -c debug_info)" -gt 0

# The driver, instrumented too.
FROM rust:1-trixie AS driver-build
ARG RUSTFLAGS_ANTITHESIS
ARG JOBS
WORKDIR /driver
COPY antithesis/musubi/driver/ .
RUN --mount=type=cache,target=/usr/local/cargo/registry,id=musubi-registry \
    --mount=type=cache,target=/driver/target,id=musubi-driver-target \
    cargo build --release --locked -j "$JOBS" \
      --config 'build.target = "x86_64-unknown-linux-gnu"' \
      --config 'profile.release.debug = true' \
      --config "target.x86_64-unknown-linux-gnu.rustflags = ${RUSTFLAGS_ANTITHESIS}" \
 && mkdir -p /out /symbols \
 && cp target/x86_64-unknown-linux-gnu/release/driver /out/ \
 && cp /out/driver /symbols/ \
 && nm /symbols/driver | grep -q 'T antithesis_load_libvoidstar' \
 && readelf -S /symbols/driver | grep -q __sancov_guards

# jj's release, the one musubi builds against.
FROM debian:trixie-slim AS jj
RUN apt-get update && apt-get install -y --no-install-recommends curl ca-certificates \
 && curl -fsSL -o /tmp/jj.tgz \
      https://github.com/jj-vcs/jj/releases/download/v0.47.1/jj-v0.47.1-x86_64-unknown-linux-musl.tar.gz \
 && echo 'd4b657f622ee50929c8916466dfa3d6a6c17a0a32b50e7b2c793707ec9ebcad7  /tmp/jj.tgz' | sha256sum -c \
 && tar xzf /tmp/jj.tgz -C /usr/local/bin ./jj

# OpenSSH's server, from a release whose seccomp sandbox allows `restart_syscall`. Debian
# trixie's 10.0 kills `sshd-auth` with SIGSYS when a container is paused while it sleeps,
# which Antithesis reports as an unexpected crash (antithesis/FINDINGS.md). 10.6p2 has the fix,
# openssh-portable 5f707ab7f9; its tarball's signature was checked against OpenSSH's release
# key before pinning its checksum. It installs over Debian's binaries, keeping Debian's
# config, PAM setup and privilege separation user, and takes Debian's session PATHs, which
# include /usr/local/bin, where musubi is.
FROM debian:trixie-slim AS openssh
ARG JOBS
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential ca-certificates curl libpam0g-dev libssl-dev zlib1g-dev \
 && curl -fsSL -o /tmp/openssh.tar.gz \
      https://cdn.openbsd.org/pub/OpenBSD/OpenSSH/portable/openssh-10.6p2.tar.gz \
 && echo '9ae44872090cf2f06b3cf9ff147e7f16f309671340763ed2f99248398ae29d5b  /tmp/openssh.tar.gz' \
      | sha256sum -c \
 && mkdir /src && tar xzf /tmp/openssh.tar.gz -C /src --strip-components=1 \
 && cd /src \
 && ./configure --prefix=/usr --sysconfdir=/etc/ssh --libexecdir=/usr/lib/openssh \
      --with-pam --with-privsep-path=/run/sshd --with-privsep-user=sshd \
      --with-default-path=/usr/local/bin:/usr/bin:/bin:/usr/games \
      --with-superuser-path=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
 && grep -q 'define SANDBOX_SECCOMP_FILTER 1' config.h \
 && grep -q 'SC_ALLOW(__NR_restart_syscall)' sandbox-seccomp-filter.c \
 && make -j"$JOBS" sshd sshd-session sshd-auth \
 && mkdir -p /out && cp sshd sshd-session sshd-auth /out/

# Keys for this test only: the hosts', the driver's, and the one each machine's musubi
# reaches the hub with.
FROM debian:trixie-slim AS keys
RUN apt-get update && apt-get install -y --no-install-recommends openssh-client \
 && mkdir -p /keys/host/etc/ssh \
 && ssh-keygen -A -f /keys/host \
 && ssh-keygen -q -t ed25519 -N '' -C driver -f /keys/driver \
 && ssh-keygen -q -t ed25519 -N '' -C musubi -f /keys/hub_key \
 && { cat /keys/driver.pub; \
      printf 'restrict,command="musubi hub connect" %s\n' "$(cat /keys/hub_key.pub)"; } \
      > /keys/authorized_keys

FROM debian:trixie-slim AS node
RUN apt-get update && apt-get install -y --no-install-recommends \
      openssh-server openssh-client git ca-certificates curl jq procps iproute2 less \
 && rm -rf /var/lib/apt/lists/*
# dpkg still records Debian's 10.0, which `sshd -V` contradicts: no apt-get may run after
# this, or it could put 10.0 back.
COPY --from=openssh /out/sshd /usr/sbin/sshd
COPY --from=openssh /out/sshd-session /out/sshd-auth /usr/lib/openssh/
COPY --from=jj /usr/local/bin/jj /usr/local/bin/jj
COPY --from=build /out/musubi /usr/local/bin/musubi
COPY --from=build /symbols/ /symbols/
COPY --from=keys /keys/host/etc/ssh/ /etc/ssh/
COPY --from=keys --chmod=600 /keys/driver /root/.ssh/id_ed25519
COPY --from=keys --chmod=600 /keys/authorized_keys /root/.ssh/authorized_keys
COPY --from=keys --chmod=600 /keys/hub_key /root/.local/state/musubi/hub_key
COPY --from=keys /keys/hub_key.pub /root/.local/state/musubi/hub_key.pub
COPY antithesis/musubi/image/ssh_config /root/.ssh/config
COPY antithesis/musubi/image/sshd.conf /etc/ssh/sshd_config.d/antithesis.conf
COPY antithesis/musubi/image/jj-config.toml /root/.config/jj/config.toml
COPY antithesis/musubi/image/gitconfig /root/.gitconfig
COPY --chmod=755 antithesis/musubi/image/entrypoint /usr/local/bin/entrypoint
RUN chmod 700 /root/.ssh /root/.local/state/musubi && mkdir -p /run/sshd
WORKDIR /root
ENTRYPOINT ["/usr/local/bin/entrypoint"]
CMD ["machine"]

FROM node AS driver
COPY --from=driver-build /out/driver /usr/local/bin/driver
COPY --from=driver-build /symbols/driver /symbols/driver
COPY --chmod=755 antithesis/musubi/image/first_start_workload /opt/antithesis/test/v1/main/first_start_workload
CMD ["driver"]

# For the local loop only (scripts/local-run.sh): musubi built for LLVM's source coverage in
# place of Antithesis's instrumentation, and the tools to read what it records.
FROM rust:1-trixie AS coverage-tools
ARG JOBS
RUN rustup component add llvm-tools-preview
WORKDIR /src
COPY . .
RUN --mount=type=cache,target=/usr/local/cargo/registry,id=musubi-registry \
    --mount=type=cache,target=/src/target,id=musubi-coverage-target \
    RUSTFLAGS='-Cinstrument-coverage -Cllvm-args=-runtime-counter-relocation' \
    cargo build --release --locked -j "$JOBS" -p jj-musubi --features antithesis \
      --config 'build.target = "x86_64-unknown-linux-gnu"' \
      --config 'profile.release.debug = true' \
 && mkdir -p /out \
 && cp target/x86_64-unknown-linux-gnu/release/musubi /out/

FROM node AS node-coverage
COPY --from=coverage-tools /out/musubi /usr/local/bin/musubi
