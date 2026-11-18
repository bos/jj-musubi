//! Why an independent native merge witness could not qualify.
//!
//! These records explain a deviation after every witness has failed. They never authorize
//! a replay, change fallback order, or enter the actor trace.

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum WitnessKind {
    CapturedMakerInputs,
    CertifiedPrivateBindings,
    NativeDag,
}

impl fmt::Display for WitnessKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::CapturedMakerInputs => "captured maker inputs",
            Self::CertifiedPrivateBindings => "certified private bindings",
            Self::NativeDag => "native DAG",
        })
    }
}

/// A failed prerequisite at the point where the witness stopped qualifying. I/O failures
/// retain their original early return or skipped candidate; no diagnostic retries a read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum RejectionCause {
    NativeMakerMissing,
    RealizationIsNotMaker,
    TwoParentsRequired { found: usize },
    ParentMappingMissing,
    OrderedParentsDiffer,
    SingleBaseRequired { found: usize },
    BaseNotShared,
    BaseMappingMissing,
    BaseSetEmpty,
    BaseIsCandidate,
    BaseCertificatesUnavailable,
    InputMappingMissing,
    CheckedInputMissing,
    CanonicalInputMissing,
    CanonicalViewMissing,
    CopiedInputMissing,
    InputPresenceUnavailable,
    InputAddsVisibleCommits,
    InputOmitsNonWorkspaceCommits,
    WorkspaceOmissionMissing,
    CertifiedInputBindingsDiffer,
    SharedInputDiffers,
    StructuralResultDiffers,
    PrivateMakerMissing,
    MakerNotActive,
    ReadFailed { input: &'static str, error: String },
}

impl fmt::Display for RejectionCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NativeMakerMissing => f.write_str("no native maker maps to this operation"),
            Self::RealizationIsNotMaker => f.write_str("the mapped operation is a realization, not a native maker"),
            Self::TwoParentsRequired { found } => write!(f, "requires two native parents, found {found}"),
            Self::ParentMappingMissing => f.write_str("a native parent has no canonical mapping"),
            Self::OrderedParentsDiffer => f.write_str("native parents do not map to the same ordered canonical parents"),
            Self::SingleBaseRequired { found } => write!(f, "requires one independently checked merge base, found {found}"),
            Self::BaseNotShared => f.write_str("an earlier version's native base is not below both canonical parents"),
            Self::BaseMappingMissing => f.write_str("a native merge base has no canonical mapping"),
            Self::BaseSetEmpty => f.write_str("the native merge has no authenticated base"),
            Self::BaseIsCandidate => f.write_str("a proposed merge base is the candidate operation itself"),
            Self::BaseCertificatesUnavailable => f.write_str("the merge bases' workspace certificates cannot be established independently"),
            Self::InputMappingMissing => f.write_str("a native input has no canonical mapping"),
            Self::CheckedInputMissing => f.write_str("a mapped input has no independently checked canonical view"),
            Self::CanonicalInputMissing => f.write_str("an authenticated canonical input operation is unavailable"),
            Self::CanonicalViewMissing => f.write_str("an authenticated canonical input view is unavailable"),
            Self::CopiedInputMissing => f.write_str("an authenticated input has no reference copy"),
            Self::InputPresenceUnavailable => f.write_str("an input's copy-presence evidence is unavailable"),
            Self::InputAddsVisibleCommits => f.write_str("a native input adds visible commits outside its checked canonical input"),
            Self::InputOmitsNonWorkspaceCommits => f.write_str("a native input omits commits other than working-copy commits"),
            Self::WorkspaceOmissionMissing => f.write_str("the captured inputs have no independently justified workspace-only omission"),
            Self::CertifiedInputBindingsDiffer => f.write_str("native workspace bindings do not bijectively match exact certified input bindings"),
            Self::SharedInputDiffers => f.write_str("a native input's shared structural summary differs from its checked canonical input"),
            Self::StructuralResultDiffers => f.write_str("the native replay's full structural result differs from the candidate"),
            Self::PrivateMakerMissing => f.write_str("the private replay has no authenticated maker"),
            Self::MakerNotActive => f.write_str("the authenticated maker is not an active copy"),
            Self::ReadFailed { input, error } => write!(f, "could not read {input}: {error}"),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct WitnessRejection {
    kind: WitnessKind,
    machine: Option<String>,
    cause: RejectionCause,
}

impl WitnessRejection {
    pub(super) fn new(kind: WitnessKind, machine: Option<&str>, cause: RejectionCause) -> Self {
        Self {
            kind,
            machine: machine.map(str::to_owned),
            cause,
        }
    }
}

impl fmt::Display for WitnessRejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)?;
        if let Some(machine) = &self.machine {
            write!(f, " on {machine}")?;
        }
        write!(f, ": {}", self.cause)
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct WitnessFailures(Vec<WitnessRejection>);

impl WitnessFailures {
    pub(super) fn reject(
        &mut self,
        kind: WitnessKind,
        machine: Option<&str>,
        cause: RejectionCause,
    ) {
        self.0.push(WitnessRejection::new(kind, machine, cause));
    }

    pub(super) fn push(&mut self, rejection: WitnessRejection) {
        self.0.push(rejection);
    }

    pub(super) fn extend(&mut self, failures: Self) {
        self.0.extend(failures.0);
    }

    /// Preserve failures so far when a read stops the entire fallback, as it did before.
    pub(super) fn stopped(&self, kind: WitnessKind, machine: &str, cause: RejectionCause) -> Self {
        let mut failures = self.clone();
        failures.reject(kind, Some(machine), cause);
        failures
    }

    pub(super) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(super) fn contains(&self, kind: WitnessKind, cause: &RejectionCause) -> bool {
        self.0.iter().any(|r| r.kind == kind && r.cause == *cause)
    }
}

impl fmt::Display for WitnessFailures {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, rejection) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str("; ")?;
            }
            write!(f, "{rejection}")?;
        }
        Ok(())
    }
}
