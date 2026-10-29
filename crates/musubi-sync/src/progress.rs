//! What a sync is doing, for a command waiting on it to show: the daemon answers it on its
//! control socket. It only observes, so nothing in the protocol depends on it.

use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;

use serde::Deserialize;
use serde::Serialize;

/// What a sync is doing at the moment.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum Activity {
    /// Waiting for the hub to answer.
    #[default]
    Asking,
    /// Sending a request's objects to the hub, by bytes.
    Sending { done: u64, total: u64 },
    /// Receiving a reply's objects from the hub, by bytes.
    Receiving { done: u64, total: u64 },
    /// Adding the objects received to the repository.
    Importing,
    /// Writing the hive's operations into the repository, this many so far.
    Applying { done: u64 },
}

/// The activity of one sync, shared with whoever asks about it.
#[derive(Clone, Debug, Default)]
pub struct Progress(Arc<Mutex<Activity>>);

impl Progress {
    pub fn get(&self) -> Activity {
        *self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub fn set(&self, activity: Activity) {
        *self.0.lock().unwrap_or_else(PoisonError::into_inner) = activity;
    }

    /// Records that `done` bytes of the current transfer have moved.
    pub(crate) fn moved(&self, moved: u64) {
        let mut activity = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        if let Activity::Sending { done, total } | Activity::Receiving { done, total } =
            &mut *activity
        {
            *done = moved.min(*total);
        }
    }
}
