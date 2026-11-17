//! Pauses that double up to a cap, for retrying and polling.

use std::time::Duration;

/// How long to wait before the next try: the first pause, then each twice the last, up to a
/// cap. Starting over after a success is [`Backoff::reset`].
pub struct Backoff {
    first: Duration,
    max: Duration,
    next: Duration,
}

impl Backoff {
    pub fn new(first: Duration, max: Duration) -> Self {
        Self {
            first,
            max,
            next: first,
        }
    }

    /// The pause that [`Backoff::next`] will return, for saying how long it will be.
    pub fn peek(&self) -> Duration {
        self.next
    }

    /// Returns the pause to take now, and doubles the one after it, up to the cap.
    pub fn next(&mut self) -> Duration {
        let now = self.next;
        self.next = (now * 2).min(self.max);
        now
    }

    /// Starts over from the first pause.
    pub fn reset(&mut self) {
        self.next = self.first;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn doubles_up_to_the_cap_and_starts_over() {
        let mut backoff = Backoff::new(Duration::from_secs(1), Duration::from_secs(5));
        let pauses: Vec<u64> = (0..5).map(|_| backoff.next().as_secs()).collect();
        assert_eq!(pauses, [1, 2, 4, 5, 5]);
        backoff.reset();
        assert_eq!(backoff.peek(), Duration::from_secs(1));
    }
}
