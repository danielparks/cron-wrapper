//! # Stateful timeouts
//!
//! [`Timeout`] provides a way to keep track of timeout that may or may not have
//! started. It simplifies managing long running timeouts, particularly when
//! they cover a number of function calls that each have their own timeouts.
//!
//! For example, you might want to allow an overall timeout for an entire run of
//! your application. If your application makes calls that have their own
//! timeouts, such as reading from a [`std::net::TcpStream`], you will need to
//! set the timeout for the read correctly so that you don’t exceed the overall
//! timeout.

use std::cmp::Ordering;
use std::fmt;
use std::time::{Duration, Instant};

/// A stateful timeout.
///
/// Create a `Timeout::Future` to represent a planned timeout. Run
/// [`Timeout::start()`] to get a new `Timeout::Pending` that tracks how much
/// time has passed, then call [`Timeout::check_expired()`] on that to get
/// `Timeout::Expired` when the timeout has expired.
///
/// Comparisons between timeouts are based entirely on the remaining timeout.
/// See [`Timeout::cmp()`] for details.
#[derive(Clone, Eq, Debug)]
pub enum Timeout {
    /// Never time out.
    Never,

    /// Time out after `timeout` has elapsed.
    ///
    /// It’s probably most convenient to use [`Timeout::from()`] to create a
    /// timeout. For example:
    ///
    /// ```rust
    /// use assert2::let_assert;
    /// use cron_wrapper::timeout::Timeout;
    /// use std::time::Duration;
    ///
    /// let_assert!(
    ///     Timeout::Future { .. } = Timeout::from(Duration::from_millis(100))
    /// );
    /// ```
    Future {
        /// The length of the timeout.
        timeout: Duration,
    },

    /// A timeout that is counting down.
    ///
    /// Produced by [`Timeout::start()`].
    Pending {
        /// The length of the timeout.
        timeout: Duration,

        /// When the timeout started.
        start: Instant,
    },

    /// A timeout that has expired.
    ///
    /// Produced by [`Timeout::check_expired()`].
    Expired {
        /// The original length of the timeout.
        requested: Duration,

        /// How much time actually elapsed before the operation was canceled.
        actual: Duration,
    },
}

impl Timeout {
    /// Get the remaining timeout if available.
    ///
    /// Returns `Some(Duration::ZERO)` if the timeout has already expired.
    #[must_use]
    pub fn timeout(&self) -> Option<Duration> {
        match &self {
            Self::Never => None,
            Self::Future { timeout } => Some(*timeout),
            Self::Pending { timeout, start } => {
                Some(timeout.saturating_sub(start.elapsed()))
            }
            Self::Expired { .. } => Some(Duration::ZERO),
        }
    }

    /// Return a pending version of this `Timeout`.
    ///
    /// If the timeout is `Never`, `Pending`, or `Expired`, then it returns a
    /// clone of `self`.
    #[must_use]
    pub fn start(&self) -> Self {
        if let Self::Future { timeout } = self {
            Self::Pending {
                timeout: *timeout,
                start: Instant::now(),
            }
        } else {
            self.clone()
        }
    }

    /// Check if the timeout has expired and return [`Timeout::Expired`] if so.
    ///
    /// Returns:
    ///   * `None` if the timeout has not expired.
    ///   * `Some(Timeout::Expired { .. })` if the timeout has expired.
    #[must_use]
    #[inline]
    pub fn check_expired(&self) -> Option<Self> {
        self.check_expired_within(Duration::from_nanos(1))
    }

    /// Check if the timeout has expired (paying attention to resolution) and
    /// return [`Timeout::Expired`] if so.
    ///
    /// This accepts a `resolution` parameter to allow for functions that have
    /// a resolution greater than nanosecond. For example, on UNIX-like systems
    /// [`poll.2`] takes a timeout measured in milliseconds. To check if a
    /// timeout is expired in that context you should pass
    /// [`Duration::from_millis(1)`] as `resolution`.
    ///
    /// Essentially, the check is `timeout - elapsed < resolution`.
    ///
    /// A `resolution` of [`Duration::ZERO`] will be converted to
    /// [`Duration::from_nanos(1)`], since no smaller resolution is possible.
    ///
    /// Returns:
    ///   * `None` if the timeout has not expired.
    ///   * `Some(Timeout::Expired { .. })` if the timeout has expired.
    ///
    /// [`poll.2`]: https://man7.org/linux/man-pages/man2/poll.2.html
    #[must_use]
    pub fn check_expired_within(&self, resolution: Duration) -> Option<Self> {
        // Timeouts cannot be negative, so a resolution of 0
        let resolution = if resolution == Duration::ZERO {
            Duration::from_nanos(1)
        } else {
            resolution
        };

        match &self {
            Self::Pending { timeout, start } => {
                let elapsed = start.elapsed();
                if timeout.saturating_sub(elapsed) < resolution {
                    Some(Self::Expired {
                        requested: *timeout,
                        actual: elapsed,
                    })
                } else {
                    None
                }
            }
            // FIXME better way of doing this?
            Self::Expired { .. } => Some(self.clone()),
            _ => None,
        }
    }

    /// Calculate how much of the timeout has elapsed.
    ///
    /// [`Timeout::Never`] and [`Timeout::Future`] both always return
    /// [`Duration::ZERO`].
    ///
    /// This will not do anything special if called on a [`Timeout::Pending`]
    /// that has expired. See [`Timeout::check_expired()`].
    #[must_use]
    pub fn elapsed(&self) -> Duration {
        match &self {
            Self::Never | Self::Future { .. } => Duration::ZERO,
            Self::Pending { start, .. } => start.elapsed(),
            Self::Expired { actual, .. } => *actual,
        }
    }

    /// Calculate how much of the timeout has elapsed, rounded to the nearest
    /// `factor` of time.
    ///
    /// For example, if `factor` is `Duration::from_millis(1)`, then it will
    /// round the elapsed time to the nearest millisecond.
    ///
    /// [`Timeout::Never`] and [`Timeout::Future`] both always return
    /// [`Duration::ZERO`].
    ///
    /// This will not do anything special if called on a [`Timeout::Pending`]
    /// that has expired. See [`Timeout::check_expired()`].
    #[must_use]
    pub fn elapsed_rounded_to(&self, factor: Duration) -> Duration {
        round_duration(self.elapsed(), factor)
    }

    /// Will this never time out?
    ///
    /// Returns `true` for [`Timeout::Never`] and `false` for everything else.
    #[must_use]
    pub const fn is_never(&self) -> bool {
        matches!(self, Self::Never)
    }
}

/// Round a `Duration` to the nearest `factor`.
///
/// # Panics
///
/// Panics if `factor` is 0.
#[inline]
fn round_duration(input: Duration, factor: Duration) -> Duration {
    let nanos = input.as_nanos();
    let factor = factor.as_nanos();

    assert_ne!(factor, 0, "0 is invalid factor for round_duration()");
    #[allow(clippy::arithmetic_side_effects)]
    let remainder = nanos % factor;

    // remainder <= nanos
    #[allow(clippy::arithmetic_side_effects)]
    let base = nanos - remainder;

    #[allow(clippy::integer_division)]
    let rounded = if remainder < factor / 2 {
        base
    } else {
        // Worst case:
        //     remainder = factor/2 - 1
        //     input = Duration::MAX - factor/2 - 1
        // FIXME think this through
        base.checked_add(factor).unwrap()
    };

    nanos_to_duration(rounded)
}

/// Create a new [`Duration`] from a `u128` of nanoseconds.
///
/// This is essentially just [`Duration::from_nanos()`] but it works on a
/// `u128`, which can represent any valid `Duration`.
///
/// # Panics
///
/// `Duration` can only represent 64 bits worth of seconds and less than 32 bits
/// (1e9) worth of nanoseconds, which works out to being roughly 94 bits. A
/// `u128` can therefore represent values that are invalid `Duration`s. This
/// will panic in those cases.
fn nanos_to_duration(total: u128) -> Duration {
    /// Just to make things clear.
    const NANOS_PER_SECOND: u128 = 1_000_000_000;
    #[allow(clippy::integer_division)]
    Duration::new(
        (total / NANOS_PER_SECOND).try_into().expect(
            "nanos_to_duration() overflowed seconds value for Duration",
        ),
        (total % NANOS_PER_SECOND).try_into().unwrap(),
    )
}

impl fmt::Display for Timeout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Self::Never => write!(f, "Never"),
            Self::Future { timeout } => {
                write!(f, "Future({timeout:?})")
            }
            Self::Pending { timeout, start } => {
                write!(
                    f,
                    "Pending({:?}, {:?} remaining)",
                    timeout,
                    timeout.saturating_sub(start.elapsed()),
                )
            }
            Self::Expired { requested, actual } => {
                write!(f, "Expired({requested:?} requested, {actual:?} actual)")
            }
        }
    }
}

impl From<Duration> for Timeout {
    fn from(timeout: Duration) -> Self {
        Self::Future { timeout }
    }
}

impl From<Option<Duration>> for Timeout {
    fn from(timeout: Option<Duration>) -> Self {
        timeout.map(Self::from).unwrap_or(Self::Never)
    }
}

impl Ord for Timeout {
    /// This method returns an [`Ordering`] between `self` and `other`.
    ///
    /// This comparison is made entirely based on timeout remaining. For
    /// example, a running timeout ([`Timeout::Pending`]) that has 5 seconds
    /// remaining is greater than a future timeout ([`Timeout::Future`]) of 1
    /// second. A running timeout of 1 second is less than a future timeout of
    /// 5 seconds.
    ///
    /// [`Timeout::Expired`] all have 0 seconds remaining and are all equal
    /// regardless of the amount of time elapsed.
    ///
    /// [`Timeout::Never`] are all treated as infinite; they are greater than
    /// all other timeouts and equal to all other `Timeout::Never`s.
    ///
    /// `self.cmp(&other)` returns `Ordering::Greater` if `self > other`.
    ///
    /// [Read more](Ord::cmp())
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.timeout(), other.timeout()) {
            (None, None) => Ordering::Equal,
            (None, _) => Ordering::Greater,
            (_, None) => Ordering::Less,
            (Some(a), Some(b)) => a.cmp(&b),
        }
    }
}

impl PartialOrd for Timeout {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Timeout {
    fn eq(&self, other: &Self) -> bool {
        self.timeout().eq(&other.timeout())
    }
}

#[cfg(test)]
mod tests {
    // This triggers for the various compare_ tests.
    #![allow(clippy::cognitive_complexity)]

    use super::*;
    use assert2::check;
    use std::time::Duration;

    const fn future_timeout(microseconds: u64) -> Timeout {
        Timeout::Future {
            timeout: Duration::from_micros(microseconds),
        }
    }

    fn pending_timeout(microseconds: u64, elapsed: u64) -> Timeout {
        Timeout::Pending {
            timeout: Duration::from_micros(microseconds),
            start: Instant::now()
                .checked_sub(Duration::from_micros(elapsed))
                .unwrap(),
        }
    }

    const fn expired_timeout(microseconds: u64) -> Timeout {
        Timeout::Expired {
            requested: Duration::from_micros(microseconds),
            actual: Duration::from_micros(microseconds),
        }
    }

    /// Convenience constant for 1 millisecond.
    const MS: Duration = Duration::from_millis(1);

    #[test]
    fn elapsed_rounded_up() {
        check!(
            expired_timeout(1_500).elapsed_rounded_to(MS).as_micros() == 2_000
        );
    }

    #[test]
    fn elapsed_rounded_exact() {
        check!(
            expired_timeout(2_000).elapsed_rounded_to(MS).as_micros() == 2_000
        );
    }

    #[test]
    fn elapsed_rounded_down() {
        check!(
            expired_timeout(2_499).elapsed_rounded_to(MS).as_micros() == 2_000
        );
    }

    #[test]
    fn compare_timeout_never() {
        let timeout = Timeout::Never;

        check!(Timeout::Never == timeout);
        check!(future_timeout(5_000) < timeout);
        check!(pending_timeout(5_000, 500) < timeout);
        check!(pending_timeout(5_000, 5_500) < timeout);
        check!(future_timeout(0) < timeout);
        check!(expired_timeout(5_000) < timeout);

        check!(timeout == Timeout::Never);
        check!(timeout > future_timeout(5_000));
        check!(timeout > pending_timeout(5_000, 500));
        check!(timeout > pending_timeout(5_000, 5_500));
        check!(timeout > future_timeout(0));
        check!(timeout > expired_timeout(5_000));
    }

    #[test]
    fn compare_timeout_future() {
        let timeout = future_timeout(5_000);

        check!(Timeout::Never > timeout);
        check!(future_timeout(5_000) == timeout);
        check!(pending_timeout(5_000, 500) < timeout);
        check!(pending_timeout(5_000, 5_500) < timeout);
        check!(future_timeout(0) < timeout);
        check!(expired_timeout(5_000) < timeout);

        check!(timeout < Timeout::Never);
        check!(timeout == future_timeout(5_000));
        check!(timeout > pending_timeout(5_000, 500));
        check!(timeout > pending_timeout(5_000, 5_500));
        check!(timeout > future_timeout(0));
        check!(timeout > expired_timeout(5_000));
    }

    #[test]
    fn compare_timeout_pending() {
        let timeout = pending_timeout(5_000, 1000);

        check!(Timeout::Never > timeout);
        check!(future_timeout(5_000) > timeout);
        check!(pending_timeout(5_000, 500) > timeout);
        check!(pending_timeout(5_000, 5_500) < timeout);
        check!(future_timeout(0) < timeout);
        check!(expired_timeout(5_000) < timeout);

        check!(timeout < Timeout::Never);
        check!(timeout < future_timeout(5_000));
        check!(timeout < pending_timeout(5_000, 500));
        check!(timeout > pending_timeout(5_000, 5_500));
        check!(timeout > future_timeout(0));
        check!(timeout > expired_timeout(5_000));
    }

    #[test]
    fn compare_timeout_pending_overtime() {
        let timeout = pending_timeout(5_000, 6_000);

        check!(Timeout::Never > timeout);
        check!(future_timeout(5_000) > timeout);
        check!(pending_timeout(5_000, 500) > timeout);
        check!(pending_timeout(5_000, 5_500) == timeout);
        check!(future_timeout(0) == timeout);
        check!(expired_timeout(5_000) == timeout);

        check!(timeout < Timeout::Never);
        check!(timeout < future_timeout(5_000));
        check!(timeout < pending_timeout(5_000, 500));
        check!(timeout == pending_timeout(5_000, 5_500));
        check!(timeout == future_timeout(0));
        check!(timeout == expired_timeout(5_000));
    }

    #[test]
    fn compare_timeout_expired() {
        let timeout = expired_timeout(5_000);

        check!(Timeout::Never > timeout);
        check!(future_timeout(5_000) > timeout);
        check!(pending_timeout(5_000, 500) > timeout);
        check!(pending_timeout(5_000, 5_500) == timeout);
        check!(future_timeout(0) == timeout);
        check!(expired_timeout(5_000) == timeout);

        check!(timeout < Timeout::Never);
        check!(timeout < future_timeout(5_000));
        check!(timeout < pending_timeout(5_000, 500));
        check!(timeout == pending_timeout(5_000, 5_500));
        check!(timeout == future_timeout(0));
        check!(timeout == expired_timeout(5_000));
    }

    #[test]
    fn check_expired_timeout_never() {
        check!(Timeout::Never.check_expired() == None);
    }

    #[test]
    fn check_expired_timeout_future() {
        check!(future_timeout(1_000).check_expired() == None);
    }

    #[test]
    fn check_expired_timeout_pending() {
        check!(pending_timeout(5_000, 1_000).check_expired() == None);
        check!(
            let Some(Timeout::Expired { .. }) =
                pending_timeout(5_000, 5_001).check_expired()
        );
    }

    #[test]
    fn check_expired_within_timeout_pending() {
        let resolution = Duration::from_millis(1);
        // This is not exact because `pending_timeout()` has to generate an
        // `Instant`, so the elapsed time grows as the test continues.
        check!(
            pending_timeout(5_000, 3_900).check_expired_within(resolution)
                == None
        );
        check!(
            let Some(Timeout::Expired { .. }) =
                pending_timeout(5_000, 4_001).check_expired_within(resolution)
        );
    }

    #[test]
    fn check_expired_timeout_expired() {
        let timeout = expired_timeout(5_000);
        check!(timeout.check_expired() == Some(timeout));
    }

    /// Convenient alias for [`Duration::from_millis()`].
    const fn ms(ms: u64) -> Duration {
        Duration::from_millis(ms)
    }

    #[test]
    fn round_duration_ms_factor() {
        check!(ms(10) == round_duration(ms(10), ms(1)));

        check!(ms(10) == round_duration(ms(10), ms(2)));
        check!(ms(10) == round_duration(ms(9), ms(2)));

        check!(ms(9) == round_duration(ms(9), ms(3)));
        check!(ms(9) == round_duration(ms(10), ms(3)));
        check!(ms(12) == round_duration(ms(11), ms(3)));
        check!(ms(12) == round_duration(ms(12), ms(3)));

        // Round values > 1 second
        check!(ms(1_010) == round_duration(ms(1_010), ms(1)));

        check!(ms(1_010) == round_duration(ms(1_010), ms(2)));
        check!(ms(1_010) == round_duration(ms(1_009), ms(2)));

        check!(ms(1_008) == round_duration(ms(1_008), ms(3)));
        check!(ms(1_008) == round_duration(ms(1_009), ms(3)));
        check!(ms(1_011) == round_duration(ms(1_010), ms(3)));
        check!(ms(1_011) == round_duration(ms(1_011), ms(3)));
    }

    #[test]
    fn round_duration_second_factor() {
        check!(ms(0) == round_duration(ms(499), ms(1_000)));
        check!(ms(1_000) == round_duration(ms(500), ms(1_000)));
        check!(ms(1_000) == round_duration(ms(1_010), ms(1_000)));
        check!(ms(1_000) == round_duration(ms(1_499), ms(1_000)));
        check!(ms(2_000) == round_duration(ms(1_500), ms(1_000)));

        check!(ms(1_001) == round_duration(ms(1_000), ms(1_001)));
        check!(ms(1_001) == round_duration(ms(1_001), ms(1_001)));
        check!(ms(1_001) == round_duration(ms(1_002), ms(1_001)));
    }

    #[test]
    fn round_duration_giant_factor() {
        check!(ms(0) == round_duration(ms(1_000_000), Duration::MAX));
        check!(Duration::MAX == round_duration(Duration::MAX, Duration::MAX));
    }

    #[test]
    #[should_panic]
    fn round_duration_zero_factor() {
        round_duration(ms(10), ms(0));
    }

    /// Theoretical maximum Duration as nanoseconds (based on u64 for seconds).
    const NANOS_MAX: u128 = u64::MAX as u128 * 1_000_000_000 + 999_999_999;

    #[test]
    #[allow(clippy::arithmetic_side_effects)]
    fn nanos_to_duration_ok() {
        check!(Duration::ZERO == nanos_to_duration(0));
        check!(Duration::new(1, 1) == nanos_to_duration(1_000_000_001));

        // Check Duration::MAX two ways, since according it its docs it can vary
        // based on platform.
        check!(Duration::MAX == nanos_to_duration(Duration::MAX.as_nanos()));
        check!(
            Duration::new(u64::MAX, 999_999_999)
                == nanos_to_duration(NANOS_MAX)
        );
    }

    #[test]
    #[should_panic]
    fn nanos_to_duration_overflow() {
        nanos_to_duration(Duration::MAX.as_nanos() + 1);
    }

    #[test]
    #[should_panic]
    #[allow(clippy::arithmetic_side_effects)]
    fn nanos_to_duration_overflow_manual() {
        // One over the maximum duration. Just in case `Duration::MAX` is some
        // other value, since the docs say it can vary by platform even if it
        // currently is always `u64::MAX * 1_000_000_000 + 999_999_999`.
        nanos_to_duration(NANOS_MAX + 1);
    }
}
