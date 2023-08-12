//! # Roundable values
//!
//! This provides and implementation of rounding for various values, including
//! [`std::time::Duration`].

use std::time::Duration;

/// Add methods to round to an arbitrary factor.
///
/// For example, you might wish to round an integer to the nearest 10s:
///
/// ```rust
/// use cron_wrapper::roundable::Roundable;
///
/// assert!(310 == 314.round_to(10));
/// assert!(300 == 314.round_to(100));
/// ```
pub trait Roundable: Sized {
    /// Round to the nearest `factor`.
    #[must_use]
    fn round_to(&self, factor: Self) -> Self {
        self.try_round_to(factor).expect("overflow while rounding")
    }

    /// Round to the nearest `factor`.
    #[must_use]
    fn try_round_to(&self, factor: Self) -> Option<Self>;
}

/// Implement rounding for numeric types.
macro_rules! roundable_num {
    ($($ty:ident)+) => {
        $(
        impl Roundable for $ty {
            fn try_round_to(&self, factor: Self) -> Option<Self> {
                // FIXME: make into error
                assert!(factor > 0, "try_round_to() requires positive factor");

                #[allow(clippy::arithmetic_side_effects)]
                let remainder = self % factor;

                // remainder <= self
                #[allow(clippy::arithmetic_side_effects)]
                let base = self - remainder;

                #[allow(clippy::integer_division)]
                if remainder < factor / 2 {
                    Some(base)
                } else {
                    base.checked_add(factor)
                }
            }
        }
        )+
    }
}

roundable_num!(i8 i16 i32 i64 i128 isize);
roundable_num!(u8 u16 u32 u64 u128 usize);

impl Roundable for Duration {
    fn try_round_to(&self, factor: Self) -> Option<Self> {
        // Duration will always fit into u128 as nanoseconds.
        self.as_nanos()
            .try_round_to(factor.as_nanos())
            .map(nanos_to_duration)
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use assert2::check;
    use std::time::Duration;

    /// Convenient alias for [`Duration::from_millis()`].
    const fn ms(ms: u64) -> Duration {
        Duration::from_millis(ms)
    }

    #[test]
    fn round_millisecond_to_nearest_millisecond() {
        check!(ms(10) == ms(10).round_to(ms(1)));

        check!(ms(10) == ms(10).round_to(ms(2)));
        check!(ms(10) == ms(9).round_to(ms(2)));

        check!(ms(9) == ms(9).round_to(ms(3)));
        check!(ms(9) == ms(10).round_to(ms(3)));
        check!(ms(12) == ms(11).round_to(ms(3)));
        check!(ms(12) == ms(12).round_to(ms(3)));
    }

    #[test]
    fn round_second_to_nearest_millisecond() {
        check!(ms(1_010) == ms(1_010).round_to(ms(1)));

        check!(ms(1_010) == ms(1_010).round_to(ms(2)));
        check!(ms(1_010) == ms(1_009).round_to(ms(2)));

        check!(ms(1_008) == ms(1_008).round_to(ms(3)));
        check!(ms(1_008) == ms(1_009).round_to(ms(3)));
        check!(ms(1_011) == ms(1_010).round_to(ms(3)));
        check!(ms(1_011) == ms(1_011).round_to(ms(3)));
    }

    #[test]
    fn round_second_to_nearest_second() {
        check!(ms(0) == ms(499).round_to(ms(1_000)));
        check!(ms(1_000) == ms(500).round_to(ms(1_000)));
        check!(ms(1_000) == ms(1_010).round_to(ms(1_000)));
        check!(ms(1_000) == ms(1_499).round_to(ms(1_000)));
        check!(ms(2_000) == ms(1_500).round_to(ms(1_000)));

        check!(ms(1_001) == ms(1_000).round_to(ms(1_001)));
        check!(ms(1_001) == ms(1_001).round_to(ms(1_001)));
        check!(ms(1_001) == ms(1_002).round_to(ms(1_001)));
    }

    #[test]
    fn round_to_giant_factor() {
        check!(ms(0) == ms(1_000_000).round_to(Duration::MAX));
        check!(Duration::MAX == Duration::MAX.round_to(Duration::MAX));
    }

    #[test]
    #[should_panic]
    fn round_to_zero_factor() {
        let _ = ms(10).round_to(ms(0));
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
