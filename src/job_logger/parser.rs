//! Parse a structured log.

use crate::job_logger::{Kind, TrailingNewline};
use anyhow::bail;
use nom::{
    branch::alt,
    bytes::complete::{is_a, is_not, tag, take_until},
    character::complete::{char, digit1},
    combinator::{
        all_consuming, consumed, flat_map, map, map_res, opt, recognize, value,
    },
    error::ParseError,
    multi::{count, many0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, tuple},
    IResult,
};
use std::option::Option;
use std::time::Duration;

/// A record of an event or wrapper error.
#[derive(Clone, Debug)]
pub struct Record {
    /// Time elapsed between start of job and recording the record.
    pub time_offset: Duration,

    /// What kind of record this is. See [`Kind`].
    pub kind: Kind,

    /// The value of the record.
    pub value: Vec<u8>,
}

/// Parse a complete structured log as a big byte string.
///
/// # Errors
///
/// This will return an error when there is a parsing problem.
///
/// # Panics
///
/// This can panic if it gets into what should be an impossible situation.
///
/// For example, it uses a parser that generates an error if it doesn’t consume
/// all of its input. If it finds the parser returned successfully and did not
/// consume all its input, it will panic.
#[allow(clippy::type_complexity)] // Hard to avoid.
pub fn parse_log(
    input: &[u8],
) -> Result<
    (Vec<(&[u8], Vec<u8>)>, Vec<Record>),
    nom::Err<nom::error::Error<&[u8]>>,
> {
    let mut parser = all_consuming(pair(
        metadata_section_parser(),
        map(
            opt(preceded(tag("\n"), many0(record_parser()))),
            Option::unwrap_or_default,
        ),
    ));

    let (rest, (metadata, records)) = parser(input)?;
    assert!(
        rest.is_empty(),
        "Should be impossible: all_consuming() returned trailing data."
    );

    Ok((metadata, records))
}

/// Generate a parser for the metadata section of a structured log.
pub fn metadata_section_parser<'a, E>(
) -> impl FnMut(&'a [u8]) -> IResult<&'a [u8], Vec<(&[u8], Vec<u8>)>, E>
where
    E: ParseError<&'a [u8]>
        + nom::error::FromExternalError<&'a [u8], anyhow::Error>,
{
    many0(separated_pair(
        is_not("\n\r \t:#"),
        tag(": "),
        // The indent for metadata is always 4 characters.
        value_parser(4, TrailingNewline::Explicit),
    ))
}

/// Generate a parser for an event record in a structured log.
pub fn record_parser<'a, E>(
) -> impl FnMut(&'a [u8]) -> IResult<&'a [u8], Record, E>
where
    E: ParseError<&'a [u8]>
        + nom::error::FromExternalError<&'a [u8], anyhow::Error>,
{
    let kind_parser = delimited(
        is_a(" "),
        alt((
            value(Kind::Stdout, tag("out")),
            value(Kind::Stderr, tag("err")),
            value(Kind::Exit, tag("exit")),
            value(Kind::Error, tag("ERROR")),
            value(Kind::WrapperError, tag("WRAPPER-ERROR")),
        )),
        char(' '),
    );

    flat_map(
        // Parse "1.123 out " and note the number of bytes captured, then...
        consumed(tuple((seconds_parser(), kind_parser))),
        // ...parse the remainder of the record (possibly multiple lines) now
        // that we know how long the indent should be.
        |(prefix, (time_offset, kind))| {
            map(
                // The indent should match the length of the prefix.
                value_parser(prefix.len(), kind.newline_behavior()),
                move |value| Record {
                    time_offset,
                    kind,
                    value,
                },
            )
        },
    )
}

/// Generate a parser for a metadata or record value.
pub fn value_parser<'a, E>(
    indent: usize,
    newline: TrailingNewline,
) -> impl FnMut(&'a [u8]) -> IResult<&'a [u8], Vec<u8>, E>
where
    E: ParseError<&'a [u8]>
        + nom::error::FromExternalError<&'a [u8], anyhow::Error>,
{
    map(
        separated_list1(
            // The indent should match the length of the prefix.
            count(char(' '), indent),
            // The rest of the line including the newline character.
            recognize(pair(take_until("\n"), tag("\n"))),
        ),
        move |lines| {
            let value: Vec<u8> = lines.concat();
            unescape_value(value.as_slice(), newline)
        },
    )
}

/// Convert escaped value to its original form.
///
/// This expects `input` to have a trailing newline.
fn unescape_value(input: &[u8], newline: TrailingNewline) -> Vec<u8> {
    /// Get the value of a hex digit [0-9a-f].
    #[inline]
    const fn parse_hex(c: u8) -> Option<u8> {
        // No side effects because the `match` limits the values used in math.
        #[allow(clippy::arithmetic_side_effects)]
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 0x0a),
            _ => None,
        }
    }

    /// Match an escape sequence starting with b'\\'.
    #[inline]
    fn match_escape(input: &[u8]) -> (Option<u8>, usize) {
        match input {
            [b'\\', b'b', ..] => (Some(0x08), 2), // backspace
            [b'\\', b'r', ..] => (Some(b'\r'), 2),
            [b'\\', b'\\', ..] => (Some(b'\\'), 2),
            [b'\\', b'x', h, l, ..] => {
                if let (Some(h), Some(l)) = (parse_hex(*h), parse_hex(*l)) {
                    // h and l are within [0x0..=0xf] so this is always safe.
                    #[allow(clippy::arithmetic_side_effects)]
                    (Some(0x10 * h + l), 4)
                } else {
                    // h and l weren’t both hex digits, so invalid escape.
                    (Some(b'\\'), 1)
                }
            }
            [b'\\', b'\n', ..] => {
                // Backslash at the end of the line: don’t append \n.
                (None, 2)
            }
            [b'\\', ..] => (Some(b'\\'), 1), // Invalid escape
            _ => panic!("input must start with backslash"),
        }
    }

    let mut output = Vec::with_capacity(input.len().checked_add(1).unwrap());
    let mut rest = input;
    let mut iter = rest.iter();
    while let Some(i) = iter.position(|&b| b == b'\\') {
        match match_escape(&rest[i..]) {
            (Some(b'\\'), 1) => {
                // Consume b'\\' and expand to b'\\' is a no-op.
            }
            (expansion, consumed) => {
                output.extend_from_slice(&rest[..i]);
                if let Some(expansion) = expansion {
                    output.push(expansion);
                }
                // `i + consumed` will always be `<= rest.len()`.
                #[allow(clippy::arithmetic_side_effects)]
                let j = i + consumed;
                rest = &rest[j..];
                iter = rest.iter();
            }
        }
    }

    if newline == TrailingNewline::Explicit && rest.ends_with(&b"\n"[..]) {
        // Strip the trailing newline.
        output.extend_from_slice(rest.split_last().unwrap().1);
    } else {
        output.extend_from_slice(rest);
    }

    output
}

/// # Parse "#.###" as seconds.
///
/// The input string may have precision down to nanoseconds, i.e. 9 digits after
/// the decimal point. More digits will cause an error.
pub fn seconds_parser<'a, E>(
) -> impl FnMut(&'a [u8]) -> IResult<&'a [u8], Duration, E>
where
    E: ParseError<&'a [u8]>
        + nom::error::FromExternalError<&'a [u8], anyhow::Error>,
{
    map_res(
        pair(digit1, opt(preceded(tag("."), digit1))),
        bstr_to_duration,
    )
}

/// Take a pair of byte strings `(seconds, fractional_seconds)` and calculate
/// what that is in nanoseconds.
///
/// `fractional_seconds` is the byte string from immediately after the period,
/// so it could have any precision.
///
/// # Errors
///
/// Returns an error if the fractional seconds have more than nanosecond
/// precision, i.e. there are more than 9 digits.
///
/// # Panics
///
/// Panics if the number being parsed wouldn’t fit in a u64, or if any of the
/// input bytes aren’t ASCII digits.
#[allow(clippy::items_after_statements)]
fn bstr_to_duration(
    (seconds, fractional_seconds): (&[u8], Option<&[u8]>),
) -> anyhow::Result<Duration> {
    // FIXME: This should return an error if the full seconds number would
    // overflow, rather than panicking.

    /// Allowable number of digits for decimal seconds.
    const PRECISION: u32 = 9;
    /// 10^PRECISION. Would use `checked_pow()`, but `expect()` is not `const`.
    const PRECISION_POW: (u64, bool) = 10u64.overflowing_pow(PRECISION);
    assert!(!PRECISION_POW.1, "10^PRECISION overflows");
    /// 10^PRECISION, i.e. the reciprocal of the smallest value expressible.
    const RECIP_PRECISION: u64 = PRECISION_POW.0;

    let mut offset = bstr_to_u64(seconds)
        .checked_mul(RECIP_PRECISION)
        .expect("seconds overflow number parser");

    // If there are decimal seconds, convert them to nanoseconds.
    if let Some(fractional_seconds) = fractional_seconds {
        // Get length of decimal seconds as u32.
        let Ok(fraction_len) = u32::try_from(fractional_seconds.len()) else {
            bail!("Found time offset with greater than nanosecond precision.");
        };

        // Figure out precision of provided decimal seconds.
        let Some(precision) = PRECISION.checked_sub(fraction_len) else {
            bail!("Found time offset with greater than nanosecond precision.");
        };

        let precision = 10u64
            .checked_pow(precision)
            .expect("10^precision overflows");

        offset = offset
            .checked_add(
                bstr_to_u64(fractional_seconds)
                    .checked_mul(precision)
                    .expect("overflow increasing precision of decimal seconds"),
            )
            .expect("overflow adding decimal seconds to seconds");
    }

    Ok(Duration::from_nanos(offset))
}

/// Convert a byte string of ASCII digits to a u64.
///
/// # Panics
///
/// Panics if the number being parsed wouldn’t fit in a u64, or if any of
/// the input bytes aren’t ASCII digits.
fn bstr_to_u64(input: &[u8]) -> u64 {
    input.iter().fold(0u64, |sum, digit| {
        let digit = digit.checked_sub(b'0').expect("input not an ASCII digit");
        assert!(digit < 10, "input not an ASCII digit");
        sum.checked_mul(10)
            .expect("number too large")
            .checked_add(digit.into())
            .expect("number too large")
    })
}

#[cfg(test)]
mod tests {
    // Tests just look complicated to clippy.
    #![allow(clippy::cognitive_complexity)]

    use super::*;
    use assert2::{check, let_assert};

    #[test]
    fn bstr_to_duration_normal() {
        // Zero and 100ms
        check!(
            Duration::ZERO
                == bstr_to_duration((&b"0"[..], Some(&b"000000"[..]))).unwrap()
        );
        check!(
            Duration::from_millis(100)
                == bstr_to_duration((&b"0"[..], Some(&b"100"[..]))).unwrap()
        );
    }

    #[test]
    fn bstr_to_duration_milliseconds() {
        // Down to millisecond precision
        check!(
            Duration::from_millis(33_000)
                == bstr_to_duration((&b"33"[..], None)).unwrap()
        );
        check!(
            Duration::from_millis(33_900)
                == bstr_to_duration((&b"33"[..], Some(&b"9"[..]))).unwrap()
        );
        check!(
            Duration::from_millis(33_090)
                == bstr_to_duration((&b"33"[..], Some(&b"09"[..]))).unwrap()
        );
        check!(
            Duration::from_millis(33_009)
                == bstr_to_duration((&b"33"[..], Some(&b"009"[..]))).unwrap()
        );
    }

    #[test]
    fn bstr_to_duration_nanoseconds() {
        check!(
            Duration::from_nanos(1_002_003)
                == bstr_to_duration((&b"0"[..], Some(&b"001002003"[..])))
                    .unwrap()
        );

        let_assert!(
            Err(_) = bstr_to_duration((&b"0"[..], Some(&b"0010020039"[..])))
        );
    }

    /// Helper function to make tests easier to read.
    fn unescape_value_str(input: &str, newline: TrailingNewline) -> String {
        String::from_utf8(unescape_value(input.as_bytes(), newline)).unwrap()
    }

    #[test]
    fn unescape() {
        let nl = TrailingNewline::Explicit;
        check!(unescape_value_str("a\\nb", nl) == "a\\nb");
        check!(unescape_value_str("a\nb", nl) == "a\nb");
        check!(unescape_value_str(r"a\bb", nl) == "a\x08b");
        check!(unescape_value_str(r"a\b\rb", nl) == "a\x08\rb");
        check!(unescape_value_str(r"\x20", nl) == " ");
        check!(unescape_value_str(r"\x00", nl) == "\0");
        check!(unescape_value_str(r"\x0", nl) == "\\x0");
        check!(unescape_value_str(r"\x0a", nl) == "\x0a");
        check!(unescape_value_str(r"\x0A", nl) == "\\x0A");
        check!(unescape_value_str(r"\x0g", nl) == "\\x0g");
        check!(unescape_value_str(r"\x", nl) == "\\x");
        check!(unescape_value_str(r"\xA", nl) == "\\xA");
        check!(unescape_value_str(r"\xA0", nl) == "\\xA0");
        check!(unescape_value_str("", nl) == "");
        check!(unescape_value_str("\\", nl) == "\\");
        check!(unescape_value_str("abc\nxyz", nl) == "abc\nxyz");
        check!(unescape_value_str("abc\\\nxyz", nl) == "abcxyz");
        check!(unescape_value_str("abc\\\\\nxyz", nl) == "abc\\\nxyz");
        check!(unescape_value_str("abc\\\\\\\nxyz", nl) == "abc\\xyz");
    }

    #[test]
    fn unescape_line_ending_output() {
        let nl = TrailingNewline::Implicit;
        check!(unescape_value_str("abc", nl) == "abc");
        check!(unescape_value_str("abc\n", nl) == "abc\n");
        check!(unescape_value_str("abc\\\n", nl) == "abc");
        check!(unescape_value_str("abc\\\\\n", nl) == "abc\\\n");
        check!(unescape_value_str("abc\\\\\\\n", nl) == "abc\\");
    }

    #[test]
    fn unescape_line_ending_non_output() {
        let nl = TrailingNewline::Explicit;
        check!(unescape_value_str("abc", nl) == "abc");
        check!(unescape_value_str("abc\n", nl) == "abc");
        check!(unescape_value_str("abc\\\n", nl) == "abc");
        check!(unescape_value_str("abc\\\\\n", nl) == "abc\\");
        check!(unescape_value_str("abc\\\\\\\n", nl) == "abc\\");
    }

    #[test]
    fn unescape_invalid_utf8() {
        let nl = TrailingNewline::Explicit;
        check!(unescape_value(br"\xff", nl) == &b"\xff"[..]);
    }
}
