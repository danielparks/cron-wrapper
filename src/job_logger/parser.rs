//! Parse a structured log.

use crate::job_logger::{Kind, TrailingNewline};
use nom::{
    branch::alt,
    bytes::complete::{is_a, is_not, tag, take_until},
    character::complete::{char, digit1},
    combinator::{
        all_consuming, consumed, flat_map, map, map_res, opt, recognize,
        success, value,
    },
    multi::{count, many0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, tuple},
    IResult,
};
use std::time::Duration;
use thiserror::Error;

/// A record of an event or wrapper error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    /// Time elapsed between start of job and recording the record.
    pub time_offset: Duration,

    /// What kind of record this is. See [`Kind`].
    pub kind: Kind,

    /// The value of the record.
    pub value: Vec<u8>,
}

/// Special errors raised by this parser.
#[derive(Debug, Error)]
pub enum Error {
    /// Time offset was found to have too many digits past the decimal point.
    #[error("Found time offset with smaller than nanosecond precision")]
    SubnanosecondPrecision,

    /// Time offset had > `u64::MAX` seconds.
    #[error("Found time offset exceeding maximum seconds ({})", u64::MAX)]
    TooManySeconds,
}

/// Alias trait for parse errors.
pub trait ParseError<'a>:
    nom::error::ParseError<&'a [u8]>
    + nom::error::FromExternalError<&'a [u8], Error>
{
}

impl<'a, T> ParseError<'a> for T where
    T: nom::error::ParseError<&'a [u8]>
        + nom::error::FromExternalError<&'a [u8], Error>
{
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
    let mut parser = alt((
        all_consuming(separated_pair(
            many0(metadata_line_parser()),
            tag("\n"),
            many0(record_parser()),
        )),
        all_consuming(pair(many0(metadata_line_parser()), success(Vec::new()))),
        all_consuming(pair(success(Vec::new()), many0(record_parser()))),
    ));

    let (rest, (metadata, records)) = parser(input)?;
    assert!(
        rest.is_empty(),
        "Should be impossible: all_consuming() returned trailing data."
    );

    Ok((metadata, records))
}

/// Generate a parser for a metadata line of a structured log.
#[allow(clippy::type_complexity)]
pub fn metadata_line_parser<'a, E>(
) -> impl FnMut(&'a [u8]) -> IResult<&'a [u8], (&'a [u8], Vec<u8>), E>
where
    E: ParseError<'a>,
{
    separated_pair(
        is_not("\n\r \t:#"),
        tag(": "),
        // The indent for metadata is always 4 characters.
        value_parser(4, TrailingNewline::Explicit),
    )
}

/// Generate a parser for an event record in a structured log.
///
/// Input is something like `b"1.123 out value\n"`.
pub fn record_parser<'a, E>(
) -> impl FnMut(&'a [u8]) -> IResult<&'a [u8], Record, E>
where
    E: ParseError<'a>,
{
    let kind_parser = delimited(
        is_a(" "),
        alt((
            value(Kind::Combined, tag("com")),
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
                move |value| Record { time_offset, kind, value },
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
    E: ParseError<'a>,
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
///
/// # Parser errors
///
/// The parser returns an error if:
///
///  * The seconds are are more than [`u64::MAX`].
///  * The fractional seconds have more than nanosecond precision, i.e. there
///    are more than 9 digits.
pub fn seconds_parser<'a, E>(
) -> impl FnMut(&'a [u8]) -> IResult<&'a [u8], Duration, E>
where
    E: ParseError<'a>,
{
    map_res(
        pair(digit1, opt(preceded(tag("."), digit1))),
        bstr_to_duration,
    )
}

/// Convert byte strings `(seconds, fractional_seconds)` to [`Duration`].
///
/// `fractional_seconds` is the byte string from immediately after the period,
/// so it could have any precision up to nanosecond.
///
/// # Errors
///
/// Returns an error if:
///
///  * The seconds are are more than [`u64::MAX`].
///  * The fractional seconds have more than nanosecond precision, i.e. there
///    are more than 9 digits.
///
/// # Panics
///
/// Panics if any of the input bytes aren’t ASCII digits.
#[allow(clippy::items_after_statements)]
fn bstr_to_duration(
    (seconds, fractional_seconds): (&[u8], Option<&[u8]>),
) -> Result<Duration, Error> {
    /// Allowable number of digits for decimal seconds.
    const PRECISION: u32 = 9;

    let seconds = bstr_to_u64(seconds).ok_or(Error::TooManySeconds)?;

    // If there are decimal seconds, convert them to nanoseconds.
    let nanoseconds = if let Some(fractional_seconds) = fractional_seconds {
        // Get length of the decimal seconds string as u32.
        let fraction_len = u32::try_from(fractional_seconds.len())
            .map_err(|_| Error::SubnanosecondPrecision)?;

        // Figure out precision of provided decimal seconds.
        let precision = PRECISION
            .checked_sub(fraction_len)
            .ok_or(Error::SubnanosecondPrecision)?;

        let precision = 10u64.checked_pow(precision).unwrap();
        let nanoseconds = bstr_to_u64(fractional_seconds)
            .unwrap()
            .checked_mul(precision)
            .unwrap();

        u32::try_from(nanoseconds).unwrap()
    } else {
        0u32
    };

    Ok(Duration::new(seconds, nanoseconds))
}

/// Convert a byte string of ASCII digits to a u64.
///
/// # Errors (`None`)
///
/// Returns `None` if the number is too large to fit in a `u64`.
///
/// # Panics
///
/// Panics if any of the input bytes aren’t ASCII digits.
fn bstr_to_u64(input: &[u8]) -> Option<u64> {
    input.iter().try_fold(0u64, |sum, digit| {
        let digit = digit.checked_sub(b'0').expect("input not an ASCII digit");
        assert!(digit < 10, "input not an ASCII digit");
        sum.checked_mul(10)?.checked_add(digit.into())
    })
}

#[cfg(test)]
mod tests {
    // Tests just look complicated to clippy.
    #![allow(clippy::cognitive_complexity)]

    use super::*;
    use assert2::{check, let_assert};

    /// Maximum number of nanoseconds in a Duration, i.e. 1s - 1ns.
    const MAX_NANOS: &str = "999999999";

    /// Wrap [`bstr_to_duration()`] to simplify tests.
    fn str_to_duration<'a, S: Into<Option<&'a str>>>(
        seconds: &str,
        fractional_seconds: S,
    ) -> Result<Duration, Error> {
        bstr_to_duration((
            seconds.as_bytes(),
            fractional_seconds.into().map(str::as_bytes),
        ))
    }

    /// Convenience function to make a [`Duration`] from seconds.
    const fn seconds(seconds: u64) -> Duration {
        Duration::from_secs(seconds)
    }

    /// Convenience function to make a [`Duration`] from milliseconds.
    const fn millis(milliseconds: u64) -> Duration {
        Duration::from_millis(milliseconds)
    }

    /// Convenience function to make a [`Duration`] from nanoseconds.
    const fn nanos(nanoseconds: u64) -> Duration {
        Duration::from_nanos(nanoseconds)
    }

    type NomError<'a> = nom::Err<nom::error::Error<&'a [u8]>>;

    /// Parse a string using `parse_log()`.
    #[allow(clippy::type_complexity)] // Hard to avoid.
    fn parse_log_str(
        input: &str,
    ) -> Result<(Vec<(&str, String)>, Vec<Record>), NomError<'_>> {
        parse_log(input.as_bytes()).map(|(metadata, records)| {
            (
                metadata
                    .iter()
                    .map(|(key, value)| {
                        (
                            std::str::from_utf8(key).unwrap(),
                            String::from_utf8(value.clone()).unwrap(),
                        )
                    })
                    .collect(),
                records,
            )
        })
    }

    #[test]
    fn log_parser_simple() {
        let_assert!(
            Ok((metadata, records)) = parse_log_str(
                "key: value\n\
                \n\
                0.000 exit 0\n"
            )
        );
        check!(metadata.as_slice() == [("key", "value".to_owned())]);
        check!(
            records.as_slice()
                == [Record {
                    time_offset: Duration::ZERO,
                    kind: Kind::Exit,
                    value: b"0".to_vec(),
                }]
        );
    }

    #[test]
    fn log_parser_blank_no_metadata() {
        let_assert!(
            Ok((metadata, records)) = parse_log_str("\n0.001 out foo\n")
        );
        check!(metadata.as_slice() == []);
        check!(
            records.as_slice()
                == [Record {
                    time_offset: millis(1),
                    kind: Kind::Stdout,
                    value: b"foo\n".to_vec(),
                }]
        );
    }

    #[test]
    fn log_parser_no_blank_no_metadata() {
        let_assert!(Ok((metadata, records)) = parse_log_str("1 err bar\\\n"));
        check!(metadata.as_slice() == []);
        check!(
            records.as_slice()
                == [Record {
                    time_offset: seconds(1),
                    kind: Kind::Stderr,
                    value: b"bar".to_vec(),
                }]
        );
    }

    #[test]
    fn log_parser_blank_no_records() {
        let_assert!(Ok((metadata, records)) = parse_log_str("k: v\n\n"));
        check!(metadata.as_slice() == [("k", "v".to_owned())]);
        check!(records.as_slice() == []);
    }

    #[test]
    fn log_parser_no_blank_no_records() {
        let_assert!(Ok((metadata, records)) = parse_log_str("k: v\n"));
        check!(metadata.as_slice() == [("k", "v".to_owned())]);
        check!(records.as_slice() == []);
    }

    #[test]
    fn log_parser_empty() {
        let_assert!(Ok((metadata, records)) = parse_log_str(""));
        check!(metadata.as_slice() == []);
        check!(records.as_slice() == []);
    }

    #[test]
    fn log_parser_just_blank() {
        let_assert!(Ok((metadata, records)) = parse_log_str("\n"));
        check!(metadata.as_slice() == []);
        check!(records.as_slice() == []);
    }

    /// Parse a string using `record_parser()`.
    fn parse_record_str(s: &str) -> Result<(&[u8], Record), NomError<'_>> {
        record_parser()(s.as_bytes())
    }

    /// Generate a `Result<..>` that might be produced by `parse_record_str()`
    /// for comparison.
    #[allow(clippy::unnecessary_wraps)]
    fn record_result<'a>(
        rest: &'a str,
        time_offset: Duration,
        kind: Kind,
        value: &'a str,
    ) -> Result<(&'a [u8], Record), NomError<'a>> {
        let value = value.as_bytes().to_vec();
        Ok((rest.as_bytes(), Record { time_offset, kind, value }))
    }

    #[test]
    fn record_parser_ok() {
        check!(
            parse_record_str("1.123 out value\n")
                == record_result("", millis(1_123), Kind::Stdout, "value\n")
        );
        check!(
            parse_record_str("100 err value\\\nmore")
                == record_result("more", seconds(100), Kind::Stderr, "value")
        );
        check!(
            parse_record_str("0.0 exit 10\nmore")
                == record_result("more", seconds(0), Kind::Exit, "10")
        );
        check!(
            parse_record_str("0.123456 ERROR <error>\nmore")
                == record_result(
                    "more",
                    nanos(123_456_000),
                    Kind::Error,
                    "<error>"
                )
        );
        check!(
            parse_record_str(
                "99.123456789 WRAPPER-ERROR <\\\\error>\n    more"
            ) == record_result(
                "    more",
                nanos(99_123_456_789),
                Kind::WrapperError,
                "<\\error>"
            )
        );
    }

    #[test]
    fn record_parser_ok_multiline() {
        check!(
            parse_record_str("0 out line1\n      line2\nrecord2")
                == record_result(
                    "record2",
                    seconds(0),
                    Kind::Stdout,
                    "line1\nline2\n"
                )
        );
        check!(
            parse_record_str("0 err a\n       b\n")
                == record_result("", seconds(0), Kind::Stderr, "a\n b\n")
        );
        check!(
            parse_record_str("0 ERROR a\n        b\\\n")
                == record_result("", seconds(0), Kind::Error, "a\nb")
        );
        check!(
            parse_record_str("0 out line1\n      line2\n      line3\n")
                == record_result(
                    "",
                    seconds(0),
                    Kind::Stdout,
                    "line1\nline2\nline3\n"
                )
        );
    }

    #[test]
    fn record_parser_err() {
        check!(parse_record_str(".123 out value\n").is_err());
        check!(parse_record_str("0.1234567890 out value\n").is_err());
        check!(
            // u64::MAX =     18446744073709551615
            parse_record_str("99999999999999999999.0 out value\n").is_err()
        );
        check!(parse_record_str("1.1 bad value\n").is_err());
        check!(parse_record_str("1.1 out\n").is_err());
        check!(parse_record_str("1.1 out value").is_err());
        check!(parse_record_str("").is_err());
        check!(parse_record_str("abc").is_err());
    }

    /// Parse a string using `metadata_line_parser()`.
    fn parse_metadata_str(
        s: &str,
    ) -> Result<(&str, (&str, String)), NomError<'_>> {
        let (rest, (key, value)) = metadata_line_parser()(s.as_bytes())?;
        Ok((
            std::str::from_utf8(rest).unwrap(),
            (
                std::str::from_utf8(key).unwrap(),
                String::from_utf8(value).unwrap(),
            ),
        ))
    }

    #[test]
    fn metadata_line_parser_ok() {
        let_assert!(Ok(("", ("key", v))) = parse_metadata_str("key: value\n"));
        check!(v == "value");
        let_assert!(Ok(("", ("key", v))) = parse_metadata_str("key:  v\n"));
        check!(v == " v");
        let_assert!(Ok(("", ("key", v))) = parse_metadata_str("key: b\\b\n"));
        check!(v == "b\x08");
        let_assert!(Ok(("", ("key", v))) = parse_metadata_str("key: \n"));
        check!(v == "");
    }

    #[test]
    fn metadata_line_parser_ok_multiline() {
        let_assert!(
            Ok(("   2\n", ("k", v))) = parse_metadata_str("k: v\n   2\n")
        );
        check!(v == "v");
        let_assert!(Ok(("", ("k", v))) = parse_metadata_str("k: v\n    2\n"));
        check!(v == "v\n2");
        let_assert!(Ok(("", ("k", v))) = parse_metadata_str("k: v\n     2\n"));
        check!(v == "v\n 2");
        let_assert!(
            Ok(("", ("k", v))) = parse_metadata_str("k: v\n    2\n    3\n")
        );
        check!(v == "v\n2\n3");
        let_assert!(Ok(("", ("k", v))) = parse_metadata_str("k: v\n    \n"));
        check!(v == "v\n");
    }

    #[test]
    fn metadata_line_parser_err() {
        check!(parse_metadata_str("key value\n").is_err());
        check!(parse_metadata_str("a b: value\n").is_err());
        check!(parse_metadata_str("#key: value\n").is_err());
        check!(parse_metadata_str("\nkey: value\n").is_err());
        check!(parse_metadata_str(": value\n").is_err());
        check!(parse_metadata_str("key: value").is_err());
    }

    /// Convenience function to get `(u64::MAX + 1)to_string()`.
    #[allow(clippy::arithmetic_side_effects)]
    fn overflow_seconds() -> String {
        (u128::from(u64::MAX) + 1).to_string()
    }

    #[test]
    fn bstr_to_duration_zero() {
        check!(Duration::ZERO == str_to_duration("0", "000000").unwrap());
        check!(Duration::ZERO == str_to_duration("0", None).unwrap());
    }

    #[test]
    fn bstr_to_duration_max() {
        let max_secs = u64::MAX.to_string();
        check!(seconds(u64::MAX) == str_to_duration(&max_secs, None).unwrap());
        check!(Duration::MAX == str_to_duration(&max_secs, MAX_NANOS).unwrap());

        let_assert!(
            Err(Error::TooManySeconds) =
                str_to_duration(&overflow_seconds(), None)
        );
    }

    #[test]
    fn bstr_to_duration_milliseconds() {
        check!(seconds(33) == str_to_duration("33", None).unwrap());
        check!(millis(33_900) == str_to_duration("33", "9").unwrap());
        check!(millis(33_090) == str_to_duration("33", "09").unwrap());
        check!(millis(33_009) == str_to_duration("33", "009").unwrap());
    }

    #[test]
    fn bstr_to_duration_nanoseconds() {
        check!(nanos(1_002_003) == str_to_duration("0", "001002003").unwrap());
        check!(nanos(999_999_999) == str_to_duration("0", MAX_NANOS).unwrap());

        let_assert!(
            Err(Error::SubnanosecondPrecision) =
                str_to_duration("0", "0010020039")
        );
        let_assert!(
            Err(Error::SubnanosecondPrecision) =
                str_to_duration("0", "0010020030")
        );
    }

    #[test]
    fn bstr_to_u64_extremes() {
        check!(Some(0u64) == bstr_to_u64(&b""[..]));
        check!(Some(0u64) == bstr_to_u64(&b"0"[..]));
        check!(Some(u64::MAX) == bstr_to_u64(u64::MAX.to_string().as_bytes()));
        check!(None == bstr_to_u64(overflow_seconds().as_bytes()));
    }

    /// Wrap [`unescape_value()`] to simplify tests.
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
