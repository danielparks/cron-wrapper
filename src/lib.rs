//! Miscellaneous useful modules that support cron-wrapper.

#![forbid(unsafe_code)]
#![warn(clippy::nursery, clippy::pedantic)]
#![allow(
    clippy::let_underscore_untyped,
    clippy::manual_string_new,
    clippy::map_unwrap_or,
    clippy::module_name_repetitions
)]
// Require docs on everything
#![warn(missing_docs, clippy::missing_docs_in_private_items)]
// Other restriction lints
#![warn(
    clippy::arithmetic_side_effects,
    clippy::as_underscore,
    clippy::assertions_on_result_states, // see if it makes sense
    clippy::dbg_macro,
    clippy::default_union_representation,
    clippy::empty_structs_with_brackets,
    clippy::filetype_is_file, // maybe?
    clippy::fn_to_numeric_cast_any,
    clippy::format_push_string, // maybe? alternative is fallible.
    clippy::get_unwrap,
    clippy::impl_trait_in_params,
    clippy::integer_division,
    clippy::lossy_float_literal,
    clippy::mem_forget,
    clippy::mixed_read_write_in_expression,
    clippy::multiple_inherent_impl,
    clippy::multiple_unsafe_ops_per_block,
    clippy::mutex_atomic,
    clippy::rc_buffer,
    clippy::rc_mutex,
    clippy::same_name_method,
    clippy::semicolon_inside_block,
    clippy::str_to_string, // maybe?
    clippy::string_to_string,
    clippy::undocumented_unsafe_blocks,
    clippy::unnecessary_safety_doc,
    clippy::unnecessary_self_imports,
    clippy::unneeded_field_pattern,
    clippy::verbose_file_reads
)]

/// Read output from child process as events.
pub mod command;

/// Log all events from a command.
pub mod job_logger;

/// Optionally buffer all writes to a stream until we decide to unpause it.
pub mod pause_writer;

/// Stateful timeouts.
pub mod timeout;
