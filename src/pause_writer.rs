use std::fmt;
use std::io;
use std::io::Write;
use termcolor::{
    Buffer, BufferWriter, ColorChoice, StandardStream, WriteColor,
};

/// Object to either buffer or write output from a job.
pub struct PausableWriter {
    paused: bool,
    writer: StandardStream,
    buffer_writer: BufferWriter,
    buffer: Buffer,
}

impl PausableWriter {
    /// Create a new paused `PausableWriter` for stdout
    #[must_use]
    pub fn stdout(color_choice: ColorChoice) -> Self {
        let buffer_writer = BufferWriter::stdout(color_choice);
        let buffer = buffer_writer.buffer();
        Self {
            paused: true,
            writer: StandardStream::stdout(color_choice),
            buffer_writer,
            buffer,
        }
    }

    /// Whether or not this is paused
    pub fn is_paused(&self) -> bool {
        self.paused
    }

    /// Unpause the writer: write any buffered data and allow future writes to
    /// pass through.
    ///
    /// # Errors
    ///
    /// This may return errors from writing or flushing the writer.
    pub fn unpause(&mut self) -> io::Result<()> {
        if self.paused {
            self.buffer_writer.print(&self.buffer)?;
            self.buffer.clear();
            self.writer.flush()?; // FIXME? does this make sense?
        }

        self.paused = false;
        Ok(())
    }

    /// Pause the writer: buffer future writes until unpaused.
    pub fn pause(&mut self) {
        self.paused = true;
    }

    /// Either pause or unpause the writer based on the parameter.
    ///
    /// # Errors
    ///
    /// This may return errors from writing or flushing the writer when setting
    /// to unpaused (`set_paused(false)`).
    pub fn set_paused(&mut self, paused: bool) -> io::Result<()> {
        if paused {
            self.pause();
            Ok(())
        } else {
            self.unpause()
        }
    }
}

impl fmt::Debug for PausableWriter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PausableWriter")
            .field("paused", &self.paused)
            .finish()
    }
}

impl Write for PausableWriter {
    fn write(&mut self, input: &[u8]) -> io::Result<usize> {
        if self.paused {
            self.buffer.write(input)
        } else {
            self.writer.write(input)
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.paused {
            self.buffer.flush()
        } else {
            self.writer.flush()
        }
    }
}

impl WriteColor for PausableWriter {
    fn supports_color(&self) -> bool {
        if self.paused {
            self.buffer.supports_color()
        } else {
            self.writer.supports_color()
        }
    }

    fn set_color(&mut self, spec: &termcolor::ColorSpec) -> io::Result<()> {
        if self.paused {
            self.buffer.set_color(spec)
        } else {
            self.writer.set_color(spec)
        }
    }

    fn reset(&mut self) -> io::Result<()> {
        if self.paused {
            self.buffer.reset()
        } else {
            self.writer.reset()
        }
    }

    fn is_synchronous(&self) -> bool {
        if self.paused {
            self.buffer.is_synchronous()
        } else {
            self.writer.is_synchronous()
        }
    }
}
