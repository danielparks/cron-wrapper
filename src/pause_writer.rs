use std::io;
use std::io::Write;

/// Whether a writer is running or paused.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum State {
    /// The writer is paused. The content is a buffer containing all data
    /// written while paused.
    Paused(Vec<u8>),

    /// The writer is running. All writes go directly to the output stream.
    Running,
}

impl State {
    fn paused() -> Self {
        Self::Paused(Vec::new())
    }
}

impl Default for State {
    fn default() -> Self {
        Self::paused()
    }
}

/// Object to either buffer or write output from a job.
#[derive(Debug)]
pub struct PausableWriter<W: io::Write> {
    state: State,
    writer: W,
}

impl<W: io::Write> PausableWriter<W> {
    /// Create a new paused `PausableWriter`
    pub fn new(writer: W) -> Self {
        Self {
            state: State::paused(),
            writer,
        }
    }

    /// Whether or not this is paused
    pub fn is_paused(&self) -> bool {
        self.state != State::Running
    }

    /// Unpause the writer: write any buffered data and allow future writes to
    /// pass through.
    pub fn unpause(&mut self) -> io::Result<()> {
        if let State::Paused(buffer) = &self.state {
            self.writer.write_all(buffer)?;
            self.writer.flush()?;
        }

        self.state = State::Running;
        Ok(())
    }

    /// Pause the writer: buffer future writes until unpaused.
    pub fn pause(&mut self) {
        if self.state == State::Running {
            self.state = State::paused();
        }
    }
}

impl<W: io::Write> Write for PausableWriter<W> {
    fn write(&mut self, input: &[u8]) -> io::Result<usize> {
        match &mut self.state {
            State::Running => self.writer.write(input),
            State::Paused(ref mut buffer) => {
                buffer.extend_from_slice(input);
                Ok(input.len())
            }
        }
    }

    /// Flush to writer if running
    ///
    /// If the writer is paused, this has no effect.
    fn flush(&mut self) -> io::Result<()> {
        if self.state == State::Running {
            self.writer.flush()
        } else {
            Ok(())
        }
    }
}
