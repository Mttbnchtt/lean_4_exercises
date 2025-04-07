def main : IO Unit :=
  IO.println s!"Hello, world!"

def bufsize : USize := 20 * 1024

/--
  Recursively reads data from the given stream and writes it to the standard output.

  The function works as follows:
  1. It reads up to `bufsize` bytes from the stream into a buffer.
  2. If the buffer is empty (i.e., end-of-stream is reached), it returns `pure ()`,
     ending the recursion.
  3. Otherwise, it retrieves the standard output stream using `IO.getStdout`,
     writes the contents of the buffer to the output, and then recursively calls itself
     to continue reading from the stream.

  Note: This function is marked `partial` because its recursive nature prevents Lean’s termination
  checker from verifying termination, even though it will stop once the stream is fully read.
-/
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream


/--
  Opens a file for reading and returns an IO stream wrapped in an Option.

  The function first checks if the file at the given `filename` exists. If the file does not exist,
  it writes an error message to the standard error stream and returns `none`. Otherwise, it opens the file
  in read mode, obtains a file handle, converts it into an IO stream, and returns that stream wrapped in `some`.

  Parameters:
  - `filename` : The path to the file to be opened.

  Returns:
  - An IO action producing an `Option IO.FS.Stream`. If the file exists, the action returns `some stream`;
    if not, it returns `none`.
-/
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    -- This line creates a file handle by calling IO.FS.Handle.mk with the filename and
    -- the mode IO.FS.Mode.read, which opens the file for reading.
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    -- The function then converts the file handle into an IO stream using IO.FS.Stream.ofHandle handle.
    -- It wraps this stream in some to indicate success, and then returns it (again, using pure to lift it into the IO monad).
    pure (some (IO.FS.Stream.ofHandle handle))

def process
