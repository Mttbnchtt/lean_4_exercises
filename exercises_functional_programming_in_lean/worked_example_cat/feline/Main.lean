-- def main : IO Unit :=
--   IO.println s!"Hello, world!"

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

/--
  Recursively processes command-line arguments to handle file and standard input.

  The `process` function takes an initial exit code and a list of command-line arguments, then
  processes each argument one at a time. Its behavior depends on the nature of the argument:

  - **No Arguments (`[]`):**
    When the list of arguments is empty, the function returns the current `exitCode` (wrapped in IO).

  - **Standard Input (`"-" :: args`):**
    If the first argument is the string `"-"`, the function:
      1. Retrieves the standard input stream using `IO.getStdin`.
      2. Calls the `dump` function to read and output the contents of standard input.
      3. Recursively processes the remaining arguments with the current `exitCode`.

  - **Filename (`filename :: args`):**
    If the first argument is interpreted as a filename, the function:
      1. Attempts to open the file by calling `fileStream filename`.
      2. If the file is not found (i.e., `fileStream` returns `none`), it updates the exit code to `1`
         to indicate an error, and then processes the remaining arguments.
      3. If the file is found (i.e., `fileStream` returns `some stream`), it calls `dump stream` to
         output the file's contents, then processes the rest of the arguments using the current `exitCode`.

  Parameters:
  - `exitCode` : A `UInt32` representing the initial exit code, which may be updated if an error occurs.
  - `args` : A list of `String` values representing the command-line arguments. Each argument should be either
             `"-"` (to indicate reading from standard input) or a filename.

  Returns:
  - An IO action producing a `UInt32` that represents the final exit code after processing all arguments.

  Example:
  ```lean
  def main : IO Unit := do
    let exitCode ← process 0 ["-", "file1.txt", "file2.txt"]
    IO.exit exitCode
  -/
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure  exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream (filename)
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

/--
  The main entry point of the program.

  This function processes the command-line arguments supplied to the program and returns an exit
  code wrapped in an IO action. Its behavior is as follows:

  - If no arguments are provided (i.e., when `args` is an empty list), it defaults to reading
    from standard input by invoking `process 0 ["-"]`. The string `"-"` is used as a conventional
    indicator to read from stdin.

  - If arguments are provided, it passes the list of arguments directly to the `process` function
    by calling `process 0 args`.

  Parameters:
  - `args` : A list of strings representing the command-line arguments.

  Returns:
  - An IO action producing a `UInt32` exit code, which typically signals the success or failure
    of the program execution.

  Example:
  ```lean
  def main (args : List String) : IO UInt32 :=
    match args with
    | [] => process 0 ["-"]
    | _ => process 0 args
-/
def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ => process 0 args
