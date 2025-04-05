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
