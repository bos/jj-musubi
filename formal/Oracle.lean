/-
The conformance oracle (`docs/internals/conformance.md`): reads one JSON request per line on
stdin, writes one JSON reply per line on stdout, flushing after each. All protocol logic is in
`Musubi.Exec.execStep`; the codec is `Musubi.Exec.Json`.
-/
import Musubi.ExecJson

open Musubi.Exec.Json

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (sess : Session) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return  -- end of input
  let req := line.trimAscii.toString
  if req.isEmpty then loop stdin stdout sess
  else
    let (reply, sess') := handle sess req
    stdout.putStrLn reply.compress
    stdout.flush
    loop stdin stdout sess'

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout) none
