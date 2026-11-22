/-
The conformance oracle (`docs/internals/conformance.md`): reads one JSON request per line on
stdin, writes one JSON reply per line on stdout, flushing after each. `Musubi.Exec.Json.handle`
dispatches on the request's `op`: the session requests (`reset`, `step`, `measure`, `upload`) drive the hive step
machine, and every other request (for example `presence`, `chunks`, `names`, `copies`, `refs`,
`expected`, `publication`, `opHeads`) runs its own executable model on that request alone. The codec
and the dispatch are in `Musubi/ExecJson.lean`; the models are the modules it imports.
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
