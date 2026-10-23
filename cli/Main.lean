/-
`leanblame`: command-line entry point.
-/
import LeanBlame.Cli.Sha256

def usage : String :=
  "usage: leanblame <command> [args]\n\
   commands: init, export, status, blame, equiv, sign, validate, release"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["-h"] | ["help"] =>
    IO.println usage
    return 0
  | cmd :: _ =>
    IO.eprintln s!"leanblame: {cmd}: not implemented"
    return 2
