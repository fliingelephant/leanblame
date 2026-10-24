/-
Canonical printing is linear in the size of a term as a graph, and depends on the tree only.
`test/run.sh` runs this with `lake env lean --run`.
-/
import LeanBlame.Cli.Canon

open Lean

/-- `x` applied to itself `n` times over, every node built afresh: a tree of `2^(n+1) - 1` nodes. -/
def tree : Nat → Expr
  | 0 => .const `x []
  | n + 1 => .app (tree n) (tree n)

/-- The same term with every node shared: a graph of `n + 1` nodes. -/
def graph (n : Nat) : Expr := Id.run do
  let mut e : Expr := .const `x []
  for _ in [0:n] do e := .app e e
  return e

def main : IO Unit := do
  let s := LeanBlame.Canon.print [] (graph 64)
  unless s.length < 1000 do
    throw <| IO.userError s!"printing a graph of 65 nodes took {s.length} characters"
  unless LeanBlame.Canon.print [] (tree 6) == LeanBlame.Canon.print [] (graph 6) do
    throw <| IO.userError "the same tree prints differently with another sharing structure"
  IO.println s!"canonical printing: {s.length} characters for a graph of 65 nodes (2^64 as a tree)"
