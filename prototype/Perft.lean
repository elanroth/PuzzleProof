import ChessProof.Basic
import ChessProof.Fen

open ChessProof

/-- `perft <depth> <fen...>` prints the node count; `perft divide <depth> <fen...>` splits it by move. -/
def main (args : List String) : IO Unit := do
  match args with
  | "divide" :: d :: rest =>
    let p := fen (" ".intercalate rest)
    for m in legal p do
      IO.println s!"{m.toUci} {perft (d.toNat! - 1) (play p m)}"
  | d :: rest =>
    IO.println (perft d.toNat! (fen (" ".intercalate rest)))
  | _ => IO.println "usage: perft [divide] <depth> <fen>"
