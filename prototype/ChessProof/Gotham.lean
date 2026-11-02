import ChessProof.Fen
import ChessProof.Cert
import ChessProof.Certs.Gotham

/-!
# The GothamChess "checkmate in 11" position

Black to move. White threatens `Rh8#` and Black cannot parry it; the only way out is
`1...Rxb2+`, which starts a forced mate in 11.

(Position transcribed from the Short https://youtube.com/shorts/KqSqHs6QYJE; Leo vs. Casim.)
-/
namespace ChessProof

def gotham : Pos := fen "2b2bk1/1r3rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/PPP4P/1K4R1 b - - 0 1"

theorem gotham_turn : gotham.turn = .black := by decide +kernel
theorem gotham_move_eq : gotham_move = uci "b7b2" := by decide +kernel

/-- Every certificate is replayed against Lean's own move generator. This uses
`native_decide` (trusts the compiler); `ChessProof.GothamKernel` re-proves the same
facts with kernel-only checks. -/
theorem gotham_check :
    onlyMove 64 10 gotham gotham_move gotham_cert gotham_refutations = true := by
  native_decide

/-- **Mate in 11.** Black to move forces checkmate within 11 Black moves. -/
theorem gotham_mate_in_11 : WinsIn .black 11 gotham := by
  obtain ⟨hmem, hwin, -⟩ := onlyMove_sound gotham_check
  rw [gotham_turn] at hwin
  exact .att _ gotham_turn hmem hwin

/-- **Only move.** Of Black's 34 legal moves, `Rxb2+` is the unique one after which Black
still has a forced win; after each of the other 33, White has a forced mate. -/
theorem gotham_only_move :
    ∀ m ∈ legal gotham, (Wins .black (play gotham m) ↔ m = uci "b7b2") := by
  obtain ⟨-, -, h⟩ := onlyMove_sound gotham_check
  rw [gotham_turn, gotham_move_eq] at h
  exact h

/-- And White cannot force a win from the starting position. -/
theorem gotham_white_cannot_win : ¬ Wins .white gotham :=
  fun ⟨_, h⟩ => not_both gotham_mate_in_11 h

end ChessProof
