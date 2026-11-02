import ChessProof.Fen
import ChessProof.Cert
import ChessProof.Certs.Ply3
import ChessProof.Certs.Ply5
import ChessProof.Certs.Ply6

/-!
# Only-move theorems further along the Gotham line

At Black's moves 3, 5 and 6 of the main line, every alternative loses to a forced White mate,
so the same `onlyMove` certificate shape applies. (Move 4 needs refutations up to a White mate
in 10; moves 2, 7 and 9 have alternatives Stockfish scores as a draw or an unforced advantage,
which no mate tree can refute.)
-/
namespace ChessProof

/-- After `1…Rxb2+ 2.Kc1 Rb1+ 3.Kxb1`. -/
def line3 : Pos := fen "2b2bk1/5rp1/p2p3R/q2Np2Q/4Pp1B/2p2P2/P1P4P/1K4R1 b - - 0 3"
/-- After `3…Qb5+ 4.Nb4 Qxb4+ 5.Kc1`. -/
def line5 : Pos := fen "2b2bk1/5rp1/p2p3R/4p2Q/1q2Pp1B/2p2P2/P1P4P/2K3R1 b - - 1 5"
/-- After `5…Qb2+ 6.Kd1`. -/
def line6 : Pos := fen "2b2bk1/5rp1/p2p3R/4p2Q/4Pp1B/2p2P2/PqP4P/3K2R1 b - - 3 6"

theorem line3_check : onlyMove 64 8 line3 ply3_move ply3_cert ply3_refutations = true := by
  native_decide
theorem line5_check : onlyMove 64 6 line5 ply5_move ply5_cert ply5_refutations = true := by
  native_decide
theorem line6_check : onlyMove 64 5 line6 ply6_move ply6_cert ply6_refutations = true := by
  native_decide

theorem line3_turn : line3.turn = .black := by decide +kernel
theorem line5_turn : line5.turn = .black := by decide +kernel
theorem line6_turn : line6.turn = .black := by decide +kernel
theorem ply3_move_eq : ply3_move = uci "a5b5" := by decide +kernel
theorem ply5_move_eq : ply5_move = uci "b4b2" := by decide +kernel
theorem ply6_move_eq : ply6_move = uci "b2b1" := by decide +kernel

/-- `3…Qb5+` is Black's only move that keeps a forced win; it mates in at most 9. -/
theorem line3_only : WinsIn .black 8 (play line3 (uci "a5b5")) ∧
    ∀ m ∈ legal line3, (Wins .black (play line3 m) ↔ m = uci "a5b5") := by
  obtain ⟨-, hw, h⟩ := onlyMove_sound line3_check
  rw [line3_turn, ply3_move_eq] at hw h
  exact ⟨hw, h⟩

/-- `5…Qb2+` is Black's only move that keeps a forced win; it mates in at most 7. -/
theorem line5_only : WinsIn .black 6 (play line5 (uci "b4b2")) ∧
    ∀ m ∈ legal line5, (Wins .black (play line5 m) ↔ m = uci "b4b2") := by
  obtain ⟨-, hw, h⟩ := onlyMove_sound line5_check
  rw [line5_turn, ply5_move_eq] at hw h
  exact ⟨hw, h⟩

/-- `6…Qb1+` is Black's only move that keeps a forced win; it mates in at most 6. -/
theorem line6_only : WinsIn .black 5 (play line6 (uci "b2b1")) ∧
    ∀ m ∈ legal line6, (Wins .black (play line6 m) ↔ m = uci "b2b1") := by
  obtain ⟨-, hw, h⟩ := onlyMove_sound line6_check
  rw [line6_turn, ply6_move_eq] at hw h
  exact ⟨hw, h⟩

end ChessProof
