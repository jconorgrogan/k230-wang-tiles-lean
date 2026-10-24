module
public import FullBoardBridge
public import BoardChannels
public section
namespace K230Verification
open K230Concrete

/-- FullBoardAt n has geometric level 2*(n+1), not 2*n. -/
theorem fullBoard_half (n : Nat) : boardHalf (n+1) = 2*squareSize n := by
  simp only [boardHalf,Nat.add_sub_cancel,squareSize_power]

theorem fullBoard_side (n : Nat) : 2*boardHalf (n+1) = 4*squareSize n := by
  rw [fullBoard_half]
  omega

/-- TapeGrid parameter k is board parameter k+2; hence its FullBoardAt index is k+1. -/
theorem computingBoard_half (k : Nat) : boardHalf (k+2) = 2*squareSize (k+1) := by
  have he : k+2=(k+1)+1 := by omega
  rw [he]
  exact fullBoard_half (k+1)

theorem computingBoard_side (k : Nat) : 2*boardHalf (k+2) = 4*squareSize (k+1) := by
  rw [computingBoard_half]
  omega

theorem computingBoard_level (k : Nat) : 2*((k+1)+1)=2*(k+2) := by omega

theorem exact_computing_board_occurrence (T : Cell → Fin 11487) (h : FullValid T) (k : Nat) :
    ∃ (v : Nat) (b : Cell), v<4 ∧ FullBoardAt T (k+1) v b :=
  exact_full_board_occurrence T h (k+1)

theorem computing_board_center_seed (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T (k+1) v b) :
    (indexedGroup (T (boardCell b (boardHalf (k+2)) (boardHalf (k+2))))).2.2=5 := by
  rw [computingBoard_half]
  exact full_board_center_seed T (k+1) v b hv hb

theorem computing_board_channel_pattern (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hb : FullBoardAt T (k+1) v b) (x y : Nat)
    (hx : x≤2*boardHalf (k+2)) (hy : y≤2*boardHalf (k+2)) :
    ((indexedFullTile (T (boardCell b x y))).e.2.1≠0 ↔ y%4=1) ∧
    ((indexedFullTile (T (boardCell b x y))).w.2.1≠0 ↔ y%4=1) ∧
    ((indexedFullTile (T (boardCell b x y))).n.2.1≠0 ↔ x%4=1) ∧
    ((indexedFullTile (T (boardCell b x y))).s.2.1≠0 ↔ x%4=1) := by
  rw [computingBoard_side] at hx hy
  exact full_board_channel_pattern T (k+1) v b (by omega) hb x y hx hy

#print axioms fullBoard_half
#print axioms exact_computing_board_occurrence
#print axioms computing_board_center_seed
end K230Verification
