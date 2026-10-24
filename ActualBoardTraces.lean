module
public import EntryIndices
public import FreeActualChannels
public import ChannelRouting
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem root_boundary_unblocked (N : Nat) :
    ¬BlockedOffset N (boardHalf N : Int) ∧ ¬BlockedOffset N (-(boardHalf N : Int)) := by
  constructor
  · rintro ⟨m,hm,hmN,hb⟩
    have hd := lower_period_dvd_half hm hmN
    have hz := Int.emod_eq_zero_of_dvd hd
    have hp : (0:Int)<boardHalf m := by have := board_half_pos m; omega
    unfold RedBand at hb
    omega
  · rintro ⟨m,hm,hmN,hb⟩
    have hd := Int.dvd_neg.mpr (lower_period_dvd_half hm hmN)
    have hz := Int.emod_eq_zero_of_dvd hd
    have hp : (0:Int)<boardHalf m := by have := board_half_pos m; omega
    unfold RedBand at hb
    omega

theorem boardCovered_swap_closed (N : Nat) (r s : Int)
    (hr : -(boardHalf N:Int)≤r ∧ r≤boardHalf N)
    (hs : -(boardHalf N:Int)≤s ∧ s≤boardHalf N) :
    BoardCovered N r s ↔ BoardCovered N s r := by
  have hbd := root_boundary_unblocked N
  constructor
  · rintro ⟨hl,hu,m,hm,hmN,hbr,hbs⟩
    have hblock : BlockedOffset N r := ⟨m,hm,hmN,hbr⟩
    have hlo : r≠-(boardHalf N:Int) := by intro he; rw [he] at hblock; exact hbd.2 hblock
    have hhi : r≠(boardHalf N:Int) := by intro he; rw [he] at hblock; exact hbd.1 hblock
    exact ⟨by omega,by omega,m,hm,hmN,hbs,hbr⟩
  · rintro ⟨hl,hu,m,hm,hmN,hbs,hbr⟩
    have hblock : BlockedOffset N s := ⟨m,hm,hmN,hbs⟩
    have hlo : s≠-(boardHalf N:Int) := by intro he; rw [he] at hblock; exact hbd.2 hblock
    have hhi : s≠(boardHalf N:Int) := by intro he; rw [he] at hblock; exact hbd.1 hblock
    exact ⟨by omega,by omega,m,hm,hmN,hbr,hbs⟩

/-- The actual vertical obstruction channel satisfies the full segment rule.
    No endpoint or copying premise remains: all come from the exact full tile table
    and the concrete canonical-board occurrence in the same tiling. -/
theorem fullBoard_vertical_segment (T : Cell → Fin 11487) (hT : FullValid T)
    (n v : Nat) (b : Cell) (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1)) (hmod : r%4=1)
    (hfree : ¬BoardCovered (n+1) r s) :
    SegmentCompatible (BoardCovered (n+1) r) s (verticalTrace T b (n+1) r s) := by
  have hm := fullBoard_root_vertical_masks T n v b hn hv hb r hr hmod
  apply vertical_segment_from_index_geometry T hT b (n+1) r ?_ ?_ ?_ hm.1 hm.2 s hs.1 hs.2 hfree
  · intro z hz0 hz1 hzfree
    exact (fullBoard_exposed_not_boundary T n v b hv hb r z hr ⟨hz0,hz1⟩ hzfree).2
  · intro z hz0 hz1 hzc hzf
    rw [fullBoard_centered_group T n v b hb r z ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact redBoard_vertical_entry n v r z hv hr hmod hzc hzf
  · intro z hz0 hz1 hzc hzf
    rw [fullBoard_centered_group T n v b hb r z ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact redBoard_vertical_exit n v r z hv hr hmod hzc hzf

theorem fullBoard_horizontal_segment (T : Cell → Fin 11487) (hT : FullValid T)
    (n v : Nat) (b : Cell) (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1)) (hmod : s%4=1)
    (hfree : ¬BoardCovered (n+1) s r) :
    SegmentCompatible (BoardCovered (n+1) s) r (horizontalTrace T b (n+1) s r) := by
  have hm := fullBoard_root_horizontal_masks T n v b hn hv hb s hs hmod
  apply horizontal_segment_from_index_geometry T hT b (n+1) s ?_ ?_ ?_ hm.1 hm.2 r hr.1 hr.2 hfree
  · intro z hz0 hz1 hzfree
    have he : ¬BoardCovered (n+1) z s := fun hc =>
      hzfree ((boardCovered_swap (n+1) z s ⟨hz0,hz1⟩ hs).mp hc)
    exact (fullBoard_exposed_not_boundary T n v b hv hb z s ⟨hz0,hz1⟩ hs he).1
  · intro z hz0 hz1 hzc hzf
    have hc : BoardCovered (n+1) z s := (boardCovered_swap (n+1) z s ⟨hz0,hz1⟩ hs).mpr hzc
    have hf : ¬BoardCovered (n+1) (z-1) s := fun hc => hzf
      ((boardCovered_swap_closed (n+1) (z-1) s ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).mp hc)
    rw [fullBoard_centered_group T n v b hb z s ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact redBoard_horizontal_entry n v z s hv ⟨hz0,hz1⟩ hmod hc hf
  · intro z hz0 hz1 hzc hzf
    have hc : BoardCovered (n+1) z s := (boardCovered_swap (n+1) z s ⟨hz0,hz1⟩ hs).mpr hzc
    have hf : ¬BoardCovered (n+1) (z+1) s := fun hc => hzf
      ((boardCovered_swap_closed (n+1) (z+1) s ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).mp hc)
    rw [fullBoard_centered_group T n v b hb z s ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact redBoard_horizontal_exit n v z s hv ⟨hz0,hz1⟩ hmod hc hf

theorem fullBoard_vertical_zero_iff (T : Cell → Fin 11487) (hT : FullValid T)
    (n v : Nat) (b : Cell) (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1)) (hmod : r%4=1)
    (hfree : ¬BoardCovered (n+1) r s) :
    vCode T (centerCell b (n+1) r s)=1 ↔ ¬BlockedOffset (n+1) r :=
  (decode_zero_iff _).symm.trans (board_zero_iff_free
    (fullBoard_vertical_segment T hT n v b hn hv hb r s hr hs hmod hfree))

theorem fullBoard_horizontal_zero_iff (T : Cell → Fin 11487) (hT : FullValid T)
    (n v : Nat) (b : Cell) (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1)) (hmod : s%4=1)
    (hfree : ¬BoardCovered (n+1) s r) :
    hCode T (centerCell b (n+1) r s)=1 ↔ ¬BlockedOffset (n+1) s :=
  (decode_zero_iff _).symm.trans (board_zero_iff_free
    (fullBoard_horizontal_segment T hT n v b hn hv hb r s hr hs hmod hfree))

/-- Complete concrete discharge of the routing layer's two trace clauses. -/
theorem actual_board_traces (T : Cell → Fin 11487) (hT : FullValid T)
    (k v : Nat) (b : Cell) (hv : v<4) (hb : FullBoardAt T (k+1) v b) : BoardTraces T b k where
  vertical r s hr hs hmod hfree :=
    fullBoard_vertical_segment T hT (k+1) v b (by omega) hv hb r s hr hs hmod hfree
  horizontal r s hr hs hmod hfree :=
    fullBoard_horizontal_segment T hT (k+1) v b (by omega) hv hb r s hr hs hmod hfree

#print axioms fullBoard_vertical_segment
#print axioms fullBoard_horizontal_segment
#print axioms actual_board_traces
#print axioms fullBoard_vertical_zero_iff
#print axioms fullBoard_horizontal_zero_iff
end K230Verification
