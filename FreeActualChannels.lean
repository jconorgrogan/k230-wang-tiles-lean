module
public import RootChannelGeometry
public import ExposedActualChannels
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem fullBoard_root_vertical_masks (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (r : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1)) (hmod : r%4=1) :
    ((indexedGroup (T (centerCell b (n+1) r (-(boardHalf (n+1):Int))))).1=136 ∨
      (indexedGroup (T (centerCell b (n+1) r (-(boardHalf (n+1):Int))))).1=142) ∧
    ((indexedGroup (T (centerCell b (n+1) r (boardHalf (n+1))))).1=134 ∨
      (indexedGroup (T (centerCell b (n+1) r (boardHalf (n+1))))).1=140) := by
  constructor
  · have h := fullBoard_root_side_options T n v b hn hv hb 2 (by decide) r hr hmod
    simpa [rootSidePoint,channelExpected,or_comm] using h
  · have h := fullBoard_root_side_options T n v b hn hv hb 3 (by decide) r hr hmod
    simpa [rootSidePoint,channelExpected,or_comm] using h

theorem fullBoard_root_horizontal_masks (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (r : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1)) (hmod : r%4=1) :
    ((indexedGroup (T (centerCell b (n+1) (-(boardHalf (n+1):Int)) r))).1=100 ∨
      (indexedGroup (T (centerCell b (n+1) (-(boardHalf (n+1):Int)) r))).1=116) ∧
    ((indexedGroup (T (centerCell b (n+1) (boardHalf (n+1)) r))).1=95 ∨
      (indexedGroup (T (centerCell b (n+1) (boardHalf (n+1)) r))).1=111) := by
  constructor
  · have h := fullBoard_root_side_options T n v b hn hv hb 0 (by decide) r hr hmod
    simpa [rootSidePoint,channelExpected,or_comm] using h
  · have h := fullBoard_root_side_options T n v b hn hv hb 1 (by decide) r hr hmod
    simpa [rootSidePoint,channelExpected,or_comm] using h

theorem free_line_uncovered {N : Nat} {r : Int} (h : ¬BlockedOffset N r) (s : Int) :
    ¬BoardCovered N r s := by
  rintro ⟨_,_,m,hm,hmN,hbr,_⟩
  exact h ⟨m,hm,hmN,hbr⟩

theorem fullBoard_free_vertical_code (T : Cell → Fin 11487) (hT : FullValid T)
    (n v : Nat) (b : Cell) (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1)) (hmod : r%4=1)
    (hfree : ¬BlockedOffset (n+1) r) : vCode T (centerCell b (n+1) r s)=1 := by
  have hm := fullBoard_root_vertical_masks T n v b hn hv hb r hr hmod
  have hseg : SegmentCompatible (BoardCovered (n+1) r) s (verticalTrace T b (n+1) r s) := by
    apply vertical_segment_from_index_geometry T hT b (n+1) r ?_ ?_ ?_ hm.1 hm.2 s hs.1 hs.2
      (free_line_uncovered hfree s)
    · intro z hz0 hz1 hzfree
      exact (fullBoard_exposed_not_boundary T n v b hv hb r z hr ⟨hz0,hz1⟩ hzfree).2
    · intro z _ _ hzc _
      exact False.elim (free_line_uncovered hfree z hzc)
    · intro z _ _ hzc _
      exact False.elim (free_line_uncovered hfree z hzc)
  have hz := (board_zero_iff_free hseg).mpr hfree
  exact (decode_zero_iff _).mp hz

theorem fullBoard_free_horizontal_code (T : Cell → Fin 11487) (hT : FullValid T)
    (n v : Nat) (b : Cell) (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1)) (hmod : s%4=1)
    (hfree : ¬BlockedOffset (n+1) s) : hCode T (centerCell b (n+1) r s)=1 := by
  have hm := fullBoard_root_horizontal_masks T n v b hn hv hb s hs hmod
  have hseg : SegmentCompatible (BoardCovered (n+1) s) r (horizontalTrace T b (n+1) s r) := by
    apply horizontal_segment_from_index_geometry T hT b (n+1) s ?_ ?_ ?_ hm.1 hm.2 r hr.1 hr.2
      (free_line_uncovered hfree r)
    · intro z hz0 hz1 hzfree
      have he : ¬BoardCovered (n+1) z s := fun hc =>
        hzfree ((boardCovered_swap (n+1) z s ⟨hz0,hz1⟩ hs).mp hc)
      exact (fullBoard_exposed_not_boundary T n v b hv hb z s ⟨hz0,hz1⟩ hs he).1
    · intro z _ _ hzc _
      exact False.elim (free_line_uncovered hfree z hzc)
    · intro z _ _ hzc _
      exact False.elim (free_line_uncovered hfree z hzc)
  have hz := (board_zero_iff_free hseg).mpr hfree
  exact (decode_zero_iff _).mp hz

#print axioms fullBoard_free_vertical_code
#print axioms fullBoard_free_horizontal_code
end K230Verification
