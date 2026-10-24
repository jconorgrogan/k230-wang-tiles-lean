module
public import ActualChannelMasks
public import CenteredFullBoard
public section
namespace K230Verification

@[expose] noncomputable def verticalTrace (T : Cell → Fin 11487) (b : Cell) (N : Nat) (r : Int) : Int → Channel :=
  fun s => vChannel T (centerCell b N r s)
@[expose] noncomputable def horizontalTrace (T : Cell → Fin 11487) (b : Cell) (N : Nat) (s : Int) : Int → Channel :=
  fun r => hChannel T (centerCell b N r s)

/-- This helper isolates precisely the concrete geometric obligations; it does not assume
    channel compatibility or free-channel behavior. -/
theorem vertical_segment_from_index_geometry
    (T : Cell → Fin 11487) (hT : FullValid T) (b : Cell) (N : Nat) (r : Int)
    (hcopy : ∀ s, -(boardHalf N:Int)<s → s<(boardHalf N:Int) → ¬BoardCovered N r s →
      ¬vBoundary (indexedGroup (T (centerCell b N r s))).1)
    (hentry : ∀ s, -(boardHalf N:Int)<s → s<(boardHalf N:Int) → BoardCovered N r s →
      ¬BoardCovered N r (s-1) →
      (indexedGroup (T (centerCell b N r s))).1=136 ∨
      (indexedGroup (T (centerCell b N r s))).1=142 ∨
      (indexedGroup (T (centerCell b N r s))).1=151)
    (hexit : ∀ s, -(boardHalf N:Int)<s → s<(boardHalf N:Int) → BoardCovered N r s →
      ¬BoardCovered N r (s+1) →
      (indexedGroup (T (centerCell b N r s))).1=134 ∨
      (indexedGroup (T (centerCell b N r s))).1=140 ∨
      (indexedGroup (T (centerCell b N r s))).1=150)
    (hbottom : (indexedGroup (T (centerCell b N r (-(boardHalf N:Int))))).1=136 ∨
      (indexedGroup (T (centerCell b N r (-(boardHalf N:Int))))).1=142)
    (htop : (indexedGroup (T (centerCell b N r (boardHalf N)))).1=134 ∨
      (indexedGroup (T (centerCell b N r (boardHalf N)))).1=140)
    (s : Int) (hsl : -(boardHalf N:Int)<s) (hsr : s<(boardHalf N:Int))
    (hfree : ¬BoardCovered N r s) :
    SegmentCompatible (BoardCovered N r) s (verticalTrace T b N r s) := by
  apply int_segmentCompatible_of_trace (BoardCovered N r) (boardHalf N) (verticalTrace T b N r)
    (board_half_pos N) (fun _ hc => ⟨hc.1,hc.2.1⟩) ?_ ?_ ?_ ?_ ?_ s hsl hsr hfree
  · intro z hz0 hz1 hzfree
    have hh := actual_vcopy T hT (centerCell b N r z) (hcopy z hz0 hz1 hzfree)
    have he : ((centerCell b N r z).1,(centerCell b N r z).2-1)=centerCell b N r (z-1) := by
      apply Prod.ext <;> dsimp [centerCell] <;> omega
    rw [he] at hh
    exact hh
  · intro z hz0 hz1 hzc hzf
    have hh := indexed_bottom_outer (T (centerCell b N r z)) (hentry z hz0 hz1 hzc hzf)
    have hm := actual_vertical_match T hT (centerCell b N r (z-1))
    rw [centerCell_vertical] at hm
    have he : z-1+1=z := by omega
    rw [he] at hm
    change EndAllows .outerLeft (decodeChannel (indexedFullTile (T (centerCell b N r (z-1)))).n.2.1)
    rw [hm]
    exact hh
  · intro z hz0 hz1 hzc hzf
    exact indexed_top_outer (T (centerCell b N r z)) (hexit z hz0 hz1 hzc hzf)
  · exact indexed_bottom_inner _ hbottom
  · have hh := indexed_top_inner (T (centerCell b N r (boardHalf N))) htop
    have hm := actual_vertical_match T hT (centerCell b N r ((boardHalf N:Int)-1))
    rw [centerCell_vertical] at hm
    have he : (boardHalf N:Int)-1+1=boardHalf N := by omega
    rw [he] at hm
    change EndAllows .innerRight (decodeChannel (indexedFullTile (T (centerCell b N r ((boardHalf N:Int)-1)))).n.2.1)
    rw [hm]
    exact hh

theorem horizontal_segment_from_index_geometry
    (T : Cell → Fin 11487) (hT : FullValid T) (b : Cell) (N : Nat) (r : Int)
    (hcopy : ∀ s, -(boardHalf N:Int)<s → s<(boardHalf N:Int) → ¬BoardCovered N r s →
      ¬hBoundary (indexedGroup (T (centerCell b N s r))).1)
    (hentry : ∀ s, -(boardHalf N:Int)<s → s<(boardHalf N:Int) → BoardCovered N r s →
      ¬BoardCovered N r (s-1) →
      (indexedGroup (T (centerCell b N s r))).1=100 ∨
      (indexedGroup (T (centerCell b N s r))).1=116 ∨
      (indexedGroup (T (centerCell b N s r))).1=101)
    (hexit : ∀ s, -(boardHalf N:Int)<s → s<(boardHalf N:Int) → BoardCovered N r s →
      ¬BoardCovered N r (s+1) →
      (indexedGroup (T (centerCell b N s r))).1=95 ∨
      (indexedGroup (T (centerCell b N s r))).1=111 ∨
      (indexedGroup (T (centerCell b N s r))).1=96)
    (hleft : (indexedGroup (T (centerCell b N (-(boardHalf N:Int)) r))).1=100 ∨
      (indexedGroup (T (centerCell b N (-(boardHalf N:Int)) r))).1=116)
    (hright : (indexedGroup (T (centerCell b N (boardHalf N) r))).1=95 ∨
      (indexedGroup (T (centerCell b N (boardHalf N) r))).1=111)
    (s : Int) (hsl : -(boardHalf N:Int)<s) (hsr : s<(boardHalf N:Int))
    (hfree : ¬BoardCovered N r s) :
    SegmentCompatible (BoardCovered N r) s (horizontalTrace T b N r s) := by
  apply int_segmentCompatible_of_trace (BoardCovered N r) (boardHalf N) (horizontalTrace T b N r)
    (board_half_pos N) (fun _ hc => ⟨hc.1,hc.2.1⟩) ?_ ?_ ?_ ?_ ?_ s hsl hsr hfree
  · intro z hz0 hz1 hzfree
    have hh := actual_hcopy T hT (centerCell b N z r) (hcopy z hz0 hz1 hzfree)
    have he : ((centerCell b N z r).1-1,(centerCell b N z r).2)=centerCell b N (z-1) r := by
      apply Prod.ext <;> dsimp [centerCell] <;> omega
    rw [he] at hh
    exact hh
  · intro z hz0 hz1 hzc hzf
    have hh := indexed_left_outer (T (centerCell b N z r)) (hentry z hz0 hz1 hzc hzf)
    have hm := actual_horizontal_match T hT (centerCell b N (z-1) r)
    rw [centerCell_horizontal] at hm
    have he : z-1+1=z := by omega
    rw [he] at hm
    change EndAllows .outerLeft (decodeChannel (indexedFullTile (T (centerCell b N (z-1) r))).e.2.1)
    rw [hm]
    exact hh
  · intro z hz0 hz1 hzc hzf
    exact indexed_right_outer (T (centerCell b N z r)) (hexit z hz0 hz1 hzc hzf)
  · exact indexed_left_inner _ hleft
  · have hh := indexed_right_inner (T (centerCell b N (boardHalf N) r)) hright
    have hm := actual_horizontal_match T hT (centerCell b N ((boardHalf N:Int)-1) r)
    rw [centerCell_horizontal] at hm
    have he : (boardHalf N:Int)-1+1=boardHalf N := by omega
    rw [he] at hm
    change EndAllows .innerRight (decodeChannel (indexedFullTile (T (centerCell b N ((boardHalf N:Int)-1) r))).e.2.1)
    rw [hm]
    exact hh

#print axioms vertical_segment_from_index_geometry
#print axioms horizontal_segment_from_index_geometry
end K230Verification
