module
public import StretchedBoundary
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

theorem k230_code_target_bound : ∀ code ∈ k230Codes.toList, code/4<231 := by decide

theorem k230_entered_bound {p q : Nat} {a b : Bool} {d : Dir}
    (hs : k230Machine p a=some (q,b,d)) : q<231 := by
  obtain ⟨code,hc,he⟩ := machine_step_has_code hs
  have hq := congrArg Prod.fst he
  change code/4=q at hq
  rw [←hq]
  exact k230_code_target_bound code hc

theorem symbol_in_vertical (a : Bool) : TMColor.symbol a ∈ tmVertical := by cases a <;> simp [tmVertical]

theorem head_in_vertical {q : Nat} (hq : q<231) (a : Bool) : TMColor.head q a ∈ tmVertical := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  exact ⟨q,List.mem_range.mpr hq,by cases a <;> simp⟩

theorem allowed_north_vertical {n s : VLabel} {e w : HLabel}
    (ha : Allowed k230Machine n e s w) : vColor n ∈ tmVertical := by
  cases ha with
  | symbol a => exact symbol_in_vertical a
  | right q a q' b hs => exact symbol_in_vertical b
  | left q a q' b hs => exact symbol_in_vertical b
  | mergeRight q a he =>
    obtain ⟨p,c,b,hs⟩ := he
    exact head_in_vertical (k230_entered_bound hs) a
  | mergeLeft q a he =>
    obtain ⟨p,c,b,hs⟩ := he
    exact head_in_vertical (k230_entered_bound hs) a

theorem allowed_east_move {n s : VLabel} {e w : HLabel}
    (ha : Allowed k230Machine n e s w) : hColor e ∈ .blank :: tmMoves := by
  cases ha with
  | symbol a => exact List.mem_cons_self
  | right q a q' b hs =>
    apply List.mem_cons_of_mem
    exact tmMoves_mem_entered.mpr ⟨q,a,b,hs⟩
  | left q a q' b hs => exact List.mem_cons_self
  | mergeRight q a he => exact List.mem_cons_self
  | mergeLeft q a he =>
    apply List.mem_cons_of_mem
    exact tmMoves_mem_entered.mpr he

theorem finiteBoard_vertical_in_alphabet {k t : Nat} (F : FiniteBoard k230Machine (2^k))
    (ht : t≤2^k) {i : Int} (hi : InTape (2^k) i) : vColor (F.vertical t i) ∈ tmVertical := by
  cases t with
  | zero =>
    rw [F.initial i hi]
    by_cases hz : i=0
    · subst i
      exact head_in_vertical (by decide) false
    · have hrow : blankConfiguration.row i=.symbol false := by
        simp [blankConfiguration,Configuration.row,configRow,hz]
      rw [hrow]
      exact symbol_in_vertical false
  | succ t => exact allowed_north_vertical (F.allowed t (by omega) i hi)

theorem finiteBoard_rank_edge_in_alphabet {k t : Nat} (F : FiniteBoard k230Machine (2^k))
    (ht : t<2^k) (r : Int) : hColor (F.edge t (columnRank k r)) ∈ .blank :: tmMoves := by
  have hrank : -(2^k : Nat)-1≤columnRank k r ∧ columnRank k r<(2^k : Nat) := by
    have hbound := cutIndex_le (tapeColumns k) r
    rw [tapeColumns_length] at hbound
    unfold columnRank
    omega
  by_cases hz : columnRank k r=-(2^k : Nat)-1
  · rw [hz,F.left t ht]
    exact List.mem_cons_self
  · have hi : InTape (2^k) (columnRank k r) := by unfold InTape; omega
    exact allowed_east_move (F.allowed t ht _ hi)

theorem stretchedTM_comp_family {k : Nat} (F : FiniteBoard k230Machine (2^k))
    {i : Int} (hi : InTape (2^k) i) {t : Nat} (ht : t<2^k) :
    stretchedTM F (physicalColumn k i hi) (physicalRow k t ht) ∈ tmFamily 13 := by
  rw [stretchedTM_computation F hi ht]
  exact List.mem_append_left _ (tmComp_complete (F.allowed t ht i hi))

theorem stretchedTM_column_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hr : TapeOffset (k+2) r) (hs : 0<s ∧ s<(boardHalf (k+2) : Int))
    (hrow : ¬TapeOffset (k+2) s) : stretchedTM F r s ∈ tmColumns := by
  rw [stretchedTM_column F hr hs hrow]
  apply List.mem_map.mpr
  refine ⟨vColor (F.vertical (timeRank k s) (columnRank k r)),?_,rfl⟩
  apply finiteBoard_vertical_in_alphabet F
  · have h := cutIndex_le (tapeRows k) s
    rw [tapeRows_length] at h
    exact h
  · exact columnRank_mem hr

theorem stretchedTM_row_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hr : -(boardHalf (k+2) : Int)<r ∧ r<(boardHalf (k+2) : Int))
    (hcol : ¬TapeOffset (k+2) r) (hs : TapeOffset (k+2) s ∧ 0<s) :
    stretchedTM F r s ∈ tmFamily 6 := by
  rw [stretchedTM_row F hr hcol hs]
  have ht := timeRank_row_bound hs
  apply List.mem_map.mpr
  exact ⟨hColor (F.edge (timeRank k s-1) (columnRank k r)),
    finiteBoard_rank_edge_in_alphabet F (by omega) r,rfl⟩

theorem stretchedTM_top_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : TapeOffset (k+2) r) : stretchedTM F r (boardHalf (k+2)) ∈ tmFamily 9 := by
  rw [stretchedTM_top F hr]
  apply List.mem_map.mpr
  exact ⟨vColor (F.vertical (2^k) (columnRank k r)),
    finiteBoard_vertical_in_alphabet F (by omega) (columnRank_mem hr),rfl⟩

theorem stretchedTM_top_south_nonblank {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : TapeOffset (k+2) r) : (stretchedTM F r (boardHalf (k+2))).s≠.blank := by
  rw [stretchedTM_top F hr]
  change vColor (F.vertical (2^k) (columnRank k r))≠TMColor.blank
  cases F.vertical (2^k) (columnRank k r) <;> simp [vColor]

theorem stretchedTM_right_wall_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) {s : Int}
    (hs : TapeOffset (k+2) s ∧ 0<s) : stretchedTM F (boardHalf (k+2)) s ∈ tmFamily 7 := by
  rw [stretchedTM_right_wall F hs]
  have ht := timeRank_row_bound hs
  have ht' : timeRank k s-1<2^k := by omega
  have hm : hColor (F.edge (timeRank k s-1) ((2^k : Nat)-1)) ∈ .blank :: tmMoves := by
    have hh := finiteBoard_rank_edge_in_alphabet F ht' ((boardHalf (k+2) : Int)-1)
    rw [columnRank_right] at hh
    exact hh
  apply List.mem_map.mpr
  refine ⟨hColor (F.edge (timeRank k s-1) ((2^k : Nat)-1)),?_,rfl⟩
  rcases F.right (timeRank k s-1) ht' with he|⟨q,he⟩
  · rw [he]
    exact List.mem_cons_self
  · rw [he] at hm ⊢
    apply List.mem_cons_of_mem
    apply List.mem_filter.mpr
    refine ⟨?_,rfl⟩
    rcases List.mem_cons.mp hm with hh|hh
    · cases hh
    · exact hh

#print axioms finiteBoard_vertical_in_alphabet
#print axioms stretchedTM_comp_family
#print axioms stretchedTM_row_family
#print axioms stretchedTM_top_family
#print axioms stretchedTM_right_wall_family
end K230Verification
