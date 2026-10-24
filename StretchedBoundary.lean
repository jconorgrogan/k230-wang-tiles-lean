module
public import StretchedWires
public section
namespace K230Verification
attribute [local instance] Classical.propDecidable

theorem columnRank_zero_iff {k : Nat} {r : Int} (hr : TapeOffset (k+2) r) :
    columnRank k r=0 ↔ r=1 := by
  obtain ⟨i,hi,he⟩ := physicalColumn_surjective hr
  rw [←he,columnRank_physical hi]
  constructor
  · intro hz; subst i; exact physicalColumn_zero k
  · intro hh
    by_cases hz : i=0
    · exact hz
    · by_cases hneg : i<0
      · have hc := physicalColumn_strict hi (logical_zero_in_tape k) hneg
        rw [physicalColumn_zero,hh] at hc
        omega
      · have hc := physicalColumn_strict (logical_zero_in_tape k) hi (by omega)
        rw [physicalColumn_zero,hh] at hc
        omega

theorem verticalWire_initial {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : TapeOffset (k+2) r) :
    verticalWire F r 0=if r=1 then .head 0 false else .symbol false := by
  have hp := board_half_pos (k+2)
  have hi := columnRank_mem hr
  have hz := columnRank_zero_iff hr
  simp only [verticalWire,if_pos hr,if_pos (show (0:Int)≤0 ∧ (0:Int)<boardHalf (k+2) by omega),
    timeRank_zero,F.initial _ hi]
  by_cases he : r=1
  · have hc : columnRank k r=0 := hz.mpr he
    simp only [blankConfiguration,Configuration.row,configRow,hc,if_pos rfl,vColor]
    simp [he]
  · have hc : columnRank k r≠0 := fun h => he (hz.mp h)
    simp [he,hc,blankConfiguration,Configuration.row,configRow,vColor]

theorem zero_not_tape (n : Nat) : ¬TapeOffset n 0 := by
  intro h
  have hh := h.2.2.1
  omega

theorem stretchedTM_seed {k : Nat} (F : FiniteBoard k230Machine (2^k)) :
    stretchedTM F 0 0=⟨.blank,.iH,.blank,.iL⟩ := by
  have hp := board_half_pos (k+2)
  simp only [stretchedTM]
  rw [verticalWire_off_column F (zero_not_tape _),verticalWire_off_column F (zero_not_tape _)]
  simp [horizontalWire,show -(boardHalf (k+2) : Int)≤(0:Int) ∧ (0:Int)<boardHalf (k+2) by omega,
    show -(boardHalf (k+2) : Int)≤(-1:Int) ∧ (-1:Int)<boardHalf (k+2) by omega,
    show boardHalf (k+2)≠0 by omega]

theorem stretchedTM_start {k : Nat} (F : FiniteBoard k230Machine (2^k)) :
    stretchedTM F 1 0=⟨.head 0 false,.iR,.blank,.iH⟩ := by
  have hr := (positiveTape_mem.mp (start_is_positive_tape k)).1
  have hp := hr.2.1
  simp only [stretchedTM]
  rw [verticalWire_initial F hr,verticalWire_below F (by omega)]
  simp [horizontalWire,show -(boardHalf (k+2) : Int)≤(1:Int) ∧ (1:Int)<boardHalf (k+2) by omega,
    show -(boardHalf (k+2) : Int)≤(0:Int) ∧ (0:Int)<boardHalf (k+2) by omega,
    show boardHalf (k+2)≠0 by omega]

theorem stretchedTM_initial_left {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : -(boardHalf (k+2) : Int)<r ∧ r<0) :
    stretchedTM F r 0=⟨(if TapeOffset (k+2) r then .symbol false else .blank),.iL,.blank,.iL⟩ := by
  classical
  have hN : verticalWire F r 0=if TapeOffset (k+2) r then .symbol false else .blank := by
    by_cases hc : TapeOffset (k+2) r
    · rw [verticalWire_initial F hc]
      simp [hc,show r≠1 by omega]
    · simp [verticalWire,hc]
  have hp := board_half_pos (k+2)
  simp only [stretchedTM]
  rw [hN,verticalWire_below F (by omega)]
  simp [horizontalWire,show -(boardHalf (k+2) : Int)≤r ∧ r<(boardHalf (k+2) : Int) by omega,
    show -(boardHalf (k+2) : Int)≤r-1 ∧ r-1<(boardHalf (k+2) : Int) by omega,
    hr.2,show r-1<0 by omega]

theorem stretchedTM_initial_right {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : 1<r ∧ r<(boardHalf (k+2) : Int)) :
    stretchedTM F r 0=⟨(if TapeOffset (k+2) r then .symbol false else .blank),.iR,.blank,.iR⟩ := by
  classical
  have hN : verticalWire F r 0=if TapeOffset (k+2) r then .symbol false else .blank := by
    by_cases hc : TapeOffset (k+2) r
    · rw [verticalWire_initial F hc]
      simp [hc,show r≠1 by omega]
    · simp [verticalWire,hc]
  have hp := board_half_pos (k+2)
  simp only [stretchedTM]
  rw [hN,verticalWire_below F (by omega)]
  simp [horizontalWire,show -(boardHalf (k+2) : Int)≤r ∧ r<(boardHalf (k+2) : Int) by omega,
    show -(boardHalf (k+2) : Int)≤r-1 ∧ r-1<(boardHalf (k+2) : Int) by omega,
    show ¬r<0 by omega,show r≠0 by omega,show ¬r-1<0 by omega,show r-1≠0 by omega]

theorem left_wall_not_tape (n : Nat) : ¬TapeOffset n (-(boardHalf n : Int)) := by
  intro h; have := h.1; omega

theorem right_wall_not_tape (n : Nat) : ¬TapeOffset n (boardHalf n : Int) := by
  intro h; have := h.2.1; omega

theorem stretchedTM_initial_left_wall {k : Nat} (F : FiniteBoard k230Machine (2^k)) :
    stretchedTM F (-(boardHalf (k+2) : Int)) 0=⟨.blank,.iL,.blank,.blank⟩ := by
  have hp := board_half_pos (k+2)
  simp only [stretchedTM]
  rw [verticalWire_off_column F (left_wall_not_tape _),verticalWire_off_column F (left_wall_not_tape _)]
  simp only [horizontalWire,if_pos (show -(boardHalf (k+2) : Int)≤-(boardHalf (k+2) : Int) ∧
    -(boardHalf (k+2) : Int)<(boardHalf (k+2) : Int) by omega),
    if_neg (show ¬(-(boardHalf (k+2) : Int)≤-(boardHalf (k+2) : Int)-1 ∧
    -(boardHalf (k+2) : Int)-1<(boardHalf (k+2) : Int)) by omega),
    if_pos rfl,if_pos (show -(boardHalf (k+2) : Int)<0 by omega)]
  simp

theorem stretchedTM_initial_right_wall {k : Nat} (F : FiniteBoard k230Machine (2^k)) :
    stretchedTM F (boardHalf (k+2)) 0=⟨.blank,.blank,.blank,.iR⟩ := by
  have hp := (positiveTape_mem.mp (start_is_positive_tape k)).1.2.1
  simp only [stretchedTM]
  rw [verticalWire_off_column F (right_wall_not_tape _),verticalWire_off_column F (right_wall_not_tape _)]
  simp [horizontalWire,show -(boardHalf (k+2) : Int)≤(boardHalf (k+2) : Int)-1 ∧
    (boardHalf (k+2) : Int)-1<(boardHalf (k+2) : Int) by omega,
    show ¬(boardHalf (k+2) : Int)-1<0 by omega,show (boardHalf (k+2) : Int)-1≠0 by omega]

theorem stretchedTM_left_wall {k : Nat} (F : FiniteBoard k230Machine (2^k)) {s : Int}
    (hs : TapeOffset (k+2) s ∧ 0<s) : stretchedTM F (-(boardHalf (k+2) : Int)) s=tmBlank := by
  have hp := board_half_pos (k+2)
  have ht := timeRank_row_bound hs
  simp only [stretchedTM]
  rw [verticalWire_off_column F (left_wall_not_tape _),verticalWire_off_column F (left_wall_not_tape _)]
  simp only [horizontalWire,if_pos (show -(boardHalf (k+2) : Int)≤-(boardHalf (k+2) : Int) ∧
    -(boardHalf (k+2) : Int)<(boardHalf (k+2) : Int) by omega),
    if_neg (show ¬(-(boardHalf (k+2) : Int)≤-(boardHalf (k+2) : Int)-1 ∧
    -(boardHalf (k+2) : Int)-1<(boardHalf (k+2) : Int)) by omega),
    if_neg (show s≠0 by have := hs.2; omega),if_pos hs,columnRank_left,
    F.left _ (show timeRank k s-1<2^k by omega),hColor]
  rfl

theorem stretchedTM_right_wall {k : Nat} (F : FiniteBoard k230Machine (2^k)) {s : Int}
    (hs : TapeOffset (k+2) s ∧ 0<s) :
    stretchedTM F (boardHalf (k+2)) s=⟨.blank,.blank,.blank,
      hColor (F.edge (timeRank k s-1) ((2^k : Nat)-1))⟩ := by
  have hp := board_half_pos (k+2)
  simp only [stretchedTM]
  rw [verticalWire_off_column F (right_wall_not_tape _),verticalWire_off_column F (right_wall_not_tape _)]
  simp [horizontalWire,show -(boardHalf (k+2) : Int)≤(boardHalf (k+2) : Int)-1 ∧
    (boardHalf (k+2) : Int)-1<(boardHalf (k+2) : Int) by omega,
    show s≠0 by have := hs.2; omega,hs,columnRank_right]

theorem stretchedTM_top {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : TapeOffset (k+2) r) :
    stretchedTM F r (boardHalf (k+2))=⟨.blank,.blank,
      vColor (F.vertical (2^k) (columnRank k r)),.blank⟩ := by
  have hp := board_half_pos (k+2)
  have hs0 : (boardHalf (k+2) : Int)≠0 := by omega
  have hs : ¬(TapeOffset (k+2) (boardHalf (k+2) : Int) ∧ 0<(boardHalf (k+2) : Int)) :=
    fun h => right_wall_not_tape _ h.1
  simp only [stretchedTM]
  rw [verticalWire_above F (by omega),horizontalWire_off_row F hs0 hs,horizontalWire_off_row F hs0 hs]
  simp only [verticalWire,if_pos hr,if_pos (show 0≤(boardHalf (k+2) : Int)-1 ∧
    (boardHalf (k+2) : Int)-1<(boardHalf (k+2) : Int) by omega),timeRank_top]

theorem stretchedTM_below {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hs : s<0) : stretchedTM F r s=tmBlank := by
  have hs0 : s≠0 := by omega
  have hno : ¬(TapeOffset (k+2) s ∧ 0<s) := by intro h; have := h.2; omega
  simp only [stretchedTM]
  rw [verticalWire_below F hs,verticalWire_below F (by omega),
    horizontalWire_off_row F hs0 hno,horizontalWire_off_row F hs0 hno]
  rfl

theorem stretchedTM_covered_blank {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hc : BoardCovered (k+2) r s) : stretchedTM F r s=tmBlank := by
  obtain ⟨_,_,m,hm,hmN,hbr,hbs⟩ := hc
  have hr : ¬TapeOffset (k+2) r := fun h => h.2.2.2 ⟨m,hm,hmN,hbr⟩
  have hs : ¬(TapeOffset (k+2) s ∧ 0<s) := fun h => h.1.2.2.2 ⟨m,hm,hmN,hbs⟩
  have hs0 : s≠0 := by
    intro he; subst s
    exact center_not_in_band (by have := board_half_pos m; omega) hbs
  exact stretchedTM_blank F hr hs hs0

#print axioms stretchedTM_seed
#print axioms stretchedTM_initial_left
#print axioms stretchedTM_initial_right
#print axioms stretchedTM_top
#print axioms stretchedTM_covered_blank
end K230Verification
