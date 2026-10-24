module
public import CutRanks
public section
namespace K230Verification

@[expose] noncomputable def verticalWire {k : Nat} (F : FiniteBoard k230Machine (2^k)) (r s : Int) : TMColor := by
  classical
  exact if TapeOffset (k+2) r then
    if 0≤s ∧ s<(boardHalf (k+2) : Int) then vColor (F.vertical (timeRank k s) (columnRank k r))
    else .blank
  else .blank

@[expose] noncomputable def horizontalWire {k : Nat} (F : FiniteBoard k230Machine (2^k)) (r s : Int) : TMColor := by
  classical
  exact if -(boardHalf (k+2) : Int)≤r ∧ r<(boardHalf (k+2) : Int) then
    if s=0 then (if r<0 then .iL else if r=0 then .iH else .iR)
    else if TapeOffset (k+2) s ∧ 0<s then
      hColor (F.edge (timeRank k s-1) (columnRank k r))
    else .blank
  else .blank

/-- Edge-defined stretching gives unit-edge matching identically. The
    finite machine board is used only at the selected physical ranks. -/
@[expose] noncomputable def stretchedTM {k : Nat} (F : FiniteBoard k230Machine (2^k)) (r s : Int) : Quad TMColor :=
  ⟨verticalWire F r s,horizontalWire F r s,verticalWire F r (s-1),horizontalWire F (r-1) s⟩

theorem stretchedTM_horizontal {k : Nat} (F : FiniteBoard k230Machine (2^k)) (r s : Int) :
    (stretchedTM F r s).e=(stretchedTM F (r+1) s).w := by
  change horizontalWire F r s=horizontalWire F (r+1-1) s
  congr 1 <;> omega

theorem stretchedTM_vertical {k : Nat} (F : FiniteBoard k230Machine (2^k)) (r s : Int) :
    (stretchedTM F r s).n=(stretchedTM F r (s+1)).s := by
  change verticalWire F r s=verticalWire F r (s+1-1)
  congr 1 <;> omega

theorem verticalWire_off_column {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hr : ¬TapeOffset (k+2) r) : verticalWire F r s=.blank := by simp [verticalWire,hr]

theorem verticalWire_below {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hs : s<0) : verticalWire F r s=.blank := by
  simp [verticalWire,show ¬0≤s by omega]

theorem verticalWire_above {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hs : (boardHalf (k+2) : Int)≤s) : verticalWire F r s=.blank := by
  simp [verticalWire,show ¬s<(boardHalf (k+2) : Int) by omega]

theorem horizontalWire_off_row {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hs0 : s≠0) (hs : ¬(TapeOffset (k+2) s ∧ 0<s)) : horizontalWire F r s=.blank := by
  simp [horizontalWire,hs0,hs]

theorem horizontalWire_outside {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hr : ¬(-(boardHalf (k+2) : Int)≤r ∧ r<(boardHalf (k+2) : Int))) : horizontalWire F r s=.blank := by
  simp [horizontalWire,hr]

theorem timeRank_zero (k : Nat) : timeRank k 0=0 := by
  apply cutIndex_zero
  intro s hs
  exact (tapeRows_mem.mp hs).2

theorem timeRank_top (k : Nat) : timeRank k ((boardHalf (k+2) : Int)-1)=2^k := by
  rw [←tapeRows_length k]
  apply cutIndex_full
  intro s hs
  have h := (tapeRows_mem.mp hs).1.2.1
  omega

theorem columnRank_left (k : Nat) : columnRank k (-(boardHalf (k+2) : Int))=-(2^k : Nat)-1 := by
  have hz : cutIndex (tapeColumns k) (-(boardHalf (k+2) : Int))=0 := by
    apply cutIndex_zero
    intro r hr
    exact (tapeColumns_mem.mp hr).1
  simp only [columnRank,hz,Int.natCast_zero]
  omega

theorem columnRank_right (k : Nat) : columnRank k ((boardHalf (k+2) : Int)-1)=(2^k : Nat)-1 := by
  have hz : cutIndex (tapeColumns k) ((boardHalf (k+2) : Int)-1)=2*2^k := by
    rw [←tapeColumns_length k]
    apply cutIndex_full
    intro r hr
    have h := (tapeColumns_mem.mp hr).2.1
    omega
  simp only [columnRank,hz,Int.natCast_mul]
  omega

theorem columnRank_mem {k : Nat} {r : Int} (hr : TapeOffset (k+2) r) : InTape (2^k) (columnRank k r) := by
  obtain ⟨i,hi,he⟩ := physicalColumn_surjective hr
  rw [←he,columnRank_physical hi]
  exact hi

theorem timeRank_row_bound {k : Nat} {s : Int} (hs : TapeOffset (k+2) s ∧ 0<s) :
    0<timeRank k s ∧ timeRank k s≤2^k := by
  constructor
  · exact cutIndex_pos (tapeRows_mem.mpr hs)
  · have h := cutIndex_le (tapeRows k) s
    rw [tapeRows_length] at h
    exact h

theorem stretchedTM_computation {k : Nat} (F : FiniteBoard k230Machine (2^k))
    {i : Int} (hi : InTape (2^k) i) {t : Nat} (ht : t<2^k) :
    stretchedTM F (physicalColumn k i hi) (physicalRow k t ht)=
      rowTile (F.vertical (t+1) i) (F.edge t i) (F.vertical t i) (F.edge t (i-1)) := by
  have hc := physicalColumn_mem hi
  have hr := physicalRow_mem ht
  have hxin : -(boardHalf (k+2) : Int)≤physicalColumn k i hi ∧ physicalColumn k i hi<(boardHalf (k+2) : Int) := ⟨by have := hc.1; omega,hc.2.1⟩
  have hxprev : -(boardHalf (k+2) : Int)≤physicalColumn k i hi-1 ∧ physicalColumn k i hi-1<(boardHalf (k+2) : Int) := by
    constructor <;> have := hc.1 <;> have := hc.2.1 <;> omega
  have hyin : 0≤physicalRow k t ht ∧ physicalRow k t ht<(boardHalf (k+2) : Int) := ⟨by have := hr.2; omega,hr.1.2.1⟩
  have hyprev : 0≤physicalRow k t ht-1 ∧ physicalRow k t ht-1<(boardHalf (k+2) : Int) := by
    constructor <;> have := hr.2 <;> have := hr.1.2.1 <;> omega
  simp only [stretchedTM,verticalWire,horizontalWire,if_pos hc,if_pos hxin,if_pos hxprev,
    if_pos hyin,if_pos hyprev,if_neg (show physicalRow k t ht≠0 by have := hr.2; omega),if_pos hr,
    timeRank_physical ht,timeRank_before_physical ht,columnRank_physical hi,columnRank_before_physical hi,
    Nat.add_sub_cancel,rowTile]

theorem stretchedTM_column {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hr : TapeOffset (k+2) r) (hs : 0<s ∧ s<(boardHalf (k+2) : Int))
    (hrow : ¬TapeOffset (k+2) s) :
    stretchedTM F r s=⟨vColor (F.vertical (timeRank k s) (columnRank k r)),.blank,
      vColor (F.vertical (timeRank k s) (columnRank k r)),.blank⟩ := by
  have hno : ¬(TapeOffset (k+2) s ∧ 0<s) := fun h => hrow h.1
  have htime := timeRank_step hno
  simp only [stretchedTM]
  rw [horizontalWire_off_row F (by omega) hno,horizontalWire_off_row F (by omega) hno]
  simp only [verticalWire,if_pos hr,if_pos (show 0≤s ∧ s<(boardHalf (k+2) : Int) by omega),
    if_pos (show 0≤s-1 ∧ s-1<(boardHalf (k+2) : Int) by omega),←htime]

theorem stretchedTM_row {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hr : -(boardHalf (k+2) : Int)<r ∧ r<(boardHalf (k+2) : Int))
    (hcol : ¬TapeOffset (k+2) r) (hs : TapeOffset (k+2) s ∧ 0<s) :
    stretchedTM F r s=⟨.blank,hColor (F.edge (timeRank k s-1) (columnRank k r)),.blank,
      hColor (F.edge (timeRank k s-1) (columnRank k r))⟩ := by
  have htime := columnRank_step hcol
  simp only [stretchedTM]
  rw [verticalWire_off_column F hcol,verticalWire_off_column F hcol]
  simp only [horizontalWire,if_pos (show -(boardHalf (k+2) : Int)≤r ∧ r<(boardHalf (k+2) : Int) by omega),
    if_pos (show -(boardHalf (k+2) : Int)≤r-1 ∧ r-1<(boardHalf (k+2) : Int) by omega),
    if_neg (show s≠0 by have := hs.2; omega),if_pos hs,←htime]

theorem stretchedTM_blank {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hr : ¬TapeOffset (k+2) r) (hs : ¬(TapeOffset (k+2) s ∧ 0<s)) (hs0 : s≠0) :
    stretchedTM F r s=tmBlank := by
  simp only [stretchedTM]
  rw [verticalWire_off_column F hr,verticalWire_off_column F hr,
    horizontalWire_off_row F hs0 hs,horizontalWire_off_row F hs0 hs]
  rfl

#print axioms stretchedTM_computation
#print axioms stretchedTM_column
#print axioms stretchedTM_row
end K230Verification
