module
public import GridWires
public section
namespace K230Verification

@[expose] def timeY (k t : Nat) (ht : t≤2^k) : Int :=
  if hz : t=0 then 0 else physicalRow k (t-1) (by omega)

theorem timeY_zero (k : Nat) (h : 0≤2^k) : timeY k 0 h=0 := by simp [timeY]
theorem timeY_next {k t : Nat} (ht : t<2^k) :
    timeY k (t+1) (by omega)=physicalRow k t ht := by simp [timeY]
theorem timeY_before {k t : Nat} (ht : t<2^k) :
    timeY k t (by omega)<physicalRow k t ht := by
  by_cases hz : t=0
  · subst t
    simpa [timeY] using (physicalRow_mem ht).2
  · have hp : t-1<t := by omega
    simpa only [timeY,dif_neg hz] using physicalRow_strict (show t-1<2^k by omega) ht hp

/-- Final local routing interface. It contains physical cells and unit-edge
    matches, not assumed compressed rows. The canonical-board geometry must
    discharge these clauses using concrete channel/template theorems. -/
structure RoutedBoard (k : Nat) where
  tile : Int → Int → Quad TMColor
  matchH : ∀ x y, (tile x y).e=(tile (x+1) y).w
  matchV : ∀ x y, (tile x y).n=(tile x (y+1)).s
  initial : ∀ i (hi : InTape (2^k) i),
    (tile (physicalColumn k i hi) 0).n=vColor (blankConfiguration.row i)
  columnCopy : ∀ t (ht : t<2^k) i (hi : InTape (2^k) i) y,
    timeY k t (by omega)<y → y<physicalRow k t ht →
    (tile (physicalColumn k i hi) y).s≠.blank →
    (tile (physicalColumn k i hi) y).n=(tile (physicalColumn k i hi) y).s
  rowCopy : ∀ t (ht : t<2^k) i (hi : InTape (2^k) i) (hj : InTape (2^k) (i+1)) x,
    physicalColumn k i hi<x → x<physicalColumn k (i+1) hj →
    (tile x (physicalRow k t ht)).e=(tile x (physicalRow k t ht)).w
  computation : ∀ t (ht : t<2^k) i (hi : InTape (2^k) i),
    (tile (physicalColumn k i hi) (physicalRow k t ht)).s≠.blank →
    tile (physicalColumn k i hi) (physicalRow k t ht) ∈ tmComp
  left : ∀ t (ht : t<2^k) i (hi : InTape (2^k) i), i=-(2^k : Nat) →
    (tile (physicalColumn k i hi) (physicalRow k t ht)).w=.blank
  right : ∀ t (ht : t<2^k) i (hi : InTape (2^k) i), i=(2^k : Nat)-1 →
    (tile (physicalColumn k i hi) (physicalRow k t ht)).e=.blank ∨
    ∃ q, (tile (physicalColumn k i hi) (physicalRow k t ht)).e=.move .right q

namespace RoutedBoard

theorem vertical_data {k : Nat} (R : RoutedBoard k) :
    ∀ t (ht : t≤2^k) i (hi : InTape (2^k) i),
      isTapeData (R.tile (physicalColumn k i hi) (timeY k t ht)).n=true := by
  intro t
  induction t with
  | zero =>
    intro ht i hi
    rw [timeY_zero,R.initial i hi]
    cases blankConfiguration.row i <;> rfl
  | succ t ih =>
    intro ht i hi
    have ht' : t<2^k := by omega
    have hv := ih (by omega) i hi
    have hn : (R.tile (physicalColumn k i hi) (timeY k t (by omega))).n≠.blank := by
      intro he
      rw [he] at hv
      cases hv
    have hw := vertical_wire (tile:=R.tile (physicalColumn k i hi)) (timeY_before ht')
      (fun y _ _ => R.matchV _ y) (R.columnCopy t ht' i hi) hn
    have hs : (R.tile (physicalColumn k i hi) (physicalRow k t ht')).s≠.blank := by rw [hw]; exact hn
    have hc := R.computation t ht' i hi hs
    have hd := (concrete_comp_vertical_data _ hc).1
    simpa only [timeY_next ht'] using hd

theorem vertical_match {k : Nat} (R : RoutedBoard k) {t : Nat} (ht : t<2^k)
    {i : Int} (hi : InTape (2^k) i) :
    (R.tile (physicalColumn k i hi) (physicalRow k t ht)).s =
      (R.tile (physicalColumn k i hi) (timeY k t (by omega))).n := by
  have hv := R.vertical_data t (by omega) i hi
  have hn : (R.tile (physicalColumn k i hi) (timeY k t (by omega))).n≠.blank := by
    intro he; rw [he] at hv; cases hv
  exact vertical_wire (tile:=R.tile (physicalColumn k i hi)) (timeY_before ht)
    (fun y _ _ => R.matchV _ y) (R.columnCopy t ht i hi) hn

theorem horizontal_match {k : Nat} (R : RoutedBoard k) {t : Nat} (ht : t<2^k)
    {i : Int} (hi : InTape (2^k) i) (hj : InTape (2^k) (i+1)) :
    (R.tile (physicalColumn k (i+1) hj) (physicalRow k t ht)).w=
      (R.tile (physicalColumn k i hi) (physicalRow k t ht)).e := by
  exact horizontal_wire (tile:=fun x => R.tile x (physicalRow k t ht))
    (physicalColumn_strict hi hj (by omega)) (fun x _ _ => R.matchH x _)
    (R.rowCopy t ht i hi hj)

@[expose] def vertical {k : Nat} (R : RoutedBoard k) (t : Nat) (i : Int) : VLabel :=
  if hi : InTape (2^k) i then
    if ht : t≤2^k then parseV (R.tile (physicalColumn k i hi) (timeY k t ht)).n else .symbol false
  else .symbol false
@[expose] def edge {k : Nat} (R : RoutedBoard k) (t : Nat) (i : Int) : HLabel :=
  if hi : InTape (2^k) i then
    if ht : t<2^k then parseH (R.tile (physicalColumn k i hi) (physicalRow k t ht)).e else none
  else none

/-- Assemble the physical wiring into the precise finite computation board.
    This proves edge matching after compression instead of assuming it. -/
noncomputable def toFiniteBoard {k : Nat} (R : RoutedBoard k) : FiniteBoard k230Machine (2^k) where
  vertical := R.vertical
  edge := R.edge
  initial := by
    intro i hi
    simp only [vertical,dif_pos hi,dif_pos (Nat.zero_le _),timeY_zero,R.initial,parseV_vColor]
  allowed := by
    intro t ht i hi
    have hdata := R.vertical_data t (by omega) i hi
    have hn : (R.tile (physicalColumn k i hi) (timeY k t (by omega))).n≠.blank := by
      intro he; rw [he] at hdata; cases hdata
    have hs := R.vertical_match ht hi
    have hsnb : (R.tile (physicalColumn k i hi) (physicalRow k t ht)).s≠.blank := by rw [hs]; exact hn
    have ha := tmComp_sound (R.computation t ht i hi hsnb)
    have hprev : parseH (R.tile (physicalColumn k i hi) (physicalRow k t ht)).w=R.edge t (i-1) := by
      by_cases hip : InTape (2^k) (i-1)
      · have he : i-1+1=i := by omega
        have hij : InTape (2^k) (i-1+1) := by rw [he]; exact hi
        have hw := R.horizontal_match ht hip hij
        simp only [he] at hw
        simp only [edge,dif_pos hip,dif_pos ht]
        exact congrArg parseH hw
      · have hei : i=-(2^k : Nat) := by unfold InTape at *; omega
        rw [R.left t ht i hi hei]
        simp [edge,hip,parseH]
    rw [hs,hprev] at ha
    simpa only [vertical,edge,dif_pos hi,dif_pos ht,dif_pos (show t≤2^k by omega),
      dif_pos (show t+1≤2^k by omega),timeY_next ht] using ha
  left := by
    intro t ht
    have hi : ¬InTape (2^k) (-(2^k : Nat)-1) := by unfold InTape; omega
    simp only [edge,dif_neg hi]
  right := by
    intro t ht
    have hp : 0<2^k := Nat.pow_pos (by decide)
    have hi : InTape (2^k) ((2^k : Nat)-1) := by unfold InTape; omega
    have hr := R.right t ht _ hi rfl
    simp only [edge,dif_pos hi,dif_pos ht]
    rcases hr with hr|⟨q,hr⟩
    · exact Or.inl (by rw [hr]; rfl)
    · exact Or.inr ⟨q,by rw [hr]; rfl⟩

end RoutedBoard
#print axioms RoutedBoard.toFiniteBoard
end K230Verification
