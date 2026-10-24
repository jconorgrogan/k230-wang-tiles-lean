module
public import GridWires
public import ChannelClasses
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

@[expose] def leftInitialBases : List Nat := [1,3,5,9,17,19,21,25,120,121,123,125,132,133,135,137]
@[expose] def rightInitialBases : List Nat := [10,11,13,15,26,27,29,31,126,127,129,131,138,139,141,143]

theorem left_initial_group : ∀ g ∈ exactGroups.toList, g.1 ∈ leftInitialBases →
    ((groupChannel g).n=0 ∨ (groupChannel g).n=1 ∨ (groupChannel g).n=3) →
    (g.2.2=1 ∨ g.2.2=8) ∧ (g.2.2=8 ↔ (groupChannel g).n=1) := by decide

theorem right_initial_group : ∀ g ∈ exactGroups.toList, g.1 ∈ rightInitialBases →
    ((groupChannel g).n=0 ∨ (groupChannel g).n=1 ∨ (groupChannel g).n=3) →
    (g.2.2=2 ∨ g.2.2=10) ∧ (g.2.2=10 ↔ (groupChannel g).n=1) := by decide

theorem left_initial_shape {f : Nat} {t : Quad TMColor}
    (hf : f=1 ∨ f=8) (ht : t ∈ tmFamily f) (hs : t.e=.iL ∨ t.w=.iL) :
    t.e=.iL ∧ t.w=.iL ∧ (f=8 → t.n=.symbol false) := by
  rcases hf with rfl|rfl
  · simp only [tmFamily,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · rcases hs with h|h <;> cases h
    · exact ⟨rfl,rfl,by intro h; contradiction⟩
  · simp only [tmFamily,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with ht | (rfl|rfl)
    · have hc := tmColumns_shape ht
      rcases hs with h|h
      · rw [hc.2.1] at h; cases h
      · rw [hc.2.2] at h; cases h
    · rcases hs with h|h <;> cases h
    · exact ⟨rfl,rfl,fun _ => rfl⟩

theorem right_initial_shape {f : Nat} {t : Quad TMColor}
    (hf : f=2 ∨ f=10) (ht : t ∈ tmFamily f) (hw : t.w=.iR) :
    t.e=.iR ∧ (f=10 → t.n=.symbol false) := by
  rcases hf with rfl|rfl
  · simp only [tmFamily,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · cases hw
    · exact ⟨rfl,by intro h; contradiction⟩
  · rw [family10_iR_init ht hw]
    exact ⟨rfl,fun _ => rfl⟩

/-- Trace iL back from the center, without assuming an already initialized
    row. Each actual left-side cell is forced to pass the signal. -/
theorem left_signal_propagates {tile : Int → Quad TMColor} {a : Int} (ha : a<0)
    (hm : ∀ x, a≤x → x<0 → (tile x).e=(tile (x+1)).w)
    (hp : ∀ x, a≤x → x<0 → (tile x).e=.iL → (tile x).w=.iL)
    (hs : (tile 0).w=.iL) : (tile a).w=.iL := by
  have he : (tile (-(-a))).w=(tile (-0)).w := by
    apply guarded_wire_constant (edge:=fun x => (tile (-x)).w) (P:=fun v => v=TMColor.iL)
      (a:=0) (b:= -a) (by omega) (by simpa using hs)
    intro x hx0 hxa hprev
    have hmatch := hm (-x) (by omega) (by omega)
    have hpos : -x+1=-(x-1) := by omega
    rw [hpos] at hmatch
    have hin : (tile (-x)).e=.iL := hmatch.trans hprev
    have hout := hp (-x) (by omega) (by omega) hin
    exact hout.trans hprev.symm
  simpa using he.trans hs

/-- Trace iR from the first head tile to any later positive tape column. -/
theorem right_signal_propagates {tile : Int → Quad TMColor} {b : Int} (hb : 1<b)
    (hm : ∀ x, 1≤x → x<b → (tile x).e=(tile (x+1)).w)
    (hp : ∀ x, 1<x → x<b → (tile x).w=.iR → (tile x).e=.iR)
    (hs : (tile 1).e=.iR) : (tile b).w=.iR := by
  have he : (tile (b-1)).e=(tile 1).e := by
    apply guarded_wire_constant (edge:=fun x => (tile x).e) (P:=fun v => v=TMColor.iR)
      (a:=1) (b:=b-1) (by omega) hs
    intro x hx hxb hprev
    have hmatch := hm (x-1) (by omega) (by omega)
    have hpos : x-1+1=x := by omega
    rw [hpos] at hmatch
    have hin : (tile x).w=.iR := hmatch.symm.trans hprev
    have hout := hp x hx (by omega) hin
    exact hout.trans hprev.symm
  have hmatch := hm (b-1) (by omega) (by omega)
  have hpos : b-1+1=b := by omega
  rw [hpos] at hmatch
  exact hmatch.symm.trans (he.trans hs)

/-- The only geometric input is the exact center-line base classes, plus
    actual channel constraints; no head or initialized tape is postulated. -/
structure InitialLine (k : Nat) where
  tile : Int → Quad TMColor
  group : Int → Nat × Nat × Nat
  groupMem : ∀ x, group x ∈ exactGroups.toList
  tmMem : ∀ x, tile x ∈ tmFamily (group x).2.2
  matchH : ∀ x, (tile x).e=(tile (x+1)).w
  seed : tile 0 ∈ tmFamily 5
  leftClass : ∀ x, -(boardHalf (k+2) : Int)<x → x<0 → (group x).1 ∈ leftInitialBases
  rightClass : ∀ x, 0<x → x<(boardHalf (k+2) : Int) → (group x).1 ∈ rightInitialBases
  channel : ∀ x, -(boardHalf (k+2) : Int)<x → x<(boardHalf (k+2) : Int) →
    (groupChannel (group x)).n=0 ∨ (groupChannel (group x)).n=1 ∨ (groupChannel (group x)).n=3
  tapeChannel : ∀ x, TapeOffset (k+2) x → (groupChannel (group x)).n=1

namespace InitialLine

theorem start_forced {k : Nat} (L : InitialLine k) :
    L.tile 0=⟨.blank,.iH,.blank,.iL⟩ ∧ L.tile 1=⟨.head 0 false,.iR,.blank,.iH⟩ := by
  have hfree := (positiveTape_mem.mp (start_is_positive_tape k)).1
  exact concrete_seed_forces_head L.seed (L.groupMem 1) (L.tmMem 1)
    (L.tapeChannel 1 hfree) (by simpa using L.matchH 0)

theorem negative_tape_blank {k : Nat} (L : InitialLine k) {r : Int}
    (hr : TapeOffset (k+2) r) (hneg : r<0) : (L.tile r).n=.symbol false := by
  have classes : ∀ x, r≤x → x<0 →
      ((L.group x).2.2=1 ∨ (L.group x).2.2=8) ∧
      ((L.group x).2.2=8 ↔ (groupChannel (L.group x)).n=1) := by
    intro x hx hx0
    apply left_initial_group _ (L.groupMem x) (L.leftClass x (by have := hr.1; omega) hx0)
    apply L.channel x (by have := hr.1; omega) (by have := hr.2.1; omega)
  have hw : (L.tile r).w=.iL := by
    apply left_signal_propagates hneg (fun x _ _ => L.matchH x)
    · intro x hx hx0 he
      exact (left_initial_shape (classes x hx hx0).1 (L.tmMem x) (Or.inl he)).2.1
    · rw [L.start_forced.1]
  have hf : (L.group r).2.2=8 := (classes r (by omega) hneg).2.mpr (L.tapeChannel r hr)
  exact (left_initial_shape (classes r (by omega) hneg).1 (L.tmMem r) (Or.inr hw)).2.2 hf

theorem positive_tape_blank {k : Nat} (L : InitialLine k) {r : Int}
    (hr : TapeOffset (k+2) r) (hpos : 1<r) : (L.tile r).n=.symbol false := by
  have classes : ∀ x, 1<x → x≤r →
      ((L.group x).2.2=2 ∨ (L.group x).2.2=10) ∧
      ((L.group x).2.2=10 ↔ (groupChannel (L.group x)).n=1) := by
    intro x hx hxR
    apply right_initial_group _ (L.groupMem x) (L.rightClass x (by omega) (by have := hr.2.1; omega))
    apply L.channel x (by have := hr.1; omega) (by have := hr.2.1; omega)
  have hw : (L.tile r).w=.iR := by
    apply right_signal_propagates hpos (fun x _ _ => L.matchH x)
    · intro x hx hxR hw
      exact (right_initial_shape (classes x hx (by omega)).1 (L.tmMem x) hw).1
    · rw [L.start_forced.2]
  have hf : (L.group r).2.2=10 := (classes r hpos (by omega)).2.mpr (L.tapeChannel r hr)
  exact (right_initial_shape (classes r hpos (by omega)).1 (L.tmMem r) hw).2 hf

/-- Exact initial tape labels on the ordered logical grid, derived from the
    two-way signal propagation and the iX exclusion theorem. -/
theorem logical_initial {k : Nat} (L : InitialLine k) {i : Int} (hi : InTape (2^k) i) :
    (L.tile (physicalColumn k i hi)).n=vColor (blankConfiguration.row i) := by
  by_cases hz : i=0
  · subst i
    rw [physicalColumn_zero,L.start_forced.2]
    rfl
  · have hfree := physicalColumn_mem hi
    have hzero := physicalColumn_zero k
    by_cases hneg : i<0
    · have hs := physicalColumn_strict hi (logical_zero_in_tape k) hneg
      rw [hzero] at hs
      have hrneg : physicalColumn k i hi<0 := by have := hfree.2.2.1; omega
      rw [L.negative_tape_blank hfree hrneg]
      simp [blankConfiguration,Configuration.row,configRow,hz,vColor]
    · have hpos : 0<i := by omega
      have hs := physicalColumn_strict (logical_zero_in_tape k) hi hpos
      rw [hzero] at hs
      rw [L.positive_tape_blank hfree hs]
      simp [blankConfiguration,Configuration.row,configRow,hz,vColor]
end InitialLine

#print axioms InitialLine.logical_initial
end K230Verification
