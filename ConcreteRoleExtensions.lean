module
public import ConcreteRoles
public import TMCoreBridge
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

/-- The converse masks remove any need for a separate scale-dependent
    transmitter type classification in an exposed channel segment. -/
theorem concrete_row_mask_forces_family : ∀ g ∈ exactGroups.toList,
    (groupChannel g).e=1 → (groupChannel g).w=1 →
    (groupChannel g).n=(groupChannel g).s →
    ((groupChannel g).n=0 ∨ (groupChannel g).n=3) → g.2.2=6 := by decide

theorem concrete_column_mask_forces_family : ∀ g ∈ exactGroups.toList,
    (groupChannel g).n=1 → (groupChannel g).s=1 →
    (groupChannel g).e=(groupChannel g).w →
    ((groupChannel g).e=0 ∨ (groupChannel g).e=2 ∨ (groupChannel g).e=3) →
      g.2.2=8 ∨ g.2.2=10 ∨ g.2.2=12 := by decide

theorem concrete_both_zero_forces_comp : ∀ g ∈ exactGroups.toList,
    (groupChannel g).n=1 → (groupChannel g).s=1 →
    (groupChannel g).e=1 → (groupChannel g).w=1 → g.2.2=13 := by decide

theorem concrete_iX_requires_a : ∀ g ∈ exactGroups.toList,
    g.2.2=11 → (groupChannel g).n=2 ∧ (groupChannel g).s=2 := by decide

theorem tmColumns_shape {t : Quad TMColor} (ht : t ∈ tmColumns) :
    t.n=t.s ∧ t.e=.blank ∧ t.w=.blank := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ht
  exact ⟨rfl,rfl,rfl⟩

/-- Above the forced initial row every incoming tape label is nonblank.
    This eliminates every initialization alternative in a column family,
    without assuming that all off-center initialization signals are absent. -/
theorem concrete_column_nonblank_copies {f : Nat} {t : Quad TMColor}
    (hf : f=8 ∨ f=10 ∨ f=12) (ht : t ∈ tmFamily f) (hs : t.s≠.blank) :
    t.n=t.s ∧ t.e=.blank ∧ t.w=.blank := by
  have hc : t ∈ tmColumns := by
    rcases hf with rfl|rfl|rfl
    · simp only [tmFamily,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with h | (rfl|rfl)
      · exact h
      · exact False.elim (hs rfl)
      · exact False.elim (hs rfl)
    · simp only [tmFamily,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with h | (rfl|rfl|rfl)
      · exact h
      · exact False.elim (hs rfl)
      · exact False.elim (hs rfl)
      · exact False.elim (hs rfl)
    · simp only [tmFamily,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with h|rfl
      · exact h
      · exact False.elim (hs rfl)
  exact tmColumns_shape hc

theorem family10_iH_start {t : Quad TMColor} (ht : t ∈ tmFamily 10) (hw : t.w=.iH) :
    t=⟨.head 0 false,.iR,.blank,.iH⟩ := by
  simp only [tmFamily,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with h | (rfl|rfl|rfl)
  · have hc := (tmColumns_shape h).2.2
    rw [hc] at hw
    cases hw
  · cases hw
  · cases hw
  · rfl

theorem family8_iL_init {t : Quad TMColor} (ht : t ∈ tmFamily 8) (he : t.e=.iL) :
    t=⟨.symbol false,.iL,.blank,.iL⟩ := by
  simp only [tmFamily,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with h | (rfl|rfl)
  · have hc := (tmColumns_shape h).2.1
    rw [hc] at he
    cases he
  · cases he
  · rfl

theorem family10_iR_init {t : Quad TMColor} (ht : t ∈ tmFamily 10) (hw : t.w=.iR) :
    t=⟨.symbol false,.iR,.blank,.iR⟩ := by
  simp only [tmFamily,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with h | (rfl|rfl|rfl)
  · have hc := (tmColumns_shape h).2.2
    rw [hc] at hw
    cases hw
  · cases hw
  · rfl
  · cases hw

/-- A concrete cell at the zero/zero channel intersection with nonblank
    incoming tape data satisfies the already-verified row transition relation. -/
theorem concrete_zero_intersection_allowed {g : Nat × Nat × Nat} {t : Quad TMColor}
    (hg : g ∈ exactGroups.toList) (hn : (groupChannel g).n=1)
    (hs : (groupChannel g).s=1) (he : (groupChannel g).e=1) (hw : (groupChannel g).w=1)
    (ht : t ∈ tmFamily g.2.2) (hdata : t.s≠.blank) :
    Allowed k230Machine (parseV t.n) (parseH t.e) (parseV t.s) (parseH t.w) := by
  have hf := concrete_both_zero_forces_comp g hg hn hs he hw
  rw [hf] at ht
  have hc : t ∈ tmComp ∨ t=tmBlank := by simpa [tmFamily] using ht
  rcases hc with hc|rfl
  · exact tmComp_sound hc
  · exact False.elim (hdata rfl)

/-- Offset +1 is genuinely free in every computing board. This statement
    intentionally starts at board index k+2 and excludes inert level-2 boards. -/
theorem start_column_channel_zero {k : Nat} {s : Int} {c : Channel}
    (hc : SegmentCompatible (BoardCovered (k+2) 1) s c) : c=.zero := by
  have hfree := (positiveTape_mem.mp (start_is_positive_tape k)).1.2.2.2
  exact (board_zero_iff_free hc).mpr hfree

/-- Decisive concrete seed exclusion: an iX seed can only feed family 11,
    which requires channel a. A free east-neighbor tape column has channel
    zero, so the seed MUST feed the q0/blank start-head tile instead. -/
theorem concrete_seed_forces_head {seed next : Quad TMColor} {g : Nat × Nat × Nat}
    (hseed : seed ∈ tmFamily 5) (hg : g ∈ exactGroups.toList)
    (hnext : next ∈ tmFamily g.2.2) (hzero : (groupChannel g).n=1)
    (hmatch : seed.e=next.w) :
    seed=⟨.blank,.iH,.blank,.iL⟩ ∧ next=⟨.head 0 false,.iR,.blank,.iH⟩ := by
  have hb := concrete_group_bounds g hg
  have hi := concrete_initial_endpoint_kinds g.2.2 (List.mem_range.mpr hb.2.2) next hnext
  simp only [tmFamily,List.mem_cons,List.not_mem_nil,or_false] at hseed
  rcases hseed with rfl|rfl
  · have hw : next.w=.iH := hmatch.symm
    have hf : g.2.2=10 := hi.2.1 (by rw [hw]; rfl)
    rw [hf] at hnext
    exact ⟨rfl,family10_iH_start hnext hw⟩
  · have hw : next.w=.iX := hmatch.symm
    have hf : g.2.2=11 := hi.2.2.1 (by rw [hw]; rfl)
    have ha := (concrete_iX_requires_a g hg hf).1
    omega

#print axioms concrete_row_mask_forces_family
#print axioms concrete_column_mask_forces_family
#print axioms concrete_column_nonblank_copies
#print axioms concrete_zero_intersection_allowed
#print axioms start_column_channel_zero
#print axioms concrete_seed_forces_head
end K230Verification
