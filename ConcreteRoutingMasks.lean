module
public import ConcreteRoleExtensions
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

theorem concrete_NE_zero_comp : ∀ g ∈ exactGroups.toList,
    (groupChannel g).n=1 → (groupChannel g).e=1 → g.2.2=13 := by decide

theorem concrete_NS_zero_not_H_column : ∀ g ∈ exactGroups.toList,
    (groupChannel g).n=1 → (groupChannel g).s=1 → (groupChannel g).e≠1 →
    g.2.2=8 ∨ g.2.2=10 ∨ g.2.2=12 := by decide

theorem concrete_EW_zero_noncomp_row : ∀ g ∈ exactGroups.toList,
    (groupChannel g).e=1 → (groupChannel g).w=1 →
    ((groupChannel g).n=0 ∨ (groupChannel g).n=3) → g.2.2=6 := by decide

theorem concrete_left_wall_group : ∀ g ∈ exactGroups.toList, g.1=100 → g.2.2=0 := by decide

theorem concrete_right_wall_group : ∀ g ∈ exactGroups.toList, g.1=95 → g.2.2=0 ∨ g.2.2=7 := by decide

theorem concrete_left_wall_blank {g : Nat × Nat × Nat} {t : Quad TMColor}
    (hg : g ∈ exactGroups.toList) (hb : g.1=100) (ht : t ∈ tmFamily g.2.2) : t.e=.blank := by
  rw [concrete_left_wall_group g hg hb] at ht
  have ht' : t=tmBlank := by simpa [tmFamily] using ht
  rw [ht']; rfl

theorem concrete_right_wall_direction {g : Nat × Nat × Nat} {t : Quad TMColor}
    (hg : g ∈ exactGroups.toList) (hb : g.1=95) (ht : t ∈ tmFamily g.2.2) :
    t.w=.blank ∨ ∃ q, t.w=.move .right q := by
  rcases concrete_right_wall_group g hg hb with hf|hf
  · rw [hf] at ht
    have ht' : t=tmBlank := by simpa [tmFamily] using ht
    rw [ht']; exact Or.inl rfl
  · rw [hf] at ht
    exact (concrete_right_absorber_no_injection ht).2.2.2

theorem concrete_NE_zero_nonblank_comp {g : Nat × Nat × Nat} {t : Quad TMColor}
    (hg : g ∈ exactGroups.toList) (hn : (groupChannel g).n=1) (he : (groupChannel g).e=1)
    (ht : t ∈ tmFamily g.2.2) (hs : t.s≠.blank) : t ∈ tmComp := by
  rw [concrete_NE_zero_comp g hg hn he] at ht
  have hc : t ∈ tmComp ∨ t=tmBlank := by simpa [tmFamily] using ht
  rcases hc with hc|rfl
  · exact hc
  · exact False.elim (hs rfl)

#print axioms concrete_NE_zero_nonblank_comp
#print axioms concrete_left_wall_blank
#print axioms concrete_right_wall_direction
end K230Verification
