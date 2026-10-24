module
public import ChannelCompleteness
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

theorem reverse_row_family : ∀ g ∈ exactGroups.toList,
    (groupChannel g).e=1 → ((groupChannel g).n=0 ∨ (groupChannel g).n=3) →
    ¬hBoundary g.1 → g.2.2=6 := by decide

theorem reverse_column_families : ∀ g ∈ exactGroups.toList,
    (groupChannel g).n=1 → (groupChannel g).e≠1 → ¬vBoundary g.1 →
    g.2.2=8 ∨ g.2.2=10 ∨ g.2.2=12 := by decide

theorem reverse_comp_family : ∀ g ∈ exactGroups.toList,
    g.1=155 → g.2.1=85 → g.2.2=13 := by decide

theorem reverse_top_family : ∀ g ∈ exactGroups.toList,
    (g.1=134 ∨ g.1=140) → (groupChannel g).s=1 → g.2.2=9 := by decide

theorem reverse_right_absorber_family : ∀ g ∈ exactGroups.toList,
    g.1=95 → (groupChannel g).w=1 → g.2.2=7 := by decide

theorem column_template_member {f : Nat} (hf : f=8 ∨ f=10 ∨ f=12)
    {t : Quad TMColor} (ht : t ∈ tmColumns) : t ∈ tmFamily f := by
  rcases hf with rfl | rfl | rfl <;> simp only [tmFamily,List.mem_append] <;> exact Or.inl ht

theorem blank_template_member (f : Nat) (hf : f<14)
    (h3 : f≠3) (h4 : f≠4) (h5 : f≠5) (h9 : f≠9) : tmBlank ∈ tmFamily f := by
  have hc : f=0 ∨ f=1 ∨ f=2 ∨ f=6 ∨ f=7 ∨ f=8 ∨ f=10 ∨ f=11 ∨ f=12 ∨ f=13 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tmFamily,tmBlank]

#print axioms reverse_row_family
#print axioms reverse_column_families
#print axioms blank_template_member
end K230Verification
