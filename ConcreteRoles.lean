module
public import FullPlaneData
public import BoardChannels
public import FreeOffsets
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

@[expose] def groupChannel (g : Nat × Nat × Nat) : Quad Nat :=
  ⟨g.2.1/64%4,g.2.1/16%4,g.2.1/4%4,g.2.1%4⟩
@[expose] def hBoundary (b : Nat) : Prop := b=95 ∨ b=96 ∨ b=100 ∨ b=101 ∨ b=111 ∨ b=116
@[expose] def vBoundary (b : Nat) : Prop := b=134 ∨ b=136 ∨ b=140 ∨ b=142 ∨ b=150 ∨ b=151
instance (b : Nat) : Decidable (hBoundary b) := by unfold hBoundary; infer_instance
instance (b : Nat) : Decidable (vBoundary b) := by unfold vBoundary; infer_instance

/-- Every concrete group obeys straight copying away from the exact
    red-ring channel-side indices. Corner/midpoint cells have no channel. -/
theorem concrete_channel_copy : ∀ g ∈ exactGroups.toList,
    (¬hBoundary g.1 → (groupChannel g).e=(groupChannel g).w) ∧
    (¬vBoundary g.1 → (groupChannel g).n=(groupChannel g).s) := by decide

/-- Ordinary left/right/bottom/top side endpoint masks, read directly from
    the exact 226 groups. Digit 1 means zero, 2 means a, 3 means b. -/
theorem concrete_channel_sides : ∀ g ∈ exactGroups.toList,
    ((g.1=100 ∨ g.1=116) →
      ((groupChannel g).e=1 ∨ (groupChannel g).e=2) ∧
      ((groupChannel g).w=2 ∨ (groupChannel g).w=3)) ∧
    ((g.1=95 ∨ g.1=111) →
      ((groupChannel g).w=1 ∨ (groupChannel g).w=3) ∧ (groupChannel g).e=3) ∧
    ((g.1=136 ∨ g.1=142) →
      ((groupChannel g).n=1 ∨ (groupChannel g).n=2) ∧
      ((groupChannel g).s=2 ∨ (groupChannel g).s=3)) ∧
    ((g.1=134 ∨ g.1=140) →
      ((groupChannel g).s=1 ∨ (groupChannel g).s=3) ∧ (groupChannel g).n=3) := by decide

theorem concrete_level_two_sides : ∀ g ∈ exactGroups.toList,
    (g.1=101 → (groupChannel g).e=2 ∧ ((groupChannel g).w=2 ∨ (groupChannel g).w=3)) ∧
    (g.1=96 → (groupChannel g).w=2 ∧ (groupChannel g).e=3) ∧
    (g.1=151 → (groupChannel g).n=2 ∧ ((groupChannel g).s=2 ∨ (groupChannel g).s=3)) ∧
    (g.1=150 → (groupChannel g).s=2 ∧ (groupChannel g).n=3) := by decide

theorem concrete_group_bounds : ∀ g ∈ exactGroups.toList,
    g.1<156 ∧ g.2.1<256 ∧ g.2.2<14 := by decide

/-- Computation tiles occur only at the (1,1)-oriented lowest cross with
    both obstruction channels zero. Conversely that group uses family 13. -/
theorem concrete_comp_group : ∀ g ∈ exactGroups.toList,
    (g.2.2=13 ↔ g.1=155 ∧ g.2.1=85) := by decide

/-- Exact metadata needed to recover the forced center seed. -/
theorem concrete_seed_groups : ∀ g ∈ exactGroups.toList,
    (g.2.2=5 ↔ g.1=65 ∨ g.1=71 ∨ g.1=79 ∨ g.1=87) := by decide

/-- A row transmitter crosses only a zero horizontal channel and either an
    absent or b vertical channel. The forbidden a case is explicit. -/
theorem concrete_row_transmitter_mask : ∀ g ∈ exactGroups.toList,
    g.2.2=6 → (groupChannel g).e=1 ∧ (groupChannel g).w=1 ∧
    (groupChannel g).n=(groupChannel g).s ∧
    ((groupChannel g).n=0 ∨ (groupChannel g).n=3) := by decide

theorem concrete_column_transmitter_mask : ∀ g ∈ exactGroups.toList,
    (g.2.2=8 ∨ g.2.2=10 ∨ g.2.2=12) →
      (groupChannel g).n=1 ∧ (groupChannel g).s=1 ∧
      (groupChannel g).e=(groupChannel g).w := by decide

theorem concrete_absorber_groups : ∀ g ∈ exactGroups.toList,
    (g.2.2=7 ↔ g.1=95 ∧ g.2.1=49) ∧
    (g.2.2=9 ↔ (g.1=134 ∨ g.1=140) ∧ g.2.1=196) := by decide

@[expose] def fullChannels (t : Quad FullColor) : Quad Nat :=
  ⟨t.n.2.1,t.e.2.1,t.s.2.1,t.w.2.1⟩
@[expose] def fullTM (t : Quad FullColor) : Quad TMColor :=
  ⟨t.n.2.2,t.e.2.2,t.s.2.2,t.w.2.2⟩
@[expose] def fullBase (t : Quad FullColor) : Quad Nat :=
  ⟨t.n.1,t.e.1,t.s.1,t.w.1⟩

theorem exact_tile_decomposition {u : Quad FullColor} (hu : u ∈ exactFullPlaneTiles) :
    ∃ g ∈ exactGroups.toList, ∃ t ∈ tmFamily g.2.2, u=decorate g t := by
  obtain ⟨g,hg,ht⟩ := List.mem_flatMap.mp hu
  obtain ⟨t,ht,hu⟩ := List.mem_map.mp ht
  exact ⟨g,hg,t,ht,hu.symm⟩

theorem exact_tile_projections {u : Quad FullColor} (hu : u ∈ exactFullPlaneTiles) :
    ∃ g ∈ exactGroups.toList, fullTM u ∈ tmFamily g.2.2 ∧
      fullChannels u=groupChannel g ∧
      fullBase u=⟨(Wang156.tile g.1).n,(Wang156.tile g.1).e,
        (Wang156.tile g.1).s,(Wang156.tile g.1).w⟩ := by
  obtain ⟨g,hg,t,ht,rfl⟩ := exact_tile_decomposition hu
  exact ⟨g,hg,ht,rfl,rfl⟩

/-- Actual exact-table computation cells cannot choose idle once the lower
    tape label is nonblank. This is the local concrete-to-row bridge. -/
theorem concrete_computation_of_nonblank {g : Nat × Nat × Nat} {t : Quad TMColor}
    (hg : g ∈ exactGroups.toList) (hb : g.1=155) (hc : g.2.1=85)
    (ht : t ∈ tmFamily g.2.2) (hs : t.s ≠ .blank) : t ∈ tmComp := by
  have hf : g.2.2=13 := (concrete_comp_group g hg).mpr ⟨hb,hc⟩
  rw [hf] at ht
  have he : t ∈ tmComp ∨ t=tmBlank := by simpa [tmFamily] using ht
  rcases he with h | h
  · exact h
  · subst t; exact False.elim (hs rfl)

@[expose] def isTapeData : TMColor → Bool
  | .symbol _ | .head _ _ => true
  | _ => false

/-- The exact comp list preserves nonblank tape-label status at every cell. -/
theorem concrete_comp_vertical_data : ∀ t ∈ tmComp,
    isTapeData t.n=true ∧ isTapeData t.s=true := by decide

@[expose] def colorKind : TMColor → Nat
  | .blank => 0 | .symbol _ => 1 | .head _ _ => 2 | .move _ _ => 3
  | .iL => 4 | .iR => 5 | .iH => 6 | .iX => 7

theorem colorKind_zero_iff (c : TMColor) : colorKind c=0 ↔ c=.blank := by cases c <;> simp [colorKind]
theorem colorKind_iL_iff (c : TMColor) : colorKind c=4 ↔ c=.iL := by cases c <;> simp [colorKind]
theorem colorKind_iR_iff (c : TMColor) : colorKind c=5 ↔ c=.iR := by cases c <;> simp [colorKind]
theorem colorKind_iH_iff (c : TMColor) : colorKind c=6 ↔ c=.iH := by cases c <;> simp [colorKind]
theorem colorKind_iX_iff (c : TMColor) : colorKind c=7 ↔ c=.iX := by cases c <;> simp [colorKind]

/-- No spurious initialization endpoint is hidden in a union of TM roles.
    These facts are checked against every member of every actual template. -/
theorem concrete_initial_endpoint_kinds : ∀ f ∈ List.range 14, ∀ t ∈ tmFamily f,
    ((colorKind t.e=6 ∨ colorKind t.e=7) → f=5) ∧
    (colorKind t.w=6 → f=10) ∧ (colorKind t.w=7 → f=11) ∧
    ((colorKind t.e=4 ∧ colorKind t.w≠4) → f=4) ∧
    ((colorKind t.w=5 ∧ colorKind t.e≠5) → f=3) ∧
    (colorKind t.e=5 → colorKind t.w=5 ∨ colorKind t.w=6 ∨ colorKind t.w=7) ∧
    (colorKind t.w=4 → colorKind t.e=4 ∨ colorKind t.e=6 ∨ colorKind t.e=7) := by decide

theorem concrete_initial_south_kind : ∀ f ∈ List.range 14, ∀ t ∈ tmFamily f,
    (colorKind t.e=4 ∨ colorKind t.e=5 ∨ colorKind t.e=6 ∨ colorKind t.e=7 ∨
     colorKind t.w=4 ∨ colorKind t.w=5 ∨ colorKind t.w=6 ∨ colorKind t.w=7) → colorKind t.s=0 := by decide

theorem concrete_row_transmitter_shape {t : Quad TMColor} (ht : t ∈ tmFamily 6) :
    t.n=.blank ∧ t.s=.blank ∧ t.e=t.w := by
  obtain ⟨m,_,rfl⟩ := List.mem_map.mp ht
  exact ⟨rfl,rfl,rfl⟩

theorem concrete_column_transmitter_shape {t : Quad TMColor} (ht : t ∈ tmFamily 12) :
    t.e=.blank ∧ t.w=.blank ∧ t.n=t.s := by
  have h : t ∈ tmColumns ∨ t=tmBlank := by simpa [tmFamily] using ht
  rcases h with h | h
  · obtain ⟨m,_,rfl⟩ := List.mem_map.mp h
    exact ⟨rfl,rfl,rfl⟩
  · subst t; exact ⟨rfl,rfl,rfl⟩

theorem concrete_right_absorber_no_injection {t : Quad TMColor} (ht : t ∈ tmFamily 7) :
    t.n=.blank ∧ t.e=.blank ∧ t.s=.blank ∧
      (t.w=.blank ∨ ∃ q, t.w=.move .right q) := by
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp ht
  refine ⟨rfl,rfl,rfl,?_⟩
  rcases List.mem_cons.mp hm with h | h
  · exact Or.inl h
  · obtain ⟨_,hf⟩ := List.mem_filter.mp h
    cases m with
    | move d q =>
      cases d with
      | left => simp at hf
      | right => exact Or.inr ⟨q,rfl⟩
    | _ => simp at hf

theorem concrete_top_absorber_no_injection {t : Quad TMColor} (ht : t ∈ tmFamily 9) :
    t.n=.blank ∧ t.e=.blank ∧ t.w=.blank := by
  obtain ⟨m,_,rfl⟩ := List.mem_map.mp ht
  exact ⟨rfl,rfl,rfl⟩

#print axioms concrete_channel_copy
#print axioms concrete_channel_sides
#print axioms concrete_comp_group
#print axioms exact_tile_decomposition
#print axioms concrete_computation_of_nonblank
#print axioms concrete_initial_endpoint_kinds
end K230Verification
