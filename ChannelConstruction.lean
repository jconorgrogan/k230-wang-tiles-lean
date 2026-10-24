module
public import BoardChannels
public section
namespace K230Verification

/-- Explicit obstruction-channel value on the edge from x to x+1.
    Its definition needs no choice of a completion or unknown parent tile. -/
@[expose] noncomputable def segmentChannel (covered : Int → Prop) (x : Int) : Channel := by
  classical
  exact if ∃ t, t ≤ x ∧ covered t then .b
    else if ∃ t, x < t ∧ covered t then .a else .zero

theorem segmentChannel_compatible (covered : Int → Prop) (x : Int) :
    SegmentCompatible covered x (segmentChannel covered x) := by
  classical
  unfold SegmentCompatible segmentChannel
  by_cases hl : ∃ t, t ≤ x ∧ covered t
  · rw [if_pos hl]
    by_cases hr : ∃ t, x < t ∧ covered t
    · simp [hl,hr,EndAllows]
    · simp [hl,hr,EndAllows]
  · rw [if_neg hl]
    by_cases hr : ∃ t, x < t ∧ covered t
    · simp [hl,hr,EndAllows]
    · simp [hl,hr,EndAllows]

theorem segmentChannel_zero_iff (covered : Int → Prop) (x : Int) :
    segmentChannel covered x = .zero ↔ ¬∃ t, covered t :=
  zero_iff_line_free (segmentChannel_compatible covered x)

/-- A non-ring exposed cell copies the constructed channel exactly. -/
theorem segmentChannel_copy {covered : Int → Prop} {x : Int} (hx : ¬covered x) :
    segmentChannel covered (x-1) = segmentChannel covered x := by
  classical
  have hl : (∃ t, t ≤ x-1 ∧ covered t) ↔ ∃ t, t ≤ x ∧ covered t := by
    constructor
    · rintro ⟨t,ht,hc⟩
      exact ⟨t,by omega,hc⟩
    · rintro ⟨t,ht,hc⟩
      have hn : t≠x := by intro he; subst t; exact hx hc
      exact ⟨t,by omega,hc⟩
  have hr : (∃ t, x-1 < t ∧ covered t) ↔ ∃ t, x < t ∧ covered t := by
    constructor
    · rintro ⟨t,ht,hc⟩
      have hn : t≠x := by intro he; subst t; exact hx hc
      exact ⟨t,by omega,hc⟩
    · rintro ⟨t,ht,hc⟩
      exact ⟨t,by omega,hc⟩
  simp only [segmentChannel,hl,hr]

/-- At a child board's left or bottom side, the parent-facing edge carries
    a or b, exactly the permitted outer-left mask. -/
theorem segmentChannel_outer_left {covered : Int → Prop} {x : Int} (hx : covered (x+1)) :
    EndAllows .outerLeft (segmentChannel covered x) := by
  classical
  have hr : ∃ t, x<t ∧ covered t := ⟨x+1,by omega,hx⟩
  unfold segmentChannel
  by_cases hl : ∃ t, t≤x ∧ covered t <;> simp [hl,hr,EndAllows]

/-- At a child board's right or top side, the parent-facing edge is b. -/
theorem segmentChannel_outer_right {covered : Int → Prop} {x : Int} (hx : covered x) :
    segmentChannel covered x = .b := by
  classical
  have hl : ∃ t, t≤x ∧ covered t := ⟨x,Int.le_refl x,hx⟩
  simp [segmentChannel,hl]

/-- The enclosing board's left/bottom inner edge has its allowed value. -/
theorem segmentChannel_inner_left {covered : Int → Prop} {H : Int}
    (hb : ∀ t, covered t → -H<t) :
    EndAllows .innerLeft (segmentChannel covered (-H)) := by
  classical
  have hn : ¬∃ t, t≤-H ∧ covered t := by
    rintro ⟨t,ht,hc⟩
    have := hb t hc
    omega
  unfold segmentChannel
  rw [if_neg hn]
  split <;> simp [EndAllows]

/-- The enclosing board's right/top inner edge has its allowed value. -/
theorem segmentChannel_inner_right {covered : Int → Prop} {H : Int}
    (hb : ∀ t, covered t → t<H) :
    EndAllows .innerRight (segmentChannel covered (H-1)) := by
  classical
  have hn : ¬∃ t, H-1<t ∧ covered t := by
    rintro ⟨t,ht,hc⟩
    have := hb t hc
    omega
  unfold segmentChannel
  by_cases hl : ∃ t, t≤H-1 ∧ covered t <;> simp [hl,hn,EndAllows]

/-- The explicit construction has the upper-half b property needed by the
    actual transmitter mask, not merely the abstract forward constraints. -/
theorem constructed_upper_blocked_b {covered : Int → Prop} {x : Int}
    (hsym : ∀ t, covered t → covered (-t)) (hcenter : ¬covered 0)
    (hne : ∃ t, covered t) (hx : 0≤x) :
    segmentChannel covered x = .b :=
  upper_blocked_segment_is_b hsym hcenter hne hx (segmentChannel_compatible covered x)

#print axioms segmentChannel_compatible
#print axioms segmentChannel_copy
#print axioms segmentChannel_outer_left
#print axioms segmentChannel_outer_right
end K230Verification
