module
public import Std
public section
namespace K230Verification

/-- The three obstruction labels. No computation labels are involved here. -/
inductive Channel where | zero | a | b deriving DecidableEq
inductive End where | innerLeft | innerRight | outerLeft | outerRight deriving DecidableEq

@[expose] def EndAllows : End → Channel → Prop
  | .innerLeft, c => c = .zero ∨ c = .a
  | .innerRight, c => c = .zero ∨ c = .b
  | .outerLeft, c => c = .a ∨ c = .b
  | .outerRight, c => c = .b

/-- A segment is either the whole unobstructed line, its prefix, a gap
    between obstacles, or its suffix. This theorem states the actual endpoint
    constraints, not a presupposed value assignment. -/
theorem whole_segment {c : Channel}
    (hl : EndAllows .innerLeft c) (hr : EndAllows .innerRight c) : c = .zero := by
  cases c <;> simp_all [EndAllows]
theorem prefix_segment {c : Channel}
    (hl : EndAllows .innerLeft c) (hr : EndAllows .outerLeft c) : c = .a := by
  cases c <;> simp_all [EndAllows]
theorem middle_segment {c : Channel}
    (hl : EndAllows .outerRight c) (_hr : EndAllows .outerLeft c) : c = .b := hl
theorem suffix_segment {c : Channel}
    (hl : EndAllows .outerRight c) (_hr : EndAllows .innerRight c) : c = .b := hl

/-- A lower-level square spans precisely this residue band on one axis.
    For a level-2m square, h = 2^(2m-1). -/
@[expose] def RedBand (h t : Int) : Prop := h ≤ t % (4*h) ∧ t % (4*h) ≤ 3*h

theorem center_not_in_band {h : Int} (hh : 0 < h) : ¬ RedBand h 0 := by
  simp [RedBand]
  omega

theorem red_band_symmetric {h t : Int} (hh : 0 < h) (hb : RedBand h t) :
    RedBand h (-t) := by
  have hd : ¬ (4*h) ∣ t := by
    intro hd
    have hz := Int.emod_eq_zero_of_dvd hd
    unfold RedBand at hb
    omega
  have ha : ((4*h).natAbs : Int) = 4*h := Int.natAbs_of_nonneg (by omega)
  unfold RedBand at *
  rw [Int.neg_emod, if_neg hd, ha]
  omega

/-- The exposed cells in a fixed complete board are reflected about its
    center. A nonempty reflected obstruction set that omits the center
    always has an obstruction strictly below the center. -/
theorem symmetric_obstacle_below {covered : Int → Prop}
    (hsym : ∀ t, covered t → covered (-t))
    (hcenter : ¬ covered 0) (hne : ∃ t, covered t) :
    ∃ t, t < 0 ∧ covered t := by
  obtain ⟨t, ht⟩ := hne
  by_cases hneg : t < 0
  · exact ⟨t, hneg, ht⟩
  · have hnzero : t ≠ 0 := by intro e; exact hcenter (e ▸ ht)
    exact ⟨-t, by omega, hsym t ht⟩

/-- A finite board's exact one-dimensional lower-board obstruction set. -/
@[expose] def CoveredLine (H : Int) (halves : List Int) (t : Int) : Prop :=
  -H < t ∧ t < H ∧ ∃ h, h ∈ halves ∧ RedBand h t

theorem covered_line_symmetric {H : Int} {halves : List Int}
    (hpos : ∀ h, h ∈ halves → 0 < h) {t : Int}
    (ht : CoveredLine H halves t) : CoveredLine H halves (-t) := by
  rcases ht with ⟨hl, hr, h, hm, hb⟩
  exact ⟨by omega, by omega, h, hm, red_band_symmetric (hpos h hm) hb⟩

theorem covered_line_center_free {H : Int} {halves : List Int}
    (hpos : ∀ h, h ∈ halves → 0 < h) : ¬ CoveredLine H halves 0 := by
  rintro ⟨_, _, h, hm, hb⟩
  exact center_not_in_band (hpos h hm) hb

/-- A segment's endpoint types are determined by whether there is any
    obstruction before and after it. This is the finite-board segment rule. -/
@[expose] noncomputable def SegmentCompatible (covered : Int → Prop) (x : Int) (c : Channel) : Prop := by
  classical
  exact EndAllows (if ∃ t, t ≤ x ∧ covered t then .outerRight else .innerLeft) c ∧
  EndAllows (if ∃ t, x < t ∧ covered t then .outerLeft else .innerRight) c

theorem zero_iff_line_free {covered : Int → Prop} {x : Int} {c : Channel}
    (hc : SegmentCompatible covered x c) : c = .zero ↔ ¬ ∃ t, covered t := by
  classical
  unfold SegmentCompatible at hc
  by_cases hl : ∃ t, t ≤ x ∧ covered t
  · rw [if_pos hl] at hc
    have hb : c = .b := hc.1
    constructor
    · intro hz; cases hb.symm.trans hz
    · intro hn; obtain ⟨t, _, ht⟩ := hl; exact False.elim (hn ⟨t, ht⟩)
  · rw [if_neg hl] at hc
    by_cases hr : ∃ t, x < t ∧ covered t
    · rw [if_pos hr] at hc
      have ha := prefix_segment hc.1 hc.2
      constructor
      · intro hz; cases ha.symm.trans hz
      · intro hn; obtain ⟨t, _, ht⟩ := hr; exact False.elim (hn ⟨t, ht⟩)
    · rw [if_neg hr] at hc
      constructor
      · intro _ hn
        obtain ⟨t, ht⟩ := hn
        by_cases htx : t ≤ x
        · exact hl ⟨t, htx, ht⟩
        · exact hr ⟨t, by omega, ht⟩
      · intro _; exact whole_segment hc.1 hc.2

/-- Crucial transmitter lemma: a blocked column's exposed segment at or
    above the center has label b, never a. This holds at every board size. -/
theorem upper_blocked_segment_is_b {covered : Int → Prop} {x : Int} {c : Channel}
    (hsym : ∀ t, covered t → covered (-t)) (hcenter : ¬ covered 0)
    (hne : ∃ t, covered t) (hx : 0 ≤ x) (hc : SegmentCompatible covered x c) :
    c = .b := by
  classical
  obtain ⟨t, ht, hcov⟩ := symmetric_obstacle_below hsym hcenter hne
  have hl : ∃ t, t ≤ x ∧ covered t := ⟨t, by omega, hcov⟩
  unfold SegmentCompatible at hc
  rw [if_pos hl] at hc
  exact hc.1

/-- Local copying on every interior cell makes all edges of a finite
    exposed segment equal. -/
theorem copy_chain_constant {edge : Nat → Channel} {len : Nat}
    (hcopy : ∀ k, k < len → edge (k+1) = edge k) :
    ∀ k, k ≤ len → edge k = edge 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    exact (hcopy k (by omega)).trans (ih (by omega))

/-- Bridge from the actual local copy rules and the four endpoint rules to
    SegmentCompatible. The geometric endpoint identification is explicit:
    an obstacle before/after the segment selects an outer endpoint. -/
theorem segment_compatible_of_copy {covered : Int → Prop} {x : Int}
    {edge : Nat → Channel} {len i : Nat} (hi : i ≤ len)
    (hcopy : ∀ k, k < len → edge (k+1) = edge k)
    (hl : ((∃ t, t ≤ x ∧ covered t) → EndAllows .outerRight (edge 0)) ∧
          ((¬ ∃ t, t ≤ x ∧ covered t) → EndAllows .innerLeft (edge 0)))
    (hr : ((∃ t, x < t ∧ covered t) → EndAllows .outerLeft (edge len)) ∧
          ((¬ ∃ t, x < t ∧ covered t) → EndAllows .innerRight (edge len))) :
    SegmentCompatible covered x (edge i) := by
  classical
  have hi0 := copy_chain_constant hcopy i hi
  have hl0 := copy_chain_constant hcopy len (Nat.le_refl len)
  unfold SegmentCompatible
  constructor
  · rw [hi0]
    by_cases hb : ∃ t, t ≤ x ∧ covered t
    · rw [if_pos hb]; exact hl.1 hb
    · rw [if_neg hb]; exact hl.2 hb
  · rw [hi0, ←hl0]
    by_cases hb : ∃ t, x < t ∧ covered t
    · rw [if_pos hb]; exact hr.1 hb
    · rw [if_neg hb]; exact hr.2 hb

/-- Half-side of the even-level board, written as 2*4^(n-1).
    This equals 2^(2*n-1) for n >= 1. -/
@[expose] def boardHalf (n : Nat) : Nat := 2 * 4^(n-1)

theorem board_half_pos (n : Nat) : 0 < boardHalf n := by
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

theorem lower_half_bound {m n : Nat} (hm : 1 ≤ m) (hmn : m < n) :
    4 * boardHalf m ≤ boardHalf n := by
  have he : m-1+1=m := by omega
  have hp : 4^m ≤ 4^(n-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hs : 4^m = 4^(m-1)*4 := by
    calc
      4^m = 4^(m-1+1) := congrArg (fun z : Nat => 4^z) he.symm
      _ = 4^(m-1)*4 := Nat.pow_succ _ _
  rw [hs] at hp
  unfold boardHalf
  omega

theorem band_at_center {h : Int} (hh : 0 < h) : RedBand h (2*h) := by
  have he : (2*h) % (4*h) = 2*h := Int.emod_eq_of_lt (by omega) (by omega)
  unfold RedBand
  rw [he]
  omega

@[expose] def BlockedOffset (n : Nat) (r : Int) : Prop :=
  ∃ m : Nat, 1 ≤ m ∧ m < n ∧ RedBand (boardHalf m) r

/-- Exact intersection of the fixed column r with all smaller red squares
    inside the complete canonical board. -/
@[expose] def BoardCovered (n : Nat) (r s : Int) : Prop :=
  -(boardHalf n : Int) < s ∧ s < (boardHalf n : Int) ∧
  ∃ m : Nat, 1 ≤ m ∧ m < n ∧
    RedBand (boardHalf m) r ∧ RedBand (boardHalf m) s

theorem board_covered_symmetric {n : Nat} {r s : Int}
    (hc : BoardCovered n r s) : BoardCovered n r (-s) := by
  rcases hc with ⟨hl,hr,m,hm,hmn,hbr,hbs⟩
  have hp : (0 : Int) < boardHalf m := by
    have := board_half_pos m
    omega
  exact ⟨by omega,by omega,m,hm,hmn,hbr,red_band_symmetric hp hbs⟩

theorem board_center_free {n : Nat} {r : Int} : ¬ BoardCovered n r 0 := by
  rintro ⟨_,_,m,_,_,_,hb⟩
  have hp : (0 : Int) < boardHalf m := by
    have := board_half_pos m
    omega
  exact center_not_in_band hp hb

theorem board_covered_nonempty_iff {n : Nat} {r : Int} :
    (∃ s, BoardCovered n r s) ↔ BlockedOffset n r := by
  constructor
  · rintro ⟨s,_,_,m,hm,hmn,hbr,_⟩
    exact ⟨m,hm,hmn,hbr⟩
  · rintro ⟨m,hm,hmn,hbr⟩
    have hp : (0 : Int) < boardHalf m := by
      have := board_half_pos m
      omega
    have hbound : (4 : Int) * boardHalf m ≤ boardHalf n := by
      have h := Int.ofNat_le.mpr (lower_half_bound hm hmn)
      simpa [Int.natCast_mul] using h
    refine ⟨2*(boardHalf m : Int), ?_, ?_, m, hm, hmn, hbr, band_at_center hp⟩ <;> omega

/-- For every board level, zero is equivalent to a genuinely free line. -/
theorem board_zero_iff_free {n : Nat} {r s : Int} {c : Channel}
    (hc : SegmentCompatible (BoardCovered n r) s c) :
    c = .zero ↔ ¬ BlockedOffset n r := by
  rw [zero_iff_line_free hc, board_covered_nonempty_iff]

/-- For every board level, upper-half free computation rows can transmit
    across every blocked tape column: its channel label is b rather than a. -/
theorem board_upper_blocked_is_b {n : Nat} {r s : Int} {c : Channel}
    (hb : BlockedOffset n r) (hs : 0 ≤ s)
    (hc : SegmentCompatible (BoardCovered n r) s c) : c = .b := by
  exact upper_blocked_segment_is_b (covered := BoardCovered n r)
    (fun _ ht => board_covered_symmetric ht) board_center_free
    (board_covered_nonempty_iff.mpr hb) hs hc

#print axioms board_zero_iff_free
#print axioms board_upper_blocked_is_b
#print axioms red_band_symmetric
end K230Verification
