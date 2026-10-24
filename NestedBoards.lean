module

public import Std

public section

/-!
Integer arithmetic for the coherent shifted-board witness.  Index n here
means board level 2(n+1).  No 2-adic type or completeness axiom is used.
The final gluing theorem is explicitly conditional on finite-patch overlap
coherence; it does not assert that a concrete TM decoration has that property.
-/

namespace K230NestedBoards

@[expose]
abbrev Point := Int × Int

@[expose]
def half : Nat → Int
  | 0 => 2
  | n + 1 => 4 * half n

@[expose]
def center : Nat → Int
  | 0 => -1
  | n + 1 => center n - 2 * half n

@[expose]
def lower (n : Nat) : Int := center n - half n
@[expose]
def upper (n : Nat) : Int := center n + half n
@[expose]
def shift (n : Nat) : Int := 2 * half n - center n

@[expose]
def InBoard (n : Nat) (p : Point) : Prop :=
  lower n ≤ p.1 ∧ p.1 ≤ upper n ∧ lower n ≤ p.2 ∧ p.2 ≤ upper n

theorem half_ge_two (n : Nat) : 2 ≤ half n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [half]; omega

theorem half_formula (n : Nat) : half n = 2 * (4 : Int)^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [half, ih, Int.pow_succ]
    omega

theorem center_formula (n : Nat) : 3 * center n = 1 - 2 * half n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [center, half]; omega

theorem lower_next (n : Nat) : lower (n+1) = lower n - 5 * half n := by
  simp only [lower, center, half]
  omega

theorem upper_next (n : Nat) : upper (n+1) = upper n + half n := by
  simp only [upper, center, half]
  omega

theorem board_step (n : Nat) (p : Point) (h : InBoard n p) : InBoard (n+1) p := by
  have hp := half_ge_two n
  simp only [InBoard] at h ⊢
  rw [lower_next, upper_next]
  omega

theorem board_mono (n m : Nat) (h : n ≤ m) (p : Point) :
    InBoard n p → InBoard m p := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact id
  | succ m ih =>
    intro hp
    by_cases hnm : n ≤ m
    · exact board_step m p (ih n hnm hp)
    · have hn : n = m + 1 := by omega
      subst n
      exact hp

theorem lower_bound (n : Nat) : lower n ≤ -3 - 2 * (n : Int) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hp := half_ge_two n
    rw [lower_next]
    omega

theorem upper_bound (n : Nat) : 1 + 2 * (n : Int) ≤ upper n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hp := half_ge_two n
    rw [upper_next]
    omega

theorem contains_box (R : Nat) (p : Point)
    (hx : -(R : Int) ≤ p.1 ∧ p.1 ≤ R)
    (hy : -(R : Int) ≤ p.2 ∧ p.2 ≤ R) : InBoard R p := by
  have hl := lower_bound R
  have hu := upper_bound R
  simp only [InBoard]
  omega

@[expose]
def coveringIndex (p : Point) : Nat := p.1.natAbs + p.2.natAbs

theorem coveringIndex_spec (p : Point) : InBoard (coveringIndex p) p := by
  have hx : p.1 ≤ (p.1.natAbs : Int) := Int.le_natAbs
  have hnx : -p.1 ≤ (p.1.natAbs : Int) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -p.1))
  have hy : p.2 ≤ (p.2.natAbs : Int) := Int.le_natAbs
  have hny : -p.2 ≤ (p.2.natAbs : Int) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -p.2))
  apply contains_box
  all_goals dsimp [coveringIndex]; omega

theorem boards_exhaust (p : Point) : ∃ n, InBoard n p :=
  ⟨coveringIndex p, coveringIndex_spec p⟩

theorem shift_center (n : Nat) : shift n + center n = 2 * half n := by
  simp only [shift]
  omega

theorem shift_formula (n : Nat) : 3 * shift n = 8 * half n - 1 := by
  have h := center_formula n
  simp only [shift]
  omega

theorem shift_step (n : Nat) : shift (n+1) - shift n = 8 * half n := by
  simp only [shift, center, half]
  omega

theorem shifted_interval (n : Nat) (x : Int)
    (h : lower n ≤ x ∧ x ≤ upper n) :
    half n ≤ shift n + x ∧ shift n + x ≤ 3 * half n := by
  simp only [lower, upper, shift] at h ⊢
  omega

@[expose]
def geometric4 : Nat → Int
  | 0 => 0
  | k + 1 => 4 * geometric4 k + 1

theorem half_add (n k : Nat) :
    half (n + k) = half n * (3 * geometric4 k + 1) := by
  induction k with
  | zero => simp [geometric4]
  | succ k ih =>
    change 4 * half (n+k) = half n * (3 * (4 * geometric4 k + 1) + 1)
    rw [ih]
    have hg : 3 * (4 * geometric4 k + 1) + 1 = 4 * (3 * geometric4 k + 1) := by omega
    rw [hg]
    exact Int.mul_left_comm 4 (half n) (3 * geometric4 k + 1)

theorem shift_add (n k : Nat) :
    shift (n + k) - shift n = (8 * half n) * geometric4 k := by
  induction k with
  | zero => simp [geometric4]
  | succ k ih =>
    have hs := shift_step (n+k)
    have hh := half_add n k
    have ha : n + (k+1) = n+k+1 := by omega
    calc
      shift (n + (k+1)) - shift n =
          (shift (n+k) - shift n) + 8 * half (n+k) := by rw [ha]; omega
      _ = (8 * half n) * geometric4 k + 8 * (half n * (3 * geometric4 k + 1)) := by rw [ih, hh]
      _ = (8 * half n) * geometric4 k + (8 * half n) * (3 * geometric4 k + 1) := by simp only [Int.mul_assoc]
      _ = (8 * half n) * (geometric4 k + (3 * geometric4 k + 1)) :=
        (Int.mul_add (8*half n) (geometric4 k) (3*geometric4 k+1)).symm
      _ = (8 * half n) * geometric4 (k+1) := by
        congr 1
        simp only [geometric4]
        omega

theorem shift_multiple (n m : Nat) (h : n ≤ m) :
    ∃ z : Int, shift m - shift n = (8 * half n) * z := by
  refine ⟨geometric4 (m-n), ?_⟩
  have hm : n + (m-n) = m := by omega
  simpa only [hm] using shift_add n (m-n)

/- Any coherent family of finite labels on these nested squares has a
   total global extension, with exact agreement rather than a subsequence. -/

@[expose]
def Coherent {Tile : Type} (patch : Nat → Point → Tile) : Prop :=
  ∀ n m, n ≤ m → ∀ p, InBoard n p → patch m p = patch n p

@[expose]
def translated {Tile : Type} (f : Point → Tile) (n : Nat) (p : Point) : Tile :=
  f (shift n + p.1, shift n + p.2)

theorem translated_coherent {Tile : Type} (f : Point → Tile)
    (periodic : ∀ n p, InBoard n p → ∀ z : Int,
      f (shift n + p.1 + (8*half n)*z, shift n + p.2 + (8*half n)*z) =
        f (shift n + p.1, shift n + p.2)) : Coherent (translated f) := by
  intro n m hnm p hp
  obtain ⟨z, hz⟩ := shift_multiple n m hnm
  have hx : shift m + p.1 = shift n + p.1 + (8*half n)*z := by omega
  have hy : shift m + p.2 = shift n + p.2 + (8*half n)*z := by omega
  simp only [translated, hx, hy]
  exact periodic n p hp z

@[expose]
def glued {Tile : Type} (patch : Nat → Point → Tile) (p : Point) : Tile :=
  patch (coveringIndex p) p

theorem glued_agrees {Tile : Type} (patch : Nat → Point → Tile)
    (coherent : Coherent patch) (n : Nat) (p : Point) (hp : InBoard n p) :
    glued patch p = patch n p := by
  unfold glued
  cases Nat.le_total n (coveringIndex p) with
  | inl h => exact coherent n (coveringIndex p) h p hp
  | inr h => exact (coherent (coveringIndex p) n h p (coveringIndex_spec p)).symm

theorem pair_in_common_board (p q : Point) :
    ∃ n, InBoard n p ∧ InBoard n q := by
  refine ⟨coveringIndex p + coveringIndex q, ?_, ?_⟩
  · exact board_mono _ _ (by omega) p (coveringIndex_spec p)
  · exact board_mono _ _ (by omega) q (coveringIndex_spec q)

theorem glue_preserves_local_relations {Tile : Type} (patch : Nat → Point → Tile)
    (coherent : Coherent patch) (Adjacent : Point → Point → Prop)
    (Matches : Tile → Tile → Prop)
    (local_match : ∀ n p q, InBoard n p → InBoard n q → Adjacent p q →
      Matches (patch n p) (patch n q)) :
    ∀ p q, Adjacent p q → Matches (glued patch p) (glued patch q) := by
  intro p q hpq
  obtain ⟨n, hp, hq⟩ := pair_in_common_board p q
  rw [glued_agrees patch coherent n p hp, glued_agrees patch coherent n q hq]
  exact local_match n p q hp hq hpq

end K230NestedBoards

#print axioms K230NestedBoards.half_formula
#print axioms K230NestedBoards.center_formula
#print axioms K230NestedBoards.shift_multiple
#print axioms K230NestedBoards.translated_coherent
#print axioms K230NestedBoards.boards_exhaust
#print axioms K230NestedBoards.glued_agrees
#print axioms K230NestedBoards.glue_preserves_local_relations
