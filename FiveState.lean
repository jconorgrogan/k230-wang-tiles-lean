module
public import SideCertificates
public section
namespace K230Concrete

theorem sideZone_bound (h j : Nat) : sideZone h j < 5 := by
  simp only [sideZone]
  repeat' first | split | omega

theorem sideZone_step (h j : Nat) (hh : 0<h) (hj : j≤8*h) :
    sideZone (4*h) j = sideAdvance (sideZone h (j/4)) (j%4) := by
  simp only [sideZone,sideAdvance]
  repeat' first | split | omega

theorem sideZone_last_digit (h j : Nat) (hh : 0<h) (hj : j≤8*h) :
    sideZone h (j/4) ≠ 4 ∨ j%4=0 := by
  simp only [sideZone]
  repeat' first | split | omega

theorem five_state_invariant
    (half : Nat → Nat) (values : Nat → Nat → Nat)
    (evolve : Nat → Nat → Nat) (states : Nat → List Nat)
    (half_zero : half 0=8)
    (half_positive : ∀ n, 0<half n)
    (half_step : ∀ n, half (n+1)=4*half n)
    (value_step : ∀ n j, j≤2*half (n+1) →
      values (n+1) j = evolve (values n (j/4)) (j%4))
    (initial : ∀ j, j≤16 → values 0 j ∈ states (sideZone 8 j))
    (transition : ∀ state k digit, state<5 → k∈states state → digit<4 →
      (state≠4 ∨ digit=0) → evolve k digit ∈ states (sideAdvance state digit)) :
    ∀ n j, j≤2*half n → values n j ∈ states (sideZone (half n) j) := by
  intro n
  induction n with
  | zero =>
    intro j hj
    rw [half_zero] at hj ⊢
    exact initial j hj
  | succ n ih =>
    intro j hj
    have hs := half_step n
    have hp := half_positive n
    have hj' : j≤8*half n := by omega
    have hd : j/4≤2*half n := by omega
    have hz := sideZone_step (half n) j hp hj'
    have hv := sideZone_last_digit (half n) j hp hj'
    rw [value_step n j hj,hs,hz]
    exact transition _ _ _ (sideZone_bound _ _) (ih _ hd) (by omega) hv

end K230Concrete
