module
public import ExactTable
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Wang156

@[expose] def parityBoundsCheck : Bool := (List.range 156).all fun k =>
  decide ((tile k).px < 2 ∧ (tile k).py < 2)
@[expose] def sigmaDataCheck : Bool := (List.range 156).all fun k => (List.range 4).all fun q =>
  decide (sigma k q < 156) && (tile (sigma k q)).px == q%2 && (tile (sigma k q)).py == q/2
@[expose] def sigmaEq (k u : Nat) : Bool := (List.range 4).all fun q => sigma k q == sigma u q
@[expose] def sigmaInjectiveCheck : Bool := (List.range 156).all fun k => (List.range 156).all fun u =>
  !sigmaEq k u || k == u
@[expose] def horizontalParityCheck : Bool := (List.range 156).all fun k => (List.range 156).all fun u =>
  !((tile k).e == (tile u).w) || ((tile k).px + (tile u).px == 1 && (tile k).py == (tile u).py)
@[expose] def verticalParityCheck : Bool := (List.range 156).all fun k => (List.range 156).all fun u =>
  !((tile k).n == (tile u).s) || ((tile k).px == (tile u).px && (tile k).py + (tile u).py == 1)

theorem parityBoundsChecked : parityBoundsCheck = true := by decide +kernel
theorem sigmaDataChecked : sigmaDataCheck = true := by decide +kernel
theorem sigmaInjectiveChecked : sigmaInjectiveCheck = true := by decide +kernel
theorem horizontalParityChecked : horizontalParityCheck = true := by decide +kernel
theorem verticalParityChecked : verticalParityCheck = true := by decide +kernel

theorem parity_bounds (k : Fin 156) : (tile k.val).px < 2 ∧ (tile k.val).py < 2 := by
  exact of_decide_eq_true (List.all_eq_true.mp parityBoundsChecked k.val (List.mem_range.mpr k.isLt))

theorem sigma_data (k : Fin 156) (q : Fin 4) : sigma k.val q.val < 156 ∧
    (tile (sigma k.val q.val)).px = q.val%2 ∧ (tile (sigma k.val q.val)).py = q.val/2 := by
  have hk := List.all_eq_true.mp sigmaDataChecked k.val (List.mem_range.mpr k.isLt)
  have hq := List.all_eq_true.mp hk q.val (List.mem_range.mpr q.isLt)
  simpa [and_assoc] using hq

theorem sigma_closed (k : Fin 156) (q : Fin 4) : sigma k.val q.val < 156 := (sigma_data k q).1

theorem sigma_parity (k : Fin 156) (q : Fin 4) :
    (tile (sigma k.val q.val)).px = q.val%2 ∧ (tile (sigma k.val q.val)).py = q.val/2 := (sigma_data k q).2

theorem sigma_injective (k u : Fin 156) (h : ∀ q : Fin 4, sigma k.val q.val = sigma u.val q.val) : k = u := by
  have hk := List.all_eq_true.mp sigmaInjectiveChecked k.val (List.mem_range.mpr k.isLt)
  have hu := List.all_eq_true.mp hk u.val (List.mem_range.mpr u.isLt)
  have heq : sigmaEq k.val u.val = true := by
    apply List.all_eq_true.mpr
    intro q hq
    simpa using h ⟨q,List.mem_range.mp hq⟩
  apply Fin.ext
  simpa [heq] using hu

theorem horizontal_parity (k u : Fin 156) (h : (tile k.val).e = (tile u.val).w) :
    (tile k.val).px + (tile u.val).px = 1 ∧ (tile k.val).py = (tile u.val).py := by
  have hk := List.all_eq_true.mp horizontalParityChecked k.val (List.mem_range.mpr k.isLt)
  have hu := List.all_eq_true.mp hk u.val (List.mem_range.mpr u.isLt)
  simpa [h] using hu

theorem vertical_parity (k u : Fin 156) (h : (tile k.val).n = (tile u.val).s) :
    (tile k.val).px = (tile u.val).px ∧ (tile k.val).py + (tile u.val).py = 1 := by
  have hk := List.all_eq_true.mp verticalParityChecked k.val (List.mem_range.mpr k.isLt)
  have hu := List.all_eq_true.mp hk u.val (List.mem_range.mpr u.isLt)
  simpa [h] using hu
#print axioms sigma_closed
#print axioms sigma_injective
#print axioms sigma_parity
#print axioms horizontal_parity
#print axioms vertical_parity
end Wang156
