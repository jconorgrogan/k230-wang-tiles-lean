module
public import ExactTable
public import PhaseHierarchy
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace K230Concrete

open Wang156

@[expose] def childrenCheck : Bool := (List.range 156).all fun k =>
  (List.range 4).all fun q => sigma k q < 156
theorem children_checked : childrenCheck = true := by decide +kernel

theorem child_bound (k : Fin 156) (q : Nat) (hq : q < 4) : sigma k.val q < 156 := by
  have hk := List.all_eq_true.mp children_checked k.val (List.mem_range.mpr k.isLt)
  have h := List.all_eq_true.mp hk q (List.mem_range.mpr hq)
  simpa using h

@[expose] def child (k : Fin 156) (q : Nat) (hq : q < 4) : Fin 156 :=
  ⟨sigma k.val q, child_bound k q hq⟩

@[expose] def internalHCheck : Bool := (List.range 156).all fun k =>
  (List.range 2).all fun y => (tile (sigma k (2*y))).e == (tile (sigma k (2*y+1))).w
@[expose] def internalVCheck : Bool := (List.range 156).all fun k =>
  (List.range 2).all fun x => (tile (sigma k x)).n == (tile (sigma k (x+2))).s
@[expose] def forwardHCheck : Bool := (List.range 156).all fun k =>
  (List.range 156).all fun u => !((tile k).e == (tile u).w) ||
    ((tile (sigma k 1)).e == (tile (sigma u 0)).w &&
     (tile (sigma k 3)).e == (tile (sigma u 2)).w)
@[expose] def forwardVCheck : Bool := (List.range 156).all fun k =>
  (List.range 156).all fun u => !((tile k).n == (tile u).s) ||
    ((tile (sigma k 2)).n == (tile (sigma u 0)).s &&
     (tile (sigma k 3)).n == (tile (sigma u 1)).s)

theorem internalH_checked : internalHCheck = true := by decide +kernel
theorem internalV_checked : internalVCheck = true := by decide +kernel
theorem forwardH_checked : forwardHCheck = true := by decide +kernel
theorem forwardV_checked : forwardVCheck = true := by decide +kernel

theorem internal_horizontal (k : Fin 156) (y : Nat) (hy : y < 2) :
    (tile (sigma k.val (2*y))).e = (tile (sigma k.val (2*y+1))).w := by
  have hk := List.all_eq_true.mp internalH_checked k.val (List.mem_range.mpr k.isLt)
  have h := List.all_eq_true.mp hk y (List.mem_range.mpr hy)
  simpa using h

theorem internal_vertical (k : Fin 156) (x : Nat) (hx : x < 2) :
    (tile (sigma k.val x)).n = (tile (sigma k.val (x+2))).s := by
  have hk := List.all_eq_true.mp internalV_checked k.val (List.mem_range.mpr k.isLt)
  have h := List.all_eq_true.mp hk x (List.mem_range.mpr hx)
  simpa using h

theorem forward_horizontal (k u : Fin 156) (y : Nat) (hy : y < 2)
    (hmatch : (tile k.val).e = (tile u.val).w) :
    (tile (sigma k.val (2*y+1))).e = (tile (sigma u.val (2*y))).w := by
  have hk := List.all_eq_true.mp forwardH_checked k.val (List.mem_range.mpr k.isLt)
  have h := List.all_eq_true.mp hk u.val (List.mem_range.mpr u.isLt)
  have hh : (tile (sigma k.val 1)).e = (tile (sigma u.val 0)).w ∧
      (tile (sigma k.val 3)).e = (tile (sigma u.val 2)).w := by simpa [hmatch] using h
  have hy' : y = 0 ∨ y = 1 := by omega
  rcases hy' with rfl | rfl
  · exact hh.1
  · exact hh.2

theorem forward_vertical (k u : Fin 156) (x : Nat) (hx : x < 2)
    (hmatch : (tile k.val).n = (tile u.val).s) :
    (tile (sigma k.val (x+2))).n = (tile (sigma u.val x)).s := by
  have hk := List.all_eq_true.mp forwardV_checked k.val (List.mem_range.mpr k.isLt)
  have h := List.all_eq_true.mp hk u.val (List.mem_range.mpr u.isLt)
  have hh : (tile (sigma k.val 2)).n = (tile (sigma u.val 0)).s ∧
      (tile (sigma k.val 3)).n = (tile (sigma u.val 1)).s := by simpa [hmatch] using h
  have hx' : x = 0 ∨ x = 1 := by omega
  rcases hx' with rfl | rfl
  · exact hh.1
  · exact hh.2

@[expose] def width : Nat → Nat
  | 0 => 1
  | n+1 => 2 * width n

@[expose] def expanded : Nat → Fin 156 → Nat → Nat → Fin 156
  | 0, k, _, _ => k
  | n+1, k, x, y => child (expanded n k (x/2) (y/2)) (x%2 + 2*(y%2)) (by omega)

theorem width_pos (n : Nat) : 0 < width n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [width]; omega

theorem expanded_horizontal (n : Nat) (k : Fin 156) (x y : Nat)
    (hx : x+1 < width n) (hy : y < width n) :
    (tile (expanded n k x y).val).e = (tile (expanded n k (x+1) y).val).w := by
  induction n generalizing x y with
  | zero => simp only [width] at hx; omega
  | succ n ih =>
    simp only [width] at hx hy
    have hyr : y%2 < 2 := by omega
    have hyd : y/2 < width n := by omega
    by_cases hr : x%2 = 0
    · have hr1 : (x+1)%2 = 1 := by omega
      have hd : (x+1)/2 = x/2 := by omega
      simpa only [expanded, child, hr, hr1, hd, Nat.zero_add, Nat.add_comm] using
        internal_horizontal (expanded n k (x/2) (y/2)) (y%2) hyr
    · have hr1 : x%2 = 1 := by omega
      have hr0 : (x+1)%2 = 0 := by omega
      have hd : (x+1)/2 = x/2+1 := by omega
      have hxd : x/2+1 < width n := by omega
      have hm := ih (x/2) (y/2) hxd hyd
      simpa only [expanded, child, hr1, hr0, hd, Nat.zero_add, Nat.add_comm] using
        forward_horizontal (expanded n k (x/2) (y/2))
          (expanded n k (x/2+1) (y/2)) (y%2) hyr hm

theorem expanded_vertical (n : Nat) (k : Fin 156) (x y : Nat)
    (hx : x < width n) (hy : y+1 < width n) :
    (tile (expanded n k x y).val).n = (tile (expanded n k x (y+1)).val).s := by
  induction n generalizing x y with
  | zero => simp only [width] at hy; omega
  | succ n ih =>
    simp only [width] at hx hy
    have hxr : x%2 < 2 := by omega
    have hxd : x/2 < width n := by omega
    by_cases hr : y%2 = 0
    · have hr1 : (y+1)%2 = 1 := by omega
      have hd : (y+1)/2 = y/2 := by omega
      simpa only [expanded, child, hr, hr1, hd, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using
        internal_vertical (expanded n k (x/2) (y/2)) (x%2) hxr
    · have hr1 : y%2 = 1 := by omega
      have hr0 : (y+1)%2 = 0 := by omega
      have hd : (y+1)/2 = y/2+1 := by omega
      have hyd : y/2+1 < width n := by omega
      have hm := ih (x/2) (y/2) hxd hyd
      simpa only [expanded, child, hr1, hr0, hd, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using
        forward_vertical (expanded n k (x/2) (y/2))
          (expanded n k (x/2) (y/2+1)) (x%2) hxr hm

@[expose] def anchor : Fin 156 := ⟨155, by decide⟩
theorem anchor_fixed : expanded 2 anchor 1 1 = anchor := by decide +kernel

end K230Concrete

#print axioms K230Concrete.expanded_horizontal
#print axioms K230Concrete.expanded_vertical
#print axioms K230Concrete.anchor_fixed
