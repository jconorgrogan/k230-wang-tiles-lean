module
public import ModuloFourCertificate
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification

theorem expanded_two_cross (k : Fin 156) : expanded 2 k 1 1 = anchor := by
  have h := (Bool.and_eq_true_iff.mp (locality_at_all k)).1
  apply Fin.ext
  simpa only [expanded_two_value,anchor,beq_iff_eq] using h

theorem expanded_two_locality (k : Fin 156) (x y : Nat) (hx : x<4) (hy : y<4) :
    (HasHChannel (expanded 2 k x y).val ↔ y=1) ∧
    (HasVChannel (expanded 2 k x y).val ↔ x=1) := by
  have hk := (Bool.and_eq_true_iff.mp (locality_at_all k)).2
  have hxy := List.all_eq_true.mp
    (List.all_eq_true.mp hk x (List.mem_range.mpr hx)) y (List.mem_range.mpr hy)
  simpa only [expanded_two_value] using of_decide_eq_true hxy

theorem expanded_two_seed (k : Fin 156) (hk : SeedBase k.val) : expanded 2 k 0 0 = k := by
  have h := List.all_eq_true.mp seedFixed_checked k.val hk
  apply Fin.ext
  simpa only [expanded_two_value,beq_iff_eq] using h

/-- The exact two-level suffix of every expansion, including translated cells. -/
theorem expanded_split_two (n : Nat) (k : Fin 156) (x y : Nat) :
    expanded (n+2) k x y =
      expanded 2 (expanded n k (x/4) (y/4)) (x%4) (y%4) := by
  have h := expanded_add 2 n k (x/4) (y/4) (x%4) (y%4) (by simp [width]; omega) (by simp [width]; omega)
  have hx : width 2*(x/4)+x%4=x := by simp [width]; omega
  have hy : width 2*(y/4)+y%4=y := by simp [width]; omega
  have hn : 2+n=n+2 := by omega
  simpa only [hx,hy,hn] using h

theorem expanded_modulo_four (n : Nat) (k : Fin 156) (x y : Nat) :
    (HasHChannel (expanded (n+2) k x y).val ↔ y%4=1) ∧
    (HasVChannel (expanded (n+2) k x y).val ↔ x%4=1) := by
  rw [expanded_split_two]
  exact expanded_two_locality _ _ _ (by omega) (by omega)

theorem expanded_modulo_four_cross (n : Nat) (k : Fin 156) (x y : Nat)
    (hx : x%4=1) (hy : y%4=1) : expanded (n+2) k x y = anchor := by
  rw [expanded_split_two,hx,hy]
  exact expanded_two_cross _

theorem expanded_seed (n : Nat) (k : Fin 156) (hk : SeedBase k.val) :
    expanded (2*n) k 0 0 = k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : 2*(n+1)=2*n+2 := by omega
    rw [hn,expanded_split_two]
    simpa only [Nat.zero_div,Nat.zero_mod,ih] using expanded_two_seed k hk

theorem four_dvd_squareSize (n : Nat) (hn : 1≤n) : 4 ∣ squareSize n := by
  have he : n=(n-1)+1 := by omega
  rw [he,squareSize_step]
  exact ⟨squareSize (n-1),rfl⟩

#print axioms expanded_two_cross
#print axioms expanded_two_locality
#print axioms expanded_two_seed
#print axioms expanded_modulo_four
#print axioms expanded_seed
end K230Concrete
