module
public import ModuloFourLocality
public import ConcreteBoards
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification

theorem redBoard_modulo_four (n : Nat) (hn : 1≤n) (v x y : Nat) :
    (HasHChannel (redBoard n v x y).val ↔ y%4=1) ∧
    (HasVChannel (redBoard n v x y).val ↔ x%4=1) := by
  have hd := four_dvd_squareSize n hn
  have hx := Nat.mod_mod_of_dvd x hd
  have hy := Nat.mod_mod_of_dvd y hd
  have he : 2*n=(2*n-2)+2 := by omega
  have h := expanded_modulo_four (2*n-2)
    (boardCore v (x/squareSize n) (y/squareSize n))
    (x%squareSize n) (y%squareSize n)
  rw [←he,hx,hy] at h
  exact h

theorem redBoard_lowest_cross (n : Nat) (hn : 1≤n) (v x y : Nat)
    (hx : x%4=1) (hy : y%4=1) : redBoard n v x y = anchor := by
  have hd := four_dvd_squareSize n hn
  have hxr : (x%squareSize n)%4=1 := (Nat.mod_mod_of_dvd x hd).trans hx
  have hyr : (y%squareSize n)%4=1 := (Nat.mod_mod_of_dvd y hd).trans hy
  have he : 2*n=(2*n-2)+2 := by omega
  have h := expanded_modulo_four_cross (2*n-2)
    (boardCore v (x/squareSize n) (y/squareSize n))
    (x%squareSize n) (y%squareSize n) hxr hyr
  rw [←he] at h
  exact h

@[expose] def coreSeedCheck : Bool := (List.range 4).all fun v =>
  decide (SeedBase (boardCore v 2 2).val)
theorem coreSeed_checked : coreSeedCheck = true := by decide +kernel

theorem boardCore_seed (v : Nat) (hv : v<4) : SeedBase (boardCore v 2 2).val :=
  of_decide_eq_true (List.all_eq_true.mp coreSeed_checked v (List.mem_range.mpr hv))

theorem redBoard_center (n v : Nat) (hv : v<4) :
    redBoard n v (2*squareSize n) (2*squareSize n) = boardCore v 2 2 := by
  have hd : 2*squareSize n/squareSize n=2 := Nat.mul_div_cancel _ (squareSize_pos n)
  have hm : 2*squareSize n%squareSize n=0 := Nat.mul_mod_left _ _
  simp only [redBoard,hd,hm]
  exact expanded_seed n _ (boardCore_seed v hv)

theorem redBoard_center_seed (n v : Nat) (hv : v<4) :
    SeedBase (redBoard n v (2*squareSize n) (2*squareSize n)).val := by
  rw [redBoard_center n v hv]
  exact boardCore_seed v hv

#print axioms redBoard_modulo_four
#print axioms redBoard_lowest_cross
#print axioms redBoard_center_seed
end K230Concrete
