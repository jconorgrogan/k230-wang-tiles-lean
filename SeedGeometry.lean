module
public import SeedCertificate
public import RingClassification
public import GeometricSubboards
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification

/-- Every exact seed is the root center or a canonical lower-board center. -/
@[expose] def SeedCenter (n x y : Nat) : Prop :=
  (x=2*squareSize n ∧ y=2*squareSize n) ∨
  ∃ m : Nat, 1≤m ∧ m≤n ∧
    CenteredAt (boardHalf m) x ∧ CenteredAt (boardHalf m) y

theorem seed_geometric (n v x y : Nat) (hv:v<4)
    (hx:x≤4*squareSize n) (hy:y≤4*squareSize n)
    (hs:SeedBase (redBoard n v x y).val) : SeedCenter n x y := by
  induction n generalizing x y with
  | zero =>
    apply Or.inl
    have he : redBoard 0 v x y=boardCore v x y := by
      simp only [redBoard,squareSize,width,Nat.mul_zero,Nat.div_one,Nat.mod_one,expanded]
    rw [he] at hs
    exact (core_seed_iff v x y hv hx hy).mp hs
  | succ n ih =>
    have hsz := squareSize_step n
    have hxd : x/4≤4*squareSize n := by omega
    have hyd : y/4≤4*squareSize n := by omega
    rw [redBoard_step n v x y hv hx hy] at hs
    obtain ⟨hx0,hy0,hs⟩ := (expanded_two_seed_iff _ _ _ (by omega) (by omega)).mp hs
    have hxe : (x:Int)=4*((x/4:Nat):Int) := by omega
    have hye : (y:Int)=4*((y/4:Nat):Int) := by omega
    rcases hs with hs | hs
    · rcases ih (x/4) (y/4) hxd hyd hs with ⟨hxc,hyc⟩ | ⟨m,hm,hmn,hxc,hyc⟩
      · apply Or.inl
        constructor <;> omega
      · apply Or.inr
        refine ⟨m+1,by omega,by omega,?_,?_⟩
        · have hh : (boardHalf (m+1):Int)=4*(boardHalf m:Int) := by
            exact_mod_cast board_half_step hm
          rw [hh,hxe]
          exact centered_scale hxc
        · have hh : (boardHalf (m+1):Int)=4*(boardHalf m:Int) := by
            exact_mod_cast board_half_step hm
          rw [hh,hye]
          exact centered_scale hyc
    · have hp := redBoard_parity n v (x/4) (y/4) hv hxd hyd
      rw [hp.1,hp.2] at hs
      apply Or.inr
      refine ⟨1,by omega,by omega,?_,?_⟩
      · change (x:Int)%8=4
        omega
      · change (y:Int)%8=4
        omega

/-- Subtracting an aligned root half-width preserves every lower center class. -/
theorem centered_sub_aligned {h c H : Int} (hh:0<h)
    (hc:CenteredAt h c) (hd:(4*h)∣H) : CenteredAt h (c-H) := by
  unfold CenteredAt at hc ⊢
  rw [Int.sub_emod,hc,Int.emod_eq_zero_of_dvd hd,Int.sub_zero]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem centered_is_band {h c : Int} (hh:0<h) (hc:CenteredAt h c) : RedBand h c := by
  unfold RedBand
  rw [hc]
  constructor <;> omega

theorem lower_center_strict {h H c : Int} (hh:0<h)
    (hc:CenteredAt h c) (hd:(4*h)∣H) (hlo:0≤c) (hhi:c≤2*H) :
    0<c ∧ c<2*H := by
  have hl := center_boundary_gap hh hc (show (0:Int)%(4*h)=0 by simp)
  have hr := center_boundary_gap hh hc
    (show (2*H)%(4*h)=0 from Int.emod_eq_zero_of_dvd (Int.dvd_mul_of_dvd_right hd))
  constructor
  · rcases hl with hl|hl <;> omega
  · rcases hr with hr|hr <;> omega

/-- In the exposed part of a canonical board, its center is the only actual
    mandatory seed. This includes all boundary positions in the input domain. -/
theorem exposed_seed_center (n v x y : Nat) (hv:v<4)
    (hx:x≤4*squareSize n) (hy:y≤4*squareSize n)
    (hs:SeedBase (redBoard n v x y).val)
    (he:¬BoardCovered (n+1)
      ((x:Int)-(boardHalf (n+1):Int)) ((y:Int)-(boardHalf (n+1):Int))) :
    x=2*squareSize n ∧ y=2*squareSize n := by
  rcases seed_geometric n v x y hv hx hy hs with hc | ⟨m,hm,hmn,hxc,hyc⟩
  · exact hc
  · exfalso
    apply he
    have hp : (0:Int)<boardHalf m := by have := board_half_pos m; omega
    have hd := lower_period_dvd_half hm (show m<n+1 by omega)
    have hy' : (y:Int)≤2*(boardHalf (n+1):Int) := by
      have hh := boardHalf_index n
      exact_mod_cast (show y≤2*boardHalf (n+1) by omega)
    have hsy := lower_center_strict hp hyc hd (by omega) hy'
    exact ⟨by omega,by omega,m,hm,by omega,
      centered_is_band hp (centered_sub_aligned hp hxc hd),
      centered_is_band hp (centered_sub_aligned hp hyc hd)⟩

end K230Concrete
#print axioms K230Concrete.seed_geometric
#print axioms K230Concrete.exposed_seed_center
