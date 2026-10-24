module
public import RingInduction
public section
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification

theorem board_half_square (n : Nat) : boardHalf (n+1)=2*squareSize n := by
  simp [boardHalf,squareSize_power]

theorem centered_shift_period {h c a : Int} (hc : CenteredAt h c) (ha : (4*h)∣a) :
    CenteredAt h (c-a) := by
  unfold CenteredAt at *
  rw [Int.sub_emod,hc,Int.emod_eq_zero_of_dvd ha]
  simp only [Int.sub_zero]
  simpa only [hc] using Int.emod_emod c (4*h)

/-- Every actual red-ring cell strictly inside a canonical board belongs to
    the arithmetic union of its strictly smaller closed red squares. -/
theorem interior_red_covered (n v x y : Nat) (hv : v<4)
    (hx : 0<x ∧ x<4*squareSize n) (hy : 0<y ∧ y<4*squareSize n)
    (hs : redStatus (redBoard n v x y).val≠0) :
    BoardCovered (n+1) ((x:Int)-2*squareSize n) ((y:Int)-2*squareSize n) := by
  have hg := red_status_geometric n v x y hv (by omega) (by omega) hs
  rcases hg with hr | ⟨m,hm,hmn,cx,cy,hcx,hcy,hstat⟩
  · have hzero := rect_status_interior
      (L:=0) (R:=4*(squareSize n:Int)) (B:=0) (T:=4*(squareSize n:Int))
      (x:=(x:Int)) (y:=(y:Int)) (by omega)
    exact False.elim (hs (hr.trans hzero))
  · have hh := board_half_square n
    have hhp : (0:Int)<boardHalf m := by have := board_half_pos m; omega
    have hd : (4*(boardHalf m:Int))∣(2*(squareSize n:Int)) := by
      have h := lower_period_dvd_half hm (show m<n+1 by omega)
      rw [hh] at h
      simpa only [Int.natCast_mul,show ((2:Nat):Int)=2 by decide] using h
    have hcx' := centered_shift_period hcx hd
    have hcy' := centered_shift_period hcy hd
    have hb := rect_status_bounds (hstat ▸ hs)
    have hxI : ClosedInterval (boardHalf m) (cx-2*squareSize n) ((x:Int)-2*squareSize n) := by
      unfold ClosedInterval
      omega
    have hyI : ClosedInterval (boardHalf m) (cy-2*squareSize n) ((y:Int)-2*squareSize n) := by
      unfold ClosedInterval
      omega
    have hbx := (red_band_iff_closed_interval hhp).mpr ⟨cx-2*squareSize n,hcx',hxI⟩
    have hby := (red_band_iff_closed_interval hhp).mpr ⟨cy-2*squareSize n,hcy',hyI⟩
    refine ⟨?_,?_,m,hm,by omega,hbx,hby⟩ <;> rw [hh] <;> simp only [Int.natCast_mul,show ((2:Nat):Int)=2 by decide] <;> omega

/-- Exact-table copying has no spurious exception in an exposed interior
    cell. Both horizontal and vertical boundary-index exclusions hold. -/
theorem exposed_not_boundary (n v x y : Nat) (hv : v<4)
    (hx : 0<x ∧ x<4*squareSize n) (hy : 0<y ∧ y<4*squareSize n)
    (he : ¬BoardCovered (n+1) ((x:Int)-2*squareSize n) ((y:Int)-2*squareSize n)) :
    ¬hBoundary (redBoard n v x y).val ∧ ¬vBoundary (redBoard n v x y).val := by
  have hz : redStatus (redBoard n v x y).val=0 := by
    apply Classical.byContradiction
    intro hn
    exact he (interior_red_covered n v x y hv hx hy hn)
  have hb := red_status_boundary (redBoard n v x y)
  constructor
  · intro h
    have hh := hb.1 h
    omega
  · intro h
    have hh := hb.2 h
    omega

end K230Concrete
#print axioms K230Concrete.exposed_not_boundary
