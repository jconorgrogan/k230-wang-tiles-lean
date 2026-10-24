module
public import MaximalChildren
public section
set_option maxHeartbeats 0
namespace K230Verification

/-- On the closed root domain, the band's own residue constraint excludes
    both vertical root walls, so the two exposure interfaces agree exactly. -/
theorem rootCovered_iff_boardCovered {n : Nat} {r s : Int}
    (hr:-(boardHalf n:Int)≤r ∧ r≤boardHalf n) :
    RootCovered n (r,s) ↔ BoardCovered n r s := by
  constructor
  · intro h
    exact h.2.2
  · intro h
    have hc0 := h
    obtain ⟨_,_,m,hm,hmn,hbr,_⟩ := h
    have hp : (0:Int)<boardHalf m := by have := board_half_pos m; omega
    obtain ⟨c,hc,hcr⟩ := (red_band_iff_closed_interval hp).mp hbr
    have hd := lower_period_dvd_half hm hmn
    have hL : (-(boardHalf n:Int))%(4*boardHalf m)=0 :=
      Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr hd)
    have hR : (boardHalf n:Int)%(4*boardHalf m)=0 := Int.emod_eq_zero_of_dvd hd
    have hi := interval_strictly_inside hp hc hL hR hcr hr
    refine ⟨?_,?_,hc0⟩
    · have := hcr.1
      omega
    · have := hcr.2
      omega
end K230Verification
#print axioms K230Verification.rootCovered_iff_boardCovered
