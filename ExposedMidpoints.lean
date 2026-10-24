module
public import SideMidpoints
public import RingExposure
public import RingBoundary
public section
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification

theorem exposed_red_on_root (n v x y : Nat) (hv:v<4)
    (hx:x≤4*squareSize n) (hy:y≤4*squareSize n)
    (he:¬BoardCovered (n+1) ((x:Int)-2*squareSize n) ((y:Int)-2*squareSize n))
    (hs:redStatus (redBoard n v x y).val≠0) :
    x=0 ∨ x=4*squareSize n ∨ y=0 ∨ y=4*squareSize n := by
  by_cases hb : x=0 ∨ x=4*squareSize n ∨ y=0 ∨ y=4*squareSize n
  · exact hb
  · exact False.elim (he (interior_red_covered n v x y hv (by omega) (by omega) hs))

theorem exposed_red_root_status (n v x y : Nat) (hv:v<4)
    (hx:x≤4*squareSize n) (hy:y≤4*squareSize n)
    (he:¬BoardCovered (n+1) ((x:Int)-2*squareSize n) ((y:Int)-2*squareSize n))
    (hs:redStatus (redBoard n v x y).val≠0) :
    redStatus (redBoard n v x y).val=
      rectStatus 0 (4*(squareSize n:Int)) 0 (4*(squareSize n:Int)) x y :=
  redBoard_ring_status n v x y hv hx hy (exposed_red_on_root n v x y hv hx hy he hs)

theorem rect_status_left_coordinate {L R B T x y : Int}
    (h:rectStatus L R B T x y=1) : x=L := by
  unfold rectStatus at h
  repeat first | split at h | omega

theorem rect_status_right_coordinate {L R B T x y : Int}
    (h:rectStatus L R B T x y=2) : x=R := by
  unfold rectStatus at h
  repeat first | split at h | omega

theorem left_midpoint_status (k : Nat) (hk:k ∈ [47,49,50,52]) : redStatus k=1 := by
  have h : ∀ k ∈ [47,49,50,52],redStatus k=1 := by decide +kernel
  exact h k hk

theorem right_midpoint_status (k : Nat) (hk:k ∈ [35,36,37,38]) : redStatus k=2 := by
  have h : ∀ k ∈ [35,36,37,38],redStatus k=2 := by decide +kernel
  exact h k hk

theorem exposed_left_midpoint (n v x y : Nat) (hv:v<4)
    (hx:x≤4*squareSize n) (hy:y≤4*squareSize n)
    (he:¬BoardCovered (n+1) ((x:Int)-2*squareSize n) ((y:Int)-2*squareSize n))
    (hb:(redBoard n v x y).val ∈ [47,49,50,52]) :
    x=0 ∧ y=2*squareSize n := by
  have hs := left_midpoint_status _ hb
  have hr := exposed_red_root_status n v x y hv hx hy he (by omega)
  have hxc := rect_status_left_coordinate (hr.symm.trans hs)
  have hxn : x=0 := by omega
  subst x
  exact ⟨rfl,(left_midpoint_iff n v y hv hy).mp hb⟩

theorem exposed_right_midpoint (n v x y : Nat) (hv:v<4)
    (hx:x≤4*squareSize n) (hy:y≤4*squareSize n)
    (he:¬BoardCovered (n+1) ((x:Int)-2*squareSize n) ((y:Int)-2*squareSize n))
    (hb:(redBoard n v x y).val ∈ [35,36,37,38]) :
    x=4*squareSize n ∧ y=2*squareSize n := by
  have hs := right_midpoint_status _ hb
  have hr := exposed_red_root_status n v x y hv hx hy he (by omega)
  have hxc := rect_status_right_coordinate (hr.symm.trans hs)
  have hxn : x=4*squareSize n := by omega
  subst x
  exact ⟨rfl,(right_midpoint_iff n v y hv hy).mp hb⟩

end K230Concrete
#print axioms K230Concrete.exposed_left_midpoint
#print axioms K230Concrete.exposed_right_midpoint
