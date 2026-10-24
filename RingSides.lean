module
public import RingBoundary
public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace K230Concrete
open K230Verification

theorem channel_red_status (k : Fin 156) :
    (HasHChannel k.val → redStatus k.val=0 ∨ redStatus k.val=1 ∨ redStatus k.val=2) ∧
    (HasVChannel k.val → redStatus k.val=0 ∨ redStatus k.val=3 ∨ redStatus k.val=4) := by
  have h : ∀ k : Fin 156,
    (HasHChannel k.val → redStatus k.val=0 ∨ redStatus k.val=1 ∨ redStatus k.val=2) ∧
    (HasVChannel k.val → redStatus k.val=0 ∨ redStatus k.val=3 ∨ redStatus k.val=4) := by decide +kernel
  exact h k

theorem rect_status_bottom (R : Int) (hR : 0<R) (x : Int) (hx : 0≤x ∧ x≤R) :
    rectStatus 0 R 0 R x 0=3 ∨ rectStatus 0 R 0 R x 0=5 ∨ rectStatus 0 R 0 R x 0=6 := by
  have hne : R≠0 := by omega
  by_cases h0 : x=0
  · simp [rectStatus,hR,Int.le_of_lt hR,h0]
  by_cases h1 : x=R
  · simp [rectStatus,hR,Int.le_of_lt hR,h0,h1,hne]
  · simp [rectStatus,hx.1,hx.2,h0,h1,hne,Int.le_of_lt hR]

theorem rect_status_top (R : Int) (hR : 0<R) (x : Int) (hx : 0≤x ∧ x≤R) :
    rectStatus 0 R 0 R x R=4 ∨ rectStatus 0 R 0 R x R=7 ∨ rectStatus 0 R 0 R x R=8 := by
  have hne : R≠0 := by omega
  by_cases h0 : x=0
  · simp [rectStatus,hR,Int.le_of_lt hR,h0,hne]
  by_cases h1 : x=R
  · simp [rectStatus,hR,Int.le_of_lt hR,h0,h1,hne]
  · simp [rectStatus,hx.1,hx.2,h0,h1,hne,Int.le_of_lt hR]

theorem rect_status_left (R : Int) (hR : 0<R) (y : Int) (hy : 0≤y ∧ y≤R) :
    rectStatus 0 R 0 R 0 y=1 ∨ rectStatus 0 R 0 R 0 y=5 ∨ rectStatus 0 R 0 R 0 y=7 := by
  have hne : R≠0 := by omega
  by_cases h0 : y=0
  · simp [rectStatus,hR,Int.le_of_lt hR,h0]
  by_cases h1 : y=R
  · simp [rectStatus,hR,Int.le_of_lt hR,h0,h1,hne]
  · simp [rectStatus,hy.1,hy.2,h0,h1,Int.le_of_lt hR]

theorem rect_status_right (R : Int) (hR : 0<R) (y : Int) (hy : 0≤y ∧ y≤R) :
    rectStatus 0 R 0 R R y=2 ∨ rectStatus 0 R 0 R R y=6 ∨ rectStatus 0 R 0 R R y=8 := by
  have hne : R≠0 := by omega
  by_cases h0 : y=0
  · simp [rectStatus,hR,Int.le_of_lt hR,h0,hne]
  by_cases h1 : y=R
  · simp [rectStatus,hR,Int.le_of_lt hR,h0,h1,hne]
  · simp [rectStatus,hy.1,hy.2,h0,h1,hne,Int.le_of_lt hR]

theorem redBoard_bottom_indices (n v j : Nat) (hv : v<4) (hj : j≤4*squareSize n)
    (hc : HasVChannel (redBoard n v j 0).val) :
    (redBoard n v j 0).val=136 ∨ (redBoard n v j 0).val=142 ∨ (redBoard n v j 0).val=151 := by
  have hs := redBoard_ring_status n v j 0 hv hj (by omega) (Or.inr (Or.inr (Or.inl rfl)))
  have hp := squareSize_pos n
  have hr := rect_status_bottom (4*(squareSize n:Int)) (by omega) j (by omega)
  have hh := (channel_red_status (redBoard n v j 0)).2 hc
  simp only [show ((0:Nat):Int)=0 by decide] at hs
  have hstat : redStatus (redBoard n v j 0).val=3 := by omega
  exact ((red_status_channel_index (redBoard n v j 0)).2 hc).1 hstat

theorem redBoard_top_indices (n v j : Nat) (hv : v<4) (hj : j≤4*squareSize n)
    (hc : HasVChannel (redBoard n v j (4*squareSize n)).val) :
    (redBoard n v j (4*squareSize n)).val=134 ∨ (redBoard n v j (4*squareSize n)).val=140 ∨
      (redBoard n v j (4*squareSize n)).val=150 := by
  have hs := redBoard_ring_status n v j (4*squareSize n) hv hj (by omega) (Or.inr (Or.inr (Or.inr rfl)))
  have hp := squareSize_pos n
  have hr := rect_status_top (4*(squareSize n:Int)) (by omega) j (by omega)
  have hh := (channel_red_status (redBoard n v j (4*squareSize n))).2 hc
  have hcast : ((4*squareSize n:Nat):Int)=4*(squareSize n:Int) := by omega
  rw [hcast] at hs
  have hstat : redStatus (redBoard n v j (4*squareSize n)).val=4 := by omega
  exact ((red_status_channel_index (redBoard n v j (4*squareSize n))).2 hc).2 hstat

theorem redBoard_left_indices (n v j : Nat) (hv : v<4) (hj : j≤4*squareSize n)
    (hc : HasHChannel (redBoard n v 0 j).val) :
    (redBoard n v 0 j).val=100 ∨ (redBoard n v 0 j).val=116 ∨ (redBoard n v 0 j).val=101 := by
  have hs := redBoard_ring_status n v 0 j hv (by omega) hj (Or.inl rfl)
  have hp := squareSize_pos n
  have hr := rect_status_left (4*(squareSize n:Int)) (by omega) j (by omega)
  have hh := (channel_red_status (redBoard n v 0 j)).1 hc
  simp only [show ((0:Nat):Int)=0 by decide] at hs
  have hstat : redStatus (redBoard n v 0 j).val=1 := by omega
  exact ((red_status_channel_index (redBoard n v 0 j)).1 hc).1 hstat

theorem redBoard_right_indices (n v j : Nat) (hv : v<4) (hj : j≤4*squareSize n)
    (hc : HasHChannel (redBoard n v (4*squareSize n) j).val) :
    (redBoard n v (4*squareSize n) j).val=95 ∨ (redBoard n v (4*squareSize n) j).val=111 ∨
      (redBoard n v (4*squareSize n) j).val=96 := by
  have hs := redBoard_ring_status n v (4*squareSize n) j hv (by omega) hj (Or.inr (Or.inl rfl))
  have hp := squareSize_pos n
  have hr := rect_status_right (4*(squareSize n:Int)) (by omega) j (by omega)
  have hh := (channel_red_status (redBoard n v (4*squareSize n) j)).1 hc
  have hcast : ((4*squareSize n:Nat):Int)=4*(squareSize n:Int) := by omega
  rw [hcast] at hs
  have hstat : redStatus (redBoard n v (4*squareSize n) j).val=2 := by omega
  exact ((red_status_channel_index (redBoard n v (4*squareSize n) j)).1 hc).2 hstat

end K230Concrete
#print axioms K230Concrete.redBoard_bottom_indices
#print axioms K230Concrete.redBoard_top_indices
