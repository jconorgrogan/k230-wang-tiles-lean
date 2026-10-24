module
public import SideGeometry
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Concrete

@[expose] def midpointStateCheck : Bool := (List.range 4).all fun side =>
  (List.range 5).all fun state => (sideList side state).all fun k =>
    decide (k ∈ sideList side 2 ↔ state=2)
theorem midpoint_state_checked : midpointStateCheck=true := by decide +kernel

theorem side_midpoint_state (side state k : Nat) (hs:side<4) (hc:state<5)
    (hk:k ∈ sideList side state) : k ∈ sideList side 2 ↔ state=2 := by
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp midpoint_state_checked
      side (List.mem_range.mpr hs)) state (List.mem_range.mpr hc)) k hk)

@[expose] def lowestSideValue (side v j : Nat) : Nat :=
  rawExpanded 3 (representativeNat v)
    (if side=0 then 2 else if side=1 then 6 else j+2)
    (if side=2 then 2 else if side=3 then 6 else j+2)
@[expose] def lowestMidpointCheck : Bool := (List.range 4).all fun side =>
  (List.range 4).all fun v => (List.range 5).all fun j =>
    decide (lowestSideValue side v j ∈ sideList side 2 ↔ j=2)
theorem lowest_midpoint_checked : lowestMidpointCheck=true := by decide +kernel

theorem redBoard_zero_value (v x y : Nat) :
    (redBoard 0 v x y).val=rawExpanded 3 (representativeNat v) (x+2) (y+2) := by
  have he : redBoard 0 v x y=boardCore v x y := by
    simp only [redBoard,squareSize,width,Nat.div_one,Nat.mod_one,expanded]
  rw [he]
  change (expanded 3 (coreRepresentative v) (x+2) (y+2)).val = _
  rw [expanded_value,coreRepresentative_value]

theorem sideCell_zero_value (side v j : Nat) (hs:side<4) :
    (sideCell 0 v side j).val=lowestSideValue side v j := by
  have hs' : side=0 ∨ side=1 ∨ side=2 ∨ side=3 := by omega
  rcases hs' with rfl|rfl|rfl|rfl
  · exact redBoard_zero_value v 0 j
  · exact redBoard_zero_value v 4 j
  · exact redBoard_zero_value v j 0
  · exact redBoard_zero_value v j 4

theorem side_midpoint_iff (n side v j : Nat) (hs:side<4) (hv:v<4)
    (hj:j≤4*squareSize n) :
    (sideCell n v side j).val ∈ sideList side 2 ↔ j=2*squareSize n := by
  cases n with
  | zero =>
    have h := of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp lowest_midpoint_checked
        side (List.mem_range.mpr hs)) v (List.mem_range.mpr hv))
          j (List.mem_range.mpr (show j<5 by exact Nat.lt_succ_of_le hj)))
    rw [sideCell_zero_value side v j hs]
    exact h
  | succ n =>
    have ha := side_allowed n side v j hs hv hj
    have h := side_midpoint_state side (sideZone (2*squareSize (n+1)) j) _
      hs (sideZone_bound _ _) ha
    rw [h]
    have hp := squareSize_pos (n+1)
    simp only [sideZone]
    split <;> rename_i h0
    · simp only [show (0:Nat)≠2 by decide, false_iff]
      omega
    · split <;> rename_i h1
      · simp only [show (1:Nat)≠2 by decide, false_iff]
        omega
      · split <;> rename_i h2
        · simp only [h2,true_iff]
        · split <;> simp_all

theorem left_midpoint_iff (n v j : Nat) (hv:v<4) (hj:j≤4*squareSize n) :
    (redBoard n v 0 j).val ∈ [47,49,50,52] ↔ j=2*squareSize n :=
  side_midpoint_iff n 0 v j (by decide) hv hj

theorem right_midpoint_iff (n v j : Nat) (hv:v<4) (hj:j≤4*squareSize n) :
    (redBoard n v (4*squareSize n) j).val ∈ [35,36,37,38] ↔ j=2*squareSize n :=
  side_midpoint_iff n 1 v j (by decide) hv hj

end K230Concrete
#print axioms K230Concrete.left_midpoint_iff
#print axioms K230Concrete.right_midpoint_iff
