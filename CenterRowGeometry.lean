module
public import FiveState
public import ConcreteBoards
public import CoreCoordinates
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace K230Concrete

@[expose] def centerList (state : Nat) : List Nat :=
  if state=0 then [47, 49, 50, 52]
  else if state=1 then [1, 3, 5, 9, 17, 19, 21, 25, 120, 121, 123, 125, 132, 133, 135, 137]
  else if state=2 then [65, 71, 79, 87]
  else if state=3 then [10, 11, 13, 15, 26, 27, 29, 31, 126, 127, 129, 131, 138, 139, 141, 143]
  else if state=4 then [35, 36, 37, 38]
  else []

@[expose] def initialCenterValue (v j : Nat) : Nat := rawExpanded 5 (representativeNat v) (j+8) 16
@[expose] def initialCenterCheck (v : Nat) : Bool := (List.range 17).all fun j =>
  (centerList (sideZone 8 j)).contains (initialCenterValue v j)
theorem initial_center_0 : initialCenterCheck 0 = true := by decide +kernel
theorem initial_center_1 : initialCenterCheck 1 = true := by decide +kernel
theorem initial_center_2 : initialCenterCheck 2 = true := by decide +kernel
theorem initial_center_3 : initialCenterCheck 3 = true := by decide +kernel
theorem initial_center_checked (v : Nat) (hv:v<4) : initialCenterCheck v=true := by
  match v with
  | 0 => exact initial_center_0
  | 1 => exact initial_center_1
  | 2 => exact initial_center_2
  | 3 => exact initial_center_3
  | n+4 => omega

theorem initial_center_member (v j : Nat) (hv:v<4) (hj:j<17) :
    initialCenterValue v j ∈ centerList (sideZone 8 j) := by
  have h := List.all_eq_true.mp (initial_center_checked v hv) j (List.mem_range.mpr hj)
  simpa using h

@[expose] def centerTransitionCheck : Bool := (List.range 5).all fun state =>
  (centerList state).all fun k => (List.range 4).all fun digit =>
    if state=4 ∧ digit≠0 then true else
      (centerList (sideAdvance state digit)).contains (rawExpanded 2 k digit 0)
theorem center_transition_checked : centerTransitionCheck=true := by decide +kernel

theorem center_transition (state k digit : Nat) (hc:state<5) (hk:k∈centerList state)
    (hd:digit<4) (hv:state≠4 ∨ digit=0) :
    rawExpanded 2 k digit 0 ∈ centerList (sideAdvance state digit) := by
  have h1 := List.all_eq_true.mp center_transition_checked state (List.mem_range.mpr hc)
  have h2 := List.all_eq_true.mp h1 k hk
  have h3 := List.all_eq_true.mp h2 digit (List.mem_range.mpr hd)
  have hskip : ¬ (state=4 ∧ digit≠0) := by omega
  simpa [hskip] using h3

@[expose] def centerSeedCheck : Bool := (List.range 5).all fun state =>
  (centerList state).all fun k => (decide (K230Verification.SeedBase k)) == (state==2)
theorem center_seed_checked : centerSeedCheck=true := by decide +kernel

theorem center_seed_class (state k : Nat) (hc:state<5) (hk:k∈centerList state) :
    K230Verification.SeedBase k ↔ state=2 := by
  have h1 := List.all_eq_true.mp center_seed_checked state (List.mem_range.mpr hc)
  have h2 := List.all_eq_true.mp h1 k hk
  have he : decide (K230Verification.SeedBase k) = (state==2) := by simpa using h2
  constructor
  · intro hp
    simpa [hp] using he.symm
  · intro hs
    subst state
    exact of_decide_eq_true (by simpa using he)

@[expose] def centerCell (n v j : Nat) : Fin 156 := redBoard n v j (2*squareSize n)

theorem centerCell_step (n v j : Nat) (hv:v<4) (hj:j≤4*squareSize (n+1)) :
    centerCell (n+1) v j = expanded 2 (centerCell n v (j/4)) (j%4) 0 := by
  have hs := squareSize_step n
  have hd : (2*squareSize (n+1))/4=2*squareSize n := by omega
  have hr : (2*squareSize (n+1))%4=0 := by omega
  have h := redBoard_step n v j (2*squareSize (n+1)) hv hj (by omega)
  simpa only [centerCell,hd,hr] using h

theorem centerCell_initial (v j : Nat) (hv:v<4) (hj:j≤16) :
    (centerCell 1 v j).val = initialCenterValue v j := by
  change (redBoard 1 v j 8).val = rawExpanded 5 (representativeNat v) (j+8) 16
  exact redBoard_one_value v j 8 hv hj (by decide)

theorem center_row_allowed (n v j : Nat) (hv:v<4) (hj:j≤4*squareSize (n+1)) :
    (centerCell (n+1) v j).val ∈ centerList (sideZone (2*squareSize (n+1)) j) := by
  apply five_state_invariant
    (fun n => 2*squareSize (n+1))
    (fun n j => (centerCell (n+1) v j).val)
    (fun k digit => rawExpanded 2 k digit 0) centerList
  · rfl
  · intro m
    have h := squareSize_pos (m+1)
    omega
  · intro m
    have h := squareSize_step (m+1)
    omega
  · intro m a ha
    have h := congrArg Fin.val (centerCell_step (m+1) v a hv (by omega))
    simpa only [expanded_value] using h
  · intro a ha
    rw [centerCell_initial v a hv ha]
    exact initial_center_member v a hv (by omega)
  · exact center_transition
  · omega

theorem center_row_left (n v j : Nat) (hv:v<4) (hj:0<j ∧ j<2*squareSize (n+1)) :
    (centerCell (n+1) v j).val ∈ centerList 1 := by
  have h := center_row_allowed n v j hv (by omega)
  simpa [sideZone,show j≠0 by omega,hj.2] using h

theorem center_row_right (n v j : Nat) (hv:v<4)
    (hj:2*squareSize (n+1)<j ∧ j<4*squareSize (n+1)) :
    (centerCell (n+1) v j).val ∈ centerList 3 := by
  have h := center_row_allowed n v j hv (by omega)
  have h0 : j≠0 := by omega
  have h1 : ¬ j<2*squareSize (n+1) := by omega
  have h2 : j≠2*squareSize (n+1) := by omega
  have h3 : j<2*(2*squareSize (n+1)) := by omega
  simpa only [sideZone,if_neg h0,if_neg h1,if_neg h2,if_pos h3] using h

theorem center_row_seed_iff (n v j : Nat) (hv:v<4) (hj:j≤4*squareSize (n+1)) :
    K230Verification.SeedBase (centerCell (n+1) v j).val ↔ j=2*squareSize (n+1) := by
  have h := center_seed_class _ _ (sideZone_bound _ _) (center_row_allowed n v j hv hj)
  have hp := squareSize_pos (n+1)
  have hz : sideZone (2*squareSize (n+1)) j=2 ↔ j=2*squareSize (n+1) := by
    simp only [sideZone]
    repeat' first | split | omega
  exact h.trans hz

end K230Concrete
#print axioms K230Concrete.center_row_allowed
#print axioms K230Concrete.center_row_seed_iff
