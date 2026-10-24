module
public import FiveState
public import ConcreteBoards
public import BoardLocality
public import CoreCoordinates
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace K230Concrete

@[expose] def sideCell (n v side j : Nat) : Fin 156 := redBoard n v
  (if side=0 then 0 else if side=1 then 4*squareSize n else j)
  (if side=2 then 0 else if side=3 then 4*squareSize n else j)

theorem sideCell_step (n v side j : Nat) (hv:v<4) (hs:side<4) (hj:j≤4*squareSize (n+1)) :
    sideCell (n+1) v side j = expanded 2 (sideCell n v side (j/4))
      (if side<2 then 0 else j%4) (if side<2 then j%4 else 0) := by
  have hsize := squareSize_step n
  have hd : (4*squareSize (n+1))/4=4*squareSize n := by omega
  have hr : (4*squareSize (n+1))%4=0 := by omega
  have hs' : side=0 ∨ side=1 ∨ side=2 ∨ side=3 := by omega
  rcases hs' with rfl | rfl | rfl | rfl
  · have h := redBoard_step n v (0) (j) hv (by omega) (by omega)
    simpa [sideCell,hd,hr] using h
  · have h := redBoard_step n v (4*squareSize (n+1)) (j) hv (by omega) (by omega)
    simpa [sideCell,hd,hr] using h
  · have h := redBoard_step n v (j) (0) hv (by omega) (by omega)
    simpa [sideCell,hd,hr] using h
  · have h := redBoard_step n v (j) (4*squareSize (n+1)) hv (by omega) (by omega)
    simpa [sideCell,hd,hr] using h

theorem sideCell_initial (side v j : Nat) (hs:side<4) (hv:v<4) (hj:j≤16) :
    (sideCell 1 v side j).val = initialSideValue side v j := by
  have hs' : side=0 ∨ side=1 ∨ side=2 ∨ side=3 := by omega
  rcases hs' with rfl | rfl | rfl | rfl
  · change (redBoard 1 v (0) (j)).val = rawExpanded 5 (representativeNat v) (8) (j+8)
    exact redBoard_one_value v (0) (j) hv (by omega) (by omega)
  · change (redBoard 1 v (16) (j)).val = rawExpanded 5 (representativeNat v) (24) (j+8)
    exact redBoard_one_value v (16) (j) hv (by omega) (by omega)
  · change (redBoard 1 v (j) (0)).val = rawExpanded 5 (representativeNat v) (j+8) (8)
    exact redBoard_one_value v (j) (0) hv (by omega) (by omega)
  · change (redBoard 1 v (j) (16)).val = rawExpanded 5 (representativeNat v) (j+8) (24)
    exact redBoard_one_value v (j) (16) hv (by omega) (by omega)

theorem side_allowed (n side v j : Nat) (hs:side<4) (hv:v<4) (hj:j≤4*squareSize (n+1)) :
    (sideCell (n+1) v side j).val ∈ sideList side (sideZone (2*squareSize (n+1)) j) := by
  apply five_state_invariant
    (fun n => 2*squareSize (n+1))
    (fun n j => (sideCell (n+1) v side j).val)
    (sideDescendant side) (sideList side)
  · rfl
  · intro m
    have h := squareSize_pos (m+1)
    omega
  · intro m
    have h := squareSize_step (m+1)
    omega
  · intro m a ha
    have h := congrArg Fin.val (sideCell_step (m+1) v side a hv hs (by omega))
    simpa only [expanded_value,sideDescendant] using h
  · intro a ha
    rw [sideCell_initial side v a hs hv ha]
    exact initial_side_member side v a hs hv (by omega)
  · intro state k digit hc hk hd ht
    exact side_transition side state k digit hs hc hk hd ht
  · omega

theorem side_allowed_of_pos (n side v j : Nat) (hn:1≤n) (hs:side<4) (hv:v<4)
    (hj:j≤4*squareSize n) :
    (sideCell n v side j).val ∈ sideList side (sideZone (2*squareSize n) j) := by
  cases n with
  | zero => omega
  | succ m => exact side_allowed m side v j hs hv hj

theorem side_lower_allowed (n side v j : Nat) (hn:1≤n) (hs:side<4) (hv:v<4)
    (hj:0<j ∧ j<2*squareSize n) : (sideCell n v side j).val ∈ sideList side 1 := by
  have h := side_allowed_of_pos n side v j hn hs hv (by omega)
  simpa [sideZone,show j≠0 by omega,hj.2] using h

theorem side_upper_allowed (n side v j : Nat) (hn:1≤n) (hs:side<4) (hv:v<4)
    (hj:2*squareSize n<j ∧ j<4*squareSize n) : (sideCell n v side j).val ∈ sideList side 3 := by
  have h := side_allowed_of_pos n side v j hn hs hv (by omega)
  have h0 : j≠0 := by omega
  have h1 : ¬ j<2*squareSize n := by omega
  have h2 : j≠2*squareSize n := by omega
  have h3 : j<2*(2*squareSize n) := by omega
  simpa only [sideZone,if_neg h0,if_neg h1,if_neg h2,if_pos h3] using h

theorem side_midpoint_allowed (n side v : Nat) (hn:1≤n) (hs:side<4) (hv:v<4) :
    (sideCell n v side (2*squareSize n)).val ∈ sideList side 2 := by
  have hp := squareSize_pos n
  have h := side_allowed_of_pos n side v (2*squareSize n) hn hs hv (by omega)
  simpa [sideZone,show 2*squareSize n≠0 by omega] using h

theorem side_has_channel (n side v j : Nat) (hn:1≤n) (hs:side<4) (hj:j%4=1) :
    SideHasChannel side (sideCell n v side j).val := by
  have hs' : side=0 ∨ side=1 ∨ side=2 ∨ side=3 := by omega
  rcases hs' with rfl | rfl | rfl | rfl
  · exact (redBoard_modulo_four n hn v 0 j).1.mpr hj
  · exact (redBoard_modulo_four n hn v (4*squareSize n) j).1.mpr hj
  · exact (redBoard_modulo_four n hn v j 0).2.mpr hj
  · exact (redBoard_modulo_four n hn v j (4*squareSize n)).2.mpr hj

theorem side_lower_channel (n side v j : Nat) (hn:1≤n) (hs:side<4) (hv:v<4)
    (hj:0<j ∧ j<2*squareSize n) (hchannel:j%4=1) :
    (sideCell n v side j).val = channelExpected side 1 :=
  side_channel_unique side 1 _ hs (Or.inl rfl)
    (side_lower_allowed n side v j hn hs hv hj) (side_has_channel n side v j hn hs hchannel)

theorem side_upper_channel (n side v j : Nat) (hn:1≤n) (hs:side<4) (hv:v<4)
    (hj:2*squareSize n<j ∧ j<4*squareSize n) (hchannel:j%4=1) :
    (sideCell n v side j).val = channelExpected side 3 :=
  side_channel_unique side 3 _ hs (Or.inr rfl)
    (side_upper_allowed n side v j hn hs hv hj) (side_has_channel n side v j hn hs hchannel)

end K230Concrete
#print axioms K230Concrete.side_allowed_of_pos
#print axioms K230Concrete.side_lower_channel
#print axioms K230Concrete.side_upper_channel
