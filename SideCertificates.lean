module
public import RawExpansion
public import ChannelClasses
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace K230Concrete

@[expose] def sideList (side state : Nat) : List Nat :=
  if side=0 ∧ state=0 then [83]
  else if side=0 ∧ state=1 then [80, 81, 82, 115, 116]
  else if side=0 ∧ state=2 then [47, 49, 50, 52]
  else if side=0 ∧ state=3 then [46, 48, 51, 99, 100]
  else if side=0 ∧ state=4 then [70]
  else if side=1 ∧ state=0 then [75]
  else if side=1 ∧ state=1 then [72, 73, 74, 110, 111]
  else if side=1 ∧ state=2 then [35, 36, 37, 38]
  else if side=1 ∧ state=3 then [32, 33, 34, 94, 95]
  else if side=1 ∧ state=4 then [64]
  else if side=2 ∧ state=0 then [83]
  else if side=2 ∧ state=1 then [14, 30, 45, 130, 142]
  else if side=2 ∧ state=2 then [6, 22, 41, 58]
  else if side=2 ∧ state=3 then [7, 23, 59, 124, 136]
  else if side=2 ∧ state=4 then [75]
  else if side=3 ∧ state=0 then [70]
  else if side=3 ∧ state=1 then [12, 28, 44, 128, 140]
  else if side=3 ∧ state=2 then [62, 68, 78, 86]
  else if side=3 ∧ state=3 then [4, 20, 57, 122, 134]
  else if side=3 ∧ state=4 then [64]
  else []

@[expose] def sideZone (half j : Nat) : Nat :=
  if j=0 then 0 else if j<half then 1 else if j=half then 2 else if j<2*half then 3 else 4
@[expose] def sideAdvance (state digit : Nat) : Nat :=
  if state=0 then (if digit=0 then 0 else 1)
  else if state=1 then 1 else if state=2 then (if digit=0 then 2 else 3)
  else if state=3 then 3 else 4
@[expose] def sideDescendant (side k digit : Nat) : Nat :=
  rawExpanded 2 k (if side<2 then 0 else digit) (if side<2 then digit else 0)
@[expose] def representativeNat (v : Nat) : Nat :=
  if v=0 then 0 else if v=1 then 120 else if v=2 then 88 else 152
@[expose] def initialSideValue (side v j : Nat) : Nat :=
  rawExpanded 5 (representativeNat v)
    (if side=0 then 8 else if side=1 then 24 else j+8)
    (if side=2 then 8 else if side=3 then 24 else j+8)
@[expose] def initialSideCheck (side v : Nat) : Bool :=
  (List.range 17).all fun j => (sideList side (sideZone 8 j)).contains (initialSideValue side v j)

theorem initial_side_0_0 : initialSideCheck 0 0 = true := by decide +kernel
theorem initial_side_0_1 : initialSideCheck 0 1 = true := by decide +kernel
theorem initial_side_0_2 : initialSideCheck 0 2 = true := by decide +kernel
theorem initial_side_0_3 : initialSideCheck 0 3 = true := by decide +kernel
theorem initial_side_1_0 : initialSideCheck 1 0 = true := by decide +kernel
theorem initial_side_1_1 : initialSideCheck 1 1 = true := by decide +kernel
theorem initial_side_1_2 : initialSideCheck 1 2 = true := by decide +kernel
theorem initial_side_1_3 : initialSideCheck 1 3 = true := by decide +kernel
theorem initial_side_2_0 : initialSideCheck 2 0 = true := by decide +kernel
theorem initial_side_2_1 : initialSideCheck 2 1 = true := by decide +kernel
theorem initial_side_2_2 : initialSideCheck 2 2 = true := by decide +kernel
theorem initial_side_2_3 : initialSideCheck 2 3 = true := by decide +kernel
theorem initial_side_3_0 : initialSideCheck 3 0 = true := by decide +kernel
theorem initial_side_3_1 : initialSideCheck 3 1 = true := by decide +kernel
theorem initial_side_3_2 : initialSideCheck 3 2 = true := by decide +kernel
theorem initial_side_3_3 : initialSideCheck 3 3 = true := by decide +kernel

theorem initial_side_checked (side v : Nat) (hs : side<4) (hv : v<4) : initialSideCheck side v = true := by
  match side,v with
  | 0,0 => exact initial_side_0_0
  | 0,1 => exact initial_side_0_1
  | 0,2 => exact initial_side_0_2
  | 0,3 => exact initial_side_0_3
  | 1,0 => exact initial_side_1_0
  | 1,1 => exact initial_side_1_1
  | 1,2 => exact initial_side_1_2
  | 1,3 => exact initial_side_1_3
  | 2,0 => exact initial_side_2_0
  | 2,1 => exact initial_side_2_1
  | 2,2 => exact initial_side_2_2
  | 2,3 => exact initial_side_2_3
  | 3,0 => exact initial_side_3_0
  | 3,1 => exact initial_side_3_1
  | 3,2 => exact initial_side_3_2
  | 3,3 => exact initial_side_3_3
  | s+4,_ => omega
  | _,v+4 => omega

theorem initial_side_member (side v j : Nat) (hs : side<4) (hv : v<4) (hj : j<17) :
    initialSideValue side v j ∈ sideList side (sideZone 8 j) := by
  have h := List.all_eq_true.mp (initial_side_checked side v hs hv) j (List.mem_range.mpr hj)
  simpa using h

@[expose] def sideTransitionCheck : Bool := (List.range 4).all fun side =>
  (List.range 5).all fun state => (sideList side state).all fun k =>
    (List.range 4).all fun digit => if state=4 ∧ digit≠0 then true else
      (sideList side (sideAdvance state digit)).contains (sideDescendant side k digit)

theorem side_transition_checked : sideTransitionCheck = true := by decide +kernel

theorem side_transition (side state k digit : Nat) (hs : side<4) (hc : state<5)
    (hk : k ∈ sideList side state) (hd : digit<4) (hv : state≠4 ∨ digit=0) :
    sideDescendant side k digit ∈ sideList side (sideAdvance state digit) := by
  have h1 := List.all_eq_true.mp side_transition_checked side (List.mem_range.mpr hs)
  have h2 := List.all_eq_true.mp h1 state (List.mem_range.mpr hc)
  have h3 := List.all_eq_true.mp h2 k hk
  have h4 := List.all_eq_true.mp h3 digit (List.mem_range.mpr hd)
  have hskip : ¬ (state=4 ∧ digit≠0) := by omega
  simpa [hskip] using h4

@[expose] def SideHasChannel (side k : Nat) : Prop :=
  if side<2 then K230Verification.HasHChannel k else K230Verification.HasVChannel k
instance (side k : Nat) : Decidable (SideHasChannel side k) := by
  unfold SideHasChannel
  infer_instance
@[expose] def channelExpected (side state : Nat) : Nat :=
  if side=0 then (if state=1 then 116 else 100)
  else if side=1 then (if state=1 then 111 else 95)
  else if side=2 then (if state=1 then 142 else 136)
  else (if state=1 then 140 else 134)
@[expose] def sideChannelCheck : Bool := (List.range 4).all fun side =>
  [1,3].all fun state => (sideList side state).all fun k =>
    !(decide (SideHasChannel side k)) || (k == channelExpected side state)

theorem side_channel_checked : sideChannelCheck = true := by decide +kernel

theorem side_channel_unique (side state k : Nat) (hs : side<4) (hc : state=1 ∨ state=3)
    (hk : k ∈ sideList side state) (hchannel : SideHasChannel side k) :
    k = channelExpected side state := by
  have h1 := List.all_eq_true.mp side_channel_checked side (List.mem_range.mpr hs)
  have hmem : state ∈ [1,3] := by simp; omega
  have h2 := List.all_eq_true.mp h1 state hmem
  have h3 := List.all_eq_true.mp h2 k hk
  simpa [hchannel] using h3

end K230Concrete
#print axioms K230Concrete.initial_side_member
#print axioms K230Concrete.side_transition
#print axioms K230Concrete.side_channel_unique
