module
public import RawExpansion
public import ConcreteBoards
public import ConcreteRoles
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Concrete

/-- 0 is not a red ring; 1,2,3,4 are left,right,bottom,top;
    5,6,7,8 are bottom-left,bottom-right,top-left,top-right. -/
@[expose] def redStatuses : Array Nat := #[0,0,0,0,4,0,3,3,0,0,0,0,4,0,3,0,0,0,0,0,4,0,3,3,0,0,0,0,4,0,3,0,2,2,2,2,2,2,2,0,0,3,0,0,4,3,1,1,1,1,1,1,1,0,0,0,0,4,3,3,0,0,4,0,8,0,0,0,4,0,7,0,2,2,2,6,0,0,4,0,1,1,1,5,0,0,4,0,0,0,0,0,0,0,2,2,2,0,0,1,1,1,0,0,0,0,0,0,0,0,2,2,2,0,0,1,1,1,0,0,0,0,4,0,3,0,0,0,4,0,3,0,0,0,4,0,3,0,0,0,4,0,3,0,0,0,4,3,0,0,4,3,0,0,0,0]
@[expose] def redStatus (k : Nat) : Nat := redStatuses[k]?.getD 0

/-- Refinement of an existing ring by a factor of four, with endpoint clipping. -/
@[expose] def refineRed (s x y : Nat) : Nat :=
  match s with
  | 1 => if x=0 then 1 else 0
  | 2 => if x=0 then 2 else 0
  | 3 => if y=0 then 3 else 0
  | 4 => if y=0 then 4 else 0
  | 5 => if x=0 then (if y=0 then 5 else 1) else (if y=0 then 3 else 0)
  | 6 => if x=0 then (if y=0 then 6 else 2) else 0
  | 7 => if y=0 then (if x=0 then 7 else 4) else 0
  | 8 => if x=0 ∧ y=0 then 8 else 0
  | _ => 0

/-- Boundary status of an axis-aligned closed rectangle, not its interior. -/
@[expose] def rectStatus (L R B T x y : Int) : Nat :=
  if L≤x ∧ x≤R ∧ B≤y ∧ y≤T then
    if x=L then (if y=B then 5 else if y=T then 7 else 1)
    else if x=R then (if y=B then 6 else if y=T then 8 else 2)
    else if y=B then 3 else if y=T then 4 else 0
  else 0

@[expose] def lowestRed (px py x y : Nat) : Nat :=
  rectStatus 2 6 2 6 (4*(px:Int)+x) (4*(py:Int)+y)

@[expose] def redRecurrenceAt (k : Nat) : Bool :=
  (List.range 4).all fun x => (List.range 4).all fun y =>
  let a := lowestRed (Wang156.tile k).px (Wang156.tile k).py x y
  let b := refineRed (redStatus k) x y
  decide (a=0 ∨ b=0) &&
  (redStatus (rawExpanded 2 k x y) == if a=0 then b else a)


end K230Concrete
