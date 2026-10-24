module
public import RawPatchBridge
public import ConcreteCoreTable
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete
@[expose] def transparentDirDecEq : DecidableEq Dir := fun a b => by
  cases a <;> cases b <;>
    solve | exact isTrue rfl | apply isFalse; intro h; cases h
@[expose] def transparentTMDecEq : DecidableEq TMColor := fun a b => by
  letI : DecidableEq Dir := transparentDirDecEq
  cases a <;> cases b <;>
    solve
    | exact isTrue rfl
    | apply isFalse; intro h; cases h
    | simp only [TMColor.symbol.injEq,TMColor.head.injEq,TMColor.move.injEq]; infer_instance
local instance : DecidableEq TMColor := transparentTMDecEq
@[expose] def transparentQuadDecEq {α : Type} [DecidableEq α] : DecidableEq (Quad α) := fun a b =>
  decidable_of_iff (a.n=b.n ∧ a.e=b.e ∧ a.s=b.s ∧ a.w=b.w) (by cases a; cases b; simp)
local instance {α : Type} [DecidableEq α] : DecidableEq (Quad α) := transparentQuadDecEq

@[expose] def levelTwoFamily (x y : Nat) : Nat :=
  if y=2 then if x=0 then 4 else if x=1 then 1 else if x=2 then 5 else if x=3 then 11 else 3 else 0
@[expose] def levelTwoTM (x y : Nat) : Quad TMColor :=
  if y=2 then
    if x=0 then ⟨.blank,.iL,.blank,.blank⟩ else
    if x=1 then ⟨.blank,.iL,.blank,.iL⟩ else
    if x=2 then ⟨.blank,.iX,.blank,.iL⟩ else
    if x=3 then ⟨.blank,.iR,.blank,.iX⟩ else ⟨.blank,.blank,.blank,.iR⟩
  else tmBlank
@[expose] def levelTwoChannels (left bottom : Bool) (x y : Nat) : Quad Nat :=
  ⟨if x=3 then if y=4 then 3 else 2 else 0,
   if y=3 then if x=4 then 3 else 2 else 0,
   if x=3 then if y=0 then (if bottom then 3 else 2) else 2 else 0,
   if y=3 then if x=0 then (if left then 3 else 2) else 2 else 0⟩
@[expose] def levelTwoGroup (v : Nat) (left bottom : Bool) (x y : Nat) : Nat×Nat×Nat :=
  let c := levelTwoChannels left bottom x y
  ((boardCore v x y).val,64*c.n+16*c.e+4*c.s+c.w,levelTwoFamily x y)
@[expose] def levelTwoTile (v : Nat) (left bottom : Bool) (x y : Nat) : Quad FullColor :=
  decorate (levelTwoGroup v left bottom x y) (levelTwoTM x y)

theorem levelTwo_tm_mem (x y : Nat) : levelTwoTM x y ∈ tmFamily (levelTwoFamily x y) := by
  by_cases hy : y=2
  · by_cases h0 : x=0 <;> by_cases h1 : x=1 <;> by_cases h2 : x=2 <;> by_cases h3 : x=3 <;>
      simp [levelTwoTM,levelTwoFamily,hy,h0,h1,h2,h3,tmFamily,tmBlank]
  · simp [levelTwoTM,levelTwoFamily,hy,tmFamily,tmBlank]

theorem levelTwo_groups_mem : ∀ v : Fin 4, ∀ l b : Bool, ∀ x y : Fin 5,
    levelTwoGroup v.val l b x.val y.val ∈ exactGroups.toList := by decide
theorem levelTwo_horizontal : ∀ v : Fin 4, ∀ l b : Bool, ∀ x : Fin 4, ∀ y : Fin 5,
    (levelTwoTile v.val l b x.val y.val).e = (levelTwoTile v.val l b (x.val+1) y.val).w := by decide
theorem levelTwo_vertical : ∀ v : Fin 4, ∀ l b : Bool, ∀ x : Fin 5, ∀ y : Fin 4,
    (levelTwoTile v.val l b x.val y.val).n = (levelTwoTile v.val l b x.val (y.val+1)).s := by decide
end K230Verification
