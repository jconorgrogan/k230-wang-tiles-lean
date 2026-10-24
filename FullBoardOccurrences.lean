module
public import FullPlaneProjection
public import ConcreteBoards
public section
namespace K230Verification
open K230PhaseHierarchy K230Concrete

/-- Arbitrarily large exact red boards occur in the same original decorated plane. -/
theorem exact_full_redBoard (T : Cell → Fin 11487) (h : FullValid T) (n : Nat) :
    ∃ (v : Nat) (b : Cell), v<4 ∧ ∀ x y : Nat,
      x≤4*squareSize n → y≤4*squareSize n →
      indexedBase (T (b.1+(x:Int),b.2+(y:Int))) = redBoard n v x y :=
  arbitrary_redBoard_occurs (projectPlane T) (exact_base_valid T h) n

theorem exact_full_redBoard_lift (T : Cell → Fin 11487) (h : FullValid T) (n : Nat) :
    ∃ (v : Nat) (b : Cell), v<4 ∧ ∀ x y : Nat,
      x≤4*squareSize n → y≤4*squareSize n →
      eraseDecoration (indexedFullTile (T (b.1+(x:Int),b.2+(y:Int)))) =
        baseQuad (redBoard n v x y) := by
  obtain ⟨v,b,hv,hb⟩ := exact_full_redBoard T h n
  refine ⟨v,b,hv,fun x y hx hy => ?_⟩
  rw [indexedBase_spec,hb x y hx hy]

/-- The actual group selected from the literal full tile list has that board index. -/
theorem exact_full_redBoard_groups (T : Cell → Fin 11487) (h : FullValid T) (n : Nat) :
    ∃ (v : Nat) (b : Cell), v<4 ∧ ∀ x y : Nat,
      x≤4*squareSize n → y≤4*squareSize n →
      (indexedGroup (T (b.1+(x:Int),b.2+(y:Int)))).1 = (redBoard n v x y).val := by
  obtain ⟨v,b,hv,hb⟩ := exact_full_redBoard T h n
  exact ⟨v,b,hv,fun x y hx hy => congrArg Fin.val (hb x y hx hy)⟩

#print axioms exact_full_redBoard
#print axioms exact_full_redBoard_groups
end K230Verification
