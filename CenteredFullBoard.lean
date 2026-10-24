module
public import FullBoardIndexing
public section
namespace K230Verification
open K230Concrete

@[expose] def centerCell (b : Cell) (N : Nat) (r s : Int) : Cell :=
  (b.1+(boardHalf N : Int)+r,b.2+(boardHalf N : Int)+s)

theorem centerCell_horizontal (b : Cell) (N : Nat) (r s : Int) :
    ((centerCell b N r s).1+1,(centerCell b N r s).2)=centerCell b N (r+1) s := by
  apply Prod.ext <;> dsimp [centerCell] <;> omega

theorem centerCell_vertical (b : Cell) (N : Nat) (r s : Int) :
    ((centerCell b N r s).1,(centerCell b N r s).2+1)=centerCell b N r (s+1) := by
  apply Prod.ext <;> dsimp [centerCell] <;> omega

theorem centerCell_nat (b : Cell) (N : Nat) (r s : Int)
    (hr : -(boardHalf N : Int)≤r) (hs : -(boardHalf N : Int)≤s) :
    centerCell b N r s = boardCell b ((boardHalf N : Int)+r).toNat ((boardHalf N : Int)+s).toNat := by
  apply Prod.ext <;> dsimp [centerCell,boardCell] <;> omega

theorem fullBoard_centered (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1) : Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1) : Int)≤s ∧ s≤boardHalf (n+1)) :
    indexedBase (T (centerCell b (n+1) r s)) =
      redBoard n v ((boardHalf (n+1) : Int)+r).toNat ((boardHalf (n+1) : Int)+s).toNat := by
  rw [centerCell_nat b (n+1) r s hr.1 hs.1]
  have hsize := fullBoard_side n
  apply hb <;> omega

theorem fullBoard_centered_group (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1) : Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1) : Int)≤s ∧ s≤boardHalf (n+1)) :
    (indexedGroup (T (centerCell b (n+1) r s))).1 =
      (redBoard n v ((boardHalf (n+1) : Int)+r).toNat ((boardHalf (n+1) : Int)+s).toNat).val :=
  congrArg Fin.val (fullBoard_centered T n v b hb r s hr hs)

#print axioms fullBoard_centered
end K230Verification
