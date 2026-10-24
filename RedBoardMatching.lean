module
public import ConcreteBoards
public section
namespace K230Concrete
open Wang156

/-- Every adjacent pair, including cells on the inclusive boundary, matches in
    its actual base color. Cropping and later decoration do not require a new
    existence or compatibility hypothesis for the base layer. -/
theorem redBoard_horizontal (n v x y : Nat) (hv:v<4)
    (hx:x<4*squareSize n) (hy:y≤4*squareSize n) :
    (tile (redBoard n v x y).val).e=(tile (redBoard n v (x+1) y).val).w := by
  have hp := squareSize_pos n
  have hw : width (2*n+3)=8*squareSize n := by
    simp only [width_add,width,squareSize]
    omega
  rw [redBoard_as_expanded n v x y hv (by omega) hy,
      redBoard_as_expanded n v (x+1) y hv (by omega) hy]
  have h := expanded_horizontal (2*n+3) (coreRepresentative v)
    (2*squareSize n+x) (2*squareSize n+y) (by omega) (by omega)
  simpa only [Nat.add_assoc] using h

theorem redBoard_vertical (n v x y : Nat) (hv:v<4)
    (hx:x≤4*squareSize n) (hy:y<4*squareSize n) :
    (tile (redBoard n v x y).val).n=(tile (redBoard n v x (y+1)).val).s := by
  have hp := squareSize_pos n
  have hw : width (2*n+3)=8*squareSize n := by
    simp only [width_add,width,squareSize]
    omega
  rw [redBoard_as_expanded n v x y hv hx (by omega),
      redBoard_as_expanded n v x (y+1) hv hx (by omega)]
  have h := expanded_vertical (2*n+3) (coreRepresentative v)
    (2*squareSize n+x) (2*squareSize n+y) (by omega) (by omega)
  simpa only [Nat.add_assoc] using h
end K230Concrete
#print axioms K230Concrete.redBoard_horizontal
#print axioms K230Concrete.redBoard_vertical
