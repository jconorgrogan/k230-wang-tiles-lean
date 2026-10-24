module
public import CanonicalBoardContract
public import MaximalChildren
public import GeometricSubboards
public section
namespace K230Verification
open K230Concrete

/-- A fully matched decoration of the root grid, allowed to violate tile
    membership inside smaller boards. Those holes will be replaced by
    recursively completed exact boards. Every field is later discharged
    by concrete channel and TM-wire constructions. -/
structure ExposedBoard (n v : Nat) (left bottom : Int → Bool) where
  tile : Cell → Quad FullColor
  member : ∀ x y : Int, 0≤x → x≤4*squareSize n → 0≤y → y≤4*squareSize n →
    ¬RootCovered (n+1) (x-2*squareSize n,y-2*squareSize n) → tile (x,y) ∈ exactFullPlaneTiles
  horizontal : ∀ x y : Int, 0≤x → x<4*squareSize n → 0≤y → y≤4*squareSize n →
    (tile (x,y)).e=(tile (x+1,y)).w
  vertical : ∀ x y : Int, 0≤x → x≤4*squareSize n → 0≤y → y<4*squareSize n →
    (tile (x,y)).n=(tile (x,y+1)).s
  base : ∀ x y : Nat, x≤4*squareSize n → y≤4*squareSize n →
    fullBase (tile (x,y))=baseTileQuad (redBoard n v x y)
  west : ∀ j : Nat, j≤4*squareSize n →
    (tile (0,j)).w.2.1=incomingOuterDigit left ((j:Int)-2*squareSize n) ∧ (tile (0,j)).w.2.2=.blank
  east : ∀ j : Nat, j≤4*squareSize n →
    (tile (4*squareSize n,j)).e.2.1=outgoingOuterDigit ((j:Int)-2*squareSize n) ∧
    (tile (4*squareSize n,j)).e.2.2=.blank
  south : ∀ j : Nat, j≤4*squareSize n →
    (tile (j,0)).s.2.1=incomingOuterDigit bottom ((j:Int)-2*squareSize n) ∧ (tile (j,0)).s.2.2=.blank
  north : ∀ j : Nat, j≤4*squareSize n →
    (tile (j,4*squareSize n)).n.2.1=outgoingOuterDigit ((j:Int)-2*squareSize n) ∧
    (tile (j,4*squareSize n)).n.2.2=.blank
  covered_blank : ∀ x y : Nat, x≤4*squareSize n → y≤4*squareSize n →
    RootCovered (n+1) ((x:Int)-2*squareSize n,(y:Int)-2*squareSize n) → fullTM (tile (x,y))=tmBlank
  lower_west : ∀ b : RedSquare, LowerSquareInside (n+1) b → ∀ j : Nat, j≤2*boardHalf b.level →
    let d := (tile (lowerOriginX n b,lowerOriginY n b+j)).w.2.1
    if ((j:Int)-boardHalf b.level)%4=1 then d=2 ∨ d=3 else d=0
  lower_east : ∀ b : RedSquare, LowerSquareInside (n+1) b → ∀ j : Nat, j≤2*boardHalf b.level →
    (tile (lowerOriginX n b+2*boardHalf b.level,lowerOriginY n b+j)).e.2.1=
      outgoingOuterDigit ((j:Int)-boardHalf b.level)
  lower_south : ∀ b : RedSquare, LowerSquareInside (n+1) b → ∀ j : Nat, j≤2*boardHalf b.level →
    let d := (tile (lowerOriginX n b+j,lowerOriginY n b)).s.2.1
    if ((j:Int)-boardHalf b.level)%4=1 then d=2 ∨ d=3 else d=0
  lower_north : ∀ b : RedSquare, LowerSquareInside (n+1) b → ∀ j : Nat, j≤2*boardHalf b.level →
    (tile (lowerOriginX n b+j,lowerOriginY n b+2*boardHalf b.level)).n.2.1=
      outgoingOuterDigit ((j:Int)-boardHalf b.level)

end K230Verification
