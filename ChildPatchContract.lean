module
public import ExposedBoardContract
public import TranslatedRawSquare
public section
namespace K230Verification
open K230Concrete

/-- A recursively completed child, with its outward full colors already
    reconciled with the root's matched placeholder decoration. -/
structure FilledChild {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom) (b : RedSquare) where
  patch : RawSquare (2*boardHalf b.level)
  base : ∀ x y : Nat, x≤2*boardHalf b.level → y≤2*boardHalf b.level →
    fullBase (patch.tile (x,y))=baseTileQuad
      (redBoard n v (lowerOriginX n b+x) (lowerOriginY n b+y))
  west : ∀ j : Nat, j≤2*boardHalf b.level →
    (patch.tile (0,j)).w=(P.tile (lowerOriginX n b,lowerOriginY n b+j)).w
  east : ∀ j : Nat, j≤2*boardHalf b.level →
    (patch.tile (2*boardHalf b.level,j)).e=
      (P.tile (lowerOriginX n b+2*boardHalf b.level,lowerOriginY n b+j)).e
  south : ∀ j : Nat, j≤2*boardHalf b.level →
    (patch.tile (j,0)).s=(P.tile (lowerOriginX n b+j,lowerOriginY n b)).s
  north : ∀ j : Nat, j≤2*boardHalf b.level →
    (patch.tile (j,2*boardHalf b.level)).n=
      (P.tile (lowerOriginX n b+j,lowerOriginY n b+2*boardHalf b.level)).n

end K230Verification
