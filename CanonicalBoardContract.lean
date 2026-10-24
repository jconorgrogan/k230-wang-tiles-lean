module
public import RawPatchBridge
public import ConcreteBoards
public import ConcreteRoles
public section
namespace K230Verification
open K230Concrete

@[expose] def baseTileQuad (k : Fin 156) : Quad Nat :=
  ⟨(Wang156.tile k.val).n,(Wang156.tile k.val).e,(Wang156.tile k.val).s,(Wang156.tile k.val).w⟩

/-- An independently selectable a/b parameter at every present outward edge. -/
@[expose] def incomingOuterDigit (choice : Int → Bool) (t : Int) : Nat :=
  if t%4=1 then (if choice t then 3 else 2) else 0
@[expose] def outgoingOuterDigit (t : Int) : Nat := if t%4=1 then 3 else 0

/-- Strong induction contract for finite decorated boards. Unlike RawSquare,
    it records the exact base crop and outward channel/TM labels needed to
    paste a completed child. Left and bottom choices vary independently at
    every transverse coordinate. -/
structure CanonicalBoard (n v : Nat) (left bottom : Int → Bool) where
  patch : RawSquare (4*squareSize n)
  base : ∀ x y : Nat, x≤4*squareSize n → y≤4*squareSize n →
    fullBase (patch.tile (x,y))=baseTileQuad (redBoard n v x y)
  west : ∀ j : Nat, j≤4*squareSize n →
    (patch.tile (0,j)).w.2.1=incomingOuterDigit left ((j:Int)-2*squareSize n) ∧
    (patch.tile (0,j)).w.2.2=.blank
  east : ∀ j : Nat, j≤4*squareSize n →
    (patch.tile (4*squareSize n,j)).e.2.1=outgoingOuterDigit ((j:Int)-2*squareSize n) ∧
    (patch.tile (4*squareSize n,j)).e.2.2=.blank
  south : ∀ j : Nat, j≤4*squareSize n →
    (patch.tile (j,0)).s.2.1=incomingOuterDigit bottom ((j:Int)-2*squareSize n) ∧
    (patch.tile (j,0)).s.2.2=.blank
  north : ∀ j : Nat, j≤4*squareSize n →
    (patch.tile (j,4*squareSize n)).n.2.1=outgoingOuterDigit ((j:Int)-2*squareSize n) ∧
    (patch.tile (j,4*squareSize n)).n.2.2=.blank

end K230Verification
