module
public import RawPatchBridge
public section
namespace K230Verification
/-- Finite-square pasting data. `none` denotes the root's exposed piece;
    `some i` denotes a child piece. Ownership may vary from cell to cell.
    No tile, edge, or completion outside the finite square is constrained. -/
structure OwnerPatchData (I : Type*) (R : Nat) where
  owner : Cell → Option I
  piece : Option I → Cell → Quad FullColor
  member : ∀ x y : Int, 0≤x → x≤R → 0≤y → y≤R →
    piece (owner (x,y)) (x,y) ∈ exactFullPlaneTiles
  horizontal_same : ∀ x y : Int, 0≤x → x<R → 0≤y → y≤R →
    owner (x,y)=owner (x+1,y) →
    (piece (owner (x,y)) (x,y)).e=(piece (owner (x,y)) (x+1,y)).w
  horizontal_seam : ∀ x y : Int, 0≤x → x<R → 0≤y → y≤R →
    owner (x,y)≠owner (x+1,y) →
    (piece (owner (x,y)) (x,y)).e=(piece (owner (x+1,y)) (x+1,y)).w
  vertical_same : ∀ x y : Int, 0≤x → x≤R → 0≤y → y<R →
    owner (x,y)=owner (x,y+1) →
    (piece (owner (x,y)) (x,y)).n=(piece (owner (x,y)) (x,y+1)).s
  vertical_seam : ∀ x y : Int, 0≤x → x≤R → 0≤y → y<R →
    owner (x,y)≠owner (x,y+1) →
    (piece (owner (x,y)) (x,y)).n=(piece (owner (x,y+1)) (x,y+1)).s

@[expose] def OwnerPatchData.toRawSquare {I : Type*} {R : Nat} (D : OwnerPatchData I R) : RawSquare R where
  tile := fun p => D.piece (D.owner p) p
  member := D.member
  horizontal := by
    classical
    intro x y hx hxR hy hyR
    by_cases h : D.owner (x,y)=D.owner (x+1,y)
    · simpa only [h] using D.horizontal_same x y hx hxR hy hyR h
    · exact D.horizontal_seam x y hx hxR hy hyR h
  vertical := by
    classical
    intro x y hx hxR hy hyR
    by_cases h : D.owner (x,y)=D.owner (x,y+1)
    · simpa only [h] using D.vertical_same x y hx hxR hy hyR h
    · exact D.vertical_seam x y hx hxR hy hyR h

theorem exactPlane_of_cofinal_owner_patches {I : Type*}
    (patches : ∀ n : Nat, ∃ R : Nat, n≤R ∧ Nonempty (OwnerPatchData I R)) : ExactPlane := by
  apply exactPlane_of_cofinal_raw_squares
  intro n
  obtain ⟨R,hR,⟨D⟩⟩ := patches n
  exact ⟨R,hR,⟨D.toRawSquare⟩⟩
end K230Verification
