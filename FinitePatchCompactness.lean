module
public import WangCompactness
public section
namespace K230Verification
/-- A square on integer coordinates 0..R, without constraints beyond its boundary. -/
@[expose] def SquareValid {C : Type*} {N : Nat} (tiles : Fin N → WangTile C)
    (f : Cell → Fin N) (R : Nat) : Prop :=
  (∀ x y : Int, 0 ≤ x → x < R → 0 ≤ y → y ≤ R →
    (tiles (f (x,y))).east = (tiles (f (x+1,y))).west) ∧
  (∀ x y : Int, 0 ≤ x → x ≤ R → 0 ≤ y → y < R →
    (tiles (f (x,y))).north = (tiles (f (x,y+1))).south)
/-- Cofinal valid finite squares suffice; their assignments need not agree
    at different sizes and need no compatible external boundary completion. -/
theorem tilesPlane_of_cofinal_squares {C : Type*} {N : Nat} (tiles : Fin N → WangTile C)
    (patches : ∀ n : Nat, ∃ R : Nat, n ≤ R ∧ ∃ f, SquareValid tiles f R) :
    TilesPlane tiles := by
  apply (tilesPlane_iff_everyWindow tiles).mpr
  intro n
  obtain ⟨R,hR,f,hh,hv⟩ := patches (2*n+1)
  let shift : Cell → Cell := fun p => (p.1+n,p.2+n)
  refine ⟨fun p => f (shift p), ?_⟩
  intro s hs
  have hx : s.1.1.natAbs ≤ n := le_trans (Nat.le_max_left _ _) hs
  have hy : s.1.2.natAbs ≤ n := le_trans (Nat.le_max_right _ _) hs
  have hxup : s.1.1 ≤ (s.1.1.natAbs : Int) := Int.le_natAbs
  have hxlo : -(s.1.1.natAbs : Int) ≤ s.1.1 := by
    have h : -s.1.1 ≤ ((-s.1.1).natAbs : Int) := Int.le_natAbs
    simp only [Int.natAbs_neg] at h
    omega
  have hyup : s.1.2 ≤ (s.1.2.natAbs : Int) := Int.le_natAbs
  have hylo : -(s.1.2.natAbs : Int) ≤ s.1.2 := by
    have h : -s.1.2 ≤ ((-s.1.2).natAbs : Int) := Int.le_natAbs
    simp only [Int.natAbs_neg] at h
    omega
  have hx0 : 0 ≤ s.1.1+(n:Int) := by omega
  have hy0 : 0 ≤ s.1.2+(n:Int) := by omega
  have hxR : s.1.1+(n:Int) < R := by omega
  have hyR : s.1.2+(n:Int) < R := by omega
  cases hdir : s.2 with
  | false =>
    have h := hv (s.1.1+n) (s.1.2+n) hx0 (by omega) hy0 hyR
    simpa [edgeCompatible,edgeNeighbor,shift,hdir,Int.add_assoc,Int.add_comm,Int.add_left_comm] using h
  | true =>
    have h := hh (s.1.1+n) (s.1.2+n) hx0 hxR hy0 (by omega)
    simpa [edgeCompatible,edgeNeighbor,shift,hdir,Int.add_assoc,Int.add_comm,Int.add_left_comm] using h
end K230Verification
