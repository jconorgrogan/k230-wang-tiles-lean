module
public import ConcreteBoards
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace K230Concrete

theorem subboard_crop (N m v x0 y0 qx qy : Nat)
    (hm:m≤N) (hv:v<4)
    (hgridx:2*squareSize N+x0 = 8*squareSize m*qx+2*squareSize m)
    (hgridy:2*squareSize N+y0 = 8*squareSize m*qy+2*squareSize m)
    (hbx:x0+4*squareSize m≤4*squareSize N)
    (hby:y0+4*squareSize m≤4*squareSize N) :
    ∃ w:Nat, w<4 ∧ ∀ r s:Nat, r≤4*squareSize m → s≤4*squareSize m →
      redBoard N v (x0+r) (y0+s) = redBoard m w r s := by
  let k := expanded (2*(N-m)) (coreRepresentative v) qx qy
  refine ⟨boardVariant k,boardVariant_bound k,?_⟩
  intro r s hr hs
  have hw := squareSize_pos m
  have he : (2*m+3)+2*(N-m)=2*N+3 := by omega
  have hwidth : width (2*m+3)=8*squareSize m := by
    rw [width_add]
    change width (2*m)*8=8*width (2*m)
    omega
  have hx : 2*squareSize m+r < width (2*m+3) := by omega
  have hy : 2*squareSize m+s < width (2*m+3) := by omega
  have h := expanded_add (2*m+3) (2*(N-m)) (coreRepresentative v) qx qy
    (2*squareSize m+r) (2*squareSize m+s) hx hy
  rw [he,hwidth] at h
  have hcx : 8*squareSize m*qx+(2*squareSize m+r)=2*squareSize N+(x0+r) := by omega
  have hcy : 8*squareSize m*qy+(2*squareSize m+s)=2*squareSize N+(y0+s) := by omega
  rw [hcx,hcy] at h
  rw [←redBoard_as_expanded N v (x0+r) (y0+s) hv (by omega) (by omega)] at h
  rw [redBoard_core_identity m k r s hr hs] at h
  exact h

end K230Concrete
#print axioms K230Concrete.subboard_crop
