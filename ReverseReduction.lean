module
public import CanonicalInduction
public section
namespace K230Verification
open K230Concrete

theorem canonical_radius_cofinal (n : Nat) : n≤4*squareSize n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hp := squareSize_pos n
    have hs := squareSize_step n
    omega

/-- Pure finite reduction to compactness. The supplied exposed pieces have
    no cross-size coherence requirement; the checked child recursion fills
    them before extracting larger and larger exact finite squares. -/
theorem exactPlane_of_exposed_boards
    (exposed : ∀ k v : Nat, v<4 → ∀ left bottom : Int → Bool,
      Nonempty (ExposedBoard (k+1) v left bottom)) : ExactPlane := by
  have allBoards := canonical_boards_of_exposed exposed
  apply exactPlane_of_cofinal_raw_squares
  intro n
  obtain ⟨D⟩ := allBoards n 0 (by decide) (fun _ => false) (fun _ => false)
  exact ⟨4*squareSize n,canonical_radius_cofinal n,⟨D.patch⟩⟩

end K230Verification
#print axioms K230Verification.exactPlane_of_exposed_boards
