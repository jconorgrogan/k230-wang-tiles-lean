module
public import PasteChildren
public import CanonicalBoardBase
public import FilledChildAssembly
public section
set_option maxHeartbeats 0
namespace K230Verification

/-- Strong finite recursion. Each child is strictly smaller, has its own
    arbitrary allowed outward parameters, and is pasted only after exact
    full-color agreement with the enclosing exposed piece is proved. -/
theorem canonical_boards_of_exposed
    (exposed : ∀ k v : Nat, v<4 → ∀ left bottom : Int → Bool,
      Nonempty (ExposedBoard (k+1) v left bottom)) :
    ∀ n v : Nat, v<4 → ∀ left bottom : Int → Bool,
      Nonempty (CanonicalBoard n v left bottom) := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv left bottom
    cases n with
    | zero => exact ⟨canonicalBoardZero ⟨v,hv⟩ left bottom⟩
    | succ k =>
      obtain ⟨P⟩ := exposed k v hv left bottom
      have children : ∀ b : RedSquare, LowerSquareInside (k+1+1) b → Nonempty (FilledChild P b) := by
        intro b hb
        apply filledChild_of_smaller_boards P hv b hb
        intro w hw l d
        have hlt : b.level-1<k+1 := by have := hb.1; have := b.level_pos; omega
        exact ih (b.level-1) hlt w hw l d
      exact ⟨pasteCanonicalBoard P (fun b hb => Classical.choice (children b hb))⟩

end K230Verification
#print axioms K230Verification.canonical_boards_of_exposed
