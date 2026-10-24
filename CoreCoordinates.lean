module
public import ConcreteBoards
public import SideCertificates
public section
namespace K230Concrete

theorem coreRepresentative_value (v : Nat) : (coreRepresentative v).val = representativeNat v := by
  by_cases h0:v=0
  · simp only [coreRepresentative,representativeNat,if_pos h0]
  · by_cases h1:v=1
    · simp only [coreRepresentative,representativeNat,if_neg h0,if_pos h1]
    · by_cases h2:v=2
      · simp only [coreRepresentative,representativeNat,if_neg h0,if_neg h1,if_pos h2]
      · simp only [coreRepresentative,representativeNat,if_neg h0,if_neg h1,if_neg h2]

theorem redBoard_one_value (v x y : Nat) (hv:v<4) (hx:x≤16) (hy:y≤16) :
    (redBoard 1 v x y).val = rawExpanded 5 (representativeNat v) (x+8) (y+8) := by
  have h := congrArg Fin.val (redBoard_as_expanded 1 v x y hv hx hy)
  rw [expanded_value,coreRepresentative_value] at h
  change (redBoard 1 v x y).val = rawExpanded 5 (representativeNat v) (8+x) (8+y) at h
  simpa only [Nat.add_comm] using h

end K230Concrete
