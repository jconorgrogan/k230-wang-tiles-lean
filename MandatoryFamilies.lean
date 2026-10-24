module
public import ConcreteRoles
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification
 theorem family_three_iff_right_midpoint : ∀ g ∈ exactGroups.toList,
    (g.2.2=3 ↔ g.1 ∈ ([35,36,37,38] : List Nat)) := by decide
 theorem family_four_iff_left_midpoint : ∀ g ∈ exactGroups.toList,
    (g.2.2=4 ↔ g.1 ∈ ([47,49,50,52] : List Nat)) := by decide
end K230Verification
