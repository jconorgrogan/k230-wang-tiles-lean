module
public import FullPlaneData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification
@[expose] def hChannelBases : List Nat := [89,90,92,93,95,96,98,100,101,103,105,108,111,114,116,119,154,155]
@[expose] def vChannelBases : List Nat := [132,133,134,135,136,137,138,139,140,141,142,143,148,149,150,151,153,155]
@[expose] def seedBases : List Nat := [65,71,79,87]
@[expose] def SeedBase (b : Nat) : Prop := b ∈ seedBases
instance (b : Nat) : Decidable (SeedBase b) := by unfold SeedBase seedBases; infer_instance
@[expose] def HasHChannel (b : Nat) : Prop := b ∈ hChannelBases
@[expose] def HasVChannel (b : Nat) : Prop := b ∈ vChannelBases
instance (b : Nat) : Decidable (HasHChannel b) := by unfold HasHChannel hChannelBases; infer_instance
instance (b : Nat) : Decidable (HasVChannel b) := by unfold HasVChannel vChannelBases; infer_instance

theorem exact_H_channel_presence : ∀ g ∈ exactGroups.toList,
    (g.2.1/16%4≠0 ↔ HasHChannel g.1) ∧ (g.2.1%4≠0 ↔ HasHChannel g.1) := by decide
theorem exact_V_channel_presence : ∀ g ∈ exactGroups.toList,
    (g.2.1/64%4≠0 ↔ HasVChannel g.1) ∧ (g.2.1/4%4≠0 ↔ HasVChannel g.1) := by decide
theorem exact_seed_class : ∀ g ∈ exactGroups.toList, g.2.2=5 ↔ g.1 ∈ seedBases := by decide
end K230Verification
