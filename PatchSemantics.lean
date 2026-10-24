module
public import ExactTable
public section
namespace Wang156
@[expose] abbrev Patch := Nat → Nat → Fin 156
@[expose] def macroX (dir which : Nat) : Nat := if which = 1 ∧ dir = 1 then 4 else 2
@[expose] def macroY (dir which : Nat) : Nat := if which = 1 ∧ dir = 2 then 4 else 2
@[expose] def blockX (dir which q : Nat) : Nat := macroX dir which + q % 2
@[expose] def blockY (dir which q : Nat) : Nat := macroY dir which + q / 2
@[expose] def Block (dir : Nat) (p : Patch) (which k : Nat) : Prop :=
  ∀ q, q < 4 → (p (blockX dir which q) (blockY dir which q)).val = sigma k q
@[expose] def Valid (w : Nat) (p : Patch) : Prop :=
  (∀ i j, i + 1 < w → j < w → (tile (p i j).val).e = (tile (p (i+1) j).val).w) ∧
  (∀ i j, i < w → j + 1 < w → (tile (p i j).val).n = (tile (p i (j+1)).val).s)
end Wang156
