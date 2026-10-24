module
public import FullBoardOccurrences
public import BoardLocality
public section
namespace K230Verification
open K230Concrete

/-- Each original indexed full tile retains the exact channel presence of its chosen base. -/
theorem indexed_H_presence (i : Fin 11487) :
    ((indexedFullTile i).e.2.1≠0 ↔ HasHChannel (indexedBase i).val) ∧
    ((indexedFullTile i).w.2.1≠0 ↔ HasHChannel (indexedBase i).val) := by
  obtain ⟨t,_,ht⟩ := (indexedGroup_spec i).2
  rw [ht]
  exact exact_H_channel_presence _ (indexedGroup_spec i).1

theorem indexed_V_presence (i : Fin 11487) :
    ((indexedFullTile i).n.2.1≠0 ↔ HasVChannel (indexedBase i).val) ∧
    ((indexedFullTile i).s.2.1≠0 ↔ HasVChannel (indexedBase i).val) := by
  obtain ⟨t,_,ht⟩ := (indexedGroup_spec i).2
  rw [ht]
  exact exact_V_channel_presence _ (indexedGroup_spec i).1

theorem indexed_seed_family (i : Fin 11487) (h : SeedBase (indexedBase i).val) :
    (indexedGroup i).2.2=5 :=
  (exact_seed_class _ (indexedGroup_spec i).1).mpr h

@[expose] def boardCell (b : Cell) (x y : Nat) : Cell :=
  (b.1+(x:Int),b.2+(y:Int))
@[expose] def FullBoardAt (T : Cell → Fin 11487) (n v : Nat) (b : Cell) : Prop :=
  ∀ x y : Nat, x≤4*squareSize n → y≤4*squareSize n →
    indexedBase (T (boardCell b x y)) = redBoard n v x y

theorem exact_full_board_occurrence (T : Cell → Fin 11487) (h : FullValid T) (n : Nat) :
    ∃ (v : Nat) (b : Cell), v<4 ∧ FullBoardAt T n v b :=
  exact_full_redBoard T h n

theorem full_board_channel_pattern (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hn : 1≤n) (hb : FullBoardAt T n v b) (x y : Nat)
    (hx : x≤4*squareSize n) (hy : y≤4*squareSize n) :
    ((indexedFullTile (T (boardCell b x y))).e.2.1≠0 ↔ y%4=1) ∧
    ((indexedFullTile (T (boardCell b x y))).w.2.1≠0 ↔ y%4=1) ∧
    ((indexedFullTile (T (boardCell b x y))).n.2.1≠0 ↔ x%4=1) ∧
    ((indexedFullTile (T (boardCell b x y))).s.2.1≠0 ↔ x%4=1) := by
  have h := indexed_H_presence (T (boardCell b x y))
  have vv := indexed_V_presence (T (boardCell b x y))
  rw [hb x y hx hy] at h vv
  have hp := redBoard_modulo_four n hn v x y
  exact ⟨h.1.trans hp.1,h.2.trans hp.1,vv.1.trans hp.2,vv.2.trans hp.2⟩

theorem full_board_lowest_cross (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hn : 1≤n) (hb : FullBoardAt T n v b) (x y : Nat)
    (hx : x≤4*squareSize n) (hy : y≤4*squareSize n)
    (hxr : x%4=1) (hyr : y%4=1) :
    (indexedGroup (T (boardCell b x y))).1=155 := by
  have h := hb x y hx hy
  rw [redBoard_lowest_cross n hn v x y hxr hyr] at h
  exact congrArg Fin.val h

theorem full_board_center_seed (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T n v b) :
    (indexedGroup (T (boardCell b (2*squareSize n) (2*squareSize n)))).2.2=5 := by
  apply indexed_seed_family
  rw [hb (2*squareSize n) (2*squareSize n) (by omega) (by omega)]
  exact redBoard_center_seed n v hv

#print axioms indexed_H_presence
#print axioms exact_full_board_occurrence
#print axioms full_board_channel_pattern
#print axioms full_board_lowest_cross
#print axioms full_board_center_seed
end K230Verification
