module
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Nodup
public section
namespace K230Verification
@[expose] def insertCode (n : Nat) : List Nat → List Nat
  | [] => [n]
  | a::xs => if n ≤ a then n::a::xs else a::insertCode n xs
@[expose] def sortCodes : List Nat → List Nat
  | [] => []
  | a::xs => insertCode a (sortCodes xs)
theorem insertCode_perm (n : Nat) (xs : List Nat) : (insertCode n xs).Perm (n::xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons a xs ih =>
    simp only [insertCode]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons a ih).trans (List.Perm.swap _ _ _)
theorem sortCodes_perm (xs : List Nat) : (sortCodes xs).Perm xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons a xs ih => exact (insertCode_perm a (sortCodes xs)).trans (List.Perm.cons a ih)
theorem nodup_of_sorted_codes {α : Type} (f : α → Nat) (xs : List α)
    (h : (sortCodes (xs.map f)).IsChain (· < ·)) : xs.Nodup := by
  apply List.Nodup.of_map f
  apply (sortCodes_perm (xs.map f)).nodup_iff.mp
  exact (List.isChain_iff_pairwise.mp h).imp (fun h => Nat.ne_of_lt h)
@[expose] def mergeFuel : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, a::xs, b::ys => if a ≤ b then a::mergeFuel n xs (b::ys) else b::mergeFuel n (a::xs) ys
@[expose] def fastSort : Nat → List Nat → List Nat
  | 0, xs => xs
  | n+1, xs =>
    if xs.length ≤ 1 then xs else
    mergeFuel xs.length (fastSort n (xs.take (xs.length/2))) (fastSort n (xs.drop (xs.length/2)))
theorem mergeFuel_perm (n : Nat) (xs ys : List Nat) : (mergeFuel n xs ys).Perm (xs++ys) := by
  induction n generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons a xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons b ys =>
        simp only [mergeFuel]
        split
        · exact List.Perm.cons a (ih xs (b::ys))
        · exact (List.Perm.cons b (ih (a::xs) ys)).trans (List.perm_cons_append_cons b (List.Perm.refl _))
theorem fastSort_perm (n : Nat) (xs : List Nat) : (fastSort n xs).Perm xs := by
  induction n generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simp only [fastSort]
    split
    · exact List.Perm.refl _
    · exact (mergeFuel_perm _ _ _).trans (by simpa using (ih (xs.take (xs.length/2))).append (ih (xs.drop (xs.length/2))))
theorem nodup_of_fast_codes {α : Type} (f : α → Nat) (xs : List α) (n : Nat)
    (h : (fastSort n (xs.map f)).IsChain (· < ·)) : xs.Nodup := by
  apply List.Nodup.of_map f
  apply (fastSort_perm n (xs.map f)).nodup_iff.mp
  exact (List.isChain_iff_pairwise.mp h).imp (fun h => Nat.ne_of_lt h)
end K230Verification
