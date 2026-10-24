module
public import ConcreteExpansion
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace K230Concrete

theorem width_add (n m : Nat) : width (n+m) = width n * width m := by
  induction n with
  | zero => simp [width]
  | succ n ih =>
    have h : n+1+m = (n+m)+1 := by omega
    rw [h]
    simp only [width, ih, Nat.mul_assoc]

theorem expanded_add (n m : Nat) (k : Fin 156) (x y r s : Nat)
    (hr : r < width n) (hs : s < width n) :
    expanded (n+m) k (width n*x+r) (width n*y+s) =
      expanded n (expanded m k x y) r s := by
  induction n generalizing r s with
  | zero =>
    have h0 : r=0 ∧ s=0 := by simp only [width] at hr hs; omega
    simp [h0.1, h0.2, width, expanded]
  | succ n ih =>
    have hn : n+1+m = (n+m)+1 := by omega
    have hx : 2*width n*x+r = 2*(width n*x)+r := by rw [Nat.mul_assoc]
    have hy : 2*width n*y+s = 2*(width n*y)+s := by rw [Nat.mul_assoc]
    have hxd : (2*width n*x+r)/2 = width n*x+r/2 := by omega
    have hyd : (2*width n*y+s)/2 = width n*y+s/2 := by omega
    have hxr : (2*width n*x+r)%2 = r%2 := by omega
    have hyr : (2*width n*y+s)%2 = s%2 := by omega
    have hrd : r/2 < width n := by simp only [width] at hr; omega
    have hsd : s/2 < width n := by simp only [width] at hs; omega
    rw [hn]
    simp only [expanded, width, hxd, hyd, hxr, hyr]
    rw [ih (r/2) (s/2) hrd hsd]

@[expose] def squareSize (n : Nat) : Nat := width (2*n)

theorem squareSize_pos (n : Nat) : 0 < squareSize n := width_pos (2*n)

theorem squareSize_step (n : Nat) : squareSize (n+1) = 4 * squareSize n := by
  have h : 2*(n+1) = 2*n+2 := by omega
  simp only [squareSize, h, width_add]
  change width (2*n) * 4 = 4 * width (2*n)
  omega

theorem nested_anchor (n r s : Nat) (hr : r < squareSize n) (hs : s < squareSize n) :
    expanded (2*(n+1)) anchor (squareSize n+r) (squareSize n+s) =
      expanded (2*n) anchor r s := by
  have h : 2*(n+1) = 2*n+2 := by omega
  have he := expanded_add (2*n) 2 anchor 1 1 r s hr hs
  simpa only [Nat.mul_one, anchor_fixed, h, squareSize] using he

@[expose] def corner : Nat → Int
  | 0 => 0
  | n+1 => corner n - squareSize n

@[expose] def squareUpper (n : Nat) : Int := corner n + squareSize n - 1
@[expose] abbrev Point := Int × Int
@[expose] def InSquare (n : Nat) (p : Point) : Prop :=
  corner n ≤ p.1 ∧ p.1 ≤ squareUpper n ∧ corner n ≤ p.2 ∧ p.2 ≤ squareUpper n

theorem squareUpper_step (n : Nat) : squareUpper (n+1) = squareUpper n + 2*squareSize n := by
  have h := squareSize_step n
  simp only [squareUpper, corner]
  omega

theorem square_step (n : Nat) (p : Point) (h : InSquare n p) : InSquare (n+1) p := by
  have hp := squareSize_pos n
  simp only [InSquare] at h ⊢
  rw [corner, squareUpper_step]
  omega

theorem square_mono (n m : Nat) (h : n ≤ m) (p : Point) : InSquare n p → InSquare m p := by
  induction m generalizing n with
  | zero =>
    have hn : n=0 := by omega
    subst n
    exact id
  | succ m ih =>
    intro hp
    by_cases hnm : n ≤ m
    · exact square_step m p (ih n hnm hp)
    · have hn : n=m+1 := by omega
      subst n
      exact hp

theorem corner_bound (n : Nat) : corner n ≤ -(n : Int) := by
  induction n with
  | zero => decide
  | succ n ih => have hp := squareSize_pos n; simp only [corner]; omega

theorem squareUpper_bound (n : Nat) : (n : Int) ≤ squareUpper n := by
  induction n with
  | zero => decide
  | succ n ih => have hp := squareSize_pos n; rw [squareUpper_step]; omega

@[expose] def cover (p : Point) : Nat := p.1.natAbs + p.2.natAbs

theorem cover_spec (p : Point) : InSquare (cover p) p := by
  have hx : p.1 ≤ (p.1.natAbs : Int) := Int.le_natAbs
  have hnx : -p.1 ≤ (p.1.natAbs : Int) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -p.1))
  have hy : p.2 ≤ (p.2.natAbs : Int) := Int.le_natAbs
  have hny : -p.2 ≤ (p.2.natAbs : Int) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -p.2))
  have hl := corner_bound (cover p)
  have hu := squareUpper_bound (cover p)
  dsimp [InSquare, cover] at *
  omega

@[expose] def squarePatch (n : Nat) (p : Point) : Fin 156 :=
  expanded (2*n) anchor (p.1-corner n).toNat (p.2-corner n).toNat

theorem local_coordinates (n : Nat) (p : Point) (hp : InSquare n p) :
    0 ≤ p.1-corner n ∧ (p.1-corner n).toNat < squareSize n ∧
    0 ≤ p.2-corner n ∧ (p.2-corner n).toNat < squareSize n := by
  simp only [InSquare, squareUpper] at hp
  omega

theorem squarePatch_step (n : Nat) (p : Point) (hp : InSquare n p) :
    squarePatch (n+1) p = squarePatch n p := by
  have hc := local_coordinates n p hp
  have hx : (p.1-corner (n+1)).toNat = squareSize n + (p.1-corner n).toNat := by
    simp only [corner]; omega
  have hy : (p.2-corner (n+1)).toNat = squareSize n + (p.2-corner n).toNat := by
    simp only [corner]; omega
  simp only [squarePatch, hx, hy]
  exact nested_anchor n _ _ hc.2.1 hc.2.2.2

theorem squarePatch_coherent (n m : Nat) (h : n ≤ m) (p : Point) (hp : InSquare n p) :
    squarePatch m p = squarePatch n p := by
  induction m generalizing n with
  | zero =>
    have hn : n=0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm : n ≤ m
    · rw [squarePatch_step m p (square_mono n m hnm p hp)]
      exact ih n hnm hp
    · have hn : n=m+1 := by omega
      subst n
      rfl

@[expose] def canonicalPlane (p : Point) : Fin 156 := squarePatch (cover p) p

theorem canonicalPlane_agrees (n : Nat) (p : Point) (hp : InSquare n p) :
    canonicalPlane p = squarePatch n p := by
  unfold canonicalPlane
  rcases Nat.le_total n (cover p) with h | h
  · exact squarePatch_coherent n (cover p) h p hp
  · exact (squarePatch_coherent (cover p) n h p (cover_spec p)).symm

theorem common_square (p q : Point) : ∃ n, InSquare n p ∧ InSquare n q := by
  refine ⟨cover p+cover q, ?_, ?_⟩
  · exact square_mono _ _ (by omega) p (cover_spec p)
  · exact square_mono _ _ (by omega) q (cover_spec q)

theorem squarePatch_horizontal (n : Nat) (p : Point)
    (hp : InSquare n p) (hq : InSquare n (p.1+1,p.2)) :
    (Wang156.tile (squarePatch n p).val).e =
      (Wang156.tile (squarePatch n (p.1+1,p.2)).val).w := by
  have hc := local_coordinates n p hp
  have hqc := local_coordinates n (p.1+1,p.2) hq
  have hx : (p.1+1-corner n).toNat = (p.1-corner n).toNat+1 := by omega
  have hb : (p.1-corner n).toNat+1 < width (2*n) := by
    change (p.1-corner n).toNat+1 < squareSize n
    omega
  simp only [squarePatch, hx]
  exact expanded_horizontal (2*n) anchor _ _ hb hc.2.2.2

theorem squarePatch_vertical (n : Nat) (p : Point)
    (hp : InSquare n p) (hq : InSquare n (p.1,p.2+1)) :
    (Wang156.tile (squarePatch n p).val).n =
      (Wang156.tile (squarePatch n (p.1,p.2+1)).val).s := by
  have hc := local_coordinates n p hp
  have hqc := local_coordinates n (p.1,p.2+1) hq
  have hy : (p.2+1-corner n).toNat = (p.2-corner n).toNat+1 := by omega
  have hb : (p.2-corner n).toNat+1 < width (2*n) := by
    change (p.2-corner n).toNat+1 < squareSize n
    omega
  simp only [squarePatch, hy]
  exact expanded_vertical (2*n) anchor _ _ hc.2.1 hb

theorem canonicalPlane_horizontal (p : Point) :
    (Wang156.tile (canonicalPlane p).val).e =
      (Wang156.tile (canonicalPlane (p.1+1,p.2)).val).w := by
  obtain ⟨n,hp,hq⟩ := common_square p (p.1+1,p.2)
  rw [canonicalPlane_agrees n p hp, canonicalPlane_agrees n (p.1+1,p.2) hq]
  exact squarePatch_horizontal n p hp hq

theorem canonicalPlane_vertical (p : Point) :
    (Wang156.tile (canonicalPlane p).val).n =
      (Wang156.tile (canonicalPlane (p.1,p.2+1)).val).s := by
  obtain ⟨n,hp,hq⟩ := common_square p (p.1,p.2+1)
  rw [canonicalPlane_agrees n p hp, canonicalPlane_agrees n (p.1,p.2+1) hq]
  exact squarePatch_vertical n p hp hq

theorem exact156_tiles_plane : ∃ T : Point → Fin 156, ∀ p,
    (Wang156.tile (T p).val).e = (Wang156.tile (T (p.1+1,p.2)).val).w ∧
    (Wang156.tile (T p).val).n = (Wang156.tile (T (p.1,p.2+1)).val).s :=
  ⟨canonicalPlane, fun p => ⟨canonicalPlane_horizontal p, canonicalPlane_vertical p⟩⟩

end K230Concrete

#print axioms K230Concrete.expanded_add
#print axioms K230Concrete.squarePatch_coherent
#print axioms K230Concrete.exact156_tiles_plane
