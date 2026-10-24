module

public import Std

public section

/-!
Conditional, phase-aware hierarchy interface.  This file does not assert
that the concrete 156-tile system satisfies the desubstitution premise.
That premise is precisely the global consequence of its finite D1/D2
certificates, parity propagation, and injectivity.
-/

namespace K230PhaseHierarchy

@[expose]
abbrev Point := Int × Int
@[expose]
abbrev Offset := Fin 2 × Fin 2
@[expose]
abbrev Tiling (Tile : Type) := Point → Tile

@[expose]
def place (epsilon : Offset) (q : Point) (r : Offset) : Point :=
  ((epsilon.1.val : Int) + 2 * q.1 + r.1.val,
   (epsilon.2.val : Int) + 2 * q.2 + r.2.val)

structure System where
  Tile : Type
  sigma : Tile → Offset → Tile
  valid : Tiling Tile → Prop
  desubstitute : ∀ T, valid T → ∃ epsilon U, valid U ∧
    ∀ q r, T (place epsilon q r) = sigma (U q) r

@[expose]
noncomputable def next (S : System) (T : { T // S.valid T }) :
    Offset × { U // S.valid U } := by
  classical
  let epsilon := Classical.choose (S.desubstitute T.val T.property)
  let U := Classical.choose (Classical.choose_spec (S.desubstitute T.val T.property))
  have h := Classical.choose_spec
    (Classical.choose_spec (S.desubstitute T.val T.property))
  exact (epsilon, ⟨U, h.1⟩)

theorem next_spec (S : System) (T : { T // S.valid T }) (q : Point) (r : Offset) :
    T.val (place (next S T).1 q r) = S.sigma ((next S T).2.val q) r := by
  classical
  exact (Classical.choose_spec
    (Classical.choose_spec (S.desubstitute T.val T.property))).2 q r

@[expose]
noncomputable def ancestor (S : System) (T : { T // S.valid T }) :
    Nat → { U // S.valid U }
  | 0 => T
  | n + 1 => (next S (ancestor S T n)).2

@[expose]
noncomputable def phase (S : System) (T : { T // S.valid T }) (n : Nat) : Offset :=
  (next S (ancestor S T n)).1

@[expose]
def shifted (bits : Nat → Offset) : Nat → Offset := fun i => bits (i + 1)

@[expose]
def location (eps : Nat → Offset) (start : Nat) : Nat → Point → (Nat → Offset) → Point
  | 0, q, _ => q
  | n + 1, q, bits => place (eps start)
      (location eps (start + 1) n q (shifted bits)) (bits 0)

@[expose]
def supertile (S : System) : Nat → S.Tile → (Nat → Offset) → S.Tile
  | 0, t, _ => t
  | n + 1, t, bits => S.sigma (supertile S n t (shifted bits)) (bits 0)

theorem all_orders (S : System) (T : { T // S.valid T })
    (n start : Nat) (q : Point) (bits : Nat → Offset) :
    (ancestor S T start).val (location (phase S T) start n q bits) =
      supertile S n ((ancestor S T (start + n)).val q) bits := by
  induction n generalizing start bits with
  | zero => rfl
  | succ n ih =>
    change (ancestor S T start).val
      (place (next S (ancestor S T start)).1
        (location (phase S T) (start + 1) n q (shifted bits)) (bits 0)) = _
    rw [next_spec]
    change S.sigma ((ancestor S T (start + 1)).val
      (location (phase S T) (start + 1) n q (shifted bits))) (bits 0) = _
    rw [ih]
    have h : start + 1 + n = start + (n + 1) := by omega
    simp only [supertile, h]

theorem contains_arbitrary_supertile (S : System) (T : { T // S.valid T })
    (n : Nat) : ∃ t : S.Tile, ∀ bits,
    T.val (location (phase S T) 0 n (0, 0) bits) = supertile S n t bits := by
  refine ⟨(ancestor S T n).val (0, 0), ?_⟩
  intro bits
  simpa only [ancestor, Nat.zero_add] using all_orders S T n 0 (0, 0) bits

theorem ancestor_valid (S : System) (T : { T // S.valid T }) (n : Nat) :
    S.valid (ancestor S T n).val := (ancestor S T n).property

/- Distinct micro-offsets really occupy adjacent unit cells at every step;
   no phase is silently fixed at zero. -/
theorem place_coordinates (epsilon : Offset) (q : Point) (r : Offset) :
    (place epsilon q r).1 = (epsilon.1.val : Int) + 2*q.1 + r.1.val ∧
    (place epsilon q r).2 = (epsilon.2.val : Int) + 2*q.2 + r.2.val := ⟨rfl, rfl⟩

/-! The exact recognition-to-hierarchy bridge.  D1/D2 below are universal
    local implications on plane tilings.  Obtaining them from the literal
    finite CNFs, and deriving the phase from parity propagation, remain
    explicit obligations of the concrete certificate checker. -/

structure WangPresentation where
  Tile : Type
  Color : Type
  north : Tile → Color
  east : Tile → Color
  south : Tile → Color
  west : Tile → Color
  sigma : Tile → Offset → Tile

@[expose]
def wangValid (W : WangPresentation) (T : Tiling W.Tile) : Prop :=
  ∀ q, W.east (T q) = W.west (T (q.1 + 1, q.2)) ∧
       W.north (T q) = W.south (T (q.1, q.2 + 1))

@[expose]
def isBlock (W : WangPresentation) (T : Tiling W.Tile)
    (epsilon : Offset) (q : Point) (t : W.Tile) : Prop :=
  ∀ r, T (place epsilon q r) = W.sigma t r

structure Recognition (W : WangPresentation) where
  phase : Tiling W.Tile → Offset
  D1 : ∀ T, wangValid W T → ∀ q, ∃ t, isBlock W T (phase T) q t
  D2h : ∀ T, wangValid W T → ∀ q a b,
    isBlock W T (phase T) q a →
    isBlock W T (phase T) (q.1 + 1, q.2) b → W.east a = W.west b
  D2v : ∀ T, wangValid W T → ∀ q a b,
    isBlock W T (phase T) q a →
    isBlock W T (phase T) (q.1, q.2 + 1) b → W.north a = W.south b

@[expose]
noncomputable def decoded (W : WangPresentation) (R : Recognition W)
    (T : Tiling W.Tile) (h : wangValid W T) : Tiling W.Tile :=
  fun q => Classical.choose (R.D1 T h q)

theorem decoded_block (W : WangPresentation) (R : Recognition W)
    (T : Tiling W.Tile) (h : wangValid W T) (q : Point) :
    isBlock W T (R.phase T) q (decoded W R T h q) :=
  Classical.choose_spec (R.D1 T h q)

theorem decoded_valid (W : WangPresentation) (R : Recognition W)
    (T : Tiling W.Tile) (h : wangValid W T) :
    wangValid W (decoded W R T h) := by
  intro q
  constructor
  · exact R.D2h T h q _ _ (decoded_block W R T h q)
      (decoded_block W R T h (q.1 + 1, q.2))
  · exact R.D2v T h q _ _ (decoded_block W R T h q)
      (decoded_block W R T h (q.1, q.2 + 1))

@[expose]
noncomputable def recognizedSystem (W : WangPresentation) (R : Recognition W) : System where
  Tile := W.Tile
  sigma := W.sigma
  valid := wangValid W
  desubstitute := by
    intro T h
    exact ⟨R.phase T, decoded W R T h, decoded_valid W R T h,
      fun q r => decoded_block W R T h q r⟩

@[expose]
def zeroOffset : Offset := (⟨0, by decide⟩, ⟨0, by decide⟩)

@[expose]
def scale : Nat → Int
  | 0 => 1
  | n + 1 => 2 * scale n

@[expose]
def origin (eps : Nat → Offset) (start : Nat) : Nat → Point
  | 0 => (0, 0)
  | n + 1 => place (eps start) (origin eps (start + 1) n) zeroOffset

@[expose]
def binaryOffset : Nat → (Nat → Offset) → Point
  | 0, _ => (0, 0)
  | n + 1, bits =>
    (2*(binaryOffset n (shifted bits)).1 + ((bits 0).1.val : Int),
     2*(binaryOffset n (shifted bits)).2 + ((bits 0).2.val : Int))

theorem location_affine (eps : Nat → Offset) (start n : Nat)
    (q : Point) (bits : Nat → Offset) :
    (location eps start n q bits).1 = (origin eps start n).1 + scale n * q.1 +
      (binaryOffset n bits).1 ∧
    (location eps start n q bits).2 = (origin eps start n).2 + scale n * q.2 +
      (binaryOffset n bits).2 := by
  induction n generalizing start bits with
  | zero => simp [location, origin, scale, binaryOffset]
  | succ n ih =>
    have hx := (ih (start + 1) (shifted bits)).1
    have hy := (ih (start + 1) (shifted bits)).2
    simp only [location, origin, binaryOffset, place, zeroOffset, scale,
      Int.mul_assoc]
    constructor <;> omega

theorem scale_pos (n : Nat) : 0 < scale n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [scale]; omega

theorem scale_eq_pow (n : Nat) : scale n = (2 : Int)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scale, ih, Int.pow_succ]; omega

theorem binaryOffset_bounds (n : Nat) (bits : Nat → Offset) :
    0 ≤ (binaryOffset n bits).1 ∧ (binaryOffset n bits).1 < scale n ∧
    0 ≤ (binaryOffset n bits).2 ∧ (binaryOffset n bits).2 < scale n := by
  induction n generalizing bits with
  | zero => simp [binaryOffset, scale]
  | succ n ih =>
    have h := ih (shifted bits)
    have hx := (bits 0).1.isLt
    have hy := (bits 0).2.isLt
    simp only [binaryOffset, scale]
    omega

theorem binaryOffset_surjective (n : Nat) (x y : Int)
    (hx : 0 ≤ x ∧ x < scale n) (hy : 0 ≤ y ∧ y < scale n) :
    ∃ bits, binaryOffset n bits = (x, y) := by
  induction n generalizing x y with
  | zero =>
    have h0 : x = 0 ∧ y = 0 := by simp only [scale] at hx hy; omega
    exact ⟨fun _ => zeroOffset, by simp [binaryOffset, h0.1, h0.2]⟩
  | succ n ih =>
    simp only [scale] at hx hy
    have hxd : 0 ≤ x / 2 ∧ x / 2 < scale n := by omega
    have hyd : 0 ≤ y / 2 ∧ y / 2 < scale n := by omega
    obtain ⟨tail, ht⟩ := ih (x / 2) (y / 2) hxd hyd
    let rx : Fin 2 := ⟨(x % 2).toNat, by omega⟩
    let ry : Fin 2 := ⟨(y % 2).toNat, by omega⟩
    let bits : Nat → Offset := fun i => match i with
      | 0 => (rx, ry)
      | j + 1 => tail j
    have htail : shifted bits = tail := by funext i; rfl
    refine ⟨bits, ?_⟩
    simp only [binaryOffset, htail, ht, bits, rx, ry]
    apply Prod.ext <;> dsimp <;> omega

theorem origin_bounds (eps : Nat → Offset) (start n : Nat) :
    0 ≤ (origin eps start n).1 ∧ (origin eps start n).1 < scale n ∧
    0 ≤ (origin eps start n).2 ∧ (origin eps start n).2 < scale n := by
  induction n generalizing start with
  | zero => simp [origin, scale]
  | succ n ih =>
    have h := ih (start + 1)
    have hx := (eps start).1.isLt
    have hy := (eps start).2.isLt
    simp only [origin, place, zeroOffset, scale]
    omega

@[expose]
def HasSupertile (S : System) (T : Tiling S.Tile) (n : Nat) (t : S.Tile)
    (base : Point) : Prop := ∀ bits,
    T (base.1 + (binaryOffset n bits).1, base.2 + (binaryOffset n bits).2) =
      supertile S n t bits

/- With binaryOffset_bounds and binaryOffset_surjective, HasSupertile is
   an equality on an entire scale(n) by scale(n) rectangular cell block,
   not a sparse set of coordinates. -/
theorem all_grid_blocks (S : System) (T : { T // S.valid T }) (n : Nat) (q : Point) :
    HasSupertile S T.val n ((ancestor S T n).val q)
      ((origin (phase S T) 0 n).1 + scale n*q.1,
       (origin (phase S T) 0 n).2 + scale n*q.2) := by
  intro bits
  have h := all_orders S T n 0 q bits
  have ha := location_affine (phase S T) 0 n q bits
  have hl : location (phase S T) 0 n q bits =
      ((origin (phase S T) 0 n).1 + scale n*q.1 + (binaryOffset n bits).1,
       (origin (phase S T) 0 n).2 + scale n*q.2 + (binaryOffset n bits).2) :=
    Prod.ext ha.1 ha.2
  rw [hl] at h
  simpa only [ancestor, Nat.zero_add] using h

theorem contains_rectangular_supertile (S : System) (T : { T // S.valid T })
    (n : Nat) : ∃ t base, HasSupertile S T.val n t base := by
  exact ⟨(ancestor S T n).val (0,0),
    ((origin (phase S T) 0 n).1 + scale n*0,
     (origin (phase S T) 0 n).2 + scale n*0), all_grid_blocks S T n (0,0)⟩

end K230PhaseHierarchy

#print axioms K230PhaseHierarchy.all_orders
#print axioms K230PhaseHierarchy.contains_arbitrary_supertile
#print axioms K230PhaseHierarchy.decoded_valid
#print axioms K230PhaseHierarchy.location_affine
#print axioms K230PhaseHierarchy.binaryOffset_surjective
#print axioms K230PhaseHierarchy.all_grid_blocks
#print axioms K230PhaseHierarchy.contains_rectangular_supertile
