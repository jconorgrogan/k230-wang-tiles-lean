module
public import Std
public import Mathlib.Topology.Compactness.Compact
/-!
# The exact K230 full-plane Wang construction

This statement concerns one explicit finite set, specified below by a 156-row
base table, 226 base/channel groups, and 14 computation templates. Tiles are
not rotated or reflected. A tiling assigns a tile to every cell of Z², matching
north/south and east/west colors everywhere. No seed, boundary, or distinguished
origin is imposed.

The machine is the literal 230-state, two-symbol transition table below. It
starts in state 0 at cell 0 on the all-false (blank) two-way tape. Nonhalting
means that every finite iterate of the ordinary deterministic transition is
defined. The theorem also asserts the exact list length and absence of duplicate
tiles, so the count and tiling property concern the same literal alphabet.

This statement does NOT formalize ZFC syntax, consistency, incompleteness, or
Glazer's external Rocq theorem. Those interpretations are described separately
and are not assumptions or axioms in the Solution.

This is a Palomar statement-only Challenge. Its final theorem hole is not a
proof and is not imported by the Solution. Comparator must check the separately
proved Solution declaration against precisely this statement.
-/
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Wang156
/-- A base Wang tile: north/east/south/west edge-color identifiers, plus parity tags used by the source table. -/
structure Tile where
  n : Nat
  e : Nat
  s : Nat
  w : Nat
  px : Nat
  py : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The literal 156-entry base table, with edge order north, east, south, west. -/
@[expose] def exact156table : Array Tile := #[
  ⟨0, 0, 12, 22, 0, 0⟩,
  ⟨0, 0, 18, 16, 0, 0⟩,
  ⟨0, 1, 12, 23, 0, 0⟩,
  ⟨0, 1, 18, 17, 0, 0⟩,
  ⟨0, 2, 18, 18, 0, 0⟩,
  ⟨0, 3, 18, 19, 0, 0⟩,
  ⟨0, 4, 12, 26, 0, 0⟩,
  ⟨0, 4, 18, 20, 0, 0⟩,
  ⟨0, 5, 12, 27, 0, 0⟩,
  ⟨0, 5, 18, 21, 0, 0⟩,
  ⟨0, 6, 18, 22, 0, 0⟩,
  ⟨0, 7, 18, 23, 0, 0⟩,
  ⟨0, 8, 18, 24, 0, 0⟩,
  ⟨0, 9, 18, 25, 0, 0⟩,
  ⟨0, 10, 18, 26, 0, 0⟩,
  ⟨0, 11, 18, 27, 0, 0⟩,
  ⟨1, 0, 13, 22, 0, 0⟩,
  ⟨1, 0, 19, 16, 0, 0⟩,
  ⟨1, 1, 13, 23, 0, 0⟩,
  ⟨1, 1, 19, 17, 0, 0⟩,
  ⟨1, 2, 19, 18, 0, 0⟩,
  ⟨1, 3, 19, 19, 0, 0⟩,
  ⟨1, 4, 13, 26, 0, 0⟩,
  ⟨1, 4, 19, 20, 0, 0⟩,
  ⟨1, 5, 13, 27, 0, 0⟩,
  ⟨1, 5, 19, 21, 0, 0⟩,
  ⟨1, 6, 19, 22, 0, 0⟩,
  ⟨1, 7, 19, 23, 0, 0⟩,
  ⟨1, 8, 19, 24, 0, 0⟩,
  ⟨1, 9, 19, 25, 0, 0⟩,
  ⟨1, 10, 19, 26, 0, 0⟩,
  ⟨1, 11, 19, 27, 0, 0⟩,
  ⟨2, 0, 14, 22, 0, 0⟩,
  ⟨2, 1, 14, 23, 0, 0⟩,
  ⟨2, 5, 14, 27, 0, 0⟩,
  ⟨2, 6, 20, 22, 0, 0⟩,
  ⟨2, 7, 20, 23, 0, 0⟩,
  ⟨2, 9, 20, 25, 0, 0⟩,
  ⟨2, 11, 20, 27, 0, 0⟩,
  ⟨3, 0, 15, 22, 0, 0⟩,
  ⟨3, 1, 15, 23, 0, 0⟩,
  ⟨3, 4, 15, 26, 0, 0⟩,
  ⟨3, 6, 21, 22, 0, 0⟩,
  ⟨3, 7, 21, 23, 0, 0⟩,
  ⟨3, 8, 21, 24, 0, 0⟩,
  ⟨3, 10, 21, 26, 0, 0⟩,
  ⟨4, 0, 16, 22, 0, 0⟩,
  ⟨4, 0, 22, 16, 0, 0⟩,
  ⟨4, 1, 16, 23, 0, 0⟩,
  ⟨4, 1, 22, 17, 0, 0⟩,
  ⟨4, 3, 22, 19, 0, 0⟩,
  ⟨4, 5, 16, 27, 0, 0⟩,
  ⟨4, 5, 22, 21, 0, 0⟩,
  ⟨5, 0, 17, 22, 0, 0⟩,
  ⟨5, 0, 23, 16, 0, 0⟩,
  ⟨5, 1, 17, 23, 0, 0⟩,
  ⟨5, 1, 23, 17, 0, 0⟩,
  ⟨5, 2, 23, 18, 0, 0⟩,
  ⟨5, 4, 17, 26, 0, 0⟩,
  ⟨5, 4, 23, 20, 0, 0⟩,
  ⟨6, 0, 18, 22, 0, 0⟩,
  ⟨6, 1, 18, 23, 0, 0⟩,
  ⟨6, 2, 18, 24, 0, 0⟩,
  ⟨6, 3, 18, 25, 0, 0⟩,
  ⟨6, 6, 14, 18, 0, 0⟩,
  ⟨6, 6, 15, 19, 0, 0⟩,
  ⟨7, 0, 19, 22, 0, 0⟩,
  ⟨7, 1, 19, 23, 0, 0⟩,
  ⟨7, 2, 19, 24, 0, 0⟩,
  ⟨7, 3, 19, 25, 0, 0⟩,
  ⟨7, 8, 16, 16, 0, 0⟩,
  ⟨7, 9, 17, 16, 0, 0⟩,
  ⟨8, 0, 20, 22, 0, 0⟩,
  ⟨8, 1, 20, 23, 0, 0⟩,
  ⟨8, 3, 20, 25, 0, 0⟩,
  ⟨8, 7, 12, 20, 0, 0⟩,
  ⟨9, 0, 21, 22, 0, 0⟩,
  ⟨9, 1, 21, 23, 0, 0⟩,
  ⟨9, 2, 21, 24, 0, 0⟩,
  ⟨9, 7, 12, 21, 0, 0⟩,
  ⟨10, 0, 22, 22, 0, 0⟩,
  ⟨10, 1, 22, 23, 0, 0⟩,
  ⟨10, 3, 22, 25, 0, 0⟩,
  ⟨10, 10, 13, 17, 0, 0⟩,
  ⟨11, 0, 23, 22, 0, 0⟩,
  ⟨11, 1, 23, 23, 0, 0⟩,
  ⟨11, 2, 23, 24, 0, 0⟩,
  ⟨11, 11, 13, 17, 0, 0⟩,
  ⟨12, 12, 0, 28, 0, 1⟩,
  ⟨12, 13, 0, 29, 0, 1⟩,
  ⟨12, 15, 0, 31, 0, 1⟩,
  ⟨13, 12, 1, 28, 0, 1⟩,
  ⟨13, 13, 1, 29, 0, 1⟩,
  ⟨13, 15, 1, 31, 0, 1⟩,
  ⟨14, 12, 2, 28, 0, 1⟩,
  ⟨14, 13, 2, 29, 0, 1⟩,
  ⟨14, 15, 2, 31, 0, 1⟩,
  ⟨15, 12, 3, 28, 0, 1⟩,
  ⟨15, 13, 3, 29, 0, 1⟩,
  ⟨16, 12, 4, 28, 0, 1⟩,
  ⟨16, 13, 4, 29, 0, 1⟩,
  ⟨16, 15, 4, 31, 0, 1⟩,
  ⟨17, 12, 5, 28, 0, 1⟩,
  ⟨17, 13, 5, 29, 0, 1⟩,
  ⟨18, 12, 6, 28, 0, 1⟩,
  ⟨18, 13, 6, 29, 0, 1⟩,
  ⟨18, 14, 6, 30, 0, 1⟩,
  ⟨19, 12, 7, 28, 0, 1⟩,
  ⟨19, 13, 7, 29, 0, 1⟩,
  ⟨19, 14, 7, 30, 0, 1⟩,
  ⟨20, 12, 8, 28, 0, 1⟩,
  ⟨20, 13, 8, 29, 0, 1⟩,
  ⟨20, 14, 8, 30, 0, 1⟩,
  ⟨21, 12, 9, 28, 0, 1⟩,
  ⟨21, 13, 9, 29, 0, 1⟩,
  ⟨22, 12, 10, 28, 0, 1⟩,
  ⟨22, 13, 10, 29, 0, 1⟩,
  ⟨22, 14, 10, 30, 0, 1⟩,
  ⟨23, 12, 11, 28, 0, 1⟩,
  ⟨23, 13, 11, 29, 0, 1⟩,
  ⟨24, 16, 28, 0, 1, 0⟩,
  ⟨24, 17, 28, 1, 1, 0⟩,
  ⟨24, 18, 28, 2, 1, 0⟩,
  ⟨24, 19, 28, 3, 1, 0⟩,
  ⟨24, 20, 28, 4, 1, 0⟩,
  ⟨24, 21, 28, 5, 1, 0⟩,
  ⟨24, 22, 28, 6, 1, 0⟩,
  ⟨24, 23, 28, 7, 1, 0⟩,
  ⟨24, 24, 28, 8, 1, 0⟩,
  ⟨24, 25, 28, 9, 1, 0⟩,
  ⟨24, 26, 28, 10, 1, 0⟩,
  ⟨24, 27, 28, 11, 1, 0⟩,
  ⟨25, 16, 29, 0, 1, 0⟩,
  ⟨25, 17, 29, 1, 1, 0⟩,
  ⟨25, 18, 29, 2, 1, 0⟩,
  ⟨25, 19, 29, 3, 1, 0⟩,
  ⟨25, 20, 29, 4, 1, 0⟩,
  ⟨25, 21, 29, 5, 1, 0⟩,
  ⟨25, 22, 29, 6, 1, 0⟩,
  ⟨25, 23, 29, 7, 1, 0⟩,
  ⟨25, 24, 29, 8, 1, 0⟩,
  ⟨25, 25, 29, 9, 1, 0⟩,
  ⟨25, 26, 29, 10, 1, 0⟩,
  ⟨25, 27, 29, 11, 1, 0⟩,
  ⟨26, 22, 30, 6, 1, 0⟩,
  ⟨26, 23, 30, 7, 1, 0⟩,
  ⟨26, 24, 30, 8, 1, 0⟩,
  ⟨26, 26, 30, 10, 1, 0⟩,
  ⟨27, 16, 31, 0, 1, 0⟩,
  ⟨27, 17, 31, 1, 1, 0⟩,
  ⟨27, 18, 31, 2, 1, 0⟩,
  ⟨27, 20, 31, 4, 1, 0⟩,
  ⟨28, 28, 26, 14, 1, 1⟩,
  ⟨29, 30, 27, 12, 1, 1⟩,
  ⟨30, 29, 24, 15, 1, 1⟩,
  ⟨31, 31, 25, 13, 1, 1⟩
]
/-- Look up a base tile by its zero-based table index; only indices below 156 occur in the exact groups. -/
@[expose] def tile (k : Nat) : Tile := exact156table[k]!

end Wang156
namespace K230Verification
/-- The two possible head movements on the integer tape. -/
inductive Dir where
  | left | right
  deriving DecidableEq, BEq
/-- A partial deterministic transition function: state and read bit give next state, written bit and movement. -/
abbrev Machine := Nat → Bool → Option (Nat × Bool × Dir)
/- Mathematical transition data independently decoded from the supplied Wang
   tile list. No Rocq file or k230.tm is included. The independent serialization
   audit recovers machine SHA256 e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8.
   Code = 4*nextState + 2*writeBit + rightDirectionBit; index=2*state+readBit. -/
/-- The literal 460 transition codes, indexed by twice the state plus the read bit. Code = 4*nextState + 2*writeBit + rightBit. -/
@[expose] def k230Codes : Array Nat := #[
  379, 3, 4, 10, 12, 10, 20, 10, 27, 16, 36, 10, 25, 41, 45, 51, 57, 55, 60, 10,
  64, 41, 104, 75, 77, 83, 364, 126, 44, 89, 92, 10, 6, 4, 97, 129, 105, 108, 113, 119,
  121, 127, 97, 241, 133, 91, 136, 10, 140, 1, 145, 103, 149, 155, 157, 160, 165, 171, 173, 179,
  181, 187, 85, 191, 193, 131, 129, 135, 200, 10, 143, 6, 205, 147, 69, 211, 53, 215, 44, 145,
  16, 218, 97, 101, 53, 64, 225, 231, 233, 239, 97, 221, 245, 251, 253, 64, 101, 195, 140, 257,
  300, 10, 65, 207, 269, 108, 273, 279, 160, 218, 89, 223, 44, 205, 245, 64, 281, 287, 249, 291,
  221, 243, 197, 101, 112, 294, 197, 221, 297, 259, 457, 51, 795, 218, 305, 919, 309, 923, 312, 127,
  165, 319, 85, 323, 225, 326, 329, 335, 3, 259, 301, 339, 341, 347, 349, 355, 357, 363, 329, 251,
  365, 168, 368, 231, 197, 133, 373, 168, 381, 387, 77, 263, 361, 399, 85, 411, 181, 415, 417, 327,
  421, 427, 329, 327, 417, 431, 433, 439, 265, 1, 109, 443, 445, 451, 454, 390, 77, 459, 245, 247,
  613, 467, 613, 683, 481, 487, 489, 208, 493, 499, 289, 239, 233, 503, 85, 507, 85, 160, 249, 171,
  509, 35, 417, 515, 369, 519, 160, 388, 521, 431, 277, 527, 689, 771, 745, 695, 621, 695, 609, 407,
  181, 40, 125, 255, 548, 4, 157, 295, 249, 555, 249, 559, 561, 64, 57, 555, 85, 567, 569, 575,
  577, 82, 581, 587, 589, 654, 305, 751, 729, 735, 765, 403, 49, 471, 121, 283, 157, 522, 641, 64,
  197, 193, 645, 64, 69, 651, 653, 659, 97, 193, 661, 315, 393, 363, 393, 667, 545, 619, 49, 667,
  361, 363, 361, 675, 621, 687, 345, 690, 633, 687, 341, 703, 685, 707, 361, 347, 709, 707, 665, 475,
  397, 399, 197, 129, 29, 108, 585, 115, 309, 395, 665, 79, 77, 719, 689, 723, 709, 727, 397, 595,
  677, 631, 733, 599, 737, 743, 613, 731, 605, 479, 304, 247, 753, 703, 665, 755, 757, 759, 777, 515,
  737, 615, 397, 707, 305, 247, 601, 395, 701, 363, 361, 739, 589, 347, 745, 735, 524, 762, 597, 626,
  49, 759, 665, 731, 689, 779, 781, 787, 69, 550, 785, 791, 309, 491, 437, 523, 794, 454, 721, 667,
  629, 671, 597, 603, 805, 607, 529, 811, 461, 815, 397, 539, 745, 799, 821, 827, 729, 799, 533, 835,
  697, 839, 829, 843, 665, 759, 761, 591, 361, 855, 589, 635, 629, 715, 865, 671, 861, 871, 857, 875,
  801, 803, 629, 883, 877, 887, 849, 891, 621, 639, 541, 775, 897, 903, 893, 907, 845, 911, 817, 915
]
/-- Decode one packed machine transition into its next state, write bit and movement. -/
@[expose] def decodeTransition (code : Nat) : Nat × Bool × Dir :=
  (code / 4, code / 2 % 2 == 1, if code % 2 = 1 then .right else .left)
/-- The specified K230 transition function; states 0 through 229 have two transitions and every state at least 230 halts. -/
@[expose] def k230Machine : Machine := fun q a =>
  if q < 230 then some (decodeTransition k230Codes[2*q + (if a then 1 else 0)]!) else none


/- Exact factorization of the supplied finite Wang set:226 base/channel groups
   and14 computation-layer templates. Independently parsed from the immutable
   TSV, not imported from the Python generator. -/
/-- Computation edge labels: blank, a tape symbol, a state-bearing head, a directed move signal, or one of four initialization markers. -/
inductive TMColor where
  | blank | symbol (a : Bool) | head (q : Nat) (a : Bool)
  | move (d : Dir) (q : Nat) | iL | iR | iH | iX
  deriving DecidableEq, BEq
/-- A tile record with edges in north, east, south, west order. No rotation operation is permitted. -/
structure Quad (α : Type) where
  n : α
  e : α
  s : α
  w : α
  deriving DecidableEq, BEq
/-- The computation tile whose four computation labels are blank. -/
@[expose] def tmBlank : Quad TMColor := ⟨.blank,.blank,.blank,.blank⟩
/-- All tape-symbol and state-bearing vertical labels, including the halting state 230. -/
@[expose] def tmVertical : List TMColor := [.symbol false,.symbol true] ++
  (List.range 231).flatMap (fun q => [.head q false,.head q true])
/-- Distinct directed next-state signals actually produced by the literal machine transitions. -/
@[expose] def tmMoves : List TMColor :=
  ((k230Codes.toList.map (fun code => 2*(code/4)+code%2)).eraseDups).map
    (fun code => .move (if code%2 = 1 then .right else .left) (code/2))
/-- Vertical transmission tiles for each tape/head label. -/
@[expose] def tmColumns : List (Quad TMColor) := tmVertical.map (fun v => ⟨v,.blank,v,.blank⟩)
/-- One head-update action tile for each of the 460 literal machine transitions. -/
@[expose] def tmActions : List (Quad TMColor) := (List.range 460).map fun i =>
  let z := decodeTransition k230Codes[i]!
  let head := TMColor.head (i/2) (i%2 == 1)
  if k230Codes[i]! % 2 = 1 then ⟨.symbol z.2.1,.move .right z.1,head,.blank⟩
  else ⟨.symbol z.2.1,.blank,head,.move .left z.1⟩
/-- Tiles that merge a directed next-state signal with the neighboring tape symbol. -/
@[expose] def tmMerges : List (Quad TMColor) := tmMoves.flatMap fun m =>
  match m with
  | .move .right q => [⟨.head q false,.blank,.symbol false,m⟩,⟨.head q true,.blank,.symbol true,m⟩]
  | .move .left q => [⟨.head q false,m,.symbol false,.blank⟩,⟨.head q true,m,.symbol true,.blank⟩]
  | _ => []
/-- The computation-step family: unchanged tape symbols, head actions and move-signal merges. -/
@[expose] def tmComp : List (Quad TMColor) :=
  [⟨.symbol false,.blank,.symbol false,.blank⟩,⟨.symbol true,.blank,.symbol true,.blank⟩] ++ tmActions ++ tmMerges
/-- The fourteen literal computation/initialization/transmission/absorption template families, indexed 0 through 13. -/
@[expose] def tmFamily : Nat → List (Quad TMColor)
  | 0 => [tmBlank]
  | 1 => [tmBlank,⟨.blank,.iL,.blank,.iL⟩]
  | 2 => [tmBlank,⟨.blank,.iR,.blank,.iR⟩]
  | 3 => [⟨.blank,.blank,.blank,.iR⟩]
  | 4 => [⟨.blank,.iL,.blank,.blank⟩]
  | 5 => [⟨.blank,.iH,.blank,.iL⟩,⟨.blank,.iX,.blank,.iL⟩]
  | 6 => (.blank :: tmMoves).map (fun m => ⟨.blank,m,.blank,m⟩)
  | 7 => (.blank :: tmMoves.filter (fun m => match m with | .move .right _ => true | _ => false)).map
      (fun m => ⟨.blank,.blank,.blank,m⟩)
  | 8 => tmColumns ++ [tmBlank,⟨.symbol false,.iL,.blank,.iL⟩]
  | 9 => tmVertical.map (fun v => ⟨.blank,.blank,v,.blank⟩)
  | 10 => tmColumns ++ [tmBlank,⟨.symbol false,.iR,.blank,.iR⟩,⟨.head 0 false,.iR,.blank,.iH⟩]
  | 11 => [tmBlank,⟨.blank,.iR,.blank,.iX⟩]
  | 12 => tmColumns ++ [tmBlank]
  | 13 => tmComp ++ [tmBlank]
  | _ => []
/- Tuple=(base index, packed NESW channel digits, template index).
   Channel codes:0 absent,1 zero,2 a,3 b. -/
/-- The literal 226 groups: base-table index, four packed channel digits, and computation-family index. -/
@[expose] def exactGroups : Array (Nat × Nat × Nat) := #[
  (0,0,0), (1,0,1), (2,0,0), (3,0,1), (4,0,0), (5,0,1),
  (6,0,0), (7,0,0), (8,0,0), (9,0,1), (10,0,2), (11,0,2),
  (12,0,0), (13,0,2), (14,0,0), (15,0,2), (16,0,0), (17,0,1),
  (18,0,0), (19,0,1), (20,0,0), (21,0,1), (22,0,0), (23,0,0),
  (24,0,0), (25,0,1), (26,0,2), (27,0,2), (28,0,0), (29,0,2),
  (30,0,0), (31,0,2), (32,0,0), (33,0,0), (34,0,0), (35,0,3),
  (36,0,3), (37,0,3), (38,0,3), (39,0,0), (40,0,0), (41,0,0),
  (42,0,2), (43,0,2), (44,0,0), (45,0,0), (46,0,0), (47,0,4),
  (48,0,0), (49,0,4), (50,0,4), (51,0,0), (52,0,4), (53,0,0),
  (54,0,1), (55,0,0), (56,0,1), (57,0,0), (58,0,0), (59,0,0),
  (60,0,0), (61,0,0), (62,0,0), (63,0,0), (64,0,0), (65,0,5),
  (66,0,0), (67,0,0), (68,0,0), (69,0,0), (70,0,0), (71,0,5),
  (72,0,0), (73,0,0), (74,0,0), (75,0,0), (76,0,0), (77,0,0),
  (78,0,0), (79,0,5), (80,0,0), (81,0,0), (82,0,0), (83,0,0),
  (84,0,0), (85,0,0), (86,0,0), (87,0,5), (88,0,0), (89,17,6),
  (89,34,0), (89,51,0), (90,17,6), (90,34,0), (90,51,0), (91,0,0),
  (92,17,6), (92,34,0), (92,51,0), (93,17,6), (93,34,0), (93,51,0),
  (94,0,0), (95,51,0), (95,49,7), (96,50,0), (97,0,0), (98,17,6),
  (98,34,0), (98,51,0), (99,0,0), (100,18,0), (100,19,0), (100,34,0),
  (100,35,0), (101,34,0), (101,35,0), (102,0,0), (103,17,6), (103,34,0),
  (103,51,0), (104,0,0), (105,17,6), (105,34,0), (105,51,0), (106,0,0),
  (107,0,0), (108,17,6), (108,34,0), (108,51,0), (109,0,0), (110,0,0),
  (111,51,0), (111,49,0), (112,0,0), (113,0,0), (114,17,6), (114,34,0),
  (114,51,0), (115,0,0), (116,18,0), (116,19,0), (116,34,0), (116,35,0),
  (117,0,0), (118,0,0), (119,17,6), (119,34,0), (119,51,0), (120,0,1),
  (121,0,1), (122,0,0), (123,0,1), (124,0,0), (125,0,1), (126,0,2),
  (127,0,2), (128,0,0), (129,0,2), (130,0,0), (131,0,2), (132,68,8),
  (132,136,0), (132,204,1), (133,68,8), (133,136,0), (133,204,1), (134,204,0),
  (134,196,9), (135,68,8), (135,136,0), (135,204,1), (136,72,0), (136,76,0),
  (136,136,0), (136,140,0), (137,68,8), (137,136,0), (137,204,1), (138,68,10),
  (138,136,11), (138,204,2), (139,68,10), (139,136,11), (139,204,2), (140,204,0),
  (140,196,9), (141,68,10), (141,136,11), (141,204,2), (142,72,0), (142,76,0),
  (142,136,0), (142,140,0), (143,68,10), (143,136,11), (143,204,2), (144,0,0),
  (145,0,0), (146,0,0), (147,0,0), (148,68,12), (148,136,0), (148,204,0),
  (149,68,12), (149,136,0), (149,204,0), (150,200,0), (151,136,0), (151,140,0),
  (152,0,0), (153,68,12), (153,136,0), (153,204,0), (154,17,6), (154,34,0),
  (154,51,0), (155,85,13), (155,153,0), (155,221,6), (155,102,12), (155,170,0),
  (155,238,0), (155,119,12), (155,187,0), (155,255,0)
]
/-- A full edge color consists of base color, obstruction-channel digit, and computation label. -/
abbrev FullColor := Nat × Nat × TMColor
/-- Combine one base/channel group and one computation template into a full Wang tile. Channel digits are packed in base 4, north first. -/
@[expose] def decorate (g : Nat × Nat × Nat) (t : Quad TMColor) : Quad FullColor :=
  let b := Wang156.tile g.1
  let c := g.2.1
  ⟨(b.n,c/64%4,t.n),(b.e,c/16%4,t.e),(b.s,c/4%4,t.s),(b.w,c%4,t.w)⟩
/-- The exact tile list obtained by decorating every template of each literal group. The theorem asserts its length and nonduplication. -/
@[expose] def exactFullPlaneTiles : List (Quad FullColor) := exactGroups.toList.flatMap fun g =>
  (tmFamily g.2.2).map (decorate g)

/-- An ordinary two-way-tape machine configuration: natural-number state, integer head position and Boolean tape. -/
structure Configuration where
  state : Nat
  position : Int
  tape : Int → Bool

/-- Write the selected bit at the current head and move exactly one cell left or right, entering the next state. -/
@[expose] def Configuration.after (c : Configuration) (q : Nat) (b : Bool) (d : Dir) : Configuration where
  state := q
  position := if d = .right then c.position+1 else c.position-1
  tape := fun i => if i = c.position then b else c.tape i

/-- Perform one deterministic transition, or return none if the current state/read pair has no transition. -/
@[expose] def machineStep (M : Machine) (c : Configuration) : Option Configuration :=
  (M c.state (c.tape c.position)).map fun (q,b,d) => c.after q b d

/-- Iterate the partial transition exactly n times from the supplied configuration; once undefined, the run remains undefined. -/
@[expose] def machineRun (M : Machine) (c : Configuration) : Nat → Option Configuration
  | 0 => some c
  | n+1 => (machineRun M c n).bind (machineStep M)

/-- Standard nonhalting: every finite iterate from the initial configuration
    remains defined. Missing transitions are halting. -/
@[expose] def NeverHalts (M : Machine) (c : Configuration) : Prop :=
  ∀ n, ∃ d, machineRun M c n = some d

/-- A Wang tile with four oriented edge colors. -/
structure WangTile (C : Type*) where
  north : C
  east : C
  south : C
  west : C

/-- An integer-grid cell, with horizontal and vertical coordinates. -/
abbrev Cell := Int × Int
/-- An integer-grid cell together with a direction bit selecting its east or north edge. -/
abbrev EdgeSite := Cell × Bool

/-- The neighboring cell one unit east for true and one unit north for false. -/
@[expose] def edgeNeighbor (s : EdgeSite) : Cell :=
  if s.2 then (s.1.1+1,s.1.2) else (s.1.1,s.1.2+1)

/-- The standard touching-edge equality for one east/west or north/south adjacent tile pair. -/
@[expose] def edgeCompatible {C : Type*} {N : Nat} (tiles : Fin N → WangTile C)
    (s : EdgeSite) (a b : Fin N) : Prop :=
  if s.2 then (tiles a).east = (tiles b).west
  else (tiles a).north = (tiles b).south

/-- The maximum absolute coordinate of an edge base point; used only by the optional finite-window definition. -/
@[expose] def edgeRadius (s : EdgeSite) : Nat := max s.1.1.natAbs s.1.2.natAbs

/-- Unseeded, boundary-free Wang tiling of every integer cell. -/
@[expose] def TilesPlane {C : Type*} {N : Nat} (tiles : Fin N → WangTile C) : Prop :=
  ∃ f : Cell → Fin N, ∀ s : EdgeSite,
    edgeCompatible tiles s (f s.1) (f (edgeNeighbor s))

/-- Arbitrarily large finite windows tile. Assignments outside the window
    are arbitrary and unconstrained; the quantified constraints are finite. -/
@[expose] def TilesEveryWindow {C : Type*} {N : Nat} (tiles : Fin N → WangTile C) : Prop :=
  ∀ n : Nat, ∃ f : Cell → Fin N, ∀ s : EdgeSite, edgeRadius s ≤ n →
    edgeCompatible tiles s (f s.1) (f (edgeNeighbor s))


theorem exact_fullplane_count : exactFullPlaneTiles.length = 11487 := by decide
/-- The literal finite tile alphabet, with the exact verified enumeration size. -/
@[expose] def indexedFullTile (i : Fin 11487) : Quad FullColor :=
  exactFullPlaneTiles[i.val]'(by rw [exact_fullplane_count]; exact i.isLt)
/-- The same literal indexed tile written in the oriented WangTile record. -/
@[expose] def indexedWangTile (i : Fin 11487) : WangTile FullColor :=
  let t := indexedFullTile i
  ⟨t.n,t.e,t.s,t.w⟩
/-- No seed, origin, boundary, or initialization constraint is imposed on the plane. -/
@[expose] def ExactPlane : Prop := TilesPlane indexedWangTile
@[expose] def ExactWindows : Prop := TilesEveryWindow indexedWangTile
/-- Initial state0, head at0, and the completely blank two-way tape. -/
@[expose] def k230Initial : Configuration := ⟨0,0,fun _ => false⟩
/-- Ordinary nonhalting of the literal K230 machine from the completely blank initial configuration. -/
@[expose] def K230NeverHalts : Prop := NeverHalts k230Machine k230Initial

/-- The literal list has 11,487 distinct Wang tiles and tiles the entire integer
plane if and only if the specified blank-tape K230 run never halts. -/
theorem exact_11487_equivalence :
    exactFullPlaneTiles.length=11487 ∧ exactFullPlaneTiles.Nodup ∧
      (ExactPlane ↔ K230NeverHalts) := by
  sorry
end K230Verification
