module
public import MachineData
public import ExactTable
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

/- Exact factorization of the supplied finite Wang set:226 base/channel groups
   and14 computation-layer templates. Independently parsed from the immutable
   TSV, not imported from the Python generator. -/
inductive TMColor where
  | blank | symbol (a : Bool) | head (q : Nat) (a : Bool)
  | move (d : Dir) (q : Nat) | iL | iR | iH | iX
  deriving DecidableEq, BEq
structure Quad (α : Type) where
  n : α
  e : α
  s : α
  w : α
  deriving DecidableEq, BEq
@[expose] def tmBlank : Quad TMColor := ⟨.blank,.blank,.blank,.blank⟩
@[expose] def tmVertical : List TMColor := [.symbol false,.symbol true] ++
  (List.range 231).flatMap (fun q => [.head q false,.head q true])
@[expose] def tmMoves : List TMColor :=
  ((k230Codes.toList.map (fun code => 2*(code/4)+code%2)).eraseDups).map
    (fun code => .move (if code%2 = 1 then .right else .left) (code/2))
@[expose] def tmColumns : List (Quad TMColor) := tmVertical.map (fun v => ⟨v,.blank,v,.blank⟩)
@[expose] def tmActions : List (Quad TMColor) := (List.range 460).map fun i =>
  let z := decodeTransition k230Codes[i]!
  let head := TMColor.head (i/2) (i%2 == 1)
  if k230Codes[i]! % 2 = 1 then ⟨.symbol z.2.1,.move .right z.1,head,.blank⟩
  else ⟨.symbol z.2.1,.blank,head,.move .left z.1⟩
@[expose] def tmMerges : List (Quad TMColor) := tmMoves.flatMap fun m =>
  match m with
  | .move .right q => [⟨.head q false,.blank,.symbol false,m⟩,⟨.head q true,.blank,.symbol true,m⟩]
  | .move .left q => [⟨.head q false,m,.symbol false,.blank⟩,⟨.head q true,m,.symbol true,.blank⟩]
  | _ => []
@[expose] def tmComp : List (Quad TMColor) :=
  [⟨.symbol false,.blank,.symbol false,.blank⟩,⟨.symbol true,.blank,.symbol true,.blank⟩] ++ tmActions ++ tmMerges
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
abbrev FullColor := Nat × Nat × TMColor
@[expose] def decorate (g : Nat × Nat × Nat) (t : Quad TMColor) : Quad FullColor :=
  let b := Wang156.tile g.1
  let c := g.2.1
  ⟨(b.n,c/64%4,t.n),(b.e,c/16%4,t.e),(b.s,c/4%4,t.s),(b.w,c%4,t.w)⟩
@[expose] def exactFullPlaneTiles : List (Quad FullColor) := exactGroups.toList.flatMap fun g =>
  (tmFamily g.2.2).map (decorate g)

theorem exact_group_count : exactGroups.size = 226 := by decide
end K230Verification
