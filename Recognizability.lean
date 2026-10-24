module
public import ArcCertificates
public import Adjacency
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Wang156

@[expose] def eastOptions (k : Nat) : List Nat := (List.range 156).filter fun u => (tile k).e == (tile u).w
@[expose] def northOptions (k : Nat) : List Nat := (List.range 156).filter fun u => (tile k).n == (tile u).s

@[expose] def alignedSquares : List Square :=
  ((List.range 156).filter fun k => (tile k).px == 0 && (tile k).py == 0).flatMap fun bl =>
  (eastOptions bl).flatMap fun br =>
  (northOptions bl).flatMap fun tl =>
  ((eastOptions tl).filter fun tr => (tile br).n == (tile tr).s).map fun tr => ⟨bl,br,tl,tr⟩

@[expose] def squaresClassified : Bool := alignedSquares.all fun b =>
  (List.range 156).any (fun k => squareEq b (imageSquare k)) || arcCertificates.any (fun c => squareEq b c.block)

theorem squares_classified : squaresClassified = true := by decide +kernel
#print axioms squares_classified

theorem square_mem_aligned (p : Patch) (hv : Valid 6 p)
    (hx : (tile (p 2 2).val).px = 0) (hy : (tile (p 2 2).val).py = 0) :
    squareOf p ∈ alignedSquares := by
  apply List.mem_flatMap.mpr
  refine ⟨(p 2 2).val, ?_, ?_⟩
  · simp [List.mem_filter, (p 2 2).isLt, hx, hy]
  apply List.mem_flatMap.mpr
  refine ⟨(p 3 2).val, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr (p 3 2).isLt, by simpa using hv.1 2 2 (by decide) (by decide)⟩
  apply List.mem_flatMap.mpr
  refine ⟨(p 2 3).val, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr (p 2 3).isLt, by simpa using hv.2 2 2 (by decide) (by decide)⟩
  apply List.mem_map.mpr
  refine ⟨(p 3 3).val, ?_, rfl⟩
  apply List.mem_filter.mpr
  constructor
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr (p 3 3).isLt, by simpa using hv.1 2 3 (by decide) (by decide)⟩
  · simpa using hv.2 3 2 (by decide) (by decide)

theorem block_of_square (p : Patch) (k : Nat) (h : squareOf p = imageSquare k) : Block 0 p 0 k := by
  intro q hq
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa [squareOf,imageSquare,blockX,blockY,macroX,macroY] using congrArg Square.bl h
  · simpa [squareOf,imageSquare,blockX,blockY,macroX,macroY] using congrArg Square.br h
  · simpa [squareOf,imageSquare,blockX,blockY,macroX,macroY] using congrArg Square.tl h
  · simpa [squareOf,imageSquare,blockX,blockY,macroX,macroY] using congrArg Square.tr h

theorem D1_six (p : Patch) (hv : Valid 6 p)
    (hx : (tile (p 2 2).val).px = 0) (hy : (tile (p 2 2).val).py = 0) :
    ∃ k : Fin 156, Block 0 p 0 k.val := by
  have hm := square_mem_aligned p hv hx hy
  have hc := List.all_eq_true.mp squares_classified (squareOf p) hm
  simp only [Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · obtain ⟨k,hk,hb⟩ := List.any_eq_true.mp hc
    exact ⟨⟨k,List.mem_range.mp hk⟩, block_of_square p k ((squareEq_iff _ _).mp hb)⟩
  · obtain ⟨c,hc,he⟩ := List.any_eq_true.mp hc
    exact False.elim (arc_no_square c (all_arcs_checked c hc) p hv ((squareEq_iff _ _).mp he))

theorem D2_horizontal_eight (p : Patch) (u v : Fin 156) (hv : Valid 8 p)
    (hu : Block 1 p 0 u.val) (hv' : Block 1 p 1 v.val) :
    (tile u.val).e = (tile v.val).w := by
  apply reflect_horizontal u v
  · have h := hv.1 3 2 (by decide) (by decide)
    have hu1 := hu 1 (by decide)
    have hv0 := hv' 0 (by decide)
    simp [blockX,blockY,macroX,macroY] at hu1 hv0
    simpa [hu1,hv0] using h
  · have h := hv.1 3 3 (by decide) (by decide)
    have hu3 := hu 3 (by decide)
    have hv2 := hv' 2 (by decide)
    simp [blockX,blockY,macroX,macroY] at hu3 hv2
    simpa [hu3,hv2] using h

theorem D2_vertical_eight (p : Patch) (u v : Fin 156) (hv : Valid 8 p)
    (hu : Block 2 p 0 u.val) (hv' : Block 2 p 1 v.val) :
    (tile u.val).n = (tile v.val).s := by
  apply reflect_vertical u v
  · have h := hv.2 2 3 (by decide) (by decide)
    have hu2 := hu 2 (by decide)
    have hv0 := hv' 0 (by decide)
    simp [blockX,blockY,macroX,macroY] at hu2 hv0
    simpa [hu2,hv0] using h
  · have h := hv.2 3 3 (by decide) (by decide)
    have hu3 := hu 3 (by decide)
    have hv1 := hv' 1 (by decide)
    simp [blockX,blockY,macroX,macroY] at hu3 hv1
    simpa [hu3,hv1] using h

#print axioms D1_six
#print axioms D2_horizontal_eight
#print axioms D2_vertical_eight
end Wang156
