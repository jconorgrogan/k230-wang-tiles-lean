module
public import ExactTable
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Wang156

@[expose] def reflectHCheck : Bool := (List.range 156).all fun k => (List.range 156).all fun u =>
  !((tile (sigma k 1)).e == (tile (sigma u 0)).w && (tile (sigma k 3)).e == (tile (sigma u 2)).w) ||
  (tile k).e == (tile u).w

@[expose] def reflectVCheck : Bool := (List.range 156).all fun k => (List.range 156).all fun u =>
  !((tile (sigma k 2)).n == (tile (sigma u 0)).s && (tile (sigma k 3)).n == (tile (sigma u 1)).s) ||
  (tile k).n == (tile u).s

theorem reflectedHChecked : reflectHCheck = true := by decide +kernel
theorem reflectedVChecked : reflectVCheck = true := by decide +kernel

theorem reflect_horizontal (k u : Fin 156)
    (h1 : (tile (sigma k.val 1)).e = (tile (sigma u.val 0)).w)
    (h2 : (tile (sigma k.val 3)).e = (tile (sigma u.val 2)).w) :
    (tile k.val).e = (tile u.val).w := by
  have hk := List.all_eq_true.mp reflectedHChecked k.val (List.mem_range.mpr k.isLt)
  have hu := List.all_eq_true.mp hk u.val (List.mem_range.mpr u.isLt)
  simpa [h1,h2] using hu

theorem reflect_vertical (k u : Fin 156)
    (h1 : (tile (sigma k.val 2)).n = (tile (sigma u.val 0)).s)
    (h2 : (tile (sigma k.val 3)).n = (tile (sigma u.val 1)).s) :
    (tile k.val).n = (tile u.val).s := by
  have hk := List.all_eq_true.mp reflectedVChecked k.val (List.mem_range.mpr k.isLt)
  have hu := List.all_eq_true.mp hk u.val (List.mem_range.mpr u.isLt)
  simpa [h1,h2] using hu
#print axioms reflect_horizontal
#print axioms reflect_vertical
end Wang156
