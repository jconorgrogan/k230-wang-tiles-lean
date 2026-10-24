module
public import FillGeometry
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

@[expose] def FilledChild.placed {n v : Nat} {left bottom : Int → Bool}
    {P : ExposedBoard n v left bottom} {b : RedSquare} (D : FilledChild P b) (p : Cell) : Quad FullColor :=
  D.patch.tileAt (lowerOriginX n b) (lowerOriginY n b) p

theorem FilledChild.placed_base {n v : Nat} {left bottom : Int → Bool}
    {P : ExposedBoard n v left bottom} {b : RedSquare} (D : FilledChild P b) {p : Cell}
    (hp : WithinChild n b p) : fullBase (D.placed p)=baseTileQuad (redBoard n v p.1.toNat p.2.toNat) := by
  let x := (p.1-lowerOriginX n b).toNat
  let y := (p.2-lowerOriginY n b).toNat
  have hx : (x:Int)=p.1-lowerOriginX n b := by dsimp [x]; unfold WithinChild at hp; omega
  have hy : (y:Int)=p.2-lowerOriginY n b := by dsimp [y]; unfold WithinChild at hp; omega
  have hxb : x≤2*boardHalf b.level := by unfold WithinChild at hp; omega
  have hyb : y≤2*boardHalf b.level := by unfold WithinChild at hp; omega
  have hxp : lowerOriginX n b+x=p.1.toNat := by omega
  have hyp : lowerOriginY n b+y=p.2.toNat := by omega
  have he := D.base x y hxb hyb
  rw [hxp,hyp] at he
  simpa only [FilledChild.placed,RawSquare.tileAt,hx,hy] using he

theorem FilledChild.placed_west {n v : Nat} {left bottom : Int → Bool}
    {P : ExposedBoard n v left bottom} {b : RedSquare} (D : FilledChild P b) {p : Cell}
    (hp : WithinChild n b p) (hside : p.1=lowerOriginX n b) :
    (D.placed p).w=(P.tile p).w := by
  let j := (p.2-lowerOriginY n b).toNat
  have hj : (j:Int)=p.2-lowerOriginY n b := by dsimp [j]; unfold WithinChild at hp; omega
  have hjb : j≤2*boardHalf b.level := by unfold WithinChild at hp; omega
  have he := D.west j hjb
  have hpos : ((lowerOriginX n b:Int),(lowerOriginY n b:Int)+j)=p := by apply Prod.ext <;> simp only <;> omega
  change (D.patch.tile (0,(j:Int))).w=(P.tile ((lowerOriginX n b:Int),(lowerOriginY n b:Int)+j)).w at he
  rw [hpos] at he
  simpa only [FilledChild.placed,RawSquare.tileAt,hside,Int.sub_self,hj] using he

theorem FilledChild.placed_east {n v : Nat} {left bottom : Int → Bool}
    {P : ExposedBoard n v left bottom} {b : RedSquare} (D : FilledChild P b) {p : Cell}
    (hp : WithinChild n b p) (hside : p.1=lowerOriginX n b+2*boardHalf b.level) :
    (D.placed p).e=(P.tile p).e := by
  let j := (p.2-lowerOriginY n b).toNat
  have hj : (j:Int)=p.2-lowerOriginY n b := by dsimp [j]; unfold WithinChild at hp; omega
  have hjb : j≤2*boardHalf b.level := by unfold WithinChild at hp; omega
  have he := D.east j hjb
  have hpos : ((lowerOriginX n b:Int)+2*boardHalf b.level,(lowerOriginY n b:Int)+j)=p := by apply Prod.ext <;> simp only <;> omega
  have hx : p.1-lowerOriginX n b=(2*boardHalf b.level:Nat) := by omega
  change (D.patch.tile ((2*boardHalf b.level:Nat),(j:Int))).e=
    (P.tile ((lowerOriginX n b:Int)+2*boardHalf b.level,(lowerOriginY n b:Int)+j)).e at he
  rw [hpos] at he
  simpa only [FilledChild.placed,RawSquare.tileAt,hx,hj] using he

theorem FilledChild.placed_south {n v : Nat} {left bottom : Int → Bool}
    {P : ExposedBoard n v left bottom} {b : RedSquare} (D : FilledChild P b) {p : Cell}
    (hp : WithinChild n b p) (hside : p.2=lowerOriginY n b) :
    (D.placed p).s=(P.tile p).s := by
  let j := (p.1-lowerOriginX n b).toNat
  have hj : (j:Int)=p.1-lowerOriginX n b := by dsimp [j]; unfold WithinChild at hp; omega
  have hjb : j≤2*boardHalf b.level := by unfold WithinChild at hp; omega
  have he := D.south j hjb
  have hpos : ((lowerOriginX n b:Int)+j,(lowerOriginY n b:Int))=p := by apply Prod.ext <;> simp only <;> omega
  change (D.patch.tile ((j:Int),0)).s=(P.tile ((lowerOriginX n b:Int)+j,(lowerOriginY n b:Int))).s at he
  rw [hpos] at he
  simpa only [FilledChild.placed,RawSquare.tileAt,hside,Int.sub_self,hj] using he

theorem FilledChild.placed_north {n v : Nat} {left bottom : Int → Bool}
    {P : ExposedBoard n v left bottom} {b : RedSquare} (D : FilledChild P b) {p : Cell}
    (hp : WithinChild n b p) (hside : p.2=lowerOriginY n b+2*boardHalf b.level) :
    (D.placed p).n=(P.tile p).n := by
  let j := (p.1-lowerOriginX n b).toNat
  have hj : (j:Int)=p.1-lowerOriginX n b := by dsimp [j]; unfold WithinChild at hp; omega
  have hjb : j≤2*boardHalf b.level := by unfold WithinChild at hp; omega
  have he := D.north j hjb
  have hpos : ((lowerOriginX n b:Int)+j,(lowerOriginY n b:Int)+2*boardHalf b.level)=p := by apply Prod.ext <;> simp only <;> omega
  have hy : p.2-lowerOriginY n b=(2*boardHalf b.level:Nat) := by omega
  change (D.patch.tile ((j:Int),(2*boardHalf b.level:Nat))).n=
    (P.tile ((lowerOriginX n b:Int)+j,(lowerOriginY n b:Int)+2*boardHalf b.level)).n at he
  rw [hpos] at he
  simpa only [FilledChild.placed,RawSquare.tileAt,hj,hy] using he

end K230Verification
