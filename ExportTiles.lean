module
public meta import FullPlaneData
public meta import Distinctness
public section
open K230Verification
meta def main : IO Unit := do
  for t in exactFullPlaneTiles do
    let codes := [t.n,t.e,t.s,t.w] |>.flatMap (fun c => [c.1,c.2.1,colorCode c.2.2])
    IO.println (String.intercalate "\t" (codes.map toString))
