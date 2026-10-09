
/- Construct exact byte lists without polymorphic numeral elaboration.
   This builds data expressions only; it does not prove or evaluate any claim. -/
open Lean Elab Term Meta in
elab "golf_bytes%[" bytes:num,* "]" : term =>
  mkListLit (mkConst ``Nat) (bytes.getElems.toList.map fun byte => mkRawNatLit byte.getNat)
