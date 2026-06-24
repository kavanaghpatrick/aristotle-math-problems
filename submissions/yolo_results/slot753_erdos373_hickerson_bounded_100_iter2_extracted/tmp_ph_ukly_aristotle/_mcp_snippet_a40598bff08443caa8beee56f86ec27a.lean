import Mathlib

def mkFactArr (n : ℕ) : Array ℕ := Id.run do
  let mut arr : Array ℕ := #[1]
  for i in List.range n do
    arr := arr.push (arr.back! * (i + 1))
  return arr

def canFormProdArr (fArr : Array ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | _, 1, _ => true
  | _, 0, _ => false
  | gas + 1, target, cur =>
    if cur < 2 then false
    else
      let f := fArr[cur]!
      if f > target then canFormProdArr fArr gas target (cur - 1)
      else if target % f == 0 then
        canFormProdArr fArr gas (target / f) cur || canFormProdArr fArr gas target (cur - 1)
      else
        canFormProdArr fArr gas target (cur - 1)

def checkNoDecompDirect (n : ℕ) : Bool :=
  if n < 3 then true
  else
    let fArr := mkFactArr n
    let target := fArr[n]!
    let gas := n * n
    not (canFormProdArr fArr gas target (n - 2))

def checkAllDirect : Bool :=
  (List.range 84).all fun i => checkNoDecompDirect (i + 17)

-- Try native_decide
theorem test_all_direct : checkAllDirect = true := by native_decide
