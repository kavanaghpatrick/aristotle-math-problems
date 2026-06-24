import Mathlib

def primesArr : Array ℕ := #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

def vpFactorial (p n : ℕ) : ℕ :=
  if p < 2 then 0
  else Id.run do
    let mut result := 0
    let mut pk := p
    while pk ≤ n do
      result := result + n / pk
      if pk > n / p then break
      pk := pk * p
    return result

def factVecArr (n : ℕ) : Array ℕ := primesArr.map (vpFactorial · n)

def arrGe (v1 v2 : Array ℕ) : Bool := Id.run do
  for i in [:v1.size] do
    if v1[i]! < v2[i]! then return false
  return true

def arrSub (v1 v2 : Array ℕ) : Array ℕ := Id.run do
  let mut r := Array.mkEmpty v1.size
  for i in [:v1.size] do
    r := r.push (v1[i]! - v2[i]!)
  return r

def arrZero (v : Array ℕ) : Bool := Id.run do
  for i in [:v.size] do
    if v[i]! > 0 then return false
  return true

def arrSum (v : Array ℕ) : ℕ := v.foldl (· + ·) 0

-- Simple version WITHOUT minRequiredA pruning
def canDecompSimple (allVecs : Array (Array ℕ)) : ℕ → Array ℕ → ℕ → Bool
  | 0, _, _ => false
  | gas + 1, residual, cur =>
    if arrZero residual then true
    else if cur < 2 then false
    else
      let fv := allVecs[cur]!
      if arrGe residual fv then
        -- Try using this factorial or skipping it
        canDecompSimple allVecs gas (arrSub residual fv) cur || canDecompSimple allVecs gas residual (cur - 1)
      else
        canDecompSimple allVecs gas residual (cur - 1)

def checkNoDecompSimple (n : ℕ) : Bool :=
  let allVecs := (Array.range (n + 1)).map factVecArr
  let nVec := allVecs[n]!
  let gas := (arrSum nVec + 1) * (n - 1)  -- generous gas
  not (canDecompSimple allVecs gas nVec (n - 2))

def checkRangeSimple : Bool :=
  (List.range 84).all fun i => checkNoDecompSimple (i + 17)

-- Test with native_decide
set_option maxRecDepth 100000 in
theorem range_simple_check : checkRangeSimple = true := by native_decide
