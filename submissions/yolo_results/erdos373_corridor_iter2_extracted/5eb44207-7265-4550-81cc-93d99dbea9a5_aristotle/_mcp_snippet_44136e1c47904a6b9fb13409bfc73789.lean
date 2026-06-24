import Mathlib

-- Same function as before
def checkAllOpt (aMax : ℕ) : Bool := Id.run do
  let mut ok := true
  for a' in List.range (aMax - 2) do
    let a := a' + 3
    let mut facts : Array ℕ := #[1, 1]
    for i in List.range a do
      facts := facts.push (facts.back! * (i + 2))
    let aFact := facts[a]!
    let mut prod := (a + 1) * (a + 2)
    for k' in List.range (a - 2) do
      let k := k' + 2
      if k > 2 then
        prod := prod * (a + k)
      if prod > aFact then break
      let n := a + k
      if n ≤ 2 * a - 1 then
        for b in List.range (a - 1) do
          let b := b + 2
          if b < facts.size then
            let bFact := facts[b]!
            if prod == bFact then
              if !(n == 10 && a == 7 && b == 6) then
                ok := false
            if bFact > prod then break
  return ok

-- Try even larger
#eval checkAllOpt 5000
