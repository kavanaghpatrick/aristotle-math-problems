
def canExtendToPDS' (fixed : List Nat) (n k : Nat) : Bool :=
  let initDiffs : List Nat := fixed.flatMap fun a => fixed.filterMap fun b =>
    if a != b then some ((a + n - b) % n) else none
  if initDiffs.length != initDiffs.toArray.toList.eraseDups.length then false
  else
    let initDiffSet := initDiffs.toArray.toList.eraseDups
    let available := (List.range n).filter fun x => !fixed.contains x
    let rec go (avail : List Nat) (remaining : Nat) (current : List Nat) (usedDiffs : List Nat) : Bool :=
      if remaining == 0 then
        usedDiffs.length == n - 1
      else match avail with
        | [] => false
        | x :: rest =>
          let newDiffs := current.flatMap fun a =>
            [(x + n - a) % n, (a + n - x) % n]
          let conflict := newDiffs.any fun d => usedDiffs.contains d || d == 0
          let selfConflict := newDiffs.length != newDiffs.toArray.toList.eraseDups.length
          let tryWith := if conflict || selfConflict then false
            else go rest (remaining - 1) (current ++ [x]) (usedDiffs ++ newDiffs)
          let tryWithout := go rest remaining current usedDiffs
          tryWith || tryWithout
    go available (k - fixed.length) fixed initDiffSet

-- Keep pushing
#eval canExtendToPDS' [0,1,3,7,12,20] 241 16
#eval canExtendToPDS' [0,1,3,7,12,20] 273 17
