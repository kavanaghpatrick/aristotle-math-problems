import Mathlib

def tau (m : Nat) : Nat := (Nat.divisors m).card
def f (m : Nat) : Nat := m + tau m

def runMax : Nat → Nat
  | 0 => 0
  | n + 1 => max (runMax n) (f n)

-- Extend to 10000
#eval (List.range 10000).filterMap (fun n =>
  if n > 24 && runMax n ≤ n + 2 then some n else none)