/-
DT Code and PD Code structures for knot enumeration
Part of Jones Unknotting Conjecture project
-/

import Mathlib

-- Dowker-Thistlethwaite code
structure DTCode where
  codes : List ℤ
  deriving Repr, DecidableEq

-- We already have LinkDiagram from our Jones polynomial work
-- This will be imported from the existing framework

-- Knot entry from database
structure KnotEntry where
  name : String
  crossings : ℕ
  dt_code : DTCode
  pd_notation_str : String  -- Store as string initially
  jones_known : Option String  -- Known Jones polynomial from database
  alternating : Bool
  deriving Repr

-- For now, we'll manually construct some entries
-- TODO: Generate automatically from JSON

-- Example: trefoil knot (3_1)
def trefoil_entry : KnotEntry := {
  name := "3_1"
  crossings := 3
  dt_code := { codes := [4, 6, 2] }
  pd_notation_str := "[[1,5,2,4],[3,1,4,6],[5,3,6,2]]"
  jones_known := some "t + t^3 - t^4"
  alternating := true
}

-- Example: figure-eight knot (4_1)
def figure_eight_entry : KnotEntry := {
  name := "4_1"
  crossings := 4
  dt_code := { codes := [4, 6, 8, 2] }
  pd_notation_str := "[[4,2,5,1],[8,6,1,5],[6,3,7,4],[2,7,3,8]]"
  jones_known := some "t^(-2) - t^(-1) + 1 - t + t^2"
  alternating := true
}

-- Database of knots (to be expanded)
def knot_database_sample : List KnotEntry := [
  trefoil_entry,
  figure_eight_entry
  -- TODO: Add remaining 2,975 knots from JSON
]

-- Helper: Check if knot is alternating (can skip Jones verification for these)
def is_alternating (K : KnotEntry) : Bool :=
  K.alternating

-- Filter: Knots that need Jones computation
def needs_jones_verification (K : KnotEntry) : Bool :=
  ¬K.alternating  -- For now, focus on non-alternating
  -- TODO: Add filters for torus knots, pretzel knots

#check trefoil_entry
#check knot_database_sample
