/-
Knot Database - Up to 10 Crossings
Generated from KnotInfo database
Part of Jones Unknotting Conjecture project

Total knots: 249
-/

import Mathlib
import «Unknotting».DTCode

-- Individual knot entries
def knot_3_1 : KnotEntry := {
  name := "3_1"
  crossings := 3
  dt_code := { codes := [4, 6, 2] }
  pd_notation_str := "[[1,5,2,4],[3,1,4,6],[5,3,6,2]]"
  jones_known := some "t+ t^3-t^4"
  alternating := true
}

def knot_4_1 : KnotEntry := {
  name := "4_1"
  crossings := 4
  dt_code := { codes := [4, 6, 8, 2] }
  pd_notation_str := "[[4,2,5,1],[8,6,1,5],[6,3,7,4],[2,7,3,8]]"
  jones_known := some "t^(-2)-t^(-1)+ 1-t+ t^2"
  alternating := true
}

def knot_5_1 : KnotEntry := {
  name := "5_1"
  crossings := 5
  dt_code := { codes := [6, 8, 10, 2, 4] }
  pd_notation_str := "[[2,8,3,7],[4,10,5,9],[6,2,7,1],[8,4,9,3],[10,6,1,5]]"
  jones_known := some "t^2+ t^4-t^5+ t^6-t^7"
  alternating := true
}

def knot_5_2 : KnotEntry := {
  name := "5_2"
  crossings := 5
  dt_code := { codes := [4, 8, 10, 2, 6] }
  pd_notation_str := "[[1,5,2,4],[3,9,4,8],[5,1,6,10],[7,3,8,2],[9,7,10,6]]"
  jones_known := some "t-t^2+ 2*t^3-t^4+ t^5-t^6"
  alternating := true
}

def knot_6_1 : KnotEntry := {
  name := "6_1"
  crossings := 6
  dt_code := { codes := [4, 8, 12, 10, 2, 6] }
  pd_notation_str := "[[1,7,2,6],[3,10,4,11],[5,3,6,2],[7,1,8,12],[9,4,10,5],[11,9,12,8]]"
  jones_known := some "t^(-2)-t^(-1)+ 2-2*t+ t^2-t^3+ t^4"
  alternating := true
}

def knot_6_2 : KnotEntry := {
  name := "6_2"
  crossings := 6
  dt_code := { codes := [4, 8, 10, 12, 2, 6] }
  pd_notation_str := "[[1,8,2,9],[3,11,4,10],[5,1,6,12],[7,2,8,3],[9,7,10,6],[11,5,12,4]]"
  jones_known := some "t^(-1)-1+ 2*t-2*t^2+ 2*t^3-2*t^4+ t^5"
  alternating := true
}

def knot_6_3 : KnotEntry := {
  name := "6_3"
  crossings := 6
  dt_code := { codes := [4, 8, 10, 2, 12, 6] }
  pd_notation_str := "[[4,2,5,1],[8,4,9,3],[12,9,1,10],[10,5,11,6],[6,11,7,12],[2,8,3,7]]"
  jones_known := some "-t^(-3)+ 2*t^(-2)-2*t^(-1)+ 3-2*t+ 2*t^2-t^3"
  alternating := true
}

def knot_7_1 : KnotEntry := {
  name := "7_1"
  crossings := 7
  dt_code := { codes := [8, 10, 12, 14, 2, 4, 6] }
  pd_notation_str := "[[1,9,2,8],[3,11,4,10],[5,13,6,12],[7,1,8,14],[9,3,10,2],[11,5,12,4],[13,7,14,6]]"
  jones_known := some "t^3+ t^5-t^6+ t^7-t^8+ t^9-t^10"
  alternating := true
}

def knot_7_2 : KnotEntry := {
  name := "7_2"
  crossings := 7
  dt_code := { codes := [4, 10, 14, 12, 2, 8, 6] }
  pd_notation_str := "[[2,10,3,9],[4,14,5,13],[6,12,7,11],[8,2,9,1],[10,8,11,7],[12,6,13,5],[14,4,1,3]]"
  jones_known := some "t-t^2+ 2*t^3-2*t^4+ 2*t^5-t^6+ t^7-t^8"
  alternating := true
}

def knot_7_3 : KnotEntry := {
  name := "7_3"
  crossings := 7
  dt_code := { codes := [6, 10, 12, 14, 2, 4, 8] }
  pd_notation_str := "[[1,9,2,8],[3,11,4,10],[5,1,6,14],[7,13,8,12],[9,3,10,2],[11,5,12,4],[13,7,14,6]]"
  jones_known := some "t^2-t^3+ 2*t^4-2*t^5+ 3*t^6-2*t^7+ t^8-t^9"
  alternating := true
}

def knot_7_4 : KnotEntry := {
  name := "7_4"
  crossings := 7
  dt_code := { codes := [6, 10, 12, 14, 4, 2, 8] }
  pd_notation_str := "[[2,10,3,9],[4,12,5,11],[6,14,7,13],[8,4,9,3],[10,2,11,1],[12,8,13,7],[14,6,1,5]]"
  jones_known := some "t-2*t^2+ 3*t^3-2*t^4+ 3*t^5-2*t^6+ t^7-t^8"
  alternating := true
}

def knot_7_5 : KnotEntry := {
  name := "7_5"
  crossings := 7
  dt_code := { codes := [4, 10, 12, 14, 2, 8, 6] }
  pd_notation_str := "[[2,10,3,9],[4,2,5,1],[6,14,7,13],[8,12,9,11],[10,4,11,3],[12,6,13,5],[14,8,1,7]]"
  jones_known := some "t^2-t^3+ 3*t^4-3*t^5+ 3*t^6-3*t^7+ 2*t^8-t^9"
  alternating := true
}

def knot_7_6 : KnotEntry := {
  name := "7_6"
  crossings := 7
  dt_code := { codes := [4, 8, 12, 2, 14, 6, 10] }
  pd_notation_str := "[[1,13,2,12],[3,9,4,8],[5,1,6,14],[7,10,8,11],[9,3,10,2],[11,6,12,7],[13,5,14,4]]"
  jones_known := some "t^(-1)-2+ 3*t-3*t^2+ 4*t^3-3*t^4+ 2*t^5-t^6"
  alternating := true
}

def knot_7_7 : KnotEntry := {
  name := "7_7"
  crossings := 7
  dt_code := { codes := [4, 8, 10, 12, 2, 14, 6] }
  pd_notation_str := "[[1,10,2,11],[3,13,4,12],[5,14,6,1],[7,5,8,4],[9,2,10,3],[11,9,12,8],[13,6,14,7]]"
  jones_known := some "t^(-4)-2*t^(-3)+ 3*t^(-2)-4*t^(-1)+ 4-3*t+ 3*t^2-t^3"
  alternating := true
}

def knot_8_1 : KnotEntry := {
  name := "8_1"
  crossings := 8
  dt_code := { codes := [4, 10, 16, 14, 12, 2, 8, 6] }
  pd_notation_str := "[[1,9,2,8],[3,7,4,6],[5,12,6,13],[7,3,8,2],[9,1,10,16],[11,15,12,14],[13,4,14,5],[15,11,16,10]]"
  jones_known := some "t^(-2)-t^(-1)+ 2-2*t+ 2*t^2-2*t^3+ t^4-t^5+ t^6"
  alternating := true
}

def knot_8_2 : KnotEntry := {
  name := "8_2"
  crossings := 8
  dt_code := { codes := [4, 10, 12, 14, 16, 2, 6, 8] }
  pd_notation_str := "[[1,10,2,11],[3,13,4,12],[5,15,6,14],[7,1,8,16],[9,2,10,3],[11,9,12,8],[13,5,14,4],[15,7,16,6]]"
  jones_known := some "1-t+ 2*t^2-2*t^3+ 3*t^4-3*t^5+ 2*t^6-2*t^7+ t^8"
  alternating := true
}

def knot_8_3 : KnotEntry := {
  name := "8_3"
  crossings := 8
  dt_code := { codes := [6, 12, 10, 16, 14, 4, 2, 8] }
  pd_notation_str := "[[6,2,7,1],[14,10,15,9],[10,5,11,6],[12,3,13,4],[4,11,5,12],[2,13,3,14],[16,8,1,7],[8,16,9,15]]"
  jones_known := some "t^(-4)-t^(-3)+ 2*t^(-2)-3*t^(-1)+ 3-3*t+ 2*t^2-t^3+ t^4"
  alternating := true
}

def knot_8_4 : KnotEntry := {
  name := "8_4"
  crossings := 8
  dt_code := { codes := [6, 10, 12, 16, 14, 4, 2, 8] }
  pd_notation_str := "[[2,11,3,12],[4,9,5,10],[6,16,7,15],[8,14,9,13],[10,1,11,2],[12,3,13,4],[14,8,15,7],[16,6,1,5]]"
  jones_known := some " t^(-5)-2*t^(-4)+ 3*t^(-3)-3*t^(-2)+ 3*t^(-1)-3+ 2*t^1-t^2+ t^3"
  alternating := true
}

def knot_8_5 : KnotEntry := {
  name := "8_5"
  crossings := 8
  dt_code := { codes := [6, 8, 12, 2, 14, 16, 4, 10] }
  pd_notation_str := "[[1,7,2,6],[3,9,4,8],[5,12,6,13],[7,3,8,2],[9,15,10,14],[11,1,12,16],[13,4,14,5],[15,11,16,10]]"
  jones_known := some "1-t+ 3*t^2-3*t^3+ 3*t^4-4*t^5+ 3*t^6-2*t^7+ t^8"
  alternating := true
}

def knot_8_6 : KnotEntry := {
  name := "8_6"
  crossings := 8
  dt_code := { codes := [4, 10, 14, 16, 12, 2, 8, 6] }
  pd_notation_str := "[[2,9,3,10],[4,14,5,13],[6,16,7,15],[8,12,9,11],[10,1,11,2],[12,8,13,7],[14,6,15,5],[16,4,1,3]]"
  jones_known := some "t^(-1)-1+ 3*t-4*t^2+ 4*t^3-4*t^4+ 3*t^5-2*t^6+ t^7"
  alternating := true
}

def knot_8_7 : KnotEntry := {
  name := "8_7"
  crossings := 8
  dt_code := { codes := [4, 10, 12, 14, 2, 16, 6, 8] }
  pd_notation_str := "[[2,9,3,10],[4,14,5,13],[6,15,7,16],[8,1,9,2],[10,5,11,6],[12,4,13,3],[14,12,15,11],[16,7,1,8]]"
  jones_known := some "-t^(-6)+ 2*t^(-5)-3*t^(-4)+ 4*t^(-3)-4*t^(-2)+ 4*t^(-1)-2+ 2*t-t^2"
  alternating := true
}

def knot_8_8 : KnotEntry := {
  name := "8_8"
  crossings := 8
  dt_code := { codes := [4, 8, 12, 2, 16, 14, 6, 10] }
  pd_notation_str := "[[1,7,2,6],[3,12,4,13],[5,9,6,8],[7,3,8,2],[9,16,10,1],[11,14,12,15],[13,4,14,5],[15,10,16,11]]"
  jones_known := some "-t^(-5)+ 2*t^(-4)-3*t^(-3)+ 4*t^(-2)-4*t^(-1)+ 5-3*t+ 2*t^2-t^3"
  alternating := true
}

def knot_8_9 : KnotEntry := {
  name := "8_9"
  crossings := 8
  dt_code := { codes := [6, 10, 12, 14, 16, 4, 2, 8] }
  pd_notation_str := "[[6,2,7,1],[14,8,15,7],[10,3,11,4],[2,13,3,14],[12,5,13,6],[4,11,5,12],[16,10,1,9],[8,16,9,15]]"
  jones_known := some "t^(-4)-2*t^(-3)+ 3*t^(-2)-4*t^(-1)+ 5-4*t+ 3*t^2-2*t^3+ t^4"
  alternating := true
}

def knot_8_10 : KnotEntry := {
  name := "8_10"
  crossings := 8
  dt_code := { codes := [4, 8, 12, 2, 14, 16, 6, 10] }
  pd_notation_str := "[[2,14,3,13],[4,9,5,10],[6,11,7,12],[8,15,9,16],[10,5,11,6],[12,2,13,1],[14,7,15,8],[16,4,1,3]]"
  jones_known := some "-t^(-6)+ 2*t^(-5)-4*t^(-4)+ 5*t^(-3)-4*t^(-2)+ 5*t^(-1)-3+ 2*t-t^2"
  alternating := true
}

def knot_8_11 : KnotEntry := {
  name := "8_11"
  crossings := 8
  dt_code := { codes := [4, 10, 12, 14, 16, 2, 8, 6] }
  pd_notation_str := "[[1,10,2,11],[3,13,4,12],[5,15,6,14],[7,1,8,16],[9,2,10,3],[11,9,12,8],[13,7,14,6],[15,5,16,4]]"
  jones_known := some "t^(-1)-2+ 4*t-4*t^2+ 5*t^3-5*t^4+ 3*t^5-2*t^6+ t^7"
  alternating := true
}

def knot_8_12 : KnotEntry := {
  name := "8_12"
  crossings := 8
  dt_code := { codes := [4, 8, 14, 10, 2, 16, 6, 12] }
  pd_notation_str := "[[4,2,5,1],[10,8,11,7],[8,3,9,4],[2,9,3,10],[14,6,15,5],[16,11,1,12],[12,15,13,16],[6,14,7,13]]"
  jones_known := some "t^(-4)-2*t^(-3)+ 4*t^(-2)-5*t^(-1)+ 5-5*t+ 4*t^2-2*t^3+ t^4"
  alternating := true
}

def knot_8_13 : KnotEntry := {
  name := "8_13"
  crossings := 8
  dt_code := { codes := [4, 10, 12, 14, 2, 16, 8, 6] }
  pd_notation_str := "[[1,9,2,8],[3,14,4,15],[5,12,6,13],[7,11,8,10],[9,3,10,2],[11,16,12,1],[13,4,14,5],[15,6,16,7]]"
  jones_known := some "-t^(-5)+ 2*t^(-4)-3*t^(-3)+ 5*t^(-2)-5*t^(-1)+ 5-4*t+ 3*t^2-t^3"
  alternating := true
}

def knot_8_14 : KnotEntry := {
  name := "8_14"
  crossings := 8
  dt_code := { codes := [4, 8, 10, 14, 2, 16, 6, 12] }
  pd_notation_str := "[[2,12,3,11],[4,8,5,7],[6,15,7,16],[8,14,9,13],[10,2,11,1],[12,10,13,9],[14,4,15,3],[16,5,1,6]]"
  jones_known := some "t^(-1)-2+ 4*t-5*t^2+ 6*t^3-5*t^4+ 4*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_8_15 : KnotEntry := {
  name := "8_15"
  crossings := 8
  dt_code := { codes := [4, 8, 12, 2, 14, 6, 16, 10] }
  pd_notation_str := "[[1,7,2,6],[3,15,4,14],[5,9,6,8],[7,3,8,2],[9,13,10,12],[11,1,12,16],[13,5,14,4],[15,11,16,10]]"
  jones_known := some "t^2-2*t^3+ 5*t^4-5*t^5+ 6*t^6-6*t^7+ 4*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_8_16 : KnotEntry := {
  name := "8_16"
  crossings := 8
  dt_code := { codes := [6, 8, 14, 12, 4, 16, 2, 10] }
  pd_notation_str := "[[2,7,3,8],[4,10,5,9],[6,1,7,2],[8,14,9,13],[10,15,11,16],[12,6,13,5],[14,3,15,4],[16,11,1,12]]"
  jones_known := some "-t^(-6)+ 3*t^(-5)-5*t^(-4)+ 6*t^(-3)-6*t^(-2)+ 6*t^(-1)-4+ 3*t-t^2"
  alternating := true
}

def knot_8_17 : KnotEntry := {
  name := "8_17"
  crossings := 8
  dt_code := { codes := [6, 8, 12, 14, 4, 16, 2, 10] }
  pd_notation_str := "[[6,2,7,1],[14,8,15,7],[8,3,9,4],[2,13,3,14],[12,5,13,6],[4,9,5,10],[16,12,1,11],[10,16,11,15]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 5*t^(-2)-6*t^(-1)+ 7-6*t+ 5*t^2-3*t^3+ t^4"
  alternating := true
}

def knot_8_18 : KnotEntry := {
  name := "8_18"
  crossings := 8
  dt_code := { codes := [6, 8, 10, 12, 14, 16, 2, 4] }
  pd_notation_str := "[[6,2,7,1],[8,3,9,4],[16,11,1,12],[2,14,3,13],[4,15,5,16],[10,6,11,5],[12,7,13,8],[14,10,15,9]]"
  jones_known := some "t^(-4)-4*t^(-3)+ 6*t^(-2)-7*t^(-1)+ 9-7*t+ 6*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_8_19 : KnotEntry := {
  name := "8_19"
  crossings := 8
  dt_code := { codes := [4, 8, -12, 2, -14, -16, -6, -10] }
  pd_notation_str := "[[2,14,3,13],[5,11,6,10],[7,15,8,14],[9,5,10,4],[11,7,12,6],[12,2,13,1],[15,9,16,8],[16,4,1,3]]"
  jones_known := some "t^3+ t^5-t^8"
  alternating := false
}

def knot_8_20 : KnotEntry := {
  name := "8_20"
  crossings := 8
  dt_code := { codes := [4, 8, -12, 2, -14, -6, -16, -10] }
  pd_notation_str := "[[1,7,2,6],[4,13,5,14],[5,9,6,8],[7,3,8,2],[10,15,11,16],[12,9,13,10],[14,3,15,4],[16,11,1,12]]"
  jones_known := some "-t^(-5)+ t^(-4)-t^(-3)+ 2*t^(-2)-t^(-1)+ 2-t"
  alternating := false
}

def knot_8_21 : KnotEntry := {
  name := "8_21"
  crossings := 8
  dt_code := { codes := [4, 8, -12, 2, 14, -6, 16, 10] }
  pd_notation_str := "[[1,7,2,6],[4,13,5,14],[5,9,6,8],[7,3,8,2],[9,13,10,12],[11,1,12,16],[14,3,15,4],[15,11,16,10]]"
  jones_known := some "2*t-2*t^2+ 3*t^3-3*t^4+ 2*t^5-2*t^6+ t^7"
  alternating := false
}

def knot_9_1 : KnotEntry := {
  name := "9_1"
  crossings := 9
  dt_code := { codes := [10, 12, 14, 16, 18, 2, 4, 6, 8] }
  pd_notation_str := "[[1,11,2,10],[3,13,4,12],[5,15,6,14],[7,17,8,16],[9,1,10,18],[11,3,12,2],[13,5,14,4],[15,7,16,6],[17,9,18,8]]"
  jones_known := some "t^4+ t^6-t^7+ t^8-t^9+ t^10-t^11+ t^12-t^13"
  alternating := true
}

def knot_9_2 : KnotEntry := {
  name := "9_2"
  crossings := 9
  dt_code := { codes := [4, 12, 18, 16, 14, 2, 10, 8, 6] }
  pd_notation_str := "[[2,8,3,7],[4,14,5,13],[6,4,7,3],[8,2,9,1],[10,18,11,17],[12,16,13,15],[14,6,15,5],[16,12,17,11],[18,10,1,9]]"
  jones_known := some "t-t^2+ 2*t^3-2*t^4+ 2*t^5-2*t^6+ 2*t^7-t^8+ t^9-t^10"
  alternating := true
}

def knot_9_3 : KnotEntry := {
  name := "9_3"
  crossings := 9
  dt_code := { codes := [8, 12, 14, 16, 18, 2, 4, 6, 10] }
  pd_notation_str := "[[1,11,2,10],[3,15,4,14],[5,13,6,12],[7,17,8,16],[9,1,10,18],[11,3,12,2],[13,5,14,4],[15,7,16,6],[17,9,18,8]]"
  jones_known := some "t^3-t^4+ 2*t^5-2*t^6+ 3*t^7-3*t^8+ 3*t^9-2*t^10+ t^11-t^12"
  alternating := true
}

def knot_9_4 : KnotEntry := {
  name := "9_4"
  crossings := 9
  dt_code := { codes := [6, 12, 14, 18, 16, 2, 4, 10, 8] }
  pd_notation_str := "[[2,14,3,13],[4,12,5,11],[6,16,7,15],[8,18,9,17],[10,6,11,5],[12,4,13,3],[14,2,15,1],[16,8,17,7],[18,10,1,9]]"
  jones_known := some "t^2-t^3+ 2*t^4-3*t^5+ 4*t^6-3*t^7+ 3*t^8-2*t^9+ t^10-t^11"
  alternating := true
}

def knot_9_5 : KnotEntry := {
  name := "9_5"
  crossings := 9
  dt_code := { codes := [6, 12, 14, 18, 16, 4, 2, 10, 8] }
  pd_notation_str := "[[2,14,3,13],[4,12,5,11],[6,16,7,15],[8,18,9,17],[10,6,11,5],[12,4,13,3],[14,2,15,1],[16,10,17,9],[18,8,1,7]]"
  jones_known := some "t-2*t^2+ 3*t^3-3*t^4+ 4*t^5-3*t^6+ 3*t^7-2*t^8+ t^9-t^10"
  alternating := true
}

def knot_9_6 : KnotEntry := {
  name := "9_6"
  crossings := 9
  dt_code := { codes := [4, 12, 14, 16, 18, 2, 10, 6, 8] }
  pd_notation_str := "[[1,13,2,12],[3,7,4,6],[5,15,6,14],[7,3,8,2],[9,17,10,16],[11,1,12,18],[13,5,14,4],[15,9,16,8],[17,11,18,10]]"
  jones_known := some "t^3-t^4+ 3*t^5-3*t^6+ 4*t^7-5*t^8+ 4*t^9-3*t^10+ 2*t^11-t^12"
  alternating := true
}

def knot_9_7 : KnotEntry := {
  name := "9_7"
  crossings := 9
  dt_code := { codes := [4, 12, 16, 18, 14, 2, 10, 8, 6] }
  pd_notation_str := "[[2,10,3,9],[4,12,5,11],[6,16,7,15],[8,6,9,5],[10,4,11,3],[12,2,13,1],[14,18,15,17],[16,8,17,7],[18,14,1,13]]"
  jones_known := some "t^2-t^3+ 3*t^4-4*t^5+ 5*t^6-5*t^7+ 4*t^8-3*t^9+ 2*t^10-t^11"
  alternating := true
}

def knot_9_8 : KnotEntry := {
  name := "9_8"
  crossings := 9
  dt_code := { codes := [4, 8, 14, 2, 18, 16, 6, 12, 10] }
  pd_notation_str := "[[1,16,2,17],[3,14,4,15],[5,11,6,10],[7,1,8,18],[9,13,10,12],[11,7,12,6],[13,4,14,5],[15,2,16,3],[17,9,18,8]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 3*t^(-1)-4+ 5*t-5*t^2+ 5*t^3-3*t^4+ 2*t^5-t^6"
  alternating := true
}

def knot_9_9 : KnotEntry := {
  name := "9_9"
  crossings := 9
  dt_code := { codes := [6, 12, 14, 16, 18, 2, 4, 10, 8] }
  pd_notation_str := "[[1,13,2,12],[3,9,4,8],[5,15,6,14],[7,17,8,16],[9,3,10,2],[11,1,12,18],[13,5,14,4],[15,7,16,6],[17,11,18,10]]"
  jones_known := some "t^3-t^4+ 3*t^5-4*t^6+ 5*t^7-5*t^8+ 5*t^9-4*t^10+ 2*t^11-t^12"
  alternating := true
}

def knot_9_10 : KnotEntry := {
  name := "9_10"
  crossings := 9
  dt_code := { codes := [8, 12, 14, 16, 18, 2, 6, 4, 10] }
  pd_notation_str := "[[1,13,2,12],[3,11,4,10],[5,17,6,16],[7,15,8,14],[9,1,10,18],[11,3,12,2],[13,5,14,4],[15,7,16,6],[17,9,18,8]]"
  jones_known := some "t^2-2*t^3+ 4*t^4-5*t^5+ 6*t^6-5*t^7+ 5*t^8-3*t^9+ t^10-t^11"
  alternating := true
}

def knot_9_11 : KnotEntry := {
  name := "9_11"
  crossings := 9
  dt_code := { codes := [4, 10, 14, 16, 12, 2, 18, 6, 8] }
  pd_notation_str := "[[2,7,3,8],[4,13,5,14],[6,15,7,16],[8,12,9,11],[10,17,11,18],[12,3,13,4],[14,5,15,6],[16,2,17,1],[18,9,1,10]]"
  jones_known := some "-t^(-9)+ 2*t^(-8)-4*t^(-7)+ 5*t^(-6)-5*t^(-5)+ 6*t^(-4)-4*t^(-3)+ 3*t^(-2)-2*t^(-1)+ 1"
  alternating := true
}

def knot_9_12 : KnotEntry := {
  name := "9_12"
  crossings := 9
  dt_code := { codes := [4, 10, 16, 14, 2, 18, 8, 6, 12] }
  pd_notation_str := "[[2,9,3,10],[4,16,5,15],[6,14,7,13],[8,3,9,4],[10,18,11,17],[12,8,13,7],[14,6,15,5],[16,2,17,1],[18,12,1,11]]"
  jones_known := some "t^(-1)-2+ 4*t-5*t^2+ 6*t^3-6*t^4+ 5*t^5-3*t^6+ 2*t^7-t^8"
  alternating := true
}

def knot_9_13 : KnotEntry := {
  name := "9_13"
  crossings := 9
  dt_code := { codes := [6, 12, 14, 16, 18, 4, 2, 10, 8] }
  pd_notation_str := "[[2,12,3,11],[4,14,5,13],[6,16,7,15],[8,18,9,17],[10,6,11,5],[12,4,13,3],[14,2,15,1],[16,10,17,9],[18,8,1,7]]"
  jones_known := some "t^2-2*t^3+ 4*t^4-5*t^5+ 7*t^6-6*t^7+ 5*t^8-4*t^9+ 2*t^10-t^11"
  alternating := true
}

def knot_9_14 : KnotEntry := {
  name := "9_14"
  crossings := 9
  dt_code := { codes := [4, 10, 12, 16, 14, 2, 18, 8, 6] }
  pd_notation_str := "[[1,12,2,13],[3,10,4,11],[5,16,6,17],[7,1,8,18],[9,4,10,5],[11,2,12,3],[13,9,14,8],[15,6,16,7],[17,15,18,14]]"
  jones_known := some "t^(-6)-2*t^(-5)+ 3*t^(-4)-5*t^(-3)+ 6*t^(-2)-6*t^(-1)+ 6-4*t+ 3*t^2-t^3"
  alternating := true
}

def knot_9_15 : KnotEntry := {
  name := "9_15"
  crossings := 9
  dt_code := { codes := [4, 8, 14, 10, 2, 18, 16, 6, 12] }
  pd_notation_str := "[[2,9,3,10],[4,7,5,8],[6,15,7,16],[8,3,9,4],[10,14,11,13],[12,17,13,18],[14,5,15,6],[16,2,17,1],[18,11,1,12]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-4*t^(-6)+ 6*t^(-5)-6*t^(-4)+ 7*t^(-3)-6*t^(-2)+ 4*t^(-1)-2+ t"
  alternating := true
}

def knot_9_16 : KnotEntry := {
  name := "9_16"
  crossings := 9
  dt_code := { codes := [4, 12, 16, 18, 14, 2, 8, 10, 6] }
  pd_notation_str := "[[1,9,2,8],[3,11,4,10],[5,15,6,14],[7,5,8,4],[9,3,10,2],[11,17,12,16],[13,1,14,18],[15,7,16,6],[17,13,18,12]]"
  jones_known := some "t^3-t^4+ 4*t^5-5*t^6+ 6*t^7-7*t^8+ 6*t^9-5*t^10+ 3*t^11-t^12"
  alternating := true
}

def knot_9_17 : KnotEntry := {
  name := "9_17"
  crossings := 9
  dt_code := { codes := [4, 10, 12, 14, 16, 2, 6, 18, 8] }
  pd_notation_str := "[[1,9,2,8],[3,12,4,13],[5,16,6,17],[7,1,8,18],[9,3,10,2],[11,4,12,5],[13,11,14,10],[15,6,16,7],[17,15,18,14]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 4*t^(-1)-5+ 6*t-7*t^2+ 6*t^3-4*t^4+ 3*t^5-t^6"
  alternating := true
}

def knot_9_18 : KnotEntry := {
  name := "9_18"
  crossings := 9
  dt_code := { codes := [4, 12, 14, 16, 18, 2, 10, 8, 6] }
  pd_notation_str := "[[2,12,3,11],[4,2,5,1],[6,16,7,15],[8,14,9,13],[10,18,11,17],[12,4,13,3],[14,8,15,7],[16,10,17,9],[18,6,1,5]]"
  jones_known := some "t^2-2*t^3+ 5*t^4-6*t^5+ 7*t^6-7*t^7+ 6*t^8-4*t^9+ 2*t^10-t^11"
  alternating := true
}

def knot_9_19 : KnotEntry := {
  name := "9_19"
  crossings := 9
  dt_code := { codes := [4, 8, 10, 14, 2, 18, 16, 6, 12] }
  pd_notation_str := "[[2,14,3,13],[4,11,5,12],[6,4,7,3],[8,17,9,18],[10,5,11,6],[12,8,13,7],[14,2,15,1],[16,9,17,10],[18,16,1,15]]"
  jones_known := some "t^(-4)-2*t^(-3)+ 4*t^(-2)-6*t^(-1)+ 7-7*t+ 6*t^2-4*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_9_20 : KnotEntry := {
  name := "9_20"
  crossings := 9
  dt_code := { codes := [4, 10, 14, 16, 2, 18, 8, 6, 12] }
  pd_notation_str := "[[1,11,2,10],[3,16,4,17],[5,13,6,12],[7,3,8,2],[9,1,10,18],[11,15,12,14],[13,7,14,6],[15,4,16,5],[17,9,18,8]]"
  jones_known := some "1-2*t+ 4*t^2-5*t^3+ 7*t^4-7*t^5+ 6*t^6-5*t^7+ 3*t^8-t^9"
  alternating := true
}

def knot_9_21 : KnotEntry := {
  name := "9_21"
  crossings := 9
  dt_code := { codes := [4, 10, 14, 16, 12, 2, 18, 8, 6] }
  pd_notation_str := "[[2,7,3,8],[4,13,5,14],[6,15,7,16],[8,12,9,11],[10,17,11,18],[12,5,13,6],[14,3,15,4],[16,2,17,1],[18,9,1,10]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-4*t^(-6)+ 6*t^(-5)-7*t^(-4)+ 8*t^(-3)-6*t^(-2)+ 5*t^(-1)-3+ t"
  alternating := true
}

def knot_9_22 : KnotEntry := {
  name := "9_22"
  crossings := 9
  dt_code := { codes := [4, 8, 10, 14, 2, 16, 18, 6, 12] }
  pd_notation_str := "[[1,7,2,6],[3,8,4,9],[5,14,6,15],[7,11,8,10],[9,2,10,3],[11,17,12,16],[13,1,14,18],[15,4,16,5],[17,13,18,12]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 4*t^(-1)-6+ 7*t-7*t^2+ 7*t^3-5*t^4+ 3*t^5-t^6"
  alternating := true
}

def knot_9_23 : KnotEntry := {
  name := "9_23"
  crossings := 9
  dt_code := { codes := [4, 10, 12, 16, 2, 8, 18, 6, 14] }
  pd_notation_str := "[[2,16,3,15],[4,12,5,11],[6,4,7,3],[8,18,9,17],[10,14,11,13],[12,6,13,5],[14,8,15,7],[16,2,17,1],[18,10,1,9]]"
  jones_known := some "t^2-2*t^3+ 5*t^4-6*t^5+ 8*t^6-8*t^7+ 6*t^8-5*t^9+ 3*t^10-t^11"
  alternating := true
}

def knot_9_24 : KnotEntry := {
  name := "9_24"
  crossings := 9
  dt_code := { codes := [4, 8, 14, 2, 16, 18, 6, 12, 10] }
  pd_notation_str := "[[1,13,2,12],[3,7,4,6],[5,1,6,18],[7,14,8,15],[9,16,10,17],[11,3,12,2],[13,10,14,11],[15,8,16,9],[17,5,18,4]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 5*t^(-2)-7*t^(-1)+ 8-7*t+ 7*t^2-4*t^3+ 2*t^4-t^5"
  alternating := true
}

def knot_9_25 : KnotEntry := {
  name := "9_25"
  crossings := 9
  dt_code := { codes := [4, 8, 12, 2, 16, 6, 18, 10, 14] }
  pd_notation_str := "[[2,10,3,9],[4,17,5,18],[6,12,7,11],[8,4,9,3],[10,14,11,13],[12,8,13,7],[14,2,15,1],[16,5,17,6],[18,16,1,15]]"
  jones_known := some "t^(-1)-2+ 5*t-7*t^2+ 8*t^3-8*t^4+ 7*t^5-5*t^6+ 3*t^7-t^8"
  alternating := true
}

def knot_9_26 : KnotEntry := {
  name := "9_26"
  crossings := 9
  dt_code := { codes := [4, 10, 12, 14, 16, 2, 18, 8, 6] }
  pd_notation_str := "[[2,10,3,9],[4,11,5,12],[6,17,7,18],[8,15,9,16],[10,14,11,13],[12,3,13,4],[14,2,15,1],[16,5,17,6],[18,7,1,8]]"
  jones_known := some "t^(-7)-3*t^(-6)+ 5*t^(-5)-7*t^(-4)+ 8*t^(-3)-8*t^(-2)+ 7*t^(-1)-4+ 3*t-t^2"
  alternating := true
}

def knot_9_27 : KnotEntry := {
  name := "9_27"
  crossings := 9
  dt_code := { codes := [4, 10, 12, 14, 2, 18, 16, 6, 8] }
  pd_notation_str := "[[2,9,3,10],[4,7,5,8],[6,14,7,13],[8,15,9,16],[10,18,11,17],[12,3,13,4],[14,6,15,5],[16,2,17,1],[18,12,1,11]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 5*t^(-2)-7*t^(-1)+ 9-8*t+ 7*t^2-5*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_9_28 : KnotEntry := {
  name := "9_28"
  crossings := 9
  dt_code := { codes := [4, 8, 12, 2, 16, 14, 6, 18, 10] }
  pd_notation_str := "[[1,16,2,17],[3,15,4,14],[5,3,6,2],[7,13,8,12],[9,7,10,6],[11,18,12,1],[13,9,14,8],[15,5,16,4],[17,10,18,11]]"
  jones_known := some "-t^(-2)+ 3*t^(-1)-5+ 8*t-8*t^2+ 9*t^3-8*t^4+ 5*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_9_29 : KnotEntry := {
  name := "9_29"
  crossings := 9
  dt_code := { codes := [6, 10, 14, 18, 4, 16, 8, 2, 12] }
  pd_notation_str := "[[2,10,3,9],[4,17,5,18],[6,12,7,11],[8,4,9,3],[10,15,11,16],[12,6,13,5],[14,1,15,2],[16,7,17,8],[18,13,1,14]]"
  jones_known := some "-t^(-6)+ 3*t^(-5)-6*t^(-4)+ 8*t^(-3)-8*t^(-2)+ 9*t^(-1)-7+ 5*t-3*t^2+ t^3"
  alternating := true
}

def knot_9_30 : KnotEntry := {
  name := "9_30"
  crossings := 9
  dt_code := { codes := [4, 8, 10, 14, 2, 16, 6, 18, 12] }
  pd_notation_str := "[[1,9,2,8],[3,16,4,17],[5,1,6,18],[7,12,8,13],[9,3,10,2],[11,6,12,7],[13,10,14,11],[15,4,16,5],[17,15,18,14]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-5*t^(-3)+ 8*t^(-2)-9*t^(-1)+ 9-8*t+ 6*t^2-3*t^3+ t^4"
  alternating := true
}

def knot_9_31 : KnotEntry := {
  name := "9_31"
  crossings := 9
  dt_code := { codes := [4, 10, 12, 14, 2, 18, 16, 8, 6] }
  pd_notation_str := "[[1,9,2,8],[3,10,4,11],[5,13,6,12],[7,1,8,18],[9,16,10,17],[11,15,12,14],[13,7,14,6],[15,4,16,5],[17,3,18,2]]"
  jones_known := some "-t^(-2)+ 3*t^(-1)-5+ 8*t-9*t^2+ 10*t^3-8*t^4+ 6*t^5-4*t^6+ t^7"
  alternating := true
}

def knot_9_32 : KnotEntry := {
  name := "9_32"
  crossings := 9
  dt_code := { codes := [4, 8, 12, 14, 2, 16, 18, 10, 6] }
  pd_notation_str := "[[2,8,3,7],[4,9,5,10],[6,13,7,14],[8,16,9,15],[10,5,11,6],[12,17,13,18],[14,3,15,4],[16,2,17,1],[18,11,1,12]]"
  jones_known := some "t^(-7)-3*t^(-6)+ 6*t^(-5)-9*t^(-4)+ 10*t^(-3)-10*t^(-2)+ 9*t^(-1)-6+ 4*t-t^2"
  alternating := true
}

def knot_9_33 : KnotEntry := {
  name := "9_33"
  crossings := 9
  dt_code := { codes := [4, 8, 14, 12, 2, 16, 18, 10, 6] }
  pd_notation_str := "[[1,15,2,14],[3,16,4,17],[5,12,6,13],[7,5,8,4],[9,2,10,3],[11,6,12,7],[13,1,14,18],[15,11,16,10],[17,8,18,9]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-6*t^(-3)+ 9*t^(-2)-10*t^(-1)+ 11-9*t+ 7*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_9_34 : KnotEntry := {
  name := "9_34"
  crossings := 9
  dt_code := { codes := [6, 8, 10, 16, 14, 18, 4, 2, 12] }
  pd_notation_str := "[[2,13,3,14],[4,17,5,18],[6,16,7,15],[8,4,9,3],[10,5,11,6],[12,8,13,7],[14,1,15,2],[16,11,17,12],[18,10,1,9]]"
  jones_known := some "-t^(-5)+ 4*t^(-4)-7*t^(-3)+ 10*t^(-2)-12*t^(-1)+ 12-10*t^1+ 8*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_9_35 : KnotEntry := {
  name := "9_35"
  crossings := 9
  dt_code := { codes := [8, 12, 16, 14, 18, 4, 2, 6, 10] }
  pd_notation_str := "[[2,12,3,11],[4,16,5,15],[6,14,7,13],[8,18,9,17],[10,4,11,3],[12,2,13,1],[14,6,15,5],[16,10,17,9],[18,8,1,7]]"
  jones_known := some "t-2*t^2+ 3*t^3-4*t^4+ 5*t^5-3*t^6+ 4*t^7-3*t^8+ t^9-t^10"
  alternating := true
}

def knot_9_36 : KnotEntry := {
  name := "9_36"
  crossings := 9
  dt_code := { codes := [4, 8, 14, 10, 2, 16, 18, 6, 12] }
  pd_notation_str := "[[2,15,3,16],[4,11,5,12],[6,4,7,3],[8,17,9,18],[10,5,11,6],[12,10,13,9],[14,1,15,2],[16,7,17,8],[18,13,1,14]]"
  jones_known := some "-t^(-9)+ 2*t^(-8)-4*t^(-7)+ 6*t^(-6)-6*t^(-5)+ 6*t^(-4)-5*t^(-3)+ 4*t^(-2)-2*t^(-1)+ 1"
  alternating := true
}

def knot_9_37 : KnotEntry := {
  name := "9_37"
  crossings := 9
  dt_code := { codes := [4, 10, 14, 12, 16, 2, 6, 18, 8] }
  pd_notation_str := "[[1,10,2,11],[3,14,4,15],[5,1,6,18],[7,17,8,16],[9,2,10,3],[11,9,12,8],[13,4,14,5],[15,13,16,12],[17,7,18,6]]"
  jones_known := some "t^(-4)-2*t^(-3)+ 5*t^(-2)-7*t^(-1)+ 7-8*t+ 7*t^2-4*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_9_38 : KnotEntry := {
  name := "9_38"
  crossings := 9
  dt_code := { codes := [6, 10, 14, 18, 4, 16, 2, 8, 12] }
  pd_notation_str := "[[2,14,3,13],[4,10,5,9],[6,16,7,15],[8,4,9,3],[10,18,11,17],[12,6,13,5],[14,2,15,1],[16,12,17,11],[18,8,1,7]]"
  jones_known := some "t^2-3*t^3+ 7*t^4-8*t^5+ 10*t^6-10*t^7+ 8*t^8-6*t^9+ 3*t^10-t^11"
  alternating := true
}

def knot_9_39 : KnotEntry := {
  name := "9_39"
  crossings := 9
  dt_code := { codes := [6, 10, 14, 18, 16, 2, 8, 4, 12] }
  pd_notation_str := "[[1,12,2,13],[3,17,4,16],[5,10,6,11],[7,18,8,1],[9,14,10,15],[11,2,12,3],[13,6,14,7],[15,5,16,4],[17,8,18,9]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-6*t^(-6)+ 8*t^(-5)-9*t^(-4)+ 10*t^(-3)-8*t^(-2)+ 6*t^(-1)-3+ t"
  alternating := true
}

def knot_9_40 : KnotEntry := {
  name := "9_40"
  crossings := 9
  dt_code := { codes := [6, 16, 14, 12, 4, 2, 18, 10, 8] }
  pd_notation_str := "[[1,15,2,14],[3,12,4,13],[5,11,6,10],[7,3,8,2],[9,18,10,1],[11,17,12,16],[13,9,14,8],[15,6,16,7],[17,5,18,4]]"
  jones_known := some "-t^(-2)+ 5*t^(-1)-8+ 11*t-13*t^2+ 13*t^3-11*t^4+ 8*t^5-4*t^6+ t^7"
  alternating := true
}

def knot_9_41 : KnotEntry := {
  name := "9_41"
  crossings := 9
  dt_code := { codes := [6, 10, 14, 12, 16, 2, 18, 4, 8] }
  pd_notation_str := "[[1,15,2,14],[3,12,4,13],[5,16,6,17],[7,3,8,2],[9,18,10,1],[11,4,12,5],[13,9,14,8],[15,6,16,7],[17,10,18,11]]"
  jones_known := some "t^(-6)-3*t^(-5)+ 5*t^(-4)-7*t^(-3)+ 8*t^(-2)-8*t^(-1)+ 8-5*t+ 3*t^2-t^3"
  alternating := true
}

def knot_9_42 : KnotEntry := {
  name := "9_42"
  crossings := 9
  dt_code := { codes := [4, 8, 10, -14, 2, -16, -18, -6, -12] }
  pd_notation_str := "[[1,5,2,4],[5,11,6,10],[3,8,4,9],[9,2,10,3],[16,11,17,12],[14,8,15,7],[6,16,7,15],[18,13,1,14],[12,17,13,18]]"
  jones_known := some "t^(-3)-t^(-2)+ t^(-1)-1+ t-t^2+ t^3"
  alternating := false
}

def knot_9_43 : KnotEntry := {
  name := "9_43"
  crossings := 9
  dt_code := { codes := [4, 8, 10, 14, 2, -16, 6, -18, -12] }
  pd_notation_str := "[[1,9,2,8],[3,16,4,17],[5,1,6,18],[6,12,7,11],[9,3,10,2],[10,14,11,13],[12,8,13,7],[15,4,16,5],[17,15,18,14]]"
  jones_known := some "1-t+ 2*t^2-2*t^3+ 2*t^4-2*t^5+ 2*t^6-t^7"
  alternating := false
}

def knot_9_44 : KnotEntry := {
  name := "9_44"
  crossings := 9
  dt_code := { codes := [4, 8, 10, -14, 2, -16, -6, -18, -12] }
  pd_notation_str := "[[2,9,3,10],[3,16,4,17],[5,1,6,18],[6,12,7,11],[8,1,9,2],[10,14,11,13],[12,8,13,7],[15,4,16,5],[17,15,18,14]]"
  jones_known := some "t^(-2)-2*t^(-1)+ 3-3*t+ 3*t^2-2*t^3+ 2*t^4-t^5"
  alternating := false
}

def knot_9_45 : KnotEntry := {
  name := "9_45"
  crossings := 9
  dt_code := { codes := [4, 8, 10, -14, 2, 16, -6, 18, 12] }
  pd_notation_str := "[[2,9,3,10],[3,16,4,17],[5,1,6,18],[7,12,8,13],[8,1,9,2],[11,6,12,7],[13,10,14,11],[15,4,16,5],[17,15,18,14]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-3*t^(-6)+ 4*t^(-5)-4*t^(-4)+ 4*t^(-3)-3*t^(-2)+ 2*t^(-1)"
  alternating := false
}

def knot_9_46 : KnotEntry := {
  name := "9_46"
  crossings := 9
  dt_code := { codes := [4, 10, -14, -12, -16, 2, -6, -18, -8] }
  pd_notation_str := "[[2,10,3,9],[3,14,4,15],[6,17,7,18],[8,11,9,12],[10,2,11,1],[13,4,14,5],[15,13,16,12],[16,7,17,8],[18,5,1,6]]"
  jones_known := some "t^(-6)-t^(-5)+ t^(-4)-2*t^(-3)+ t^(-2)-t^(-1)+ 2"
  alternating := false
}

def knot_9_47 : KnotEntry := {
  name := "9_47"
  crossings := 9
  dt_code := { codes := [6, 8, 10, 16, 14, -18, 4, 2, -12] }
  pd_notation_str := "[[1,15,2,14],[4,17,5,18],[6,16,7,15],[8,4,9,3],[10,5,11,6],[12,8,13,7],[13,3,14,2],[16,11,17,12],[18,10,1,9]]"
  jones_known := some "-t^(-2)+ 3*t^(-1)-3+ 5*t-5*t^2+ 4*t^3-4*t^4+ 2*t^5"
  alternating := false
}

def knot_9_48 : KnotEntry := {
  name := "9_48"
  crossings := 9
  dt_code := { codes := [4, 10, -14, -12, 16, 2, -6, 18, 8] }
  pd_notation_str := "[[1,10,2,11],[3,14,4,15],[6,17,7,18],[9,2,10,3],[11,9,12,8],[13,4,14,5],[15,13,16,12],[16,7,17,8],[18,5,1,6]]"
  jones_known := some "-2*t^(-6)+ 3*t^(-5)-4*t^(-4)+ 6*t^(-3)-4*t^(-2)+ 4*t^(-1)-3+ t"
  alternating := false
}

def knot_9_49 : KnotEntry := {
  name := "9_49"
  crossings := 9
  dt_code := { codes := [6, -10, -14, 12, -16, -2, 18, -4, -8] }
  pd_notation_str := "[[1,15,2,14],[4,12,5,11],[6,16,7,15],[7,3,8,2],[10,18,11,17],[12,4,13,3],[13,9,14,8],[16,6,17,5],[18,10,1,9]]"
  jones_known := some "t^2-2*t^3+ 4*t^4-4*t^5+ 5*t^6-4*t^7+ 3*t^8-2*t^9"
  alternating := false
}

def knot_10_1 : KnotEntry := {
  name := "10_1"
  crossings := 10
  dt_code := { codes := [4, 12, 20, 18, 16, 14, 2, 10, 8, 6] }
  pd_notation_str := "[[2,11,3,12],[4,20,5,19],[6,18,7,17],[8,16,9,15],[10,14,11,13],[12,1,13,2],[14,10,15,9],[16,8,17,7],[18,6,19,5],[20,4,1,3]]"
  jones_known := some "t^(-2)-t^(-1)+ 2-2*t+ 2*t^2-2*t^3+ 2*t^4-2*t^5+ t^6-t^7+ t^8"
  alternating := true
}

def knot_10_2 : KnotEntry := {
  name := "10_2"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 16, 18, 20, 2, 6, 8, 10] }
  pd_notation_str := "[[1,13,2,12],[3,14,4,15],[5,3,6,2],[7,17,8,16],[9,19,10,18],[11,1,12,20],[13,4,14,5],[15,7,16,6],[17,9,18,8],[19,11,20,10]]"
  jones_known := some "t-t^2+ 2*t^3-2*t^4+ 3*t^5-3*t^6+ 3*t^7-3*t^8+ 2*t^9-2*t^10+ t^11"
  alternating := true
}

def knot_10_3 : KnotEntry := {
  name := "10_3"
  crossings := 10
  dt_code := { codes := [6, 14, 12, 20, 18, 16, 4, 2, 10, 8] }
  pd_notation_str := "[[2,10,3,9],[4,17,5,18],[6,15,7,16],[8,4,9,3],[10,2,11,1],[12,20,13,19],[14,7,15,8],[16,5,17,6],[18,14,19,13],[20,12,1,11]]"
  jones_known := some "t^(-4)-t^(-3)+ 2*t^(-2)-3*t^(-1)+ 4-4*t+ 3*t^2-3*t^3+ 2*t^4-t^5+ t^6"
  alternating := true
}

def knot_10_4 : KnotEntry := {
  name := "10_4"
  crossings := 10
  dt_code := { codes := [6, 12, 14, 20, 18, 16, 4, 2, 10, 8] }
  pd_notation_str := "[[2,13,3,14],[4,11,5,12],[6,20,7,19],[8,18,9,17],[10,16,11,15],[12,1,13,2],[14,3,15,4],[16,10,17,9],[18,8,19,7],[20,6,1,5]]"
  jones_known := some "t^(-5)-2*t^(-4)+ 3*t^(-3)-3*t^(-2)+ 4*t^(-1)-4+ 3*t-3*t^2+ 2*t^3-t^4+ t^5"
  alternating := true
}

def knot_10_5 : KnotEntry := {
  name := "10_5"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 16, 18, 2, 20, 6, 8, 10] }
  pd_notation_str := "[[2,13,3,14],[4,17,5,18],[6,16,7,15],[8,6,9,5],[10,19,11,20],[12,1,13,2],[14,3,15,4],[16,8,17,7],[18,9,19,10],[20,11,1,12]]"
  jones_known := some "-t^(-9)+ 2*t^(-8)-3*t^(-7)+ 4*t^(-6)-5*t^(-5)+ 5*t^(-4)-4*t^(-3)+ 4*t^(-2)-2*t^(-1)+ 2-t"
  alternating := true
}

def knot_10_6 : KnotEntry := {
  name := "10_6"
  crossings := 10
  dt_code := { codes := [4, 12, 16, 18, 20, 14, 2, 10, 6, 8] }
  pd_notation_str := "[[2,11,3,12],[4,16,5,15],[6,18,7,17],[8,20,9,19],[10,14,11,13],[12,1,13,2],[14,10,15,9],[16,6,17,5],[18,8,19,7],[20,4,1,3]]"
  jones_known := some "1-t+ 3*t^2-4*t^3+ 5*t^4-6*t^5+ 6*t^6-5*t^7+ 3*t^8-2*t^9+ t^10"
  alternating := true
}

def knot_10_7 : KnotEntry := {
  name := "10_7"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 18, 16, 20, 2, 10, 8, 6] }
  pd_notation_str := "[[1,12,2,13],[3,15,4,14],[5,19,6,18],[7,17,8,16],[9,1,10,20],[11,2,12,3],[13,11,14,10],[15,9,16,8],[17,7,18,6],[19,5,20,4]]"
  jones_known := some "t^(-1)-2+ 4*t-5*t^2+ 7*t^3-7*t^4+ 6*t^5-5*t^6+ 3*t^7-2*t^8+ t^9"
  alternating := true
}

def knot_10_8 : KnotEntry := {
  name := "10_8"
  crossings := 10
  dt_code := { codes := [6, 14, 12, 16, 18, 20, 4, 2, 8, 10] }
  pd_notation_str := "[[1,12,2,13],[3,10,4,11],[5,15,6,14],[7,17,8,16],[9,19,10,18],[11,2,12,3],[13,20,14,1],[15,7,16,6],[17,9,18,8],[19,5,20,4]]"
  jones_known := some "t^(-2)-t^(-1)+ 2-3*t+ 4*t^2-4*t^3+ 4*t^4-4*t^5+ 3*t^6-2*t^7+ t^8"
  alternating := true
}

def knot_10_9 : KnotEntry := {
  name := "10_9"
  crossings := 10
  dt_code := { codes := [6, 12, 14, 16, 18, 20, 4, 2, 8, 10] }
  pd_notation_str := "[[1,13,2,12],[3,16,4,17],[5,14,6,15],[7,3,8,2],[9,19,10,18],[11,1,12,20],[13,4,14,5],[15,6,16,7],[17,9,18,8],[19,11,20,10]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 3*t^(-1)-4+ 6*t-6*t^2+ 6*t^3-5*t^4+ 3*t^5-2*t^6+ t^7"
  alternating := true
}

def knot_10_10 : KnotEntry := {
  name := "10_10"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 18, 16, 2, 20, 10, 8, 6] }
  pd_notation_str := "[[1,11,2,10],[3,18,4,19],[5,16,6,17],[7,14,8,15],[9,13,10,12],[11,3,12,2],[13,20,14,1],[15,6,16,7],[17,4,18,5],[19,8,20,9]]"
  jones_known := some "-t^(-7)+ 2*t^(-6)-3*t^(-5)+ 5*t^(-4)-6*t^(-3)+ 7*t^(-2)-7*t^(-1)+ 6-4*t+ 3*t^2-t^3"
  alternating := true
}

def knot_10_11 : KnotEntry := {
  name := "10_11"
  crossings := 10
  dt_code := { codes := [6, 14, 12, 18, 20, 16, 4, 2, 10, 8] }
  pd_notation_str := "[[2,15,3,16],[4,13,5,14],[6,2,7,1],[8,18,9,17],[10,20,11,19],[12,5,13,6],[14,3,15,4],[16,12,17,11],[18,10,19,9],[20,8,1,7]]"
  jones_known := some "t^(-3)-t^(-2)+ 3*t^(-1)-5+ 6*t-7*t^2+ 7*t^3-6*t^4+ 4*t^5-2*t^6+ t^7"
  alternating := true
}

def knot_10_12 : KnotEntry := {
  name := "10_12"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 16, 2, 20, 18, 6, 8, 12] }
  pd_notation_str := "[[2,11,3,12],[4,18,5,17],[6,13,7,14],[8,19,9,20],[10,1,11,2],[12,7,13,8],[14,5,15,6],[16,4,17,3],[18,16,19,15],[20,9,1,10]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-4*t^(-6)+ 6*t^(-5)-7*t^(-4)+ 8*t^(-3)-7*t^(-2)+ 6*t^(-1)-3+ 2*t-t^2"
  alternating := true
}

def knot_10_13 : KnotEntry := {
  name := "10_13"
  crossings := 10
  dt_code := { codes := [4, 10, 18, 16, 12, 2, 20, 8, 6, 14] }
  pd_notation_str := "[[2,17,3,18],[4,8,5,7],[6,13,7,14],[8,2,9,1],[10,20,11,19],[12,16,13,15],[14,5,15,6],[16,3,17,4],[18,12,19,11],[20,10,1,9]]"
  jones_known := some "t^(-4)-2*t^(-3)+ 5*t^(-2)-7*t^(-1)+ 8-9*t+ 8*t^2-6*t^3+ 4*t^4-2*t^5+ t^6"
  alternating := true
}

def knot_10_14 : KnotEntry := {
  name := "10_14"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 16, 18, 2, 20, 6, 8, 14] }
  pd_notation_str := "[[1,14,2,15],[3,17,4,16],[5,11,6,10],[7,19,8,18],[9,1,10,20],[11,5,12,4],[13,2,14,3],[15,13,16,12],[17,7,18,6],[19,9,20,8]]"
  jones_known := some "1-2*t+ 4*t^2-6*t^3+ 9*t^4-9*t^5+ 9*t^6-8*t^7+ 5*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_10_15 : KnotEntry := {
  name := "10_15"
  crossings := 10
  dt_code := { codes := [4, 12, 16, 18, 14, 2, 10, 20, 6, 8] }
  pd_notation_str := "[[2,6,3,5],[4,16,5,15],[6,2,7,1],[8,17,9,18],[10,19,11,20],[12,7,13,8],[14,4,15,3],[16,14,17,13],[18,9,19,10],[20,11,1,12]]"
  jones_known := some "-t^(-6)+ 2*t^(-5)-4*t^(-4)+ 6*t^(-3)-6*t^(-2)+ 7*t^(-1)-6+ 5*t-3*t^2+ 2*t^3-t^4"
  alternating := true
}

def knot_10_16 : KnotEntry := {
  name := "10_16"
  crossings := 10
  dt_code := { codes := [6, 14, 12, 16, 18, 20, 4, 2, 10, 8] }
  pd_notation_str := "[[1,10,2,11],[3,15,4,14],[5,17,6,16],[7,19,8,18],[9,2,10,3],[11,20,12,1],[13,9,14,8],[15,7,16,6],[17,5,18,4],[19,12,20,13]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 4*t^(-1)-5+ 7*t-8*t^2+ 7*t^3-6*t^4+ 4*t^5-2*t^6+ t^7"
  alternating := true
}

def knot_10_17 : KnotEntry := {
  name := "10_17"
  crossings := 10
  dt_code := { codes := [6, 12, 14, 16, 18, 2, 4, 20, 8, 10] }
  pd_notation_str := "[[6,2,7,1],[12,4,13,3],[20,15,1,16],[16,7,17,8],[18,9,19,10],[8,17,9,18],[10,19,11,20],[14,6,15,5],[2,12,3,11],[4,14,5,13]]"
  jones_known := some "-t^(-5)+ 2*t^(-4)-3*t^(-3)+ 5*t^(-2)-6*t^(-1)+ 7-6*t+ 5*t^2-3*t^3+ 2*t^4-t^5"
  alternating := true
}

def knot_10_18 : KnotEntry := {
  name := "10_18"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 18, 16, 2, 10, 20, 8, 6] }
  pd_notation_str := "[[2,14,3,13],[4,10,5,9],[6,17,7,18],[8,15,9,16],[10,20,11,19],[12,2,13,1],[14,12,15,11],[16,7,17,8],[18,5,19,6],[20,4,1,3]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 4*t^(-1)-6+ 8*t-9*t^2+ 9*t^3-7*t^4+ 5*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_10_19 : KnotEntry := {
  name := "10_19"
  crossings := 10
  dt_code := { codes := [6, 12, 14, 16, 18, 2, 4, 20, 10, 8] }
  pd_notation_str := "[[1,13,2,12],[3,15,4,14],[5,10,6,11],[7,16,8,17],[9,18,10,19],[11,1,12,20],[13,3,14,2],[15,8,16,9],[17,6,18,7],[19,5,20,4]]"
  jones_known := some "-t^(-4)+ 2*t^(-3)-3*t^(-2)+ 6*t^(-1)-7+ 8*t-8*t^2+ 7*t^3-5*t^4+ 3*t^5-t^6"
  alternating := true
}

def knot_10_20 : KnotEntry := {
  name := "10_20"
  crossings := 10
  dt_code := { codes := [4, 12, 18, 20, 16, 14, 2, 10, 8, 6] }
  pd_notation_str := "[[2,8,3,7],[4,15,5,16],[6,4,7,3],[8,2,9,1],[10,18,11,17],[12,20,13,19],[14,5,15,6],[16,14,17,13],[18,12,19,11],[20,10,1,9]]"
  jones_known := some "t^(-1)-1+ 3*t-4*t^2+ 5*t^3-6*t^4+ 5*t^5-4*t^6+ 3*t^7-2*t^8+ t^9"
  alternating := true
}

def knot_10_21 : KnotEntry := {
  name := "10_21"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 16, 18, 20, 2, 6, 10, 8] }
  pd_notation_str := "[[1,15,2,14],[3,13,4,12],[5,17,6,16],[7,11,8,10],[9,18,10,19],[11,1,12,20],[13,3,14,2],[15,5,16,4],[17,7,18,6],[19,8,20,9]]"
  jones_known := some "1-2*t+ 4*t^2-5*t^3+ 7*t^4-7*t^5+ 7*t^6-6*t^7+ 3*t^8-2*t^9+ t^10"
  alternating := true
}

def knot_10_22 : KnotEntry := {
  name := "10_22"
  crossings := 10
  dt_code := { codes := [6, 12, 14, 18, 20, 16, 4, 2, 10, 8] }
  pd_notation_str := "[[2,11,3,12],[4,18,5,17],[6,16,7,15],[8,14,9,13],[10,1,11,2],[12,19,13,20],[14,6,15,5],[16,8,17,7],[18,4,19,3],[20,9,1,10]]"
  jones_known := some "t^(-4)-2*t^(-3)+ 4*t^(-2)-6*t^(-1)+ 8-8*t+ 7*t^2-6*t^3+ 4*t^4-2*t^5+ t^6"
  alternating := true
}

def knot_10_23 : KnotEntry := {
  name := "10_23"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 16, 18, 2, 20, 6, 10, 8] }
  pd_notation_str := "[[2,13,3,14],[4,11,5,12],[6,18,7,17],[8,19,9,20],[10,1,11,2],[12,3,13,4],[14,7,15,8],[16,6,17,5],[18,16,19,15],[20,9,1,10]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-4*t^(-6)+ 7*t^(-5)-9*t^(-4)+ 10*t^(-3)-9*t^(-2)+ 8*t^(-1)-5+ 3*t-t^2"
  alternating := true
}

def knot_10_24 : KnotEntry := {
  name := "10_24"
  crossings := 10
  dt_code := { codes := [4, 12, 16, 18, 20, 14, 2, 10, 8, 6] }
  pd_notation_str := "[[2,14,3,13],[4,10,5,9],[6,17,7,18],[8,6,9,5],[10,4,11,3],[12,20,13,19],[14,2,15,1],[16,7,17,8],[18,12,19,11],[20,16,1,15]]"
  jones_known := some "t^(-1)-2+ 5*t-7*t^2+ 9*t^3-9*t^4+ 8*t^5-7*t^6+ 4*t^7-2*t^8+ t^9"
  alternating := true
}

def knot_10_25 : KnotEntry := {
  name := "10_25"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 16, 18, 20, 2, 10, 8, 6] }
  pd_notation_str := "[[1,11,2,10],[3,15,4,14],[5,13,6,12],[7,18,8,19],[9,1,10,20],[11,5,12,4],[13,7,14,6],[15,3,16,2],[17,8,18,9],[19,17,20,16]]"
  jones_known := some "1-2*t+ 5*t^2-7*t^3+ 10*t^4-11*t^5+ 10*t^6-9*t^7+ 6*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_10_26 : KnotEntry := {
  name := "10_26"
  crossings := 10
  dt_code := { codes := [6, 12, 14, 16, 18, 20, 4, 2, 10, 8] }
  pd_notation_str := "[[1,12,2,13],[3,14,4,15],[5,17,6,16],[7,19,8,18],[9,1,10,20],[11,4,12,5],[13,2,14,3],[15,11,16,10],[17,9,18,8],[19,7,20,6]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 6*t^(-2)-8*t^(-1)+ 10-10*t+ 9*t^2-7*t^3+ 4*t^4-2*t^5+ t^6"
  alternating := true
}

def knot_10_27 : KnotEntry := {
  name := "10_27"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 16, 18, 2, 20, 10, 8, 6] }
  pd_notation_str := "[[1,11,2,10],[3,18,4,19],[5,16,6,17],[7,14,8,15],[9,13,10,12],[11,3,12,2],[13,20,14,1],[15,4,16,5],[17,6,18,7],[19,8,20,9]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-6*t^(-6)+ 9*t^(-5)-11*t^(-4)+ 12*t^(-3)-11*t^(-2)+ 9*t^(-1)-5+ 3*t-t^2"
  alternating := true
}

def knot_10_28 : KnotEntry := {
  name := "10_28"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 16, 2, 20, 18, 8, 6, 12] }
  pd_notation_str := "[[1,9,2,8],[3,16,4,17],[5,14,6,15],[7,11,8,10],[9,3,10,2],[11,20,12,1],[13,18,14,19],[15,4,16,5],[17,6,18,7],[19,12,20,13]]"
  jones_known := some "-t^(-7)+ 2*t^(-6)-4*t^(-5)+ 6*t^(-4)-7*t^(-3)+ 9*t^(-2)-8*t^(-1)+ 7-5*t+ 3*t^2-t^3"
  alternating := true
}

def knot_10_29 : KnotEntry := {
  name := "10_29"
  crossings := 10
  dt_code := { codes := [4, 10, 16, 18, 12, 2, 20, 8, 6, 14] }
  pd_notation_str := "[[2,15,3,16],[4,2,5,1],[6,11,7,12],[8,18,9,17],[10,20,11,19],[12,5,13,6],[14,3,15,4],[16,14,17,13],[18,10,19,9],[20,8,1,7]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 5*t^(-1)-7+ 9*t-11*t^2+ 10*t^3-8*t^4+ 6*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_10_30 : KnotEntry := {
  name := "10_30"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 16, 18, 2, 20, 8, 6, 14] }
  pd_notation_str := "[[1,14,2,15],[3,17,4,16],[5,11,6,10],[7,19,8,18],[9,1,10,20],[11,5,12,4],[13,2,14,3],[15,13,16,12],[17,9,18,8],[19,7,20,6]]"
  jones_known := some "t^(-1)-3+ 6*t-8*t^2+ 11*t^3-11*t^4+ 10*t^5-8*t^6+ 5*t^7-3*t^8+ t^9"
  alternating := true
}

def knot_10_31 : KnotEntry := {
  name := "10_31"
  crossings := 10
  dt_code := { codes := [4, 12, 16, 18, 14, 2, 10, 20, 8, 6] }
  pd_notation_str := "[[2,6,3,5],[4,16,5,15],[6,2,7,1],[8,17,9,18],[10,19,11,20],[12,7,13,8],[14,4,15,3],[16,14,17,13],[18,11,19,12],[20,9,1,10]]"
  jones_known := some "-t^(-5)+ 2*t^(-4)-4*t^(-3)+ 7*t^(-2)-8*t^(-1)+ 10-9*t+ 7*t^2-5*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_32 : KnotEntry := {
  name := "10_32"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 16, 18, 2, 10, 20, 8, 6] }
  pd_notation_str := "[[2,14,3,13],[4,10,5,9],[6,15,7,16],[8,17,9,18],[10,20,11,19],[12,2,13,1],[14,12,15,11],[16,7,17,8],[18,5,19,6],[20,4,1,3]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 6*t^(-2)-9*t^(-1)+ 11-11*t+ 11*t^2-8*t^3+ 5*t^4-3*t^5+ t^6"
  alternating := true
}

def knot_10_33 : KnotEntry := {
  name := "10_33"
  crossings := 10
  dt_code := { codes := [6, 12, 14, 16, 18, 4, 2, 20, 10, 8] }
  pd_notation_str := "[[6,2,7,1],[14,6,15,5],[20,15,1,16],[16,7,17,8],[8,19,9,20],[18,9,19,10],[10,17,11,18],[2,14,3,13],[12,4,13,3],[4,12,5,11]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-5*t^(-3)+ 8*t^(-2)-10*t^(-1)+ 11-10*t+ 8*t^2-5*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_34 : KnotEntry := {
  name := "10_34"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, 20, 18, 16, 6, 12, 10] }
  pd_notation_str := "[[1,7,2,6],[3,14,4,15],[5,9,6,8],[7,3,8,2],[9,20,10,1],[11,18,12,19],[13,16,14,17],[15,4,16,5],[17,12,18,13],[19,10,20,11]]"
  jones_known := some "-t^(-7)+ 2*t^(-6)-3*t^(-5)+ 4*t^(-4)-5*t^(-3)+ 6*t^(-2)-5*t^(-1)+ 5-3*t+ 2*t^2-t^3"
  alternating := true
}

def knot_10_35 : KnotEntry := {
  name := "10_35"
  crossings := 10
  dt_code := { codes := [4, 8, 16, 10, 2, 20, 18, 6, 14, 12] }
  pd_notation_str := "[[1,11,2,10],[3,18,4,19],[5,3,6,2],[7,14,8,15],[9,12,10,13],[11,1,12,20],[13,8,14,9],[15,6,16,7],[17,4,18,5],[19,17,20,16]]"
  jones_known := some "t^(-6)-2*t^(-5)+ 4*t^(-4)-6*t^(-3)+ 7*t^(-2)-8*t^(-1)+ 8-6*t+ 4*t^2-2*t^3+ t^4"
  alternating := true
}

def knot_10_36 : KnotEntry := {
  name := "10_36"
  crossings := 10
  dt_code := { codes := [4, 8, 10, 16, 2, 20, 18, 6, 14, 12] }
  pd_notation_str := "[[2,15,3,16],[4,14,5,13],[6,12,7,11],[8,18,9,17],[10,8,11,7],[12,6,13,5],[14,20,15,19],[16,1,17,2],[18,10,19,9],[20,4,1,3]]"
  jones_known := some "t^(-1)-2+ 4*t-6*t^2+ 8*t^3-8*t^4+ 8*t^5-6*t^6+ 4*t^7-3*t^8+ t^9"
  alternating := true
}

def knot_10_37 : KnotEntry := {
  name := "10_37"
  crossings := 10
  dt_code := { codes := [4, 10, 16, 12, 2, 8, 20, 18, 6, 14] }
  pd_notation_str := "[[4,2,5,1],[10,4,11,3],[12,8,13,7],[8,12,9,11],[18,15,19,16],[16,5,17,6],[6,17,7,18],[20,13,1,14],[14,19,15,20],[2,10,3,9]]"
  jones_known := some "-t^(-5)+ 2*t^(-4)-4*t^(-3)+ 7*t^(-2)-8*t^(-1)+ 9-8*t+ 7*t^2-4*t^3+ 2*t^4-t^5"
  alternating := true
}

def knot_10_38 : KnotEntry := {
  name := "10_38"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 16, 2, 8, 20, 18, 6, 14] }
  pd_notation_str := "[[2,16,3,15],[4,12,5,11],[6,10,7,9],[8,17,9,18],[10,6,11,5],[12,20,13,19],[14,2,15,1],[16,14,17,13],[18,7,19,8],[20,4,1,3]]"
  jones_known := some "t^(-1)-2+ 5*t-7*t^2+ 9*t^3-10*t^4+ 9*t^5-7*t^6+ 5*t^7-3*t^8+ t^9"
  alternating := true
}

def knot_10_39 : KnotEntry := {
  name := "10_39"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 14, 18, 2, 6, 20, 8, 16] }
  pd_notation_str := "[[1,14,2,15],[3,17,4,16],[5,19,6,18],[7,11,8,10],[9,1,10,20],[11,7,12,6],[13,2,14,3],[15,13,16,12],[17,5,18,4],[19,9,20,8]]"
  jones_known := some "1-2*t+ 5*t^2-7*t^3+ 9*t^4-10*t^5+ 10*t^6-8*t^7+ 5*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_10_40 : KnotEntry := {
  name := "10_40"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 16, 2, 20, 6, 18, 8, 14] }
  pd_notation_str := "[[2,11,3,12],[4,18,5,17],[6,19,7,20],[8,13,9,14],[10,1,11,2],[12,9,13,10],[14,5,15,6],[16,4,17,3],[18,16,19,15],[20,7,1,8]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-6*t^(-6)+ 9*t^(-5)-12*t^(-4)+ 13*t^(-3)-11*t^(-2)+ 10*t^(-1)-6+ 3*t-t^2"
  alternating := true
}

def knot_10_41 : KnotEntry := {
  name := "10_41"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 16, 20, 2, 8, 18, 6, 14] }
  pd_notation_str := "[[1,14,2,15],[3,17,4,16],[5,10,6,11],[7,19,8,18],[9,6,10,7],[11,1,12,20],[13,2,14,3],[15,13,16,12],[17,9,18,8],[19,5,20,4]]"
  jones_known := some "t^(-3)-3*t^(-2)+ 6*t^(-1)-8+ 11*t-12*t^2+ 11*t^3-9*t^4+ 6*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_10_42 : KnotEntry := {
  name := "10_42"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 16, 2, 20, 8, 18, 6, 14] }
  pd_notation_str := "[[1,9,2,8],[3,18,4,19],[5,14,6,15],[7,11,8,10],[9,3,10,2],[11,20,12,1],[13,17,14,16],[15,4,16,5],[17,13,18,12],[19,6,20,7]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-6*t^(-3)+ 10*t^(-2)-12*t^(-1)+ 14-13*t+ 10*t^2-7*t^3+ 4*t^4-t^5"
  alternating := true
}

def knot_10_43 : KnotEntry := {
  name := "10_43"
  crossings := 10
  dt_code := { codes := [4, 10, 16, 14, 2, 20, 8, 18, 6, 12] }
  pd_notation_str := "[[4,2,5,1],[10,4,11,3],[14,8,15,7],[20,11,1,12],[12,19,13,20],[8,14,9,13],[18,15,19,16],[16,5,17,6],[6,17,7,18],[2,10,3,9]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-6*t^(-3)+ 9*t^(-2)-11*t^(-1)+ 13-11*t+ 9*t^2-6*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_44 : KnotEntry := {
  name := "10_44"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 16, 14, 2, 20, 18, 8, 6] }
  pd_notation_str := "[[1,14,2,15],[3,17,4,16],[5,20,6,1],[7,19,8,18],[9,7,10,6],[11,5,12,4],[13,2,14,3],[15,13,16,12],[17,10,18,11],[19,9,20,8]]"
  jones_known := some "t^(-3)-3*t^(-2)+ 6*t^(-1)-9+ 12*t-13*t^2+ 13*t^3-10*t^4+ 7*t^5-4*t^6+ t^7"
  alternating := true
}

def knot_10_45 : KnotEntry := {
  name := "10_45"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 14, 16, 2, 20, 18, 8, 6] }
  pd_notation_str := "[[4,2,5,1],[12,6,13,5],[10,3,11,4],[2,11,3,12],[20,14,1,13],[14,7,15,8],[6,19,7,20],[18,15,19,16],[16,10,17,9],[8,18,9,17]]"
  jones_known := some "-t^(-5)+ 4*t^(-4)-7*t^(-3)+ 11*t^(-2)-14*t^(-1)+ 15-14*t+ 11*t^2-7*t^3+ 4*t^4-t^5"
  alternating := true
}

def knot_10_46 : KnotEntry := {
  name := "10_46"
  crossings := 10
  dt_code := { codes := [6, 8, 14, 2, 16, 18, 20, 4, 10, 12] }
  pd_notation_str := "[[1,15,2,14],[3,9,4,8],[5,11,6,10],[7,16,8,17],[9,5,10,4],[11,19,12,18],[13,1,14,20],[15,3,16,2],[17,6,18,7],[19,13,20,12]]"
  jones_known := some "t-t^2+ 3*t^3-3*t^4+ 4*t^5-5*t^6+ 4*t^7-4*t^8+ 3*t^9-2*t^10+ t^11"
  alternating := true
}

def knot_10_47 : KnotEntry := {
  name := "10_47"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, 16, 18, 20, 6, 10, 12] }
  pd_notation_str := "[[2,9,3,10],[4,11,5,12],[6,17,7,18],[8,1,9,2],[10,3,11,4],[12,5,13,6],[14,20,15,19],[16,14,17,13],[18,7,19,8],[20,16,1,15]]"
  jones_known := some "-t^(-9)+ 2*t^(-8)-4*t^(-7)+ 5*t^(-6)-6*t^(-5)+ 7*t^(-4)-5*t^(-3)+ 5*t^(-2)-3*t^(-1)+ 2-t"
  alternating := true
}

def knot_10_48 : KnotEntry := {
  name := "10_48"
  crossings := 10
  dt_code := { codes := [6, 8, 14, 2, 16, 18, 4, 20, 10, 12] }
  pd_notation_str := "[[6,2,7,1],[8,4,9,3],[14,6,15,5],[20,15,1,16],[16,9,17,10],[18,11,19,12],[10,17,11,18],[12,19,13,20],[2,8,3,7],[4,14,5,13]]"
  jones_known := some "-t^(-5)+ 2*t^(-4)-4*t^(-3)+ 6*t^(-2)-7*t^(-1)+ 9-7*t+ 6*t^2-4*t^3+ 2*t^4-t^5"
  alternating := true
}

def knot_10_49 : KnotEntry := {
  name := "10_49"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, 16, 18, 6, 20, 10, 12] }
  pd_notation_str := "[[1,7,2,6],[3,17,4,16],[5,9,6,8],[7,3,8,2],[9,15,10,14],[11,19,12,18],[13,1,14,20],[15,5,16,4],[17,11,18,10],[19,13,20,12]]"
  jones_known := some "t^3-2*t^4+ 5*t^5-6*t^6+ 9*t^7-10*t^8+ 9*t^9-8*t^10+ 5*t^11-3*t^12+ t^13"
  alternating := true
}

def knot_10_50 : KnotEntry := {
  name := "10_50"
  crossings := 10
  dt_code := { codes := [6, 8, 14, 2, 16, 18, 20, 4, 12, 10] }
  pd_notation_str := "[[1,10,2,11],[3,19,4,18],[5,13,6,12],[7,15,8,14],[9,17,10,16],[11,20,12,1],[13,9,14,8],[15,7,16,6],[17,3,18,2],[19,5,20,4]]"
  jones_known := some "1-2*t+ 5*t^2-6*t^3+ 8*t^4-9*t^5+ 8*t^6-7*t^7+ 4*t^8-2*t^9+ t^10"
  alternating := true
}

def knot_10_51 : KnotEntry := {
  name := "10_51"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, 16, 18, 20, 6, 12, 10] }
  pd_notation_str := "[[2,18,3,17],[4,11,5,12],[6,13,7,14],[8,15,9,16],[10,19,11,20],[12,7,13,8],[14,5,15,6],[16,2,17,1],[18,9,19,10],[20,4,1,3]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-5*t^(-6)+ 8*t^(-5)-10*t^(-4)+ 12*t^(-3)-10*t^(-2)+ 9*t^(-1)-6+ 3*t-t^2"
  alternating := true
}

def knot_10_52 : KnotEntry := {
  name := "10_52"
  crossings := 10
  dt_code := { codes := [6, 8, 14, 2, 16, 18, 4, 20, 12, 10] }
  pd_notation_str := "[[1,13,2,12],[3,19,4,18],[5,10,6,11],[7,14,8,15],[9,16,10,17],[11,1,12,20],[13,8,14,9],[15,6,16,7],[17,3,18,2],[19,5,20,4]]"
  jones_known := some "-t^(-4)+ 2*t^(-3)-4*t^(-2)+ 7*t^(-1)-8+ 10*t-9*t^2+ 8*t^3-6*t^4+ 3*t^5-t^6"
  alternating := true
}

def knot_10_53 : KnotEntry := {
  name := "10_53"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, 16, 18, 6, 20, 12, 10] }
  pd_notation_str := "[[1,7,2,6],[3,17,4,16],[5,9,6,8],[7,3,8,2],[9,15,10,14],[11,19,12,18],[13,1,14,20],[15,5,16,4],[17,13,18,12],[19,11,20,10]]"
  jones_known := some "t^2-3*t^3+ 7*t^4-9*t^5+ 12*t^6-12*t^7+ 11*t^8-9*t^9+ 5*t^10-3*t^11+ t^12"
  alternating := true
}

def knot_10_54 : KnotEntry := {
  name := "10_54"
  crossings := 10
  dt_code := { codes := [4, 10, 16, 12, 2, 8, 18, 20, 6, 14] }
  pd_notation_str := "[[2,16,3,15],[4,9,5,10],[6,11,7,12],[8,19,9,20],[10,5,11,6],[12,18,13,17],[14,2,15,1],[16,14,17,13],[18,7,19,8],[20,4,1,3]]"
  jones_known := some "-t^(-6)+ 2*t^(-5)-4*t^(-4)+ 6*t^(-3)-7*t^(-2)+ 8*t^(-1)-6+ 6*t-4*t^2+ 2*t^3-t^4"
  alternating := true
}

def knot_10_55 : KnotEntry := {
  name := "10_55"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 2, 16, 6, 20, 18, 10, 14] }
  pd_notation_str := "[[2,10,3,9],[4,18,5,17],[6,12,7,11],[8,2,9,1],[10,8,11,7],[12,6,13,5],[14,20,15,19],[16,14,17,13],[18,4,19,3],[20,16,1,15]]"
  jones_known := some "t^2-2*t^3+ 5*t^4-7*t^5+ 10*t^6-10*t^7+ 9*t^8-8*t^9+ 5*t^10-3*t^11+ t^12"
  alternating := true
}

def knot_10_56 : KnotEntry := {
  name := "10_56"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 16, 2, 8, 18, 20, 6, 14] }
  pd_notation_str := "[[2,16,3,15],[4,10,5,9],[6,12,7,11],[8,17,9,18],[10,6,11,5],[12,20,13,19],[14,2,15,1],[16,14,17,13],[18,7,19,8],[20,4,1,3]]"
  jones_known := some "1-2*t+ 5*t^2-7*t^3+ 10*t^4-11*t^5+ 10*t^6-9*t^7+ 6*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_10_57 : KnotEntry := {
  name := "10_57"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 2, 14, 18, 6, 20, 10, 16] }
  pd_notation_str := "[[1,4,2,5],[3,16,4,17],[5,20,6,1],[7,13,8,12],[9,7,10,6],[11,18,12,19],[13,9,14,8],[15,2,16,3],[17,10,18,11],[19,14,20,15]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-7*t^(-6)+ 10*t^(-5)-12*t^(-4)+ 14*t^(-3)-12*t^(-2)+ 10*t^(-1)-6+ 3*t-t^2"
  alternating := true
}

def knot_10_58 : KnotEntry := {
  name := "10_58"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 10, 2, 18, 6, 20, 12, 16] }
  pd_notation_str := "[[2,15,3,16],[4,10,5,9],[6,13,7,14],[8,6,9,5],[10,20,11,19],[12,7,13,8],[14,18,15,17],[16,1,17,2],[18,12,19,11],[20,4,1,3]]"
  jones_known := some "t^(-4)-2*t^(-3)+ 5*t^(-2)-8*t^(-1)+ 10-11*t+ 10*t^2-8*t^3+ 6*t^4-3*t^5+ t^6"
  alternating := true
}

def knot_10_59 : KnotEntry := {
  name := "10_59"
  crossings := 10
  dt_code := { codes := [4, 8, 10, 14, 2, 18, 6, 20, 12, 16] }
  pd_notation_str := "[[1,4,2,5],[3,17,4,16],[5,20,6,1],[7,14,8,15],[9,7,10,6],[11,19,12,18],[13,8,14,9],[15,11,16,10],[17,3,18,2],[19,13,20,12]]"
  jones_known := some "t^(-3)-3*t^(-2)+ 6*t^(-1)-9+ 12*t-12*t^2+ 12*t^3-10*t^4+ 6*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_10_60 : KnotEntry := {
  name := "10_60"
  crossings := 10
  dt_code := { codes := [4, 8, 10, 14, 2, 16, 18, 6, 20, 12] }
  pd_notation_str := "[[2,15,3,16],[4,8,5,7],[6,11,7,12],[8,14,9,13],[10,17,11,18],[12,5,13,6],[14,20,15,19],[16,1,17,2],[18,9,19,10],[20,4,1,3]]"
  jones_known := some "t^(-6)-3*t^(-5)+ 6*t^(-4)-10*t^(-3)+ 13*t^(-2)-14*t^(-1)+ 14-11*t+ 8*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_10_61 : KnotEntry := {
  name := "10_61"
  crossings := 10
  dt_code := { codes := [8, 10, 16, 14, 2, 18, 20, 6, 4, 12] }
  pd_notation_str := "[[1,9,2,8],[3,16,4,17],[5,14,6,15],[7,1,8,20],[9,3,10,2],[11,19,12,18],[13,6,14,7],[15,4,16,5],[17,11,18,10],[19,13,20,12]]"
  jones_known := some "t^(-2)-t^(-1)+ 3-4*t+ 4*t^2-5*t^3+ 5*t^4-4*t^5+ 3*t^6-2*t^7+ t^8"
  alternating := true
}

def knot_10_62 : KnotEntry := {
  name := "10_62"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 16, 2, 18, 20, 6, 8, 12] }
  pd_notation_str := "[[2,11,3,12],[4,18,5,17],[6,13,7,14],[8,19,9,20],[10,1,11,2],[12,5,13,6],[14,7,15,8],[16,4,17,3],[18,16,19,15],[20,9,1,10]]"
  jones_known := some "-t^(-9)+ 2*t^(-8)-4*t^(-7)+ 6*t^(-6)-7*t^(-5)+ 7*t^(-4)-6*t^(-3)+ 6*t^(-2)-3*t^(-1)+ 2-t"
  alternating := true
}

def knot_10_63 : KnotEntry := {
  name := "10_63"
  crossings := 10
  dt_code := { codes := [4, 10, 16, 14, 2, 18, 8, 6, 20, 12] }
  pd_notation_str := "[[1,9,2,8],[3,19,4,18],[5,17,6,16],[7,11,8,10],[9,3,10,2],[11,15,12,14],[13,1,14,20],[15,7,16,6],[17,5,18,4],[19,13,20,12]]"
  jones_known := some "t^2-2*t^3+ 5*t^4-7*t^5+ 9*t^6-9*t^7+ 9*t^8-7*t^9+ 4*t^10-3*t^11+ t^12"
  alternating := true
}

def knot_10_64 : KnotEntry := {
  name := "10_64"
  crossings := 10
  dt_code := { codes := [8, 10, 14, 16, 2, 18, 20, 6, 4, 12] }
  pd_notation_str := "[[2,11,3,12],[4,18,5,17],[6,14,7,13],[8,16,9,15],[10,1,11,2],[12,19,13,20],[14,8,15,7],[16,4,17,3],[18,6,19,5],[20,9,1,10]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 4*t^(-1)-6+ 8*t-8*t^2+ 8*t^3-7*t^4+ 4*t^5-2*t^6+ t^7"
  alternating := true
}

def knot_10_65 : KnotEntry := {
  name := "10_65"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 16, 2, 18, 20, 8, 6, 12] }
  pd_notation_str := "[[1,9,2,8],[3,16,4,17],[5,14,6,15],[7,11,8,10],[9,3,10,2],[11,18,12,19],[13,20,14,1],[15,4,16,5],[17,6,18,7],[19,12,20,13]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-5*t^(-6)+ 8*t^(-5)-9*t^(-4)+ 11*t^(-3)-10*t^(-2)+ 8*t^(-1)-5+ 3*t-t^2"
  alternating := true
}

def knot_10_66 : KnotEntry := {
  name := "10_66"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 16, 2, 18, 8, 6, 20, 12] }
  pd_notation_str := "[[1,11,2,10],[3,13,4,12],[5,19,6,18],[7,15,8,14],[9,5,10,4],[11,3,12,2],[13,17,14,16],[15,9,16,8],[17,1,18,20],[19,7,20,6]]"
  jones_known := some "t^3-2*t^4+ 6*t^5-8*t^6+ 11*t^7-13*t^8+ 12*t^9-10*t^10+ 7*t^11-4*t^12+ t^13"
  alternating := true
}

def knot_10_67 : KnotEntry := {
  name := "10_67"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 12, 18, 2, 6, 20, 8, 16] }
  pd_notation_str := "[[1,14,2,15],[3,19,4,18],[5,17,6,16],[7,11,8,10],[9,1,10,20],[11,7,12,6],[13,2,14,3],[15,13,16,12],[17,5,18,4],[19,9,20,8]]"
  jones_known := some "t^(-1)-2+ 5*t-8*t^2+ 10*t^3-10*t^4+ 10*t^5-8*t^6+ 5*t^7-3*t^8+ t^9"
  alternating := true
}

def knot_10_68 : KnotEntry := {
  name := "10_68"
  crossings := 10
  dt_code := { codes := [4, 12, 16, 14, 18, 2, 20, 6, 10, 8] }
  pd_notation_str := "[[1,11,2,10],[3,16,4,17],[5,14,6,15],[7,18,8,19],[9,13,10,12],[11,3,12,2],[13,20,14,1],[15,4,16,5],[17,8,18,9],[19,6,20,7]]"
  jones_known := some "-t^(-7)+ 2*t^(-6)-4*t^(-5)+ 7*t^(-4)-8*t^(-3)+ 9*t^(-2)-9*t^(-1)+ 8-5*t+ 3*t^2-t^3"
  alternating := true
}

def knot_10_69 : KnotEntry := {
  name := "10_69"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 12, 18, 2, 16, 6, 20, 8] }
  pd_notation_str := "[[2,13,3,14],[4,17,5,18],[6,2,7,1],[8,19,9,20],[10,7,11,8],[12,3,13,4],[14,12,15,11],[16,5,17,6],[18,16,19,15],[20,9,1,10]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-7*t^(-6)+ 11*t^(-5)-13*t^(-4)+ 15*t^(-3)-14*t^(-2)+ 11*t^(-1)-7+ 4*t-t^2"
  alternating := true
}

def knot_10_70 : KnotEntry := {
  name := "10_70"
  crossings := 10
  dt_code := { codes := [4, 8, 16, 10, 2, 18, 20, 6, 14, 12] }
  pd_notation_str := "[[2,15,3,16],[4,11,5,12],[6,13,7,14],[8,20,9,19],[10,7,11,8],[12,5,13,6],[14,18,15,17],[16,1,17,2],[18,10,19,9],[20,4,1,3]]"
  jones_known := some "t^(-7)-3*t^(-6)+ 6*t^(-5)-9*t^(-4)+ 11*t^(-3)-11*t^(-2)+ 10*t^(-1)-8+ 5*t-2*t^2+ t^3"
  alternating := true
}

def knot_10_71 : KnotEntry := {
  name := "10_71"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 2, 18, 14, 6, 20, 10, 16] }
  pd_notation_str := "[[1,4,2,5],[3,8,4,9],[11,15,12,14],[5,13,6,12],[13,7,14,6],[9,19,10,18],[15,20,16,1],[19,16,20,17],[17,11,18,10],[7,2,8,3]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-6*t^(-3)+ 10*t^(-2)-12*t^(-1)+ 13-12*t+ 10*t^2-6*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_72 : KnotEntry := {
  name := "10_72"
  crossings := 10
  dt_code := { codes := [4, 8, 10, 16, 2, 18, 20, 6, 14, 12] }
  pd_notation_str := "[[2,15,3,16],[4,12,5,11],[6,14,7,13],[8,18,9,17],[10,8,11,7],[12,6,13,5],[14,20,15,19],[16,1,17,2],[18,10,19,9],[20,4,1,3]]"
  jones_known := some "1-2*t+ 5*t^2-8*t^3+ 11*t^4-12*t^5+ 12*t^6-10*t^7+ 7*t^8-4*t^9+ t^10"
  alternating := true
}

def knot_10_73 : KnotEntry := {
  name := "10_73"
  crossings := 10
  dt_code := { codes := [4, 8, 10, 14, 2, 18, 16, 6, 20, 12] }
  pd_notation_str := "[[2,15,3,16],[4,7,5,8],[6,13,7,14],[8,12,9,11],[10,17,11,18],[12,5,13,6],[14,20,15,19],[16,1,17,2],[18,9,19,10],[20,4,1,3]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-6*t^(-6)+ 10*t^(-5)-13*t^(-4)+ 14*t^(-3)-13*t^(-2)+ 11*t^(-1)-7+ 4*t-t^2"
  alternating := true
}

def knot_10_74 : KnotEntry := {
  name := "10_74"
  crossings := 10
  dt_code := { codes := [4, 12, 14, 16, 20, 18, 2, 8, 6, 10] }
  pd_notation_str := "[[1,12,2,13],[3,15,4,14],[5,17,6,16],[7,1,8,20],[9,19,10,18],[11,2,12,3],[13,11,14,10],[15,7,16,6],[17,5,18,4],[19,9,20,8]]"
  jones_known := some "t^(-1)-3+ 6*t-8*t^2+ 11*t^3-10*t^4+ 9*t^5-8*t^6+ 4*t^7-2*t^8+ t^9"
  alternating := true
}

def knot_10_75 : KnotEntry := {
  name := "10_75"
  crossings := 10
  dt_code := { codes := [4, 10, 12, 14, 18, 2, 16, 6, 20, 8] }
  pd_notation_str := "[[1,14,2,15],[3,17,4,16],[5,18,6,19],[7,5,8,4],[9,20,10,1],[11,9,12,8],[13,2,14,3],[15,13,16,12],[17,6,18,7],[19,10,20,11]]"
  jones_known := some "t^(-6)-3*t^(-5)+ 6*t^(-4)-10*t^(-3)+ 12*t^(-2)-13*t^(-1)+ 14-10*t+ 7*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_10_76 : KnotEntry := {
  name := "10_76"
  crossings := 10
  dt_code := { codes := [4, 12, 18, 20, 14, 16, 2, 10, 8, 6] }
  pd_notation_str := "[[2,11,3,12],[4,18,5,17],[6,20,7,19],[8,14,9,13],[10,16,11,15],[12,1,13,2],[14,10,15,9],[16,8,17,7],[18,6,19,5],[20,4,1,3]]"
  jones_known := some "1-t+ 4*t^2-6*t^3+ 8*t^4-10*t^5+ 9*t^6-8*t^7+ 6*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_10_77 : KnotEntry := {
  name := "10_77"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, 18, 20, 16, 6, 12, 10] }
  pd_notation_str := "[[1,7,2,6],[3,14,4,15],[5,9,6,8],[7,3,8,2],[9,18,10,19],[11,20,12,1],[13,16,14,17],[15,4,16,5],[17,12,18,13],[19,10,20,11]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-6*t^(-6)+ 8*t^(-5)-10*t^(-4)+ 11*t^(-3)-9*t^(-2)+ 8*t^(-1)-4+ 2*t-t^2"
  alternating := true
}

def knot_10_78 : KnotEntry := {
  name := "10_78"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, 18, 16, 6, 12, 20, 10] }
  pd_notation_str := "[[1,7,2,6],[3,17,4,16],[5,9,6,8],[7,3,8,2],[9,13,10,12],[11,1,12,20],[13,18,14,19],[15,5,16,4],[17,14,18,15],[19,11,20,10]]"
  jones_known := some "1-3*t+ 6*t^2-8*t^3+ 11*t^4-11*t^5+ 11*t^6-9*t^7+ 5*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_10_79 : KnotEntry := {
  name := "10_79"
  crossings := 10
  dt_code := { codes := [6, 8, 12, 2, 16, 4, 18, 20, 10, 14] }
  pd_notation_str := "[[6,2,7,1],[8,4,9,3],[12,6,13,5],[18,13,19,14],[16,9,17,10],[10,17,11,18],[20,15,1,16],[14,19,15,20],[2,8,3,7],[4,12,5,11]]"
  jones_known := some "-t^(-5)+ 2*t^(-4)-5*t^(-3)+ 8*t^(-2)-9*t^(-1)+ 11-9*t+ 8*t^2-5*t^3+ 2*t^4-t^5"
  alternating := true
}

def knot_10_80 : KnotEntry := {
  name := "10_80"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 2, 16, 6, 18, 20, 10, 14] }
  pd_notation_str := "[[1,17,2,16],[3,11,4,10],[5,19,6,18],[7,13,8,12],[9,5,10,4],[11,15,12,14],[13,9,14,8],[15,1,16,20],[17,3,18,2],[19,7,20,6]]"
  jones_known := some "t^3-2*t^4+ 6*t^5-8*t^6+ 11*t^7-12*t^8+ 11*t^9-10*t^10+ 6*t^11-3*t^12+ t^13"
  alternating := true
}

def knot_10_81 : KnotEntry := {
  name := "10_81"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 2, 16, 6, 18, 10, 20, 14] }
  pd_notation_str := "[[4,2,5,1],[8,4,9,3],[12,6,13,5],[16,9,17,10],[20,17,1,18],[18,13,19,14],[14,19,15,20],[10,15,11,16],[6,12,7,11],[2,8,3,7]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-7*t^(-3)+ 11*t^(-2)-13*t^(-1)+ 15-13*t+ 11*t^2-7*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_82 : KnotEntry := {
  name := "10_82"
  crossings := 10
  dt_code := { codes := [6, 8, 14, 16, 4, 18, 20, 2, 10, 12] }
  pd_notation_str := "[[1,12,2,13],[3,15,4,14],[5,19,6,18],[7,1,8,20],[9,2,10,3],[11,16,12,17],[13,9,14,8],[15,10,16,11],[17,5,18,4],[19,7,20,6]]"
  jones_known := some "t^(-3)-3*t^(-2)+ 5*t^(-1)-7+ 10*t-10*t^2+ 10*t^3-8*t^4+ 5*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_10_83 : KnotEntry := {
  name := "10_83"
  crossings := 10
  dt_code := { codes := [6, 8, 16, 14, 4, 18, 20, 2, 12, 10] }
  pd_notation_str := "[[2,7,3,8],[4,10,5,9],[6,1,7,2],[8,16,9,15],[10,17,11,18],[12,19,13,20],[14,6,15,5],[16,3,17,4],[18,13,19,14],[20,11,1,12]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-6*t^(-6)+ 10*t^(-5)-13*t^(-4)+ 14*t^(-3)-13*t^(-2)+ 11*t^(-1)-7+ 4*t-t^2"
  alternating := true
}

def knot_10_84 : KnotEntry := {
  name := "10_84"
  crossings := 10
  dt_code := { codes := [4, 10, 16, 14, 2, 8, 18, 20, 12, 6] }
  pd_notation_str := "[[2,10,3,9],[4,2,5,1],[6,13,7,14],[8,12,9,11],[10,4,11,3],[12,17,13,18],[14,20,15,19],[16,7,17,8],[18,6,19,5],[20,16,1,15]]"
  jones_known := some "-t^(-2)+ 3*t^(-1)-6+ 11*t-13*t^2+ 15*t^3-14*t^4+ 11*t^5-8*t^6+ 4*t^7-t^8"
  alternating := true
}

def knot_10_85 : KnotEntry := {
  name := "10_85"
  crossings := 10
  dt_code := { codes := [6, 8, 16, 14, 4, 18, 20, 2, 10, 12] }
  pd_notation_str := "[[2,7,3,8],[4,10,5,9],[6,1,7,2],[8,16,9,15],[10,17,11,18],[12,19,13,20],[14,6,15,5],[16,3,17,4],[18,11,19,12],[20,13,1,14]]"
  jones_known := some "-t^(-9)+ 3*t^(-8)-5*t^(-7)+ 7*t^(-6)-9*t^(-5)+ 9*t^(-4)-8*t^(-3)+ 7*t^(-2)-4*t^(-1)+ 3-t"
  alternating := true
}

def knot_10_86 : KnotEntry := {
  name := "10_86"
  crossings := 10
  dt_code := { codes := [6, 8, 14, 16, 4, 18, 20, 2, 12, 10] }
  pd_notation_str := "[[2,7,3,8],[4,10,5,9],[6,1,7,2],[8,15,9,16],[10,18,11,17],[12,20,13,19],[14,4,15,3],[16,5,17,6],[18,14,19,13],[20,12,1,11]]"
  jones_known := some "t^(-4)-4*t^(-3)+ 8*t^(-2)-11*t^(-1)+ 14-14*t+ 13*t^2-10*t^3+ 6*t^4-3*t^5+ t^6"
  alternating := true
}

def knot_10_87 : KnotEntry := {
  name := "10_87"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 16, 2, 8, 18, 20, 12, 6] }
  pd_notation_str := "[[2,11,3,12],[4,14,5,13],[6,1,7,2],[8,16,9,15],[10,8,11,7],[12,19,13,20],[14,18,15,17],[16,10,17,9],[18,4,19,3],[20,5,1,6]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 6*t^(-2)-10*t^(-1)+ 13-13*t+ 13*t^2-10*t^3+ 7*t^4-4*t^5+ t^6"
  alternating := true
}

def knot_10_88 : KnotEntry := {
  name := "10_88"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 14, 2, 16, 20, 18, 10, 6] }
  pd_notation_str := "[[4,2,5,1],[20,14,1,13],[8,3,9,4],[2,9,3,10],[14,7,15,8],[18,15,19,16],[12,6,13,5],[10,18,11,17],[16,12,17,11],[6,19,7,20]]"
  jones_known := some "-t^(-5)+ 4*t^(-4)-8*t^(-3)+ 13*t^(-2)-16*t^(-1)+ 17-16*t+ 13*t^2-8*t^3+ 4*t^4-t^5"
  alternating := true
}

def knot_10_89 : KnotEntry := {
  name := "10_89"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 12, 2, 16, 20, 18, 10, 6] }
  pd_notation_str := "[[2,7,3,8],[4,13,5,14],[6,12,7,11],[8,1,9,2],[10,15,11,16],[12,19,13,20],[14,18,15,17],[16,9,17,10],[18,5,19,6],[20,4,1,3]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-7*t^(-6)+ 12*t^(-5)-15*t^(-4)+ 17*t^(-3)-16*t^(-2)+ 13*t^(-1)-9+ 5*t-t^2"
  alternating := true
}

def knot_10_90 : KnotEntry := {
  name := "10_90"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 2, 16, 20, 18, 8, 4, 12] }
  pd_notation_str := "[[2,9,3,10],[4,13,5,14],[6,20,7,19],[8,16,9,15],[10,3,11,4],[12,18,13,17],[14,1,15,2],[16,12,17,11],[18,8,19,7],[20,6,1,5]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 7*t^(-2)-10*t^(-1)+ 12-13*t+ 12*t^2-9*t^3+ 6*t^4-3*t^5+ t^6"
  alternating := true
}

def knot_10_91 : KnotEntry := {
  name := "10_91"
  crossings := 10
  dt_code := { codes := [6, 10, 20, 14, 16, 18, 4, 8, 2, 12] }
  pd_notation_str := "[[6,2,7,1],[20,6,1,5],[16,9,17,10],[10,3,11,4],[2,18,3,17],[14,7,15,8],[8,15,9,16],[12,20,13,19],[18,12,19,11],[4,13,5,14]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-6*t^(-3)+ 9*t^(-2)-11*t^(-1)+ 13-11*t+ 9*t^2-6*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_92 : KnotEntry := {
  name := "10_92"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 18, 2, 16, 8, 20, 12, 6] }
  pd_notation_str := "[[1,9,2,8],[3,19,4,18],[5,12,6,13],[7,11,8,10],[9,3,10,2],[11,17,12,16],[13,4,14,5],[15,1,16,20],[17,7,18,6],[19,15,20,14]]"
  jones_known := some "1-3*t+ 7*t^2-10*t^3+ 14*t^4-15*t^5+ 14*t^6-12*t^7+ 8*t^8-4*t^9+ t^10"
  alternating := true
}

def knot_10_93 : KnotEntry := {
  name := "10_93"
  crossings := 10
  dt_code := { codes := [6, 10, 16, 20, 14, 4, 18, 2, 12, 8] }
  pd_notation_str := "[[2,17,3,18],[4,12,5,11],[6,20,7,19],[8,15,9,16],[10,6,11,5],[12,4,13,3],[14,7,15,8],[16,1,17,2],[18,13,19,14],[20,10,1,9]]"
  jones_known := some "-t^(-6)+ 3*t^(-5)-6*t^(-4)+ 9*t^(-3)-10*t^(-2)+ 11*t^(-1)-10+ 8*t-5*t^2+ 3*t^3-t^4"
  alternating := true
}

def knot_10_94 : KnotEntry := {
  name := "10_94"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 2, 16, 18, 20, 8, 4, 12] }
  pd_notation_str := "[[1,9,2,8],[3,10,4,11],[5,14,6,15],[7,1,8,20],[9,17,10,16],[11,4,12,5],[13,19,14,18],[15,2,16,3],[17,13,18,12],[19,7,20,6]]"
  jones_known := some "t^(-3)-3*t^(-2)+ 6*t^(-1)-8+ 11*t-12*t^2+ 11*t^3-9*t^4+ 6*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_10_95 : KnotEntry := {
  name := "10_95"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 18, 2, 16, 20, 8, 12, 6] }
  pd_notation_str := "[[2,16,3,15],[4,11,5,12],[6,17,7,18],[8,13,9,14],[10,19,11,20],[12,7,13,8],[14,2,15,1],[16,9,17,10],[18,5,19,6],[20,4,1,3]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-7*t^(-6)+ 11*t^(-5)-14*t^(-4)+ 16*t^(-3)-14*t^(-2)+ 12*t^(-1)-8+ 4*t-t^2"
  alternating := true
}

def knot_10_96 : KnotEntry := {
  name := "10_96"
  crossings := 10
  dt_code := { codes := [4, 8, 18, 12, 2, 16, 20, 6, 10, 14] }
  pd_notation_str := "[[1,16,2,17],[3,10,4,11],[5,1,6,20],[7,12,8,13],[9,4,10,5],[11,19,12,18],[13,6,14,7],[15,2,16,3],[17,15,18,14],[19,9,20,8]]"
  jones_known := some "t^(-6)-3*t^(-5)+ 7*t^(-4)-11*t^(-3)+ 14*t^(-2)-16*t^(-1)+ 15-12*t+ 9*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_10_97 : KnotEntry := {
  name := "10_97"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 18, 2, 16, 20, 6, 10, 14] }
  pd_notation_str := "[[2,12,3,11],[4,18,5,17],[6,13,7,14],[8,6,9,5],[10,20,11,19],[12,7,13,8],[14,2,15,1],[16,10,17,9],[18,4,19,3],[20,16,1,15]]"
  jones_known := some "t^(-1)-3+ 7*t-11*t^2+ 14*t^3-14*t^4+ 14*t^5-11*t^6+ 7*t^7-4*t^8+ t^9"
  alternating := true
}

def knot_10_98 : KnotEntry := {
  name := "10_98"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 18, 2, 16, 20, 4, 8, 12] }
  pd_notation_str := "[[1,10,2,11],[3,17,4,16],[5,13,6,12],[7,19,8,18],[9,15,10,14],[11,20,12,1],[13,7,14,6],[15,3,16,2],[17,9,18,8],[19,5,20,4]]"
  jones_known := some "1-3*t+ 7*t^2-9*t^3+ 13*t^4-14*t^5+ 12*t^6-11*t^7+ 7*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_10_99 : KnotEntry := {
  name := "10_99"
  crossings := 10
  dt_code := { codes := [6, 10, 18, 14, 2, 16, 20, 8, 4, 12] }
  pd_notation_str := "[[6,2,7,1],[10,4,11,3],[16,11,17,12],[14,7,15,8],[8,15,9,16],[20,13,1,14],[12,19,13,20],[18,6,19,5],[2,10,3,9],[4,18,5,17]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-7*t^(-3)+ 10*t^(-2)-12*t^(-1)+ 15-12*t+ 10*t^2-7*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_100 : KnotEntry := {
  name := "10_100"
  crossings := 10
  dt_code := { codes := [6, 10, 18, 14, 16, 4, 20, 8, 2, 12] }
  pd_notation_str := "[[2,9,3,10],[4,17,5,18],[6,12,7,11],[8,1,9,2],[10,16,11,15],[12,19,13,20],[14,8,15,7],[16,3,17,4],[18,5,19,6],[20,13,1,14]]"
  jones_known := some "-t^(-9)+ 3*t^(-8)-6*t^(-7)+ 8*t^(-6)-10*t^(-5)+ 11*t^(-4)-9*t^(-3)+ 8*t^(-2)-5*t^(-1)+ 3-t"
  alternating := true
}

def knot_10_101 : KnotEntry := {
  name := "10_101"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 18, 2, 16, 6, 20, 8, 12] }
  pd_notation_str := "[[2,12,3,11],[4,18,5,17],[6,14,7,13],[8,20,9,19],[10,6,11,5],[12,2,13,1],[14,10,15,9],[16,4,17,3],[18,16,19,15],[20,8,1,7]]"
  jones_known := some "t^2-3*t^3+ 7*t^4-10*t^5+ 14*t^6-14*t^7+ 13*t^8-11*t^9+ 7*t^10-4*t^11+ t^12"
  alternating := true
}

def knot_10_102 : KnotEntry := {
  name := "10_102"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 18, 16, 4, 20, 2, 8, 12] }
  pd_notation_str := "[[2,9,3,10],[4,12,5,11],[6,18,7,17],[8,16,9,15],[10,19,11,20],[12,6,13,5],[14,1,15,2],[16,8,17,7],[18,4,19,3],[20,13,1,14]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 6*t^(-2)-9*t^(-1)+ 12-12*t+ 11*t^2-9*t^3+ 6*t^4-3*t^5+ t^6"
  alternating := true
}

def knot_10_103 : KnotEntry := {
  name := "10_103"
  crossings := 10
  dt_code := { codes := [6, 10, 18, 16, 14, 4, 20, 8, 2, 12] }
  pd_notation_str := "[[2,9,3,10],[4,17,5,18],[6,12,7,11],[8,1,9,2],[10,16,11,15],[12,19,13,20],[14,8,15,7],[16,5,17,6],[18,3,19,4],[20,13,1,14]]"
  jones_known := some "-t^(-8)+ 3*t^(-7)-6*t^(-6)+ 9*t^(-5)-12*t^(-4)+ 13*t^(-3)-11*t^(-2)+ 10*t^(-1)-6+ 3*t-t^2"
  alternating := true
}

def knot_10_104 : KnotEntry := {
  name := "10_104"
  crossings := 10
  dt_code := { codes := [6, 16, 12, 14, 18, 4, 20, 2, 8, 10] }
  pd_notation_str := "[[6,2,7,1],[16,4,17,3],[18,9,19,10],[14,7,15,8],[20,13,1,14],[8,17,9,18],[10,19,11,20],[12,6,13,5],[4,12,5,11],[2,16,3,15]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-6*t^(-3)+ 10*t^(-2)-12*t^(-1)+ 13-12*t+ 10*t^2-6*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_105 : KnotEntry := {
  name := "10_105"
  crossings := 10
  dt_code := { codes := [4, 12, 16, 20, 18, 2, 8, 6, 10, 14] }
  pd_notation_str := "[[1,11,2,10],[3,16,4,17],[5,1,6,20],[7,18,8,19],[9,13,10,12],[11,3,12,2],[13,7,14,6],[15,4,16,5],[17,8,18,9],[19,15,20,14]]"
  jones_known := some "t^(-3)-3*t^(-2)+ 7*t^(-1)-11+ 14*t-15*t^2+ 15*t^3-12*t^4+ 8*t^5-4*t^6+ t^7"
  alternating := true
}

def knot_10_106 : KnotEntry := {
  name := "10_106"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 16, 18, 4, 20, 2, 8, 12] }
  pd_notation_str := "[[1,15,2,14],[3,10,4,11],[5,17,6,16],[7,13,8,12],[9,2,10,3],[11,18,12,19],[13,1,14,20],[15,5,16,4],[17,7,18,6],[19,8,20,9]]"
  jones_known := some "t^(-3)-3*t^(-2)+ 6*t^(-1)-9+ 12*t-12*t^2+ 12*t^3-10*t^4+ 6*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_10_107 : KnotEntry := {
  name := "10_107"
  crossings := 10
  dt_code := { codes := [4, 12, 16, 14, 18, 2, 8, 20, 10, 6] }
  pd_notation_str := "[[1,11,2,10],[3,16,4,17],[5,1,6,20],[7,14,8,15],[9,13,10,12],[11,3,12,2],[13,18,14,19],[15,4,16,5],[17,8,18,9],[19,7,20,6]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-7*t^(-3)+ 12*t^(-2)-14*t^(-1)+ 16-15*t+ 12*t^2-8*t^3+ 4*t^4-t^5"
  alternating := true
}

def knot_10_108 : KnotEntry := {
  name := "10_108"
  crossings := 10
  dt_code := { codes := [6, 16, 12, 14, 18, 4, 20, 2, 10, 8] }
  pd_notation_str := "[[1,15,2,14],[3,11,4,10],[5,12,6,13],[7,16,8,17],[9,3,10,2],[11,18,12,19],[13,1,14,20],[15,8,16,9],[17,6,18,7],[19,5,20,4]]"
  jones_known := some "-t^(-4)+ 3*t^(-3)-5*t^(-2)+ 8*t^(-1)-9+ 10*t-10*t^2+ 8*t^3-5*t^4+ 3*t^5-t^6"
  alternating := true
}

def knot_10_109 : KnotEntry := {
  name := "10_109"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 16, 2, 18, 4, 20, 8, 12] }
  pd_notation_str := "[[6,2,7,1],[10,4,11,3],[18,11,19,12],[16,7,17,8],[8,17,9,18],[20,15,1,16],[12,19,13,20],[14,6,15,5],[2,10,3,9],[4,14,5,13]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-7*t^(-3)+ 11*t^(-2)-13*t^(-1)+ 15-13*t+ 11*t^2-7*t^3+ 3*t^4-t^5"
  alternating := true
}

def knot_10_110 : KnotEntry := {
  name := "10_110"
  crossings := 10
  dt_code := { codes := [6, 10, 16, 20, 14, 2, 18, 4, 8, 12] }
  pd_notation_str := "[[1,14,2,15],[3,10,4,11],[5,1,6,20],[7,17,8,16],[9,4,10,5],[11,19,12,18],[13,2,14,3],[15,7,16,6],[17,13,18,12],[19,9,20,8]]"
  jones_known := some "t^(-3)-3*t^(-2)+ 7*t^(-1)-10+ 13*t-14*t^2+ 13*t^3-11*t^4+ 7*t^5-3*t^6+ t^7"
  alternating := true
}

def knot_10_111 : KnotEntry := {
  name := "10_111"
  crossings := 10
  dt_code := { codes := [6, 10, 16, 14, 2, 18, 8, 20, 4, 12] }
  pd_notation_str := "[[1,9,2,8],[3,19,4,18],[5,11,6,10],[7,14,8,15],[9,3,10,2],[11,17,12,16],[13,1,14,20],[15,6,16,7],[17,5,18,4],[19,13,20,12]]"
  jones_known := some "1-3*t+ 7*t^2-9*t^3+ 12*t^4-13*t^5+ 12*t^6-10*t^7+ 6*t^8-3*t^9+ t^10"
  alternating := true
}

def knot_10_112 : KnotEntry := {
  name := "10_112"
  crossings := 10
  dt_code := { codes := [6, 8, 10, 14, 16, 18, 20, 2, 4, 12] }
  pd_notation_str := "[[2,10,3,9],[4,11,5,12],[6,19,7,20],[8,14,9,13],[10,15,11,16],[12,18,13,17],[14,1,15,2],[16,4,17,3],[18,5,19,6],[20,7,1,8]]"
  jones_known := some "t^(-7)-4*t^(-6)+ 7*t^(-5)-11*t^(-4)+ 14*t^(-3)-14*t^(-2)+ 14*t^(-1)-10+ 7*t-4*t^2+ t^3"
  alternating := true
}

def knot_10_113 : KnotEntry := {
  name := "10_113"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 12, 2, 16, 18, 20, 8, 6] }
  pd_notation_str := "[[2,8,3,7],[4,14,5,13],[6,11,7,12],[8,16,9,15],[10,2,11,1],[12,19,13,20],[14,18,15,17],[16,10,17,9],[18,4,19,3],[20,5,1,6]]"
  jones_known := some "-t^(-2)+ 4*t^(-1)-8+ 14*t-17*t^2+ 19*t^3-18*t^4+ 14*t^5-10*t^6+ 5*t^7-t^8"
  alternating := true
}

def knot_10_114 : KnotEntry := {
  name := "10_114"
  crossings := 10
  dt_code := { codes := [6, 8, 10, 14, 16, 20, 18, 2, 4, 12] }
  pd_notation_str := "[[1,8,2,9],[3,11,4,10],[5,14,6,15],[7,12,8,13],[9,17,10,16],[11,18,12,19],[13,6,14,7],[15,1,16,20],[17,2,18,3],[19,5,20,4]]"
  jones_known := some "t^(-6)-4*t^(-5)+ 7*t^(-4)-11*t^(-3)+ 15*t^(-2)-15*t^(-1)+ 15-12*t+ 8*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_10_115 : KnotEntry := {
  name := "10_115"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 16, 4, 18, 2, 20, 12, 8] }
  pd_notation_str := "[[6,2,7,1],[14,6,15,5],[20,15,1,16],[16,7,17,8],[8,19,9,20],[18,11,19,12],[10,4,11,3],[4,10,5,9],[12,17,13,18],[2,14,3,13]]"
  jones_known := some "-t^(-5)+ 4*t^(-4)-9*t^(-3)+ 14*t^(-2)-17*t^(-1)+ 19-17*t+ 14*t^2-9*t^3+ 4*t^4-t^5"
  alternating := true
}

def knot_10_116 : KnotEntry := {
  name := "10_116"
  crossings := 10
  dt_code := { codes := [6, 16, 18, 14, 2, 4, 20, 8, 10, 12] }
  pd_notation_str := "[[2,16,3,15],[4,17,5,18],[6,12,7,11],[8,1,9,2],[10,4,11,3],[12,19,13,20],[14,8,15,7],[16,9,17,10],[18,5,19,6],[20,13,1,14]]"
  jones_known := some "t^(-7)-4*t^(-6)+ 8*t^(-5)-12*t^(-4)+ 15*t^(-3)-16*t^(-2)+ 15*t^(-1)-11+ 8*t-4*t^2+ t^3"
  alternating := true
}

def knot_10_117 : KnotEntry := {
  name := "10_117"
  crossings := 10
  dt_code := { codes := [6, 10, 16, 14, 18, 4, 20, 2, 12, 8] }
  pd_notation_str := "[[1,14,2,15],[3,8,4,9],[5,18,6,19],[7,17,8,16],[9,20,10,1],[11,4,12,5],[13,7,14,6],[15,2,16,3],[17,13,18,12],[19,10,20,11]]"
  jones_known := some "-t^(-8)+ 4*t^(-7)-9*t^(-6)+ 13*t^(-5)-16*t^(-4)+ 18*t^(-3)-16*t^(-2)+ 13*t^(-1)-8+ 4*t-t^2"
  alternating := true
}

def knot_10_118 : KnotEntry := {
  name := "10_118"
  crossings := 10
  dt_code := { codes := [6, 8, 18, 14, 16, 4, 20, 2, 10, 12] }
  pd_notation_str := "[[6,2,7,1],[18,6,19,5],[20,13,1,14],[12,19,13,20],[14,7,15,8],[8,3,9,4],[2,16,3,15],[10,18,11,17],[16,10,17,9],[4,11,5,12]]"
  jones_known := some "-t^(-5)+ 4*t^(-4)-8*t^(-3)+ 12*t^(-2)-15*t^(-1)+ 17-15*t+ 12*t^2-8*t^3+ 4*t^4-t^5"
  alternating := true
}

def knot_10_119 : KnotEntry := {
  name := "10_119"
  crossings := 10
  dt_code := { codes := [6, 8, 14, 18, 16, 4, 20, 10, 2, 12] }
  pd_notation_str := "[[1,16,2,17],[3,10,4,11],[5,1,6,20],[7,2,8,3],[9,14,10,15],[11,19,12,18],[13,4,14,5],[15,8,16,9],[17,7,18,6],[19,13,20,12]]"
  jones_known := some "t^(-6)-4*t^(-5)+ 8*t^(-4)-12*t^(-3)+ 16*t^(-2)-17*t^(-1)+ 16-13*t+ 9*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_10_120 : KnotEntry := {
  name := "10_120"
  crossings := 10
  dt_code := { codes := [6, 10, 18, 12, 4, 16, 20, 8, 2, 14] }
  pd_notation_str := "[[2,10,3,9],[4,18,5,17],[6,12,7,11],[8,4,9,3],[10,16,11,15],[12,20,13,19],[14,8,15,7],[16,2,17,1],[18,14,19,13],[20,6,1,5]]"
  jones_known := some "t^2-4*t^3+ 10*t^4-13*t^5+ 17*t^6-18*t^7+ 16*t^8-13*t^9+ 8*t^10-4*t^11+ t^12"
  alternating := true
}

def knot_10_121 : KnotEntry := {
  name := "10_121"
  crossings := 10
  dt_code := { codes := [6, 10, 12, 20, 18, 16, 8, 2, 4, 14] }
  pd_notation_str := "[[2,11,3,12],[4,10,5,9],[6,2,7,1],[8,16,9,15],[10,17,11,18],[12,8,13,7],[14,20,15,19],[16,3,17,4],[18,6,19,5],[20,14,1,13]]"
  jones_known := some "-t^(-2)+ 5*t^(-1)-10+ 15*t-18*t^2+ 20*t^3-18*t^4+ 14*t^5-9*t^6+ 4*t^7-t^8"
  alternating := true
}

def knot_10_122 : KnotEntry := {
  name := "10_122"
  crossings := 10
  dt_code := { codes := [6, 10, 12, 14, 18, 16, 20, 2, 4, 8] }
  pd_notation_str := "[[1,8,2,9],[3,11,4,10],[5,12,6,13],[7,16,8,17],[9,15,10,14],[11,18,12,19],[13,1,14,20],[15,2,16,3],[17,6,18,7],[19,5,20,4]]"
  jones_known := some "t^(-6)-5*t^(-5)+ 9*t^(-4)-13*t^(-3)+ 17*t^(-2)-17*t^(-1)+ 17-13*t+ 8*t^2-4*t^3+ t^4"
  alternating := true
}

def knot_10_123 : KnotEntry := {
  name := "10_123"
  crossings := 10
  dt_code := { codes := [8, 10, 12, 14, 16, 18, 20, 2, 4, 6] }
  pd_notation_str := "[[8,2,9,1],[10,3,11,4],[12,6,13,5],[4,18,5,17],[18,11,19,12],[2,15,3,16],[16,10,17,9],[20,14,1,13],[14,7,15,8],[6,19,7,20]]"
  jones_known := some "-t^(-5)+ 5*t^(-4)-10*t^(-3)+ 15*t^(-2)-19*t^(-1)+ 21-19*t+ 15*t^2-10*t^3+ 5*t^4-t^5"
  alternating := true
}

def knot_10_124 : KnotEntry := {
  name := "10_124"
  crossings := 10
  dt_code := { codes := [4, 8, -14, 2, -16, -18, -20, -6, -10, -12] }
  pd_notation_str := "[[1,9,2,8],[3,11,4,10],[5,13,6,12],[7,19,8,18],[9,3,10,2],[11,5,12,4],[14,20,15,19],[16,14,17,13],[17,7,18,6],[20,16,1,15]]"
  jones_known := some "t^4+ t^6-t^10"
  alternating := false
}

def knot_10_125 : KnotEntry := {
  name := "10_125"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, -16, -18, 6, -20, -10, -12] }
  pd_notation_str := "[[1,5,2,4],[3,9,4,8],[5,15,6,14],[20,15,1,16],[16,9,17,10],[18,11,19,12],[10,17,11,18],[12,19,13,20],[13,7,14,6],[7,3,8,2]]"
  jones_known := some "-t^(-4)+ t^(-3)-t^(-2)+ 2*t^(-1)-1+ 2*t-t^2+ t^3-t^4"
  alternating := false
}

def knot_10_126 : KnotEntry := {
  name := "10_126"
  crossings := 10
  dt_code := { codes := [4, 8, -14, 2, -16, -18, -6, -20, -10, -12] }
  pd_notation_str := "[[1,7,2,6],[4,15,5,16],[5,9,6,8],[7,3,8,2],[10,17,11,18],[12,19,13,20],[14,9,15,10],[16,3,17,4],[18,11,19,12],[20,13,1,14]]"
  jones_known := some "-t^(-8)+ t^(-7)-2*t^(-6)+ 3*t^(-5)-3*t^(-4)+ 4*t^(-3)-2*t^(-2)+ 2*t^(-1)-1"
  alternating := false
}

def knot_10_127 : KnotEntry := {
  name := "10_127"
  crossings := 10
  dt_code := { codes := [4, 8, -14, 2, 16, 18, -6, 20, 10, 12] }
  pd_notation_str := "[[1,7,2,6],[4,15,5,16],[5,9,6,8],[7,3,8,2],[9,15,10,14],[11,19,12,18],[13,1,14,20],[16,3,17,4],[17,11,18,10],[19,13,20,12]]"
  jones_known := some "2*t^2-2*t^3+ 4*t^4-5*t^5+ 5*t^6-5*t^7+ 3*t^8-2*t^9+ t^10"
  alternating := false
}

def knot_10_128 : KnotEntry := {
  name := "10_128"
  crossings := 10
  dt_code := { codes := [4, 8, -14, 2, -16, -18, -20, -6, -12, -10] }
  pd_notation_str := "[[1,9,2,8],[3,11,4,10],[5,13,6,12],[7,19,8,18],[9,5,10,4],[11,3,12,2],[14,20,15,19],[16,14,17,13],[17,7,18,6],[20,16,1,15]]"
  jones_known := some "t^3-t^4+ 2*t^5-t^6+ 2*t^7-2*t^8+ t^9-t^10"
  alternating := false
}

def knot_10_129 : KnotEntry := {
  name := "10_129"
  crossings := 10
  dt_code := { codes := [4, 8, 14, 2, -16, -18, 6, -20, -12, -10] }
  pd_notation_str := "[[1,7,2,6],[3,17,4,16],[5,9,6,8],[7,3,8,2],[10,19,11,20],[12,17,13,18],[14,9,15,10],[15,5,16,4],[18,11,19,12],[20,13,1,14]]"
  jones_known := some "-t^(-3)+ 2*t^(-2)-3*t^(-1)+ 5-4*t+ 4*t^2-3*t^3+ 2*t^4-t^5"
  alternating := false
}

def knot_10_130 : KnotEntry := {
  name := "10_130"
  crossings := 10
  dt_code := { codes := [4, 8, -14, 2, -16, -18, -6, -20, -12, -10] }
  pd_notation_str := "[[1,7,2,6],[4,15,5,16],[5,9,6,8],[7,3,8,2],[10,19,11,20],[12,17,13,18],[14,9,15,10],[16,3,17,4],[18,11,19,12],[20,13,1,14]]"
  jones_known := some "-t^(-7)+ t^(-6)-2*t^(-5)+ 3*t^(-4)-2*t^(-3)+ 3*t^(-2)-2*t^(-1)+ 2-t"
  alternating := false
}

def knot_10_131 : KnotEntry := {
  name := "10_131"
  crossings := 10
  dt_code := { codes := [4, 8, -14, 2, 16, 18, -6, 20, 12, 10] }
  pd_notation_str := "[[1,7,2,6],[4,15,5,16],[5,9,6,8],[7,3,8,2],[9,15,10,14],[11,19,12,18],[13,1,14,20],[16,3,17,4],[17,13,18,12],[19,11,20,10]]"
  jones_known := some "2*t-3*t^2+ 5*t^3-5*t^4+ 5*t^5-5*t^6+ 3*t^7-2*t^8+ t^9"
  alternating := false
}

def knot_10_132 : KnotEntry := {
  name := "10_132"
  crossings := 10
  dt_code := { codes := [4, 8, -12, 2, -16, -6, -20, -18, -10, -14] }
  pd_notation_str := "[[1,8,2,9],[3,18,4,19],[5,12,6,13],[7,10,8,11],[9,2,10,3],[11,6,12,7],[14,20,15,19],[16,14,17,13],[17,4,18,5],[20,16,1,15]]"
  jones_known := some "-t^(-7)+ t^(-6)-t^(-5)+ t^(-4)+ t^(-2)"
  alternating := false
}

def knot_10_133 : KnotEntry := {
  name := "10_133"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 2, -14, -18, 6, -20, -10, -16] }
  pd_notation_str := "[[2,16,3,15],[4,2,5,1],[7,13,8,12],[9,7,10,6],[11,18,12,19],[13,9,14,8],[14,20,15,19],[16,4,17,3],[17,10,18,11],[20,6,1,5]]"
  jones_known := some "t-t^2+ 3*t^3-3*t^4+ 3*t^5-3*t^6+ 2*t^7-2*t^8+ t^9"
  alternating := false
}

def knot_10_134 : KnotEntry := {
  name := "10_134"
  crossings := 10
  dt_code := { codes := [4, 8, -12, 2, -14, -18, -6, -20, -10, -16] }
  pd_notation_str := "[[2,16,3,15],[4,2,5,1],[7,13,8,12],[9,7,10,6],[10,18,11,17],[13,9,14,8],[14,20,15,19],[16,4,17,3],[18,12,19,11],[20,6,1,5]]"
  jones_known := some "t^3-t^4+ 3*t^5-3*t^6+ 4*t^7-4*t^8+ 3*t^9-3*t^10+ t^11"
  alternating := false
}

def knot_10_135 : KnotEntry := {
  name := "10_135"
  crossings := 10
  dt_code := { codes := [4, 8, -12, 2, 14, 18, -6, 20, 10, 16] }
  pd_notation_str := "[[1,4,2,5],[3,16,4,17],[5,20,6,1],[7,13,8,12],[9,7,10,6],[10,18,11,17],[13,9,14,8],[15,2,16,3],[18,12,19,11],[19,14,20,15]]"
  jones_known := some "-2*t^(-3)+ 4*t^(-2)-5*t^(-1)+ 7-6*t+ 6*t^2-4*t^3+ 2*t^4-t^5"
  alternating := false
}

def knot_10_136 : KnotEntry := {
  name := "10_136"
  crossings := 10
  dt_code := { codes := [4, 8, 10, -14, 2, -18, -6, -20, -12, -16] }
  pd_notation_str := "[[2,17,3,18],[4,2,5,1],[7,14,8,15],[9,7,10,6],[12,19,13,20],[13,8,14,9],[15,11,16,10],[16,3,17,4],[18,11,19,12],[20,6,1,5]]"
  jones_known := some "-t^(-4)+ 2*t^(-3)-2*t^(-2)+ 3*t^(-1)-2+ 2*t-2*t^2+ t^3"
  alternating := false
}

def knot_10_137 : KnotEntry := {
  name := "10_137"
  crossings := 10
  dt_code := { codes := [4, 8, 10, -14, 2, -16, -18, -6, -20, -12] }
  pd_notation_str := "[[1,15,2,14],[4,8,5,7],[6,19,7,20],[9,17,10,16],[11,8,12,9],[13,3,14,2],[15,11,16,10],[17,12,18,13],[18,4,19,3],[20,5,1,6]]"
  jones_known := some "t^(-2)-2*t^(-1)+ 4-4*t+ 4*t^2-4*t^3+ 3*t^4-2*t^5+ t^6"
  alternating := false
}

def knot_10_138 : KnotEntry := {
  name := "10_138"
  crossings := 10
  dt_code := { codes := [4, 8, 10, -14, 2, 16, 18, -6, 20, 12] }
  pd_notation_str := "[[1,15,2,14],[4,8,5,7],[6,19,7,20],[8,12,9,11],[10,15,11,16],[12,18,13,17],[13,3,14,2],[16,9,17,10],[18,4,19,3],[20,5,1,6]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 4*t^(-1)-5+ 6*t-6*t^2+ 5*t^3-4*t^4+ 2*t^5"
  alternating := false
}

def knot_10_139 : KnotEntry := {
  name := "10_139"
  crossings := 10
  dt_code := { codes := [4, 10, -14, -16, 2, -18, -20, -6, -8, -12] }
  pd_notation_str := "[[1,11,2,10],[4,18,5,17],[5,13,6,12],[7,15,8,14],[9,1,10,20],[11,3,12,2],[13,7,14,6],[16,4,17,3],[18,16,19,15],[19,9,20,8]]"
  jones_known := some "t^4+ t^6-t^8+ t^9-t^10+ t^11-t^12"
  alternating := false
}

def knot_10_140 : KnotEntry := {
  name := "10_140"
  crossings := 10
  dt_code := { codes := [4, 10, -14, -16, 2, 18, 20, -8, -6, 12] }
  pd_notation_str := "[[1,15,2,14],[3,10,4,11],[5,12,6,13],[6,18,7,17],[8,16,9,15],[11,4,12,5],[13,1,14,20],[16,8,17,7],[18,10,19,9],[19,3,20,2]]"
  jones_known := some "1-t+ t^2-t^3+ 2*t^4-t^5+ t^6-t^7"
  alternating := false
}

def knot_10_141 : KnotEntry := {
  name := "10_141"
  crossings := 10
  dt_code := { codes := [4, 10, -14, -16, 2, 18, -8, -6, 20, 12] }
  pd_notation_str := "[[2,11,3,12],[4,9,5,10],[5,19,6,18],[7,15,8,14],[10,1,11,2],[12,3,13,4],[13,17,14,16],[15,9,16,8],[17,1,18,20],[19,7,20,6]]"
  jones_known := some "t^(-2)-2*t^(-1)+ 3-3*t+ 4*t^2-3*t^3+ 2*t^4-2*t^5+ t^6"
  alternating := false
}

def knot_10_142 : KnotEntry := {
  name := "10_142"
  crossings := 10
  dt_code := { codes := [4, 10, -14, -16, 2, -18, -20, -8, -6, -12] }
  pd_notation_str := "[[1,15,2,14],[4,12,5,11],[6,18,7,17],[8,16,9,15],[10,4,11,3],[12,6,13,5],[13,1,14,20],[16,8,17,7],[18,10,19,9],[19,3,20,2]]"
  jones_known := some "t^3-t^4+ 2*t^5-2*t^6+ 3*t^7-2*t^8+ 2*t^9-2*t^10"
  alternating := false
}

def knot_10_143 : KnotEntry := {
  name := "10_143"
  crossings := 10
  dt_code := { codes := [4, 10, -14, -16, 2, -18, -8, -6, -20, -12] }
  pd_notation_str := "[[2,11,3,12],[4,9,5,10],[6,19,7,20],[7,15,8,14],[10,1,11,2],[12,3,13,4],[13,17,14,16],[15,9,16,8],[18,5,19,6],[20,17,1,18]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-3*t^(-6)+ 4*t^(-5)-5*t^(-4)+ 5*t^(-3)-3*t^(-2)+ 3*t^(-1)-1"
  alternating := false
}

def knot_10_144 : KnotEntry := {
  name := "10_144"
  crossings := 10
  dt_code := { codes := [4, 10, 14, 16, 2, -18, -20, 8, 6, -12] }
  pd_notation_str := "[[1,9,2,8],[3,16,4,17],[5,14,6,15],[7,11,8,10],[9,3,10,2],[12,20,13,19],[15,4,16,5],[17,6,18,7],[18,12,19,11],[20,14,1,13]]"
  jones_known := some "2*t^(-1)-3+ 5*t-7*t^2+ 7*t^3-6*t^4+ 5*t^5-3*t^6+ t^7"
  alternating := false
}

def knot_10_145 : KnotEntry := {
  name := "10_145"
  crossings := 10
  dt_code := { codes := [4, 8, -12, -18, 2, -16, -20, -6, -10, -14] }
  pd_notation_str := "[[1,14,2,15],[3,18,4,19],[6,13,7,14],[8,6,9,5],[9,16,10,17],[11,2,12,3],[12,7,13,8],[15,20,16,1],[17,4,18,5],[19,10,20,11]]"
  jones_known := some "-t^(-10)+ t^(-9)-t^(-8)+ t^(-7)+ t^(-2)"
  alternating := false
}

def knot_10_146 : KnotEntry := {
  name := "10_146"
  crossings := 10
  dt_code := { codes := [4, 8, -18, -12, 2, -16, -20, -6, -10, -14] }
  pd_notation_str := "[[1,14,2,15],[4,10,5,9],[6,14,7,13],[8,17,9,18],[10,4,11,3],[12,8,13,7],[15,20,16,1],[16,11,17,12],[18,5,19,6],[19,3,20,2]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-4*t^(-3)+ 5*t^(-2)-6*t^(-1)+ 6-4*t+ 3*t^2-t^3"
  alternating := false
}

def knot_10_147 : KnotEntry := {
  name := "10_147"
  crossings := 10
  dt_code := { codes := [4, 10, -14, 12, 2, 16, 18, -20, 8, -6] }
  pd_notation_str := "[[2,8,3,7],[3,18,4,19],[6,11,7,12],[8,16,9,15],[10,2,11,1],[13,4,14,5],[14,18,15,17],[16,10,17,9],[19,13,20,12],[20,5,1,6]]"
  jones_known := some "t^(-3)-2*t^(-2)+ 3*t^(-1)-4+ 5*t-4*t^2+ 4*t^3-3*t^4+ t^5"
  alternating := false
}

def knot_10_148 : KnotEntry := {
  name := "10_148"
  crossings := 10
  dt_code := { codes := [4, 8, -12, 2, -16, -6, -18, -20, -10, -14] }
  pd_notation_str := "[[2,17,3,18],[4,9,5,10],[6,19,7,20],[7,13,8,12],[10,3,11,4],[11,15,12,14],[13,9,14,8],[16,1,17,2],[18,5,19,6],[20,15,1,16]]"
  jones_known := some "-t^(-8)+ 2*t^(-7)-4*t^(-6)+ 5*t^(-5)-5*t^(-4)+ 6*t^(-3)-4*t^(-2)+ 3*t^(-1)-1"
  alternating := false
}

def knot_10_149 : KnotEntry := {
  name := "10_149"
  crossings := 10
  dt_code := { codes := [4, 8, -12, 2, 16, -6, 18, 20, 10, 14] }
  pd_notation_str := "[[1,17,2,16],[4,9,5,10],[5,19,6,18],[7,13,8,12],[10,3,11,4],[11,15,12,14],[13,9,14,8],[15,1,16,20],[17,3,18,2],[19,7,20,6]]"
  jones_known := some "2*t^2-3*t^3+ 6*t^4-7*t^5+ 7*t^6-7*t^7+ 5*t^8-3*t^9+ t^10"
  alternating := false
}

def knot_10_150 : KnotEntry := {
  name := "10_150"
  crossings := 10
  dt_code := { codes := [4, 8, -12, 2, -16, -6, -18, -10, -20, -14] }
  pd_notation_str := "[[1,17,2,16],[3,7,4,6],[5,1,6,20],[8,14,9,13],[10,8,11,7],[11,18,12,19],[14,10,15,9],[15,3,16,2],[17,12,18,13],[19,5,20,4]]"
  jones_known := some "1-2*t+ 4*t^2-4*t^3+ 5*t^4-5*t^5+ 4*t^6-3*t^7+ t^8"
  alternating := false
}

def knot_10_151 : KnotEntry := {
  name := "10_151"
  crossings := 10
  dt_code := { codes := [4, 8, -12, 2, 16, -6, 18, 10, 20, 14] }
  pd_notation_str := "[[2,15,3,16],[4,19,5,20],[6,3,7,4],[8,14,9,13],[10,8,11,7],[11,18,12,19],[14,10,15,9],[16,1,17,2],[17,12,18,13],[20,5,1,6]]"
  jones_known := some "-2*t^(-6)+ 4*t^(-5)-6*t^(-4)+ 8*t^(-3)-7*t^(-2)+ 7*t^(-1)-5+ 3*t-t^2"
  alternating := false
}

def knot_10_152 : KnotEntry := {
  name := "10_152"
  crossings := 10
  dt_code := { codes := [6, 8, 12, 2, -16, 4, -18, -20, -10, -14] }
  pd_notation_str := "[[1,7,2,6],[3,9,4,8],[5,19,6,18],[7,3,8,2],[10,16,11,15],[12,20,13,19],[14,10,15,9],[16,12,17,11],[17,5,18,4],[20,14,1,13]]"
  jones_known := some "t^4+ t^6+ t^7-2*t^8+ 2*t^9-3*t^10+ 2*t^11-2*t^12+ t^13"
  alternating := false
}

def knot_10_153 : KnotEntry := {
  name := "10_153"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 2, -16, 6, -18, -20, -10, -14] }
  pd_notation_str := "[[2,17,3,18],[3,11,4,10],[6,19,7,20],[7,13,8,12],[9,5,10,4],[11,15,12,14],[13,9,14,8],[16,1,17,2],[18,5,19,6],[20,15,1,16]]"
  jones_known := some "-t^(-5)+ t^(-4)-t^(-3)+ t^(-2)+ 1+ t-t^2+ t^3-t^4"
  alternating := false
}

def knot_10_154 : KnotEntry := {
  name := "10_154"
  crossings := 10
  dt_code := { codes := [4, 8, 12, 2, -16, 6, -18, -10, -20, -14] }
  pd_notation_str := "[[1,17,2,16],[3,7,4,6],[5,1,6,20],[8,14,9,13],[10,8,11,7],[12,18,13,17],[14,10,15,9],[15,3,16,2],[18,12,19,11],[19,5,20,4]]"
  jones_known := some "t^3+ 2*t^6-2*t^7+ 2*t^8-3*t^9+ 2*t^10-2*t^11+ t^12"
  alternating := false
}

def knot_10_155 : KnotEntry := {
  name := "10_155"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 16, 18, 4, -20, 2, 8, -12] }
  pd_notation_str := "[[1,11,2,10],[3,13,4,12],[5,14,6,15],[6,19,7,20],[9,16,10,17],[11,3,12,2],[13,19,14,18],[15,8,16,9],[17,4,18,5],[20,7,1,8]]"
  jones_known := some "t^(-6)-2*t^(-5)+ 3*t^(-4)-4*t^(-3)+ 4*t^(-2)-4*t^(-1)+ 4-2*t+ t^2"
  alternating := false
}

def knot_10_156 : KnotEntry := {
  name := "10_156"
  crossings := 10
  dt_code := { codes := [4, 12, 16, -14, 18, 2, -8, 20, 10, 6] }
  pd_notation_str := "[[1,13,2,12],[3,8,4,9],[5,14,6,15],[7,18,8,19],[10,15,11,16],[11,1,12,20],[13,6,14,7],[16,9,17,10],[17,4,18,5],[19,3,20,2]]"
  jones_known := some "-t^(-6)+ 3*t^(-5)-5*t^(-4)+ 6*t^(-3)-6*t^(-2)+ 6*t^(-1)-4+ 3*t-t^2"
  alternating := false
}

def knot_10_157 : KnotEntry := {
  name := "10_157"
  crossings := 10
  dt_code := { codes := [6, -10, -18, 14, -2, -16, 20, 8, -4, 12] }
  pd_notation_str := "[[2,8,3,7],[3,10,4,11],[5,18,6,19],[8,15,9,16],[11,4,12,5],[14,1,15,2],[16,9,17,10],[17,13,18,12],[19,6,20,7],[20,13,1,14]]"
  jones_known := some "t^(-10)-4*t^(-9)+ 6*t^(-8)-8*t^(-7)+ 9*t^(-6)-8*t^(-5)+ 7*t^(-4)-4*t^(-3)+ 2*t^(-2)"
  alternating := false
}

def knot_10_158 : KnotEntry := {
  name := "10_158"
  crossings := 10
  dt_code := { codes := [6, -10, -16, 14, -2, -18, 8, 20, -4, -12] }
  pd_notation_str := "[[3,9,4,8],[4,11,5,12],[6,20,7,19],[9,17,10,16],[12,5,13,6],[14,1,15,2],[15,11,16,10],[17,3,18,2],[18,8,19,7],[20,13,1,14]]"
  jones_known := some "t^(-4)-3*t^(-3)+ 6*t^(-2)-7*t^(-1)+ 8-8*t+ 6*t^2-4*t^3+ 2*t^4"
  alternating := false
}

def knot_10_159 : KnotEntry := {
  name := "10_159"
  crossings := 10
  dt_code := { codes := [6, 8, 10, 14, 16, -18, -20, 2, 4, -12] }
  pd_notation_str := "[[2,10,3,9],[4,11,5,12],[5,19,6,18],[7,1,8,20],[8,14,9,13],[10,15,11,16],[12,18,13,17],[14,1,15,2],[16,4,17,3],[19,7,20,6]]"
  jones_known := some "-1+ 4*t-5*t^2+ 7*t^3-7*t^4+ 6*t^5-5*t^6+ 3*t^7-t^8"
  alternating := false
}

def knot_10_160 : KnotEntry := {
  name := "10_160"
  crossings := 10
  dt_code := { codes := [4, 12, -16, -14, -18, 2, -8, -20, -10, -6] }
  pd_notation_str := "[[1,13,2,12],[4,18,5,17],[6,14,7,13],[8,4,9,3],[10,15,11,16],[11,1,12,20],[14,6,15,5],[16,9,17,10],[18,8,19,7],[19,3,20,2]]"
  jones_known := some "1-2*t+ 3*t^2-3*t^3+ 4*t^4-3*t^5+ 3*t^6-2*t^7"
  alternating := false
}

def knot_10_161 : KnotEntry := {
  name := "10_161"
  crossings := 10
  dt_code := { codes := [4, 12, -16, 14, -18, 2, 8, -20, -10, -6] }
  pd_notation_str := "[[1,13,2,12],[4,18,5,17],[6,14,7,13],[8,4,9,3],[9,17,10,16],[11,1,12,20],[14,6,15,5],[15,11,16,10],[18,8,19,7],[19,3,20,2]]"
  jones_known := some "t^3+ t^6-t^7+ t^8-t^9+ t^10-t^11"
  alternating := false
}

def knot_10_162 : KnotEntry := {
  name := "10_162"
  crossings := 10
  dt_code := { codes := [6, 10, 14, 18, 16, 4, -20, 2, 8, -12] }
  pd_notation_str := "[[2,9,3,10],[5,12,6,13],[6,18,7,17],[8,16,9,15],[10,19,11,20],[11,4,12,5],[14,1,15,2],[16,8,17,7],[18,4,19,3],[20,13,1,14]]"
  jones_known := some "t^(-7)-2*t^(-6)+ 4*t^(-5)-6*t^(-4)+ 6*t^(-3)-6*t^(-2)+ 5*t^(-1)-3+ 2*t"
  alternating := false
}

def knot_10_163 : KnotEntry := {
  name := "10_163"
  crossings := 10
  dt_code := { codes := [6, 8, 10, 14, 16, -20, -18, 2, 4, -12] }
  pd_notation_str := "[[1,8,2,9],[3,11,4,10],[6,14,7,13],[9,17,10,16],[11,18,12,19],[12,8,13,7],[14,6,15,5],[15,1,16,20],[17,2,18,3],[19,5,20,4]]"
  jones_known := some "-t^(-2)+ 4*t^(-1)-6+ 8*t-9*t^2+ 9*t^3-7*t^4+ 5*t^5-2*t^6"
  alternating := false
}

def knot_10_164 : KnotEntry := {
  name := "10_164"
  crossings := 10
  dt_code := { codes := [6, -10, -12, 14, -18, -16, 20, -2, -4, -8] }
  pd_notation_str := "[[2,12,3,11],[3,16,4,17],[6,14,7,13],[8,15,9,16],[9,5,10,4],[12,2,13,1],[14,19,15,20],[17,10,18,11],[18,5,19,6],[20,8,1,7]]"
  jones_known := some "-t^(-5)+ 3*t^(-4)-5*t^(-3)+ 7*t^(-2)-8*t^(-1)+ 8-6*t+ 5*t^2-2*t^3"
  alternating := false
}

def knot_10_165 : KnotEntry := {
  name := "10_165"
  crossings := 10
  dt_code := { codes := [6, 8, 14, 18, 16, 4, -20, 10, 2, -12] }
  pd_notation_str := "[[1,8,2,9],[3,12,4,13],[4,17,5,18],[7,2,8,3],[9,14,10,15],[11,17,12,16],[13,6,14,7],[15,20,16,1],[18,5,19,6],[19,11,20,10]]"
  jones_known := some "t^(-9)-3*t^(-8)+ 4*t^(-7)-6*t^(-6)+ 7*t^(-5)-6*t^(-4)+ 6*t^(-3)-4*t^(-2)+ 2*t^(-1)"
  alternating := false
}


-- Complete database (249 knots)
def knot_database_10 : List KnotEntry := [
  knot_3_1,
  knot_4_1,
  knot_5_1,
  knot_5_2,
  knot_6_1,
  knot_6_2,
  knot_6_3,
  knot_7_1,
  knot_7_2,
  knot_7_3,
  knot_7_4,
  knot_7_5,
  knot_7_6,
  knot_7_7,
  knot_8_1,
  knot_8_2,
  knot_8_3,
  knot_8_4,
  knot_8_5,
  knot_8_6,
  knot_8_7,
  knot_8_8,
  knot_8_9,
  knot_8_10,
  knot_8_11,
  knot_8_12,
  knot_8_13,
  knot_8_14,
  knot_8_15,
  knot_8_16,
  knot_8_17,
  knot_8_18,
  knot_8_19,
  knot_8_20,
  knot_8_21,
  knot_9_1,
  knot_9_2,
  knot_9_3,
  knot_9_4,
  knot_9_5,
  knot_9_6,
  knot_9_7,
  knot_9_8,
  knot_9_9,
  knot_9_10,
  knot_9_11,
  knot_9_12,
  knot_9_13,
  knot_9_14,
  knot_9_15,
  knot_9_16,
  knot_9_17,
  knot_9_18,
  knot_9_19,
  knot_9_20,
  knot_9_21,
  knot_9_22,
  knot_9_23,
  knot_9_24,
  knot_9_25,
  knot_9_26,
  knot_9_27,
  knot_9_28,
  knot_9_29,
  knot_9_30,
  knot_9_31,
  knot_9_32,
  knot_9_33,
  knot_9_34,
  knot_9_35,
  knot_9_36,
  knot_9_37,
  knot_9_38,
  knot_9_39,
  knot_9_40,
  knot_9_41,
  knot_9_42,
  knot_9_43,
  knot_9_44,
  knot_9_45,
  knot_9_46,
  knot_9_47,
  knot_9_48,
  knot_9_49,
  knot_10_1,
  knot_10_2,
  knot_10_3,
  knot_10_4,
  knot_10_5,
  knot_10_6,
  knot_10_7,
  knot_10_8,
  knot_10_9,
  knot_10_10,
  knot_10_11,
  knot_10_12,
  knot_10_13,
  knot_10_14,
  knot_10_15,
  knot_10_16,
  knot_10_17,
  knot_10_18,
  knot_10_19,
  knot_10_20,
  knot_10_21,
  knot_10_22,
  knot_10_23,
  knot_10_24,
  knot_10_25,
  knot_10_26,
  knot_10_27,
  knot_10_28,
  knot_10_29,
  knot_10_30,
  knot_10_31,
  knot_10_32,
  knot_10_33,
  knot_10_34,
  knot_10_35,
  knot_10_36,
  knot_10_37,
  knot_10_38,
  knot_10_39,
  knot_10_40,
  knot_10_41,
  knot_10_42,
  knot_10_43,
  knot_10_44,
  knot_10_45,
  knot_10_46,
  knot_10_47,
  knot_10_48,
  knot_10_49,
  knot_10_50,
  knot_10_51,
  knot_10_52,
  knot_10_53,
  knot_10_54,
  knot_10_55,
  knot_10_56,
  knot_10_57,
  knot_10_58,
  knot_10_59,
  knot_10_60,
  knot_10_61,
  knot_10_62,
  knot_10_63,
  knot_10_64,
  knot_10_65,
  knot_10_66,
  knot_10_67,
  knot_10_68,
  knot_10_69,
  knot_10_70,
  knot_10_71,
  knot_10_72,
  knot_10_73,
  knot_10_74,
  knot_10_75,
  knot_10_76,
  knot_10_77,
  knot_10_78,
  knot_10_79,
  knot_10_80,
  knot_10_81,
  knot_10_82,
  knot_10_83,
  knot_10_84,
  knot_10_85,
  knot_10_86,
  knot_10_87,
  knot_10_88,
  knot_10_89,
  knot_10_90,
  knot_10_91,
  knot_10_92,
  knot_10_93,
  knot_10_94,
  knot_10_95,
  knot_10_96,
  knot_10_97,
  knot_10_98,
  knot_10_99,
  knot_10_100,
  knot_10_101,
  knot_10_102,
  knot_10_103,
  knot_10_104,
  knot_10_105,
  knot_10_106,
  knot_10_107,
  knot_10_108,
  knot_10_109,
  knot_10_110,
  knot_10_111,
  knot_10_112,
  knot_10_113,
  knot_10_114,
  knot_10_115,
  knot_10_116,
  knot_10_117,
  knot_10_118,
  knot_10_119,
  knot_10_120,
  knot_10_121,
  knot_10_122,
  knot_10_123,
  knot_10_124,
  knot_10_125,
  knot_10_126,
  knot_10_127,
  knot_10_128,
  knot_10_129,
  knot_10_130,
  knot_10_131,
  knot_10_132,
  knot_10_133,
  knot_10_134,
  knot_10_135,
  knot_10_136,
  knot_10_137,
  knot_10_138,
  knot_10_139,
  knot_10_140,
  knot_10_141,
  knot_10_142,
  knot_10_143,
  knot_10_144,
  knot_10_145,
  knot_10_146,
  knot_10_147,
  knot_10_148,
  knot_10_149,
  knot_10_150,
  knot_10_151,
  knot_10_152,
  knot_10_153,
  knot_10_154,
  knot_10_155,
  knot_10_156,
  knot_10_157,
  knot_10_158,
  knot_10_159,
  knot_10_160,
  knot_10_161,
  knot_10_162,
  knot_10_163,
  knot_10_164,
  knot_10_165
]

-- Statistics
-- Total knots: 249
-- Alternating: 196
-- Non-alternating: 53

-- Verify database size
theorem database_10_size :
  knot_database_10.length = 249 := by native_decide

#check knot_database_10
#eval knot_database_10.length
