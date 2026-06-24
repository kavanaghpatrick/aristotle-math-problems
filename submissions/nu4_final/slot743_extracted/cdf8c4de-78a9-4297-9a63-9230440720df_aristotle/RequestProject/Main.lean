import Mathlib

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

private def M : ℕ := 625942982474437835576448580641867239959237377760067219877585649

private lemma index1_5 :
    (((Finset.univ : Finset (Fin (5 - 1) × Fin (5 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 5)).card = 5 - 1) := by native_decide

private lemma index1_7 :
    (((Finset.univ : Finset (Fin (7 - 1) × Fin (7 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 7)).card = 7 - 1) := by native_decide

private lemma index1_11 :
    (((Finset.univ : Finset (Fin (11 - 1) × Fin (11 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 11)).card = 11 - 1) := by native_decide

private lemma index1_13 :
    (((Finset.univ : Finset (Fin (13 - 1) × Fin (13 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 13)).card = 13 - 1) := by native_decide

private lemma index1_17 :
    (((Finset.univ : Finset (Fin (17 - 1) × Fin (17 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 17)).card = 17 - 1) := by native_decide

private lemma index1_19 :
    (((Finset.univ : Finset (Fin (19 - 1) × Fin (19 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 19)).card = 19 - 1) := by native_decide

private lemma index1_29 :
    (((Finset.univ : Finset (Fin (29 - 1) × Fin (29 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 29)).card = 29 - 1) := by native_decide

private lemma index1_31 :
    (((Finset.univ : Finset (Fin (31 - 1) × Fin (31 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 31)).card = 31 - 1) := by native_decide

private lemma index1_37 :
    (((Finset.univ : Finset (Fin (37 - 1) × Fin (37 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 37)).card = 37 - 1) := by native_decide

private lemma index1_41 :
    (((Finset.univ : Finset (Fin (41 - 1) × Fin (41 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 41)).card = 41 - 1) := by native_decide

private lemma index1_43 :
    (((Finset.univ : Finset (Fin (43 - 1) × Fin (43 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 43)).card = 43 - 1) := by native_decide

private lemma index1_53 :
    (((Finset.univ : Finset (Fin (53 - 1) × Fin (53 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 53)).card = 53 - 1) := by native_decide

private lemma index1_59 :
    (((Finset.univ : Finset (Fin (59 - 1) × Fin (59 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 59)).card = 59 - 1) := by native_decide

private lemma index1_61 :
    (((Finset.univ : Finset (Fin (61 - 1) × Fin (61 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 61)).card = 61 - 1) := by native_decide

private lemma index1_67 :
    (((Finset.univ : Finset (Fin (67 - 1) × Fin (67 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 67)).card = 67 - 1) := by native_decide

private lemma index1_79 :
    (((Finset.univ : Finset (Fin (79 - 1) × Fin (79 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 79)).card = 79 - 1) := by native_decide

private lemma index1_83 :
    (((Finset.univ : Finset (Fin (83 - 1) × Fin (83 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 83)).card = 83 - 1) := by native_decide

private lemma index1_89 :
    (((Finset.univ : Finset (Fin (89 - 1) × Fin (89 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 89)).card = 89 - 1) := by native_decide

private lemma index1_101 :
    (((Finset.univ : Finset (Fin (101 - 1) × Fin (101 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 101)).card = 101 - 1) := by native_decide

private lemma index1_103 :
    (((Finset.univ : Finset (Fin (103 - 1) × Fin (103 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 103)).card = 103 - 1) := by native_decide

private lemma index1_107 :
    (((Finset.univ : Finset (Fin (107 - 1) × Fin (107 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 107)).card = 107 - 1) := by native_decide

private lemma index1_109 :
    (((Finset.univ : Finset (Fin (109 - 1) × Fin (109 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 109)).card = 109 - 1) := by native_decide

private lemma index1_113 :
    (((Finset.univ : Finset (Fin (113 - 1) × Fin (113 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 113)).card = 113 - 1) := by native_decide

private lemma index1_127 :
    (((Finset.univ : Finset (Fin (127 - 1) × Fin (127 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 127)).card = 127 - 1) := by native_decide

private lemma index1_131 :
    (((Finset.univ : Finset (Fin (131 - 1) × Fin (131 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 131)).card = 131 - 1) := by native_decide

private lemma index1_157 :
    (((Finset.univ : Finset (Fin (157 - 1) × Fin (157 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 157)).card = 157 - 1) := by native_decide

private lemma index1_163 :
    (((Finset.univ : Finset (Fin (163 - 1) × Fin (163 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 163)).card = 163 - 1) := by native_decide

private lemma index1_179 :
    (((Finset.univ : Finset (Fin (179 - 1) × Fin (179 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 179)).card = 179 - 1) := by native_decide

private lemma index1_211 :
    (((Finset.univ : Finset (Fin (211 - 1) × Fin (211 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 211)).card = 211 - 1) := by native_decide

private lemma index1_227 :
    (((Finset.univ : Finset (Fin (227 - 1) × Fin (227 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 227)).card = 227 - 1) := by native_decide

private lemma index1_229 :
    (((Finset.univ : Finset (Fin (229 - 1) × Fin (229 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 229)).card = 229 - 1) := by native_decide

private lemma index1_269 :
    (((Finset.univ : Finset (Fin (269 - 1) × Fin (269 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 269)).card = 269 - 1) := by native_decide

private lemma index1_691 :
    (((Finset.univ : Finset (Fin (691 - 1) × Fin (691 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 691)).card = 691 - 1) := by native_decide

private lemma index1_971 :
    (((Finset.univ : Finset (Fin (971 - 1) × Fin (971 - 1))).image
      (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % 971)).card = 971 - 1) := by native_decide

private lemma prime_5 : Nat.Prime 5 := by decide
private lemma prime_7 : Nat.Prime 7 := by decide
private lemma prime_11 : Nat.Prime 11 := by decide
private lemma prime_13 : Nat.Prime 13 := by decide
private lemma prime_17 : Nat.Prime 17 := by decide
private lemma prime_19 : Nat.Prime 19 := by decide
private lemma prime_29 : Nat.Prime 29 := by decide
private lemma prime_31 : Nat.Prime 31 := by decide
private lemma prime_37 : Nat.Prime 37 := by decide
private lemma prime_41 : Nat.Prime 41 := by decide
private lemma prime_43 : Nat.Prime 43 := by decide
private lemma prime_53 : Nat.Prime 53 := by decide
private lemma prime_59 : Nat.Prime 59 := by decide
private lemma prime_61 : Nat.Prime 61 := by decide
private lemma prime_67 : Nat.Prime 67 := by decide
private lemma prime_79 : Nat.Prime 79 := by decide
private lemma prime_83 : Nat.Prime 83 := by decide
private lemma prime_89 : Nat.Prime 89 := by decide
private lemma prime_101 : Nat.Prime 101 := by decide
private lemma prime_103 : Nat.Prime 103 := by decide
private lemma prime_107 : Nat.Prime 107 := by decide
private lemma prime_109 : Nat.Prime 109 := by decide
private lemma prime_113 : Nat.Prime 113 := by decide
private lemma prime_127 : Nat.Prime 127 := by decide
private lemma prime_131 : Nat.Prime 131 := by decide
private lemma prime_157 : Nat.Prime 157 := by decide
private lemma prime_163 : Nat.Prime 163 := by decide
private lemma prime_179 : Nat.Prime 179 := by decide
private lemma prime_211 : Nat.Prime 211 := by decide
private lemma prime_227 : Nat.Prime 227 := by decide
private lemma prime_229 : Nat.Prime 229 := by decide
private lemma prime_269 : Nat.Prime 269 := by decide
private lemma prime_691 : Nat.Prime 691 := by decide
private lemma prime_971 : Nat.Prime 971 := by decide

private lemma dvd_0_0 : 5 ∣ 2 ^ 0 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_0_1 : 13 ∣ 2 ^ 0 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_0_2 : 43 ∣ 2 ^ 0 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_0_3 : 17 ∣ 2 ^ 0 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_0_4 : 5 ∣ 2 ^ 0 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_0_5 : 11 ∣ 2 ^ 0 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_0_6 : 7 ∣ 2 ^ 0 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_0_7 : 13 ∣ 2 ^ 0 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_0_8 : 5 ∣ 2 ^ 0 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_0_9 : 19 ∣ 2 ^ 0 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_0_10 : 11 ∣ 2 ^ 0 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_0_11 : 79 ∣ 2 ^ 0 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_1_0 : 37 ∣ 2 ^ 1 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_1_1 : 5 ∣ 2 ^ 1 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_1_2 : 19 ∣ 2 ^ 1 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_1_3 : 89 ∣ 2 ^ 1 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_1_4 : 7 ∣ 2 ^ 1 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_1_5 : 5 ∣ 2 ^ 1 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_1_6 : 127 ∣ 2 ^ 1 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_1_7 : 79 ∣ 2 ^ 1 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_1_8 : 29 ∣ 2 ^ 1 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_1_9 : 5 ∣ 2 ^ 1 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_1_10 : 7 ∣ 2 ^ 1 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_1_11 : 59 ∣ 2 ^ 1 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_2_0 : 67 ∣ 2 ^ 2 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_2_1 : 11 ∣ 2 ^ 2 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_2_2 : 5 ∣ 2 ^ 2 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_2_3 : 79 ∣ 2 ^ 2 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_2_4 : 691 ∣ 2 ^ 2 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_2_5 : 53 ∣ 2 ^ 2 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_2_6 : 5 ∣ 2 ^ 2 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_2_7 : 17 ∣ 2 ^ 2 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_2_8 : 7 ∣ 2 ^ 2 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_2_9 : 83 ∣ 2 ^ 2 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_2_10 : 5 ∣ 2 ^ 2 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_2_11 : 11 ∣ 2 ^ 2 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_3_0 : 7 ∣ 2 ^ 3 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_3_1 : 157 ∣ 2 ^ 3 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_3_2 : 29 ∣ 2 ^ 3 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_3_3 : 5 ∣ 2 ^ 3 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_3_4 : 59 ∣ 2 ^ 3 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_3_5 : 43 ∣ 2 ^ 3 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_3_6 : 7 ∣ 2 ^ 3 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_3_7 : 5 ∣ 2 ^ 3 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_3_8 : 53 ∣ 2 ^ 3 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_3_9 : 17 ∣ 2 ^ 3 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_3_10 : 103 ∣ 2 ^ 3 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_3_11 : 5 ∣ 2 ^ 3 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_4_0 : 5 ∣ 2 ^ 4 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_4_1 : 83 ∣ 2 ^ 4 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_4_2 : 11 ∣ 2 ^ 4 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_4_3 : 13 ∣ 2 ^ 4 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_4_4 : 5 ∣ 2 ^ 4 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_4_5 : 227 ∣ 2 ^ 4 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_4_6 : 13 ∣ 2 ^ 4 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_4_7 : 11 ∣ 2 ^ 4 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_4_8 : 5 ∣ 2 ^ 4 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_4_9 : 13 ∣ 2 ^ 4 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_4_10 : 7 ∣ 2 ^ 4 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_4_11 : 17 ∣ 2 ^ 4 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_5_0 : 971 ∣ 2 ^ 5 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_5_1 : 5 ∣ 2 ^ 5 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_5_2 : 7 ∣ 2 ^ 5 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_5_3 : 31 ∣ 2 ^ 5 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_5_4 : 37 ∣ 2 ^ 5 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_5_5 : 5 ∣ 2 ^ 5 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_5_6 : 107 ∣ 2 ^ 5 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_5_7 : 41 ∣ 2 ^ 5 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_5_8 : 7 ∣ 2 ^ 5 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_5_9 : 5 ∣ 2 ^ 5 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_5_10 : 19 ∣ 2 ^ 5 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_5_11 : 61 ∣ 2 ^ 5 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_6_0 : 7 ∣ 2 ^ 6 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_6_1 : 131 ∣ 2 ^ 6 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_6_2 : 5 ∣ 2 ^ 6 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_6_3 : 11 ∣ 2 ^ 6 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_6_4 : 103 ∣ 2 ^ 6 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_6_5 : 211 ∣ 2 ^ 6 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_6_6 : 5 ∣ 2 ^ 6 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_6_7 : 29 ∣ 2 ^ 6 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_6_8 : 11 ∣ 2 ^ 6 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_6_9 : 31 ∣ 2 ^ 6 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_6_10 : 5 ∣ 2 ^ 6 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_6_11 : 89 ∣ 2 ^ 6 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_7_0 : 101 ∣ 2 ^ 7 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_7_1 : 17 ∣ 2 ^ 7 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_7_2 : 179 ∣ 2 ^ 7 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_7_3 : 5 ∣ 2 ^ 7 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_7_4 : 7 ∣ 2 ^ 7 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_7_5 : 971 ∣ 2 ^ 7 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_7_6 : 109 ∣ 2 ^ 7 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_7_7 : 5 ∣ 2 ^ 7 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_7_8 : 163 ∣ 2 ^ 7 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_7_9 : 107 ∣ 2 ^ 7 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_7_10 : 7 ∣ 2 ^ 7 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_7_11 : 5 ∣ 2 ^ 7 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_8_0 : 5 ∣ 2 ^ 8 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_8_1 : 29 ∣ 2 ^ 8 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_8_2 : 7 ∣ 2 ^ 8 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_8_3 : 17 ∣ 2 ^ 8 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_8_4 : 5 ∣ 2 ^ 8 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_8_5 : 13 ∣ 2 ^ 8 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_8_6 : 127 ∣ 2 ^ 8 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_8_7 : 19 ∣ 2 ^ 8 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_8_8 : 5 ∣ 2 ^ 8 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_8_9 : 11 ∣ 2 ^ 8 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_8_10 : 67 ∣ 2 ^ 8 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_8_11 : 13 ∣ 2 ^ 8 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_9_0 : 7 ∣ 2 ^ 9 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_9_1 : 5 ∣ 2 ^ 9 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_9_2 : 229 ∣ 2 ^ 9 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_9_3 : 269 ∣ 2 ^ 9 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_9_4 : 157 ∣ 2 ^ 9 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_9_5 : 5 ∣ 2 ^ 9 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_9_6 : 7 ∣ 2 ^ 9 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_9_7 : 691 ∣ 2 ^ 9 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_9_8 : 37 ∣ 2 ^ 9 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_9_9 : 5 ∣ 2 ^ 9 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_9_10 : 971 ∣ 2 ^ 9 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_9_11 : 43 ∣ 2 ^ 9 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_10_0 : 11 ∣ 2 ^ 10 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_10_1 : 41 ∣ 2 ^ 10 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_10_2 : 5 ∣ 2 ^ 10 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_10_3 : 31 ∣ 2 ^ 10 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_10_4 : 7 ∣ 2 ^ 10 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_10_5 : 11 ∣ 2 ^ 10 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_10_6 : 5 ∣ 2 ^ 10 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_10_7 : 17 ∣ 2 ^ 10 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_10_8 : 113 ∣ 2 ^ 10 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_10_9 : 41 ∣ 2 ^ 10 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_10_10 : 5 ∣ 2 ^ 10 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_10_11 : 19 ∣ 2 ^ 10 * 3 ^ 11 * M + 1 := by native_decide
private lemma dvd_11_0 : 61 ∣ 2 ^ 11 * 3 ^ 0 * M + 1 := by native_decide
private lemma dvd_11_1 : 37 ∣ 2 ^ 11 * 3 ^ 1 * M + 1 := by native_decide
private lemma dvd_11_2 : 7 ∣ 2 ^ 11 * 3 ^ 2 * M + 1 := by native_decide
private lemma dvd_11_3 : 5 ∣ 2 ^ 11 * 3 ^ 3 * M + 1 := by native_decide
private lemma dvd_11_4 : 19 ∣ 2 ^ 11 * 3 ^ 4 * M + 1 := by native_decide
private lemma dvd_11_5 : 59 ∣ 2 ^ 11 * 3 ^ 5 * M + 1 := by native_decide
private lemma dvd_11_6 : 29 ∣ 2 ^ 11 * 3 ^ 6 * M + 1 := by native_decide
private lemma dvd_11_7 : 5 ∣ 2 ^ 11 * 3 ^ 7 * M + 1 := by native_decide
private lemma dvd_11_8 : 7 ∣ 2 ^ 11 * 3 ^ 8 * M + 1 := by native_decide
private lemma dvd_11_9 : 17 ∣ 2 ^ 11 * 3 ^ 9 * M + 1 := by native_decide
private lemma dvd_11_10 : 61 ∣ 2 ^ 11 * 3 ^ 10 * M + 1 := by native_decide
private lemma dvd_11_11 : 5 ∣ 2 ^ 11 * 3 ^ 11 * M + 1 := by native_decide

theorem erdos203_grid_12x12_B1000_exists :
    ∃ m : ℕ, ∀ k l : ℕ, k < 12 → l < 12 →
      ∃ p ∈ Finset.range 1001, p.Prime ∧ 3 < p ∧
        (((Finset.univ : Finset (Fin (p-1) × Fin (p-1))).image
          (fun ab => (2 ^ ab.1.val * 3 ^ ab.2.val) % p)).card = p - 1) ∧
        p ∣ 2 ^ k * 3 ^ l * m + 1 := by
  refine ⟨M, fun k l hk hl => ?_⟩
  interval_cases k <;> interval_cases l
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_0_0⟩
  · exact ⟨13, Finset.mem_range.mpr (by omega), prime_13, by omega, index1_13, dvd_0_1⟩
  · exact ⟨43, Finset.mem_range.mpr (by omega), prime_43, by omega, index1_43, dvd_0_2⟩
  · exact ⟨17, Finset.mem_range.mpr (by omega), prime_17, by omega, index1_17, dvd_0_3⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_0_4⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_0_5⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_0_6⟩
  · exact ⟨13, Finset.mem_range.mpr (by omega), prime_13, by omega, index1_13, dvd_0_7⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_0_8⟩
  · exact ⟨19, Finset.mem_range.mpr (by omega), prime_19, by omega, index1_19, dvd_0_9⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_0_10⟩
  · exact ⟨79, Finset.mem_range.mpr (by omega), prime_79, by omega, index1_79, dvd_0_11⟩
  · exact ⟨37, Finset.mem_range.mpr (by omega), prime_37, by omega, index1_37, dvd_1_0⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_1_1⟩
  · exact ⟨19, Finset.mem_range.mpr (by omega), prime_19, by omega, index1_19, dvd_1_2⟩
  · exact ⟨89, Finset.mem_range.mpr (by omega), prime_89, by omega, index1_89, dvd_1_3⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_1_4⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_1_5⟩
  · exact ⟨127, Finset.mem_range.mpr (by omega), prime_127, by omega, index1_127, dvd_1_6⟩
  · exact ⟨79, Finset.mem_range.mpr (by omega), prime_79, by omega, index1_79, dvd_1_7⟩
  · exact ⟨29, Finset.mem_range.mpr (by omega), prime_29, by omega, index1_29, dvd_1_8⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_1_9⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_1_10⟩
  · exact ⟨59, Finset.mem_range.mpr (by omega), prime_59, by omega, index1_59, dvd_1_11⟩
  · exact ⟨67, Finset.mem_range.mpr (by omega), prime_67, by omega, index1_67, dvd_2_0⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_2_1⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_2_2⟩
  · exact ⟨79, Finset.mem_range.mpr (by omega), prime_79, by omega, index1_79, dvd_2_3⟩
  · exact ⟨691, Finset.mem_range.mpr (by omega), prime_691, by omega, index1_691, dvd_2_4⟩
  · exact ⟨53, Finset.mem_range.mpr (by omega), prime_53, by omega, index1_53, dvd_2_5⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_2_6⟩
  · exact ⟨17, Finset.mem_range.mpr (by omega), prime_17, by omega, index1_17, dvd_2_7⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_2_8⟩
  · exact ⟨83, Finset.mem_range.mpr (by omega), prime_83, by omega, index1_83, dvd_2_9⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_2_10⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_2_11⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_3_0⟩
  · exact ⟨157, Finset.mem_range.mpr (by omega), prime_157, by omega, index1_157, dvd_3_1⟩
  · exact ⟨29, Finset.mem_range.mpr (by omega), prime_29, by omega, index1_29, dvd_3_2⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_3_3⟩
  · exact ⟨59, Finset.mem_range.mpr (by omega), prime_59, by omega, index1_59, dvd_3_4⟩
  · exact ⟨43, Finset.mem_range.mpr (by omega), prime_43, by omega, index1_43, dvd_3_5⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_3_6⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_3_7⟩
  · exact ⟨53, Finset.mem_range.mpr (by omega), prime_53, by omega, index1_53, dvd_3_8⟩
  · exact ⟨17, Finset.mem_range.mpr (by omega), prime_17, by omega, index1_17, dvd_3_9⟩
  · exact ⟨103, Finset.mem_range.mpr (by omega), prime_103, by omega, index1_103, dvd_3_10⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_3_11⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_4_0⟩
  · exact ⟨83, Finset.mem_range.mpr (by omega), prime_83, by omega, index1_83, dvd_4_1⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_4_2⟩
  · exact ⟨13, Finset.mem_range.mpr (by omega), prime_13, by omega, index1_13, dvd_4_3⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_4_4⟩
  · exact ⟨227, Finset.mem_range.mpr (by omega), prime_227, by omega, index1_227, dvd_4_5⟩
  · exact ⟨13, Finset.mem_range.mpr (by omega), prime_13, by omega, index1_13, dvd_4_6⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_4_7⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_4_8⟩
  · exact ⟨13, Finset.mem_range.mpr (by omega), prime_13, by omega, index1_13, dvd_4_9⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_4_10⟩
  · exact ⟨17, Finset.mem_range.mpr (by omega), prime_17, by omega, index1_17, dvd_4_11⟩
  · exact ⟨971, Finset.mem_range.mpr (by omega), prime_971, by omega, index1_971, dvd_5_0⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_5_1⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_5_2⟩
  · exact ⟨31, Finset.mem_range.mpr (by omega), prime_31, by omega, index1_31, dvd_5_3⟩
  · exact ⟨37, Finset.mem_range.mpr (by omega), prime_37, by omega, index1_37, dvd_5_4⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_5_5⟩
  · exact ⟨107, Finset.mem_range.mpr (by omega), prime_107, by omega, index1_107, dvd_5_6⟩
  · exact ⟨41, Finset.mem_range.mpr (by omega), prime_41, by omega, index1_41, dvd_5_7⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_5_8⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_5_9⟩
  · exact ⟨19, Finset.mem_range.mpr (by omega), prime_19, by omega, index1_19, dvd_5_10⟩
  · exact ⟨61, Finset.mem_range.mpr (by omega), prime_61, by omega, index1_61, dvd_5_11⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_6_0⟩
  · exact ⟨131, Finset.mem_range.mpr (by omega), prime_131, by omega, index1_131, dvd_6_1⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_6_2⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_6_3⟩
  · exact ⟨103, Finset.mem_range.mpr (by omega), prime_103, by omega, index1_103, dvd_6_4⟩
  · exact ⟨211, Finset.mem_range.mpr (by omega), prime_211, by omega, index1_211, dvd_6_5⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_6_6⟩
  · exact ⟨29, Finset.mem_range.mpr (by omega), prime_29, by omega, index1_29, dvd_6_7⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_6_8⟩
  · exact ⟨31, Finset.mem_range.mpr (by omega), prime_31, by omega, index1_31, dvd_6_9⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_6_10⟩
  · exact ⟨89, Finset.mem_range.mpr (by omega), prime_89, by omega, index1_89, dvd_6_11⟩
  · exact ⟨101, Finset.mem_range.mpr (by omega), prime_101, by omega, index1_101, dvd_7_0⟩
  · exact ⟨17, Finset.mem_range.mpr (by omega), prime_17, by omega, index1_17, dvd_7_1⟩
  · exact ⟨179, Finset.mem_range.mpr (by omega), prime_179, by omega, index1_179, dvd_7_2⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_7_3⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_7_4⟩
  · exact ⟨971, Finset.mem_range.mpr (by omega), prime_971, by omega, index1_971, dvd_7_5⟩
  · exact ⟨109, Finset.mem_range.mpr (by omega), prime_109, by omega, index1_109, dvd_7_6⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_7_7⟩
  · exact ⟨163, Finset.mem_range.mpr (by omega), prime_163, by omega, index1_163, dvd_7_8⟩
  · exact ⟨107, Finset.mem_range.mpr (by omega), prime_107, by omega, index1_107, dvd_7_9⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_7_10⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_7_11⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_8_0⟩
  · exact ⟨29, Finset.mem_range.mpr (by omega), prime_29, by omega, index1_29, dvd_8_1⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_8_2⟩
  · exact ⟨17, Finset.mem_range.mpr (by omega), prime_17, by omega, index1_17, dvd_8_3⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_8_4⟩
  · exact ⟨13, Finset.mem_range.mpr (by omega), prime_13, by omega, index1_13, dvd_8_5⟩
  · exact ⟨127, Finset.mem_range.mpr (by omega), prime_127, by omega, index1_127, dvd_8_6⟩
  · exact ⟨19, Finset.mem_range.mpr (by omega), prime_19, by omega, index1_19, dvd_8_7⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_8_8⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_8_9⟩
  · exact ⟨67, Finset.mem_range.mpr (by omega), prime_67, by omega, index1_67, dvd_8_10⟩
  · exact ⟨13, Finset.mem_range.mpr (by omega), prime_13, by omega, index1_13, dvd_8_11⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_9_0⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_9_1⟩
  · exact ⟨229, Finset.mem_range.mpr (by omega), prime_229, by omega, index1_229, dvd_9_2⟩
  · exact ⟨269, Finset.mem_range.mpr (by omega), prime_269, by omega, index1_269, dvd_9_3⟩
  · exact ⟨157, Finset.mem_range.mpr (by omega), prime_157, by omega, index1_157, dvd_9_4⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_9_5⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_9_6⟩
  · exact ⟨691, Finset.mem_range.mpr (by omega), prime_691, by omega, index1_691, dvd_9_7⟩
  · exact ⟨37, Finset.mem_range.mpr (by omega), prime_37, by omega, index1_37, dvd_9_8⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_9_9⟩
  · exact ⟨971, Finset.mem_range.mpr (by omega), prime_971, by omega, index1_971, dvd_9_10⟩
  · exact ⟨43, Finset.mem_range.mpr (by omega), prime_43, by omega, index1_43, dvd_9_11⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_10_0⟩
  · exact ⟨41, Finset.mem_range.mpr (by omega), prime_41, by omega, index1_41, dvd_10_1⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_10_2⟩
  · exact ⟨31, Finset.mem_range.mpr (by omega), prime_31, by omega, index1_31, dvd_10_3⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_10_4⟩
  · exact ⟨11, Finset.mem_range.mpr (by omega), prime_11, by omega, index1_11, dvd_10_5⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_10_6⟩
  · exact ⟨17, Finset.mem_range.mpr (by omega), prime_17, by omega, index1_17, dvd_10_7⟩
  · exact ⟨113, Finset.mem_range.mpr (by omega), prime_113, by omega, index1_113, dvd_10_8⟩
  · exact ⟨41, Finset.mem_range.mpr (by omega), prime_41, by omega, index1_41, dvd_10_9⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_10_10⟩
  · exact ⟨19, Finset.mem_range.mpr (by omega), prime_19, by omega, index1_19, dvd_10_11⟩
  · exact ⟨61, Finset.mem_range.mpr (by omega), prime_61, by omega, index1_61, dvd_11_0⟩
  · exact ⟨37, Finset.mem_range.mpr (by omega), prime_37, by omega, index1_37, dvd_11_1⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_11_2⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_11_3⟩
  · exact ⟨19, Finset.mem_range.mpr (by omega), prime_19, by omega, index1_19, dvd_11_4⟩
  · exact ⟨59, Finset.mem_range.mpr (by omega), prime_59, by omega, index1_59, dvd_11_5⟩
  · exact ⟨29, Finset.mem_range.mpr (by omega), prime_29, by omega, index1_29, dvd_11_6⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_11_7⟩
  · exact ⟨7, Finset.mem_range.mpr (by omega), prime_7, by omega, index1_7, dvd_11_8⟩
  · exact ⟨17, Finset.mem_range.mpr (by omega), prime_17, by omega, index1_17, dvd_11_9⟩
  · exact ⟨61, Finset.mem_range.mpr (by omega), prime_61, by omega, index1_61, dvd_11_10⟩
  · exact ⟨5, Finset.mem_range.mpr (by omega), prime_5, by omega, index1_5, dvd_11_11⟩
