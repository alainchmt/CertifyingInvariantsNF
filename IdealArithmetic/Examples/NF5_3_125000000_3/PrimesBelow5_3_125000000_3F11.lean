
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}

def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 0, 0, 0, 0]] i)))

def SI541N0: IdealEqSpanCertificate' Table ![![541, 0, 0, 0, 0]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![0, 0, 541, 0, 0], ![0, 0, 0, 541, 0], ![0, 0, 0, 0, 541]] where
  M :=![![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![0, 0, 541, 0, 0], ![0, 0, 0, 541, 0], ![0, 0, 0, 0, 541]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P0 : CertificateIrreducibleZModOfList' 541 5 2 9 [522, 4, 407, 252, 447, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 329, 460, 484, 99], [404, 10, 495, 316, 382], [96, 140, 518, 365, 434], [39, 61, 150, 458, 167], [0, 1]]
 g := ![![[62, 430, 9, 129, 380], [388, 333, 394, 532], [492, 381, 211, 112, 15], [110, 44, 118, 421, 243], [504, 160, 503, 412, 285], [422, 441, 335, 173], [515, 469, 94, 1], [], []], ![[473, 267, 209, 379, 513, 400, 100, 259], [339, 155, 18, 66], [260, 18, 103, 281, 66, 525, 275, 116], [438, 106, 376, 436, 210, 356, 531, 96], [198, 437, 291, 266, 253, 249, 151, 200], [256, 79, 261, 431], [399, 10, 234, 31], [62, 262, 57, 49], [190, 4, 46, 63]], ![[142, 206, 160, 36, 13, 89, 107, 366], [364, 201, 399, 397], [117, 448, 166, 464, 299, 519, 44, 463], [277, 373, 267, 208, 296, 176, 224, 141], [443, 82, 90, 148, 463, 65, 500, 60], [124, 377, 394, 142], [34, 476, 475, 240], [209, 26, 21, 315], [484, 13, 480, 395]], ![[150, 375, 248, 191, 516, 458, 275, 70], [38, 219, 107, 532], [476, 203, 291, 494, 502, 536, 175, 356], [280, 169, 515, 57, 468, 417, 180, 156], [376, 285, 518, 131, 18, 514, 530, 342], [469, 521, 379, 207], [478, 332, 482, 394], [156, 235, 160, 252], [72, 460, 492, 88]], ![[150, 63, 391, 530, 308, 71, 390, 473], [246, 370, 355, 221], [102, 258, 235, 385, 398, 326, 252, 374], [393, 182, 136, 478, 274, 322, 76, 86], [521, 76, 511, 201, 427, 393, 60, 344], [26, 243, 236, 151], [280, 426, 492, 161], [510, 471, 368, 448], [388, 497, 290, 298]]]
 h' := ![![[96, 329, 460, 484, 99], [418, 41, 181, 456, 238], [151, 468, 335, 107, 385], [467, 131, 216, 387, 352], [379, 482, 458, 73, 28], [489, 403, 144, 531, 291], [47, 359, 213, 334, 160], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[404, 10, 495, 316, 382], [110, 534, 383, 533, 98], [474, 238, 131, 24, 74], [10, 131, 180, 203, 255], [339, 66, 190, 510, 73], [164, 388, 152, 263, 49], [528, 482, 3, 341, 56], [174, 335, 416, 251, 471], [383, 269, 528, 332, 7], [96, 329, 460, 484, 99]], ![[96, 140, 518, 365, 434], [381, 509, 354, 485, 271], [223, 253, 412, 374, 83], [172, 11, 14, 155, 111], [276, 396, 306, 361, 164], [18, 411, 498, 31, 394], [340, 99, 78, 190, 356], [482, 391, 101, 498, 326], [374, 440, 68, 189, 72], [404, 10, 495, 316, 382]], ![[39, 61, 150, 458, 167], [193, 486, 454, 494, 111], [114, 172, 336, 505, 385], [523, 428, 525, 89, 416], [242, 395, 83, 180, 325], [33, 334, 315, 516, 250], [150, 207, 23, 464, 289], [232, 216, 415, 361, 351], [305, 167, 421, 263, 198], [96, 140, 518, 365, 434]], ![[0, 1], [26, 53, 251, 196, 364], [155, 492, 409, 72, 155], [203, 381, 147, 248, 489], [292, 284, 45, 499, 492], [61, 87, 514, 282, 98], [342, 476, 224, 294, 221], [398, 140, 150, 513, 474], [237, 206, 64, 298, 264], [39, 61, 150, 458, 167]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [338, 308, 167, 388], [], [], []]
 b := ![[], [50, 124, 26, 75, 395], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N0 : CertifiedPrimeIdeal' SI541N0 541 where
  n := 5
  hpos := by decide
  P := [522, 4, 407, 252, 447, 1]
  hirr := P541P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38119426477054402, 18657566566633276, -40623441520851557, -21832394333599951, -76358811895510105]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![70461047092522, 34487184041836, -75089540703977, -40355627234011, -141143829751405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N0 : Ideal.IsPrime I541N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N0 B_one_repr
lemma NI541N0 : Nat.card (O ⧸ I541N0) = 46343232758701 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N0

def PBC541 : ContainsPrimesAboveP 541 ![I541N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI541N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![541, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 541 (by decide) 𝕀



lemma PB547I11_primes (p : ℕ) :
  p ∈ Set.range ![541] ↔ Nat.Prime p ∧ 523 < p ∧ p ≤ 546 := by
  rw [← List.mem_ofFn']
  convert primes_range 523 546 (by omega)

def PB547I11 : PrimesBelowBoundCertificateInterval O 523 546 547 where
  m := 1
  g := ![1]
  P := ![541]
  hP := PB547I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I541N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC541
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![46343232758701]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI541N0
  β := ![]
  Il := ![[]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
