
import IdealArithmetic.Examples.NF3_1_946067_1.RI3_1_946067_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0]] 
 ![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [261, 138, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 24, 163], [138, 238, 100], [0, 1]]
 g := ![![[154, 100, 122], [260, 72, 1], [227, 75, 138], [133, 17], [123, 256], [17, 133], [183, 1], []], ![[171, 231, 199, 79], [230, 192, 198, 126], [22, 256, 189, 77], [262, 89], [17, 35], [6, 187], [64, 99], [243, 6]], ![[130, 104, 103, 198], [162, 238, 182, 111], [103, 61, 32, 8], [165, 129], [105, 157], [203, 221], [172, 50], [43, 6]]]
 h' := ![![[45, 24, 163], [257, 219, 139], [191, 76, 1], [179, 228, 123], [121, 31, 198], [123, 252, 247], [103, 259, 213], [0, 0, 1], [0, 1]], ![[138, 238, 100], [146, 166, 136], [73, 181, 2], [10, 107, 162], [46, 235, 103], [217, 250, 185], [87, 261, 72], [144, 198, 238], [45, 24, 163]], ![[0, 1], [111, 141, 251], [90, 6, 260], [12, 191, 241], [205, 260, 225], [235, 24, 94], [108, 6, 241], [194, 65, 24], [138, 238, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [206, 135], []]
 b := ![[], [91, 70, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [261, 138, 80, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36031, 789, 789]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-137, 3, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def PBC263 : ContainsPrimesAboveP 263 ![I263N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![263, 0, 0]]) timesTableT_eq_Table B_one_repr 263 (by decide) 𝕀

instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0]] 
 ![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [9, 76, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [267, 9, 33], [239, 259, 236], [0, 1]]
 g := ![![[60, 237, 255], [224, 9], [9, 111, 235], [195, 85, 172], [187, 199], [19, 244], [237, 1], []], ![[215, 252, 226, 171], [55, 70], [117, 250, 260, 178], [188, 99, 93, 83], [183, 126], [229, 1], [75, 100], [178, 13]], ![[133, 99, 189, 250], [26, 117], [43, 248, 9, 82], [116, 120, 75, 134], [118, 150], [53, 258], [221, 81], [244, 13]]]
 h' := ![![[267, 9, 33], [241, 6, 229], [188, 175, 3], [128, 242, 43], [254, 232, 248], [190, 202, 198], [19, 2, 141], [0, 0, 1], [0, 1]], ![[239, 259, 236], [127, 148, 60], [155, 75, 96], [63, 46, 24], [261, 214, 65], [264, 196, 113], [119, 265, 1], [16, 38, 259], [267, 9, 33]], ![[0, 1], [253, 115, 249], [196, 19, 170], [86, 250, 202], [66, 92, 225], [66, 140, 227], [143, 2, 127], [49, 231, 9], [239, 259, 236]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154, 92], []]
 b := ![[], [20, 159, 201], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [9, 76, 32, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![671155, 417757, 43847]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2495, 1553, 163]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def PBC269 : ContainsPrimesAboveP 269 ![I269N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![269, 0, 0]]) timesTableT_eq_Table B_one_repr 269 (by decide) 𝕀

instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0]] 
 ![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [7, 60, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [157, 93, 92], [113, 177, 179], [0, 1]]
 g := ![![[55, 131, 9], [33, 43, 39], [204, 11, 14], [239, 226, 39], [267, 178], [21, 229], [270, 1], []], ![[21, 9, 0, 6], [19, 165, 165, 142], [224, 216, 35, 93], [250, 265, 22, 42], [190, 179], [222, 200], [40, 164], [247, 63]], ![[263, 92, 144, 212], [70, 181, 97, 72], [156, 168, 192, 166], [131, 143, 193, 25], [253, 245], [268, 160], [196, 248], [160, 63]]]
 h' := ![![[157, 93, 92], [40, 67, 268], [198, 190, 227], [224, 267, 234], [147, 80, 44], [173, 47, 146], [7, 53, 212], [0, 0, 1], [0, 1]], ![[113, 177, 179], [64, 180, 213], [129, 195, 207], [57, 66, 129], [59, 254, 243], [247, 211, 85], [208, 17, 124], [156, 120, 177], [157, 93, 92]], ![[0, 1], [35, 24, 61], [164, 157, 108], [191, 209, 179], [68, 208, 255], [22, 13, 40], [270, 201, 206], [267, 151, 93], [113, 177, 179]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [261, 68], []]
 b := ![[], [268, 6, 176], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [7, 60, 1, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-200269, -25474, -21138]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-739, -94, -78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 19902511 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def PBC271 : ContainsPrimesAboveP 271 ![I271N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![271, 0, 0]]) timesTableT_eq_Table B_one_repr 271 (by decide) 𝕀



lemma PB276I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 275 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 275 (by omega)

def PB276I5 : PrimesBelowBoundCertificateInterval O 257 275 276 where
  m := 3
  g := ![1, 1, 1]
  P := ![263, 269, 271]
  hP := PB276I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0]
    · exact ![I269N0]
    · exact ![I271N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
    · exact PBC271
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![18191447]
    · exact ![19465109]
    · exact ![19902511]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
  β := ![]
  Il := ![[], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
