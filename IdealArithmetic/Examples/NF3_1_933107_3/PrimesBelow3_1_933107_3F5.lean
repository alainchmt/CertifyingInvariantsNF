
import IdealArithmetic.Examples.NF3_1_933107_3.RI3_1_933107_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![11, 1, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![11, 1, 0]] 
 ![![263, 0, 0], ![11, 1, 0], ![118, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![11, 1, 0], ![2, 10, 8], ![23, -31, 12]]]
  hmulB := by decide  
  f := ![![![-4319, -21600, -17280], ![0, 568080, 0]], ![![-180, -900, -720], ![1, 23670, 0]], ![![-1935, -9691, -7753], ![-67, 254880, 0]]]
  g := ![![![1, 0, 0], ![-11, 263, 0], ![-118, 0, 263]], ![![0, 1, 0], ![-4, 10, 8], ![-4, -31, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N0 : Nat.card (O ⧸ I263N0) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N0)

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := prime_ideal_of_norm_prime hp263.out _ NI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![110, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![110, 1, 0]] 
 ![![263, 0, 0], ![110, 1, 0], ![211, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![110, 1, 0], ![2, 109, 8], ![23, -31, 111]]]
  hmulB := by decide  
  f := ![![![-109, -5995, -440], ![0, 14465, 0]], ![![-46, -2507, -184], ![1, 6049, 0]], ![![-123, -4810, -353], ![85, 11605, 0]]]
  g := ![![![1, 0, 0], ![-110, 263, 0], ![-211, 0, 263]], ![![0, 1, 0], ![-52, 109, 8], ![-76, -31, 111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-121, 1, 0]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-121, 1, 0]] 
 ![![263, 0, 0], ![142, 1, 0], ![259, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-121, 1, 0], ![2, -122, 8], ![23, -31, -120]]]
  hmulB := by decide  
  f := ![![![78855, -6522254, 427704], ![-61016, -14060769, 0]], ![![42606, -3521405, 230920], ![-32874, -7591495, 0]], ![![77750, -6423057, 421199], ![-59883, -13846917, 0]]]
  g := ![![![1, 0, 0], ![-142, 263, 0], ![-259, 0, 263]], ![![-1, 1, 0], ![58, -122, 8], ![135, -31, -120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![11, 1, 0]] ![![263, 0, 0], ![110, 1, 0]]
  ![![263, 0, 0], ![20, 15, 1]] where
 M := ![![![69169, 0, 0], ![28930, 263, 0]], ![![2893, 263, 0], ![1212, 120, 8]]]
 hmul := by decide  
 g := ![![![![243, -15, -1], ![263, 0, 0]], ![![90, -14, -1], ![263, 0, 0]]], ![![![-9, -14, -1], ![263, 0, 0]], ![![4, 0, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![20, 15, 1]] ![![263, 0, 0], ![-121, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-31823, 263, 0]], ![![5260, 3945, 263], ![-2367, -1841, 0]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-121, 1, 0]]], ![![![20, 15, 1]], ![![-9, -7, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
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


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [42, 208, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [217, 55, 178], [249, 213, 91], [0, 1]]
 g := ![![[219, 9, 62], [206, 253], [64, 213, 67], [63, 162, 180], [165, 216], [112, 202], [197, 1], []], ![[60, 248, 143, 159], [227, 9], [132, 218, 155, 32], [240, 146, 217, 261], [38, 67], [122, 215], [142, 177], [84, 211]], ![[134, 45, 198, 198], [209, 177], [18, 101, 33, 17], [127, 205, 238, 74], [186, 58], [133, 126], [247, 66], [171, 211]]]
 h' := ![![[217, 55, 178], [229, 7, 185], [2, 122, 210], [44, 150, 41], [48, 172, 218], [59, 9, 111], [65, 139, 134], [0, 0, 1], [0, 1]], ![[249, 213, 91], [217, 231, 32], [41, 101, 3], [155, 31, 194], [41, 86, 116], [125, 26, 228], [243, 0, 22], [252, 226, 213], [217, 55, 178]], ![[0, 1], [35, 31, 52], [118, 46, 56], [87, 88, 34], [53, 11, 204], [8, 234, 199], [138, 130, 113], [212, 43, 55], [249, 213, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218, 165], []]
 b := ![[], [264, 131, 191], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [42, 208, 72, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-427441, 344051, -1943256]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1589, 1279, -7224]
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


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [172, 153, 255, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 46, 122], [210, 224, 149], [0, 1]]
 g := ![![[61, 193, 256], [118, 22, 106], [57, 166, 40], [209, 213, 206], [257, 77], [210, 40], [16, 1], []], ![[55, 19, 77, 129], [121, 47, 218, 166], [66, 254, 83, 148], [6, 261, 99, 156], [186, 179], [72, 164], [199, 41], [48, 250]], ![[79, 109, 232, 19], [9, 209, 90, 159], [59, 78, 174, 111], [51, 48, 183, 42], [26, 83], [237, 81], [266, 219], [21, 250]]]
 h' := ![![[77, 46, 122], [29, 249, 255], [223, 207, 102], [95, 197, 168], [167, 255, 54], [61, 42, 211], [229, 90, 103], [0, 0, 1], [0, 1]], ![[210, 224, 149], [66, 98, 236], [215, 210, 135], [205, 117, 149], [105, 57, 117], [98, 268, 85], [267, 77, 177], [112, 100, 224], [77, 46, 122]], ![[0, 1], [169, 195, 51], [69, 125, 34], [157, 228, 225], [254, 230, 100], [173, 232, 246], [4, 104, 262], [109, 171, 46], [210, 224, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 35], []]
 b := ![[], [164, 247, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [172, 153, 255, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![599452, -723028, 714898]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2212, -2668, 2638]
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



lemma PB274I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 273 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 273 (by omega)

def PB274I5 : PrimesBelowBoundCertificateInterval O 257 273 274 where
  m := 3
  g := ![3, 1, 1]
  P := ![263, 269, 271]
  hP := PB274I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1, I263N2]
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
    · exact ![263, 263, 263]
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
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
  β := ![I263N0, I263N1, I263N2]
  Il := ![[I263N0, I263N1, I263N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
