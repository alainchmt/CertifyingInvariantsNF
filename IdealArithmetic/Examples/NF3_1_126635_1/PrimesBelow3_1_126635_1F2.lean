
import IdealArithmetic.Examples.NF3_1_126635_1.RI3_1_126635_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-36, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-36, 1, 0]] 
 ![![83, 0, 0], ![47, 1, 0], ![78, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-36, 1, 0], ![0, -35, 3], ![-72, 7, -36]]]
  hmulB := by decide  
  f := ![![![1441, -40, 0], ![3320, 0, 0]], ![![829, -23, 0], ![1910, 0, 0]], ![![1362, -26, -1], ![3138, 28, 0]]]
  g := ![![![1, 0, 0], ![-47, 83, 0], ![-78, 0, 83]], ![![-1, 1, 0], ![17, -35, 3], ![29, 7, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-25, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-25, 1, 0]] 
 ![![83, 0, 0], ![58, 1, 0], ![49, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-25, 1, 0], ![0, -24, 3], ![-72, 7, -25]]]
  hmulB := by decide  
  f := ![![![801, -32, 0], ![2656, 0, 0]], ![![576, -23, 0], ![1910, 0, 0]], ![![503, -12, -1], ![1668, 28, 0]]]
  g := ![![![1, 0, 0], ![-58, 83, 0], ![-49, 0, 83]], ![![-1, 1, 0], ![15, -24, 3], ![9, 7, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-23, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-23, 1, 0]] 
 ![![83, 0, 0], ![60, 1, 0], ![25, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-23, 1, 0], ![0, -22, 3], ![-72, 7, -23]]]
  hmulB := by decide  
  f := ![![![1588, -69, 0], ![5727, 0, 0]], ![![1174, -51, 0], ![4234, 0, 0]], ![![516, -15, -1], ![1861, 28, 0]]]
  g := ![![![1, 0, 0], ![-60, 83, 0], ![-25, 0, 83]], ![![-1, 1, 0], ![15, -22, 3], ![1, 7, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-36, 1, 0]] ![![83, 0, 0], ![-25, 1, 0]]
  ![![83, 0, 0], ![-32, -20, 1]] where
 M := ![![![6889, 0, 0], ![-2075, 83, 0]], ![![-2988, 83, 0], ![900, -60, 3]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![7, 21, -1], ![83, 0, 0]]], ![![![-4, 21, -1], ![83, 0, 0]], ![![12, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-32, -20, 1]] ![![83, 0, 0], ![-23, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1909, 83, 0]], ![![-2656, -1660, 83], ![664, 415, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-23, 1, 0]]], ![![![-32, -20, 1]], ![![8, 5, -1]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-36, -29, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-36, -29, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![53, 60, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-36, -29, 1], ![-72, -58, -87], ![2112, -227, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -60, 89]], ![![-1, -1, 1], ![51, 58, -87], ![41, 17, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [52, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 88], [0, 1]]
 g := ![![[64, 73], [39], [80], [77, 80], [14, 68], [1]], ![[1, 16], [39], [80], [36, 9], [37, 21], [1]]]
 h' := ![![[54, 88], [61, 47], [24, 22], [1, 76], [73, 13], [37, 54], [0, 1]], ![[0, 1], [18, 42], [55, 67], [11, 13], [63, 76], [16, 35], [54, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [67, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [52, 35, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-788, -526, 12]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -14, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-2, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-2, 1, 0]] 
 ![![89, 0, 0], ![87, 1, 0], ![29, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-2, 1, 0], ![0, -1, 3], ![-72, 7, -2]]]
  hmulB := by decide  
  f := ![![![3, 43, -132], ![89, 3916, 0]], ![![1, 43, -129], ![1, 3827, 0]], ![![1, 14, -43], ![30, 1276, 0]]]
  g := ![![![1, 0, 0], ![-87, 89, 0], ![-29, 0, 89]], ![![-1, 1, 0], ![0, -1, 3], ![-7, 7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-36, -29, 1]] ![![89, 0, 0], ![-2, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-178, 89, 0]], ![![-3204, -2581, 89], ![0, 0, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-2, 1, 0]]], ![![![-36, -29, 1]], ![![0, 0, -1]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [76, 28, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 41, 43], [69, 55, 54], [0, 1]]
 g := ![![[60, 5, 50], [85, 49], [90, 2], [84, 12], [30, 65], [1]], ![[14, 28, 42, 94], [47, 96], [54, 18], [55, 49], [82, 2], [84, 14, 46, 64]], ![[65, 28, 44, 70], [62, 65], [50, 8], [55, 72], [82, 31], [15, 46, 33, 33]]]
 h' := ![![[96, 41, 43], [8, 0, 70], [39, 31, 90], [34, 64, 83], [4, 28, 77], [21, 69, 68], [0, 1]], ![[69, 55, 54], [15, 60, 67], [17, 4, 75], [85, 90, 42], [71, 50, 7], [17, 5, 14], [96, 41, 43]], ![[0, 1], [49, 37, 57], [69, 62, 29], [38, 40, 69], [12, 19, 13], [91, 23, 15], [69, 55, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 34], []]
 b := ![[], [41, 94, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [76, 28, 29, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![195940, -53059, 8536]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2020, -547, 88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀



lemma PB101I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 100 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 100 (by omega)

def PB101I2 : PrimesBelowBoundCertificateInterval O 79 100 101 where
  m := 3
  g := ![3, 2, 1]
  P := ![83, 89, 97]
  hP := PB101I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![912673]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
  β := ![I83N0, I83N1, I83N2, I89N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
