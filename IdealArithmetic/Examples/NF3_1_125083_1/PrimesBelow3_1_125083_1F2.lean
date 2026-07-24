
import IdealArithmetic.Examples.NF3_1_125083_1.RI3_1_125083_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [52, 45, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 21, 75], [31, 61, 8], [0, 1]]
 g := ![![[69, 25, 27], [20, 13, 29], [12, 37], [62, 59], [16, 12, 1], []], ![[51, 28, 0, 63], [0, 20, 41, 51], [61, 9], [64, 51], [38, 29, 8, 29], [17, 64]], ![[18, 31, 0, 74], [8, 39, 1, 42], [31, 48], [28, 26], [49, 59, 74, 42], [1, 64]]]
 h' := ![![[64, 21, 75], [39, 10, 39], [80, 72, 19], [17, 16, 28], [81, 67, 15], [0, 0, 1], [0, 1]], ![[31, 61, 8], [36, 29, 58], [63, 49, 2], [9, 6, 3], [10, 3, 47], [58, 6, 61], [64, 21, 75]], ![[0, 1], [27, 44, 69], [78, 45, 62], [69, 61, 52], [23, 13, 21], [79, 77, 21], [31, 61, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 51], []]
 b := ![[], [32, 66, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [52, 45, 71, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11952, 3735, -581]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![144, 45, -7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![27, -5, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![27, -5, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![27, 84, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![27, -5, 1], ![70, 20, -4], ![-280, 98, 16]]]
  hmulB := by decide  
  f := ![![![-26, 5, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -84, 89]], ![![0, -1, 1], ![2, 4, -4], ![-8, -14, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [83, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 88], [0, 1]]
 g := ![![[28, 8], [49], [47], [80, 1], [37, 11], [1]], ![[37, 81], [49], [47], [70, 88], [16, 78], [1]]]
 h' := ![![[79, 88], [63, 39], [83, 82], [35, 74], [44, 88], [6, 79], [0, 1]], ![[0, 1], [29, 50], [64, 7], [7, 15], [54, 1], [17, 10], [79, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [76, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [83, 10, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-136, 635, -38]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 43, -38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![4, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![4, 1, 0]] 
 ![![89, 0, 0], ![4, 1, 0], ![73, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![4, 1, 0], ![0, 4, 1], ![70, -7, 5]]]
  hmulB := by decide  
  f := ![![![245, 61, 0], ![-5429, 0, 0]], ![![4, 1, 0], ![-88, 0, 0]], ![![205, 51, 0], ![-4543, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 89, 0], ![-73, 0, 89]], ![![0, 1, 0], ![-1, 4, 1], ![-3, -7, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![27, -5, 1]] ![![89, 0, 0], ![4, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![356, 89, 0]], ![![2403, -445, 89], ![178, 0, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![4, 1, 0]]], ![![![27, -5, 1]], ![![2, 0, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [31, 42, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 54, 96], [15, 42, 1], [0, 1]]
 g := ![![[25, 55, 16], [], [80, 62], [54, 25], [36, 62], [1]], ![[57, 29, 43, 25], [77, 93], [65, 50], [77, 50], [67, 61], [85, 35, 49, 96]], ![[52, 34, 81, 81], [85, 93], [11, 24], [68, 96], [26, 79], [12, 1, 45, 1]]]
 h' := ![![[1, 54, 96], [44, 13, 93], [74, 44], [41, 20, 16], [39, 43, 5], [66, 55, 16], [0, 1]], ![[15, 42, 1], [91, 70, 13], [21, 48, 53], [22, 19, 70], [88, 8, 70], [82, 66, 35], [1, 54, 96]], ![[0, 1], [2, 14, 88], [55, 5, 44], [28, 58, 11], [83, 46, 22], [93, 73, 46], [15, 42, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 1], []]
 b := ![[], [34, 86, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [31, 42, 81, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69355, -5626, -1164]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![715, -58, -12]
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
  g := ![1, 2, 1]
  P := ![83, 89, 97]
  hP := PB101I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
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
    · exact ![571787]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
  β := ![I89N1]
  Il := ![[], [I89N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
