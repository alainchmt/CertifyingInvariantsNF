
import IdealArithmetic.Examples.NF3_1_119660_3.RI3_1_119660_3
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [53, 40, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 22, 72], [36, 60, 11], [0, 1]]
 g := ![![[27, 40, 9], [56, 61, 23], [42, 4], [0, 78], [50, 16, 1], []], ![[11, 65, 70, 80], [71, 22, 13, 34], [76, 65], [21, 40], [7, 13, 39, 74], [41, 38]], ![[52, 76, 57, 81], [77, 80, 14, 81], [28, 44], [6, 49], [73, 40, 35, 12], [19, 38]]]
 h' := ![![[63, 22, 72], [20, 45, 80], [66, 36, 43], [36, 36, 2], [6, 57, 24], [0, 0, 1], [0, 1]], ![[36, 60, 11], [40, 67, 72], [48, 50, 26], [3, 24, 56], [55, 6, 66], [53, 31, 60], [63, 22, 72]], ![[0, 1], [26, 54, 14], [11, 80, 14], [1, 23, 25], [30, 20, 76], [40, 52, 22], [36, 60, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 69], []]
 b := ![[], [76, 16, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [53, 40, 67, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6059, 3984, -747]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, 48, -9]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [86, 26, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 53, 53], [72, 35, 36], [0, 1]]
 g := ![![[48, 33, 71], [78, 8], [23, 47], [78, 17, 21], [83, 38, 1], []], ![[76, 41, 13, 39], [68, 10], [9, 42], [31, 85, 81, 55], [3, 52, 43, 44], [42, 50]], ![[6, 10, 46, 72], [51, 81], [1, 8], [60, 67, 16, 22], [37, 39, 30, 20], [59, 50]]]
 h' := ![![[55, 53, 53], [57, 76, 58], [1, 61, 39], [56, 38, 74], [71, 3, 33], [0, 0, 1], [0, 1]], ![[72, 35, 36], [6, 62, 6], [43, 23, 59], [4, 72, 65], [0, 17, 68], [36, 82, 35], [55, 53, 53]], ![[0, 1], [72, 40, 25], [50, 5, 80], [74, 68, 39], [1, 69, 77], [21, 7, 53], [72, 35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 61], []]
 b := ![[], [85, 36, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [86, 26, 51, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107690, 3738, -5607]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1210, 42, -63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-1, 31, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-1, 31, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![96, 31, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-1, 31, 1], ![66, -9, 31], ![2046, -182, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -31, 97]], ![![-1, 0, 1], ![-30, -10, 31], ![30, 1, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [72, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 96], [0, 1]]
 g := ![![[56, 31], [44], [62], [79], [6], [42, 1]], ![[0, 66], [44], [62], [79], [6], [84, 96]]]
 h' := ![![[42, 96], [49, 15], [93, 23], [17, 81], [51, 51], [80, 43], [0, 1]], ![[0, 1], [0, 82], [89, 74], [24, 16], [59, 46], [43, 54], [42, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [2, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [72, 55, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![516, 9, 66]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, -21, 66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-31, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-31, 1, 0]] 
 ![![97, 0, 0], ![66, 1, 0], ![9, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-31, 1, 0], ![0, -31, 1], ![66, -8, -31]]]
  hmulB := by decide  
  f := ![![![2605, -84, 0], ![8148, 0, 0]], ![![1768, -57, 0], ![5530, 0, 0]], ![![289, -9, 0], ![904, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 97, 0], ![-9, 0, 97]], ![![-1, 1, 0], ![21, -31, 1], ![9, -8, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-1, 31, 1]] ![![97, 0, 0], ![-31, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3007, 97, 0]], ![![-97, 3007, 97], ![97, -970, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-31, 1, 0]]], ![![![-1, 31, 1]], ![![1, -10, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)


lemma PB98I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 97 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 97 (by omega)

def PB98I2 : PrimesBelowBoundCertificateInterval O 79 97 98 where
  m := 3
  g := ![1, 1, 2]
  P := ![83, 89, 97]
  hP := PB98I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
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
    · exact ![704969]
    · exact ![9409, 97]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
  β := ![I97N1]
  Il := ![[], [], [I97N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
