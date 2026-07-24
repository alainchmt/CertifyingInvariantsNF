
import IdealArithmetic.Examples.NF3_1_107543_1.RI3_1_107543_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [2, 49, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 64, 2], [30, 18, 81], [0, 1]]
 g := ![![[65, 65, 59], [34, 4, 78], [68, 21], [13, 61], [74, 66, 1], []], ![[76, 63, 13, 73], [14, 30, 50, 73], [46, 11], [68, 3], [1, 72, 28, 67], [22, 4]], ![[43, 70, 52, 4], [63, 37, 46, 40], [29, 61], [69, 44], [75, 14, 17, 25], [26, 4]]]
 h' := ![![[36, 64, 2], [15, 64, 68], [24, 45, 24], [49, 73, 41], [18, 60, 71], [0, 0, 1], [0, 1]], ![[30, 18, 81], [56, 70, 24], [69, 9, 24], [59, 6, 54], [19, 5, 70], [7, 36, 18], [36, 64, 2]], ![[0, 1], [5, 32, 74], [63, 29, 35], [72, 4, 71], [25, 18, 25], [18, 47, 64], [30, 18, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 7], []]
 b := ![[], [59, 42, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [2, 49, 17, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1086719, -205757, -45650]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13093, -2479, -550]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31616, 3796, -2851]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-31616, 3796, -2851]] 
 ![![89, 0, 0], ![0, 89, 0], ![7, 40, 1]] where
  M :=![![![-31616, 3796, -2851], ![168209, -20196, 15168], ![-55755, 6695, -5028]]]
  hmulB := by decide  
  f := ![![![48, 13, 12]], ![![-708, -87, 139]], ![![-331, -41, 64]]]
  g := ![![![-131, 1324, -2851], ![697, -7044, 15168], ![-231, 2335, -5028]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [37, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 88], [0, 1]]
 g := ![![[69, 2], [45], [87], [32, 47], [33, 72], [1]], ![[36, 87], [45], [87], [13, 42], [2, 17], [1]]]
 h' := ![![[28, 88], [30, 64], [2, 57], [62, 49], [25, 74], [52, 28], [0, 1]], ![[0, 1], [42, 25], [85, 32], [10, 40], [50, 15], [35, 61], [28, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [9, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [37, 61, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![229, -90, 109]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -50, 109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48, 13, 12]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![48, 13, 12]] 
 ![![89, 0, 0], ![72, 1, 0], ![15, 0, 1]] where
  M :=![![![48, 13, 12], ![-708, -87, 139], ![-1475, -260, 52]]]
  hmulB := by decide  
  f := ![![![-31616, 3796, -2851]], ![![-23687, 2844, -2136]], ![![-5955, 715, -537]]]
  g := ![![![-12, 13, 12], ![39, -87, 139], ![185, -260, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-31616, 3796, -2851]] ![![48, 13, 12]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB93I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 92 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 92 (by omega)

def PB93I2 : PrimesBelowBoundCertificateInterval O 79 92 93 where
  m := 2
  g := ![1, 2]
  P := ![83, 89]
  hP := PB93I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
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
  β := ![I89N1]
  Il := ![[], [I89N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
