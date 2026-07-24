
import IdealArithmetic.Examples.NF3_1_116116_1.RI3_1_116116_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [81, 67, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 8, 40], [9, 74, 43], [0, 1]]
 g := ![![[57, 26, 40], [33, 38, 21], [28, 16], [35, 27], [39, 40, 1], []], ![[22, 25, 27, 28], [45, 6, 18, 4], [23, 44], [9, 21], [4, 71, 7, 3], [66, 23]], ![[26, 23, 55, 45], [43, 47, 62, 20], [35, 26], [13, 9], [72, 27, 21, 13], [63, 23]]]
 h' := ![![[31, 8, 40], [66, 17, 66], [34, 55, 41], [12, 48, 4], [78, 40, 44], [0, 0, 1], [0, 1]], ![[9, 74, 43], [23, 28, 3], [72, 56, 5], [62, 53, 58], [25, 82, 42], [14, 21, 74], [31, 8, 40]], ![[0, 1], [20, 38, 14], [52, 55, 37], [27, 65, 21], [1, 44, 80], [41, 62, 8], [9, 74, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 18], []]
 b := ![[], [4, 32, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [81, 67, 43, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10790, 5561, -3320]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![130, 67, -40]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![4, 9, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![4, 9, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![4, 9, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![4, 9, 1], ![76, -7, 19], ![631, -71, 2]]]
  hmulB := by decide  
  f := ![![![-3, -9, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -9, 89]], ![![0, 0, 1], ![0, -2, 19], ![7, -1, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [25, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 88], [0, 1]]
 g := ![![[21, 57], [18], [10], [8, 69], [12, 81], [1]], ![[0, 32], [18], [10], [6, 20], [29, 8], [1]]]
 h' := ![![[9, 88], [16, 18], [56, 75], [67, 59], [56, 43], [64, 9], [0, 1]], ![[0, 1], [0, 71], [19, 14], [64, 30], [87, 46], [56, 80], [9, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [37, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [25, 80, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-447, 752, 133]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -5, 133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-19, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-19, 1, 0]] 
 ![![89, 0, 0], ![70, 1, 0], ![87, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-19, 1, 0], ![1, -19, 2], ![67, -11, -18]]]
  hmulB := by decide  
  f := ![![![-339, 7180, -756], ![178, 33642, 0]], ![![-258, 5641, -594], ![179, 26433, 0]], ![![-319, 7018, -739], ![232, 32886, 0]]]
  g := ![![![1, 0, 0], ![-70, 89, 0], ![-87, 0, 89]], ![![-1, 1, 0], ![13, -19, 2], ![27, -11, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![4, 9, 1]] ![![89, 0, 0], ![-19, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1691, 89, 0]], ![![356, 801, 89], ![0, -178, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-19, 1, 0]]], ![![![4, 9, 1]], ![![0, -2, 0]]]]
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


lemma PB97I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 96 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 96 (by omega)

def PB97I2 : PrimesBelowBoundCertificateInterval O 79 96 97 where
  m := 2
  g := ![1, 2]
  P := ![83, 89]
  hP := PB97I2_primes
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
