
import IdealArithmetic.Examples.NF3_1_105791_3.RI3_1_105791_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![33, 17, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![33, 17, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![33, 17, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![33, 17, 1], ![63, 40, 17], ![1071, 182, 40]]]
  hmulB := by decide  
  f := ![![![-32, -17, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -17, 83]], ![![0, 0, 1], ![-6, -3, 17], ![-3, -6, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [63, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 82], [0, 1]]
 g := ![![[81, 29], [45, 7], [51], [59], [53, 23], [1]], ![[0, 54], [14, 76], [51], [59], [46, 60], [1]]]
 h' := ![![[43, 82], [70, 64], [75, 16], [47, 36], [64, 68], [20, 43], [0, 1]], ![[0, 1], [0, 19], [16, 67], [18, 47], [0, 15], [43, 40], [43, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [81, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [63, 40, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![189, 37, -32]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 7, -32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-17, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-17, 1, 0]] 
 ![![83, 0, 0], ![66, 1, 0], ![43, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-17, 1, 0], ![0, -17, 1], ![63, 7, -17]]]
  hmulB := by decide  
  f := ![![![919, -54, 0], ![4482, 0, 0]], ![![732, -43, 0], ![3570, 0, 0]], ![![463, -27, 0], ![2258, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 83, 0], ![-43, 0, 83]], ![![-1, 1, 0], ![13, -17, 1], ![4, 7, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![33, 17, 1]] ![![83, 0, 0], ![-17, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1411, 83, 0]], ![![2739, 1411, 83], ![-498, -249, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-17, 1, 0]]], ![![![33, 17, 1]], ![![-6, -3, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-25, -31, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-25, -31, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![64, 58, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-25, -31, 1], ![63, -18, -31], ![-1953, -154, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -58, 89]], ![![-1, -1, 1], ![23, 20, -31], ![-9, 10, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [85, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 88], [0, 1]]
 g := ![![[8, 22], [64], [67], [], [5, 45], [1]], ![[0, 67], [64], [67], [], [21, 44], [1]]]
 h' := ![![[32, 88], [79, 17], [1, 8], [0, 44], [20], [4, 32], [0, 1]], ![[0, 1], [0, 72], [79, 81], [73, 45], [20], [49, 57], [32, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [37, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [85, 57, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-727, 373, 232]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-175, -147, 232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![31, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![31, 1, 0]] 
 ![![89, 0, 0], ![31, 1, 0], ![18, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![31, 1, 0], ![0, 31, 1], ![63, 7, 31]]]
  hmulB := by decide  
  f := ![![![590, 19, 0], ![-1691, 0, 0]], ![![186, 6, 0], ![-533, 0, 0]], ![![104, 3, 0], ![-298, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 89, 0], ![-18, 0, 89]], ![![0, 1, 0], ![-11, 31, 1], ![-8, 7, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-25, -31, 1]] ![![89, 0, 0], ![31, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2759, 89, 0]], ![![-2225, -2759, 89], ![-712, -979, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![31, 1, 0]]], ![![![-25, -31, 1]], ![![-8, -11, 0]]]]
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
  g := ![2, 2]
  P := ![83, 89]
  hP := PB93I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
  β := ![I83N1, I89N1]
  Il := ![[I83N1], [I89N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
