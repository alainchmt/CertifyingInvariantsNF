
import IdealArithmetic.Examples.NF3_1_116424_1.RI3_1_116424_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [49, 80, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 71, 55], [1, 11, 28], [0, 1]]
 g := ![![[11, 7, 40], [12, 70, 27], [65, 30], [27, 51], [26, 43, 1], []], ![[42, 24, 10, 52], [44, 25, 74, 5], [34, 28], [56, 26], [16, 5, 2, 15], [22, 37]], ![[70, 4, 64, 30], [67, 27, 5, 65], [23, 75], [8, 12], [26, 73, 34, 48], [49, 37]]]
 h' := ![![[42, 71, 55], [76, 4, 66], [59, 64, 44], [16, 60, 14], [54, 46, 36], [0, 0, 1], [0, 1]], ![[1, 11, 28], [36, 58, 33], [63, 22, 20], [22, 52, 51], [39, 34, 21], [22, 67, 11], [42, 71, 55]], ![[0, 1], [44, 21, 67], [16, 80, 19], [8, 54, 18], [20, 3, 26], [7, 16, 71], [1, 11, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 48], []]
 b := ![[], [65, 65, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [49, 80, 40, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14857, 12118, -35690]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![179, 146, -430]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![29, 5, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![29, 5, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![29, 5, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![29, 5, 1], ![44, 26, 23], ![232, -49, 8]]]
  hmulB := by decide  
  f := ![![![-28, -5, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -5, 89]], ![![0, 0, 1], ![-7, -1, 23], ![0, -1, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [30, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 88], [0, 1]]
 g := ![![[74, 32], [68], [4], [70, 80], [3, 25], [1]], ![[56, 57], [68], [4], [25, 9], [39, 64], [1]]]
 h' := ![![[5, 88], [12, 78], [19, 54], [36, 87], [88, 76], [59, 5], [0, 1]], ![[0, 1], [46, 11], [22, 35], [26, 2], [23, 13], [84, 84], [5, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [14, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [30, 84, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3253, 1836, -772]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![215, 64, -772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-23, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-23, 1, 0]] 
 ![![89, 0, 0], ![66, 1, 0], ![81, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-23, 1, 0], ![-2, -21, 5], ![54, -13, -25]]]
  hmulB := by decide  
  f := ![![![8309, 90144, -21460], ![-1068, 381988, 0]], ![![6158, 66831, -15910], ![-800, 283198, 0]], ![![7566, 82041, -19531], ![-957, 347652, 0]]]
  g := ![![![1, 0, 0], ![-66, 89, 0], ![-81, 0, 89]], ![![-1, 1, 0], ![11, -21, 5], ![33, -13, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![29, 5, 1]] ![![89, 0, 0], ![-23, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2047, 89, 0]], ![![2581, 445, 89], ![-623, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-23, 1, 0]]], ![![![29, 5, 1]], ![![-7, -1, 0]]]]
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
