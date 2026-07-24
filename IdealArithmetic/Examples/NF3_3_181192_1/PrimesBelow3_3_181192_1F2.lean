
import IdealArithmetic.Examples.NF3_3_181192_1.RI3_3_181192_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [81, 59, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 6, 22], [37, 76, 61], [0, 1]]
 g := ![![[32, 2, 23], [79, 76, 65], [47, 78], [44, 44], [16, 18, 1], []], ![[55, 76, 20, 46], [6, 74, 38, 50], [17, 4], [9, 51], [54, 22, 48, 82], [12, 69]], ![[78, 61, 33, 17], [73, 60, 81, 70], [16, 12], [39, 38], [8, 11, 82, 38], [56, 69]]]
 h' := ![![[64, 6, 22], [75, 82, 40], [21, 51, 56], [33, 53, 24], [32, 5, 58], [0, 0, 1], [0, 1]], ![[37, 76, 61], [56, 29, 30], [28, 23, 66], [49, 7, 2], [23, 60, 36], [53, 32, 76], [64, 6, 22]], ![[0, 1], [16, 55, 13], [18, 9, 44], [22, 23, 57], [44, 18, 72], [70, 51, 6], [37, 76, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 77], []]
 b := ![[], [36, 19, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [81, 59, 65, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-375160, -179363, -100596]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4520, -2161, -1212]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-858, -404, -169]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-858, -404, -169]] 
 ![![89, 0, 0], ![0, 89, 0], ![53, 54, 1]] where
  M :=![![![-858, -404, -169], ![-9934, -4679, -1954], ![-30773, -14494, -6060]]]
  hmulB := by decide  
  f := ![![![-376, -14, 15]], ![![782, 13, -26]], ![![251, 0, -7]]]
  g := ![![![91, 98, -169], ![1052, 1133, -1954], ![3263, 3514, -6060]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [78, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 88], [0, 1]]
 g := ![![[46, 8], [32], [84], [24, 17], [38, 72], [1]], ![[0, 81], [32], [84], [82, 72], [69, 17], [1]]]
 h' := ![![[61, 88], [65, 50], [43, 11], [86, 66], [62, 27], [11, 61], [0, 1]], ![[0, 1], [0, 39], [2, 78], [18, 23], [18, 62], [83, 28], [61, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [55, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [78, 28, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![518, 113, 1464]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-866, -887, 1464]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![376, 14, -15]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![376, 14, -15]] 
 ![![89, 0, 0], ![49, 1, 0], ![80, 0, 1]] where
  M :=![![![376, 14, -15], ![-782, -13, 26], ![-39, -40, 14]]]
  hmulB := by decide  
  f := ![![![858, 404, 169]], ![![584, 275, 115]], ![![1117, 526, 220]]]
  g := ![![![10, 14, -15], ![-25, -13, 26], ![9, -40, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-858, -404, -169]] ![![376, 14, -15]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB95I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 94 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 94 (by omega)

def PB95I2 : PrimesBelowBoundCertificateInterval O 79 94 95 where
  m := 2
  g := ![1, 2]
  P := ![83, 89]
  hP := PB95I2_primes
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
