
import IdealArithmetic.Examples.NF3_3_157300_2.RI3_3_157300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-44, 22, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-44, 22, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![39, 22, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-44, 22, 1], ![40, -20, 67], ![410, 542, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -22, 83]], ![![-1, 0, 1], ![-31, -18, 67], ![4, 6, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [23, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 82], [0, 1]]
 g := ![![[79, 65], [25, 28], [69], [49], [66, 81], [1]], ![[0, 18], [28, 55], [69], [49], [48, 2], [1]]]
 h' := ![![[9, 82], [6, 27], [60, 32], [30, 22], [59, 7], [60, 9], [0, 1]], ![[0, 1], [0, 56], [16, 51], [62, 61], [39, 76], [58, 74], [9, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [52, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [23, 74, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![185, 198, 9]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 0, 9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![16, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![16, 1, 0]] 
 ![![83, 0, 0], ![16, 1, 0], ![81, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![16, 1, 0], ![1, 16, 3], ![18, 24, 17]]]
  hmulB := by decide  
  f := ![![![-617, -10398, -1950], ![-166, 53950, 0]], ![![-125, -2000, -375], ![1, 10375, 0]], ![![-595, -10147, -1903], ![-199, 52650, 0]]]
  g := ![![![1, 0, 0], ![-16, 83, 0], ![-81, 0, 83]], ![![0, 1, 0], ![-6, 16, 3], ![-21, 24, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-44, 22, 1]] ![![83, 0, 0], ![16, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1328, 83, 0]], ![![-3652, 1826, 83], ![-664, 332, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![16, 1, 0]]], ![![![-44, 22, 1]], ![![-8, 4, 1]]]]
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


lemma PB89I2_primes (p : ℕ) :
  p ∈ Set.range ![83] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 88 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 88 (by omega)

def PB89I2 : PrimesBelowBoundCertificateInterval O 79 88 89 where
  m := 1
  g := ![2]
  P := ![83]
  hP := PB89I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
  β := ![I83N1]
  Il := ![[I83N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
