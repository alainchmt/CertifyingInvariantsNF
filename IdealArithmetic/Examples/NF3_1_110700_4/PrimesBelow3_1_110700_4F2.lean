
import IdealArithmetic.Examples.NF3_1_110700_4.RI3_1_110700_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![60, 14, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![60, 14, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![60, 14, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![60, 14, 1], ![10, 30, 14], ![140, -410, 30]]]
  hmulB := by decide  
  f := ![![![-59, -14, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -14, 83]], ![![0, 0, 1], ![-10, -2, 14], ![-20, -10, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [81, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 82], [0, 1]]
 g := ![![[52, 41], [68, 41], [31], [36], [49, 26], [1]], ![[0, 42], [16, 42], [31], [36], [14, 57], [1]]]
 h' := ![![[21, 82], [53, 37], [42, 37], [48, 23], [15, 6], [2, 21], [0, 1]], ![[0, 1], [0, 46], [72, 46], [33, 60], [58, 77], [28, 62], [21, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [47, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [81, 62, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![101, -112, -91]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![67, 14, -91]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-14, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-14, 1, 0]] 
 ![![83, 0, 0], ![69, 1, 0], ![53, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-14, 1, 0], ![0, -14, 1], ![10, -30, -14]]]
  hmulB := by decide  
  f := ![![![113, -8, 0], ![664, 0, 0]], ![![99, -7, 0], ![582, 0, 0]], ![![87, -6, 0], ![512, 1, 0]]]
  g := ![![![1, 0, 0], ![-69, 83, 0], ![-53, 0, 83]], ![![-1, 1, 0], ![11, -14, 1], ![34, -30, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![60, 14, 1]] ![![83, 0, 0], ![-14, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1162, 83, 0]], ![![4980, 1162, 83], ![-830, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-14, 1, 0]]], ![![![60, 14, 1]], ![![-10, -2, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [58, 41, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 60, 25], [15, 28, 64], [0, 1]]
 g := ![![[74, 86, 68], [65, 36], [30, 2], [11, 69, 87], [73, 84, 1], []], ![[65, 68, 27, 79], [11, 79], [78, 64], [61, 42, 11, 42], [38, 59, 77, 20], [53, 2]], ![[11, 22, 5, 69], [30, 68], [81, 21], [30, 18, 17, 20], [84, 63, 52, 68], [14, 2]]]
 h' := ![![[69, 60, 25], [61, 1, 35], [87, 13, 6], [74, 17, 64], [38, 56, 49], [0, 0, 1], [0, 1]], ![[15, 28, 64], [79, 61, 26], [70, 58, 48], [12, 53, 81], [57, 15, 13], [85, 28, 28], [69, 60, 25]], ![[0, 1], [1, 27, 28], [53, 18, 35], [52, 19, 33], [61, 18, 27], [36, 61, 60], [15, 28, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 65], []]
 b := ![[], [79, 50, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [58, 41, 5, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18601, -63368, 22250]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![209, -712, 250]
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



lemma PB95I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 94 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 94 (by omega)

def PB95I2 : PrimesBelowBoundCertificateInterval O 79 94 95 where
  m := 2
  g := ![2, 1]
  P := ![83, 89]
  hP := PB95I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
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
    · exact ![704969]
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
  β := ![I83N1]
  Il := ![[I83N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
