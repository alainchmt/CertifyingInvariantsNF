
import IdealArithmetic.Examples.NF3_3_418605_1.RI3_3_418605_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-47, 20, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-47, 20, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![92, 20, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-47, 20, 1], ![52, -31, 61], ![1476, 756, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -20, 139]], ![![-1, 0, 1], ![-40, -9, 61], ![4, 4, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [61, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 138], [0, 1]]
 g := ![![[117, 20], [27, 100], [28], [15, 6], [35], [80], [1]], ![[130, 119], [92, 39], [28], [5, 133], [35], [80], [1]]]
 h' := ![![[91, 138], [21, 115], [127, 129], [58, 81], [74, 80], [92, 70], [78, 91], [0, 1]], ![[0, 1], [61, 24], [51, 10], [62, 58], [126, 59], [68, 69], [19, 48], [91, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [102, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [61, 48, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![434, 324, 183]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-118, -24, 183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-61, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-61, 1, 0]] 
 ![![139, 0, 0], ![78, 1, 0], ![129, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-61, 1, 0], ![-1, -62, 3], ![72, 36, -60]]]
  hmulB := by decide  
  f := ![![![2235, 134725, -6519], ![139, 302047, 0]], ![![1281, 75577, -3657], ![140, 169441, 0]], ![![2047, 125033, -6050], ![67, 280317, 0]]]
  g := ![![![1, 0, 0], ![-78, 139, 0], ![-129, 0, 139]], ![![-1, 1, 0], ![32, -62, 3], ![36, 36, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-47, 20, 1]] ![![139, 0, 0], ![-61, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-8479, 139, 0]], ![![-6533, 2780, 139], ![2919, -1251, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-61, 1, 0]]], ![![![-47, 20, 1]], ![![21, -9, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)


lemma PB144I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 143 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 143 (by omega)

def PB144I3 : PrimesBelowBoundCertificateInterval O 137 143 144 where
  m := 1
  g := ![2]
  P := ![139]
  hP := PB144I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
  β := ![I139N1]
  Il := ![[I139N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
