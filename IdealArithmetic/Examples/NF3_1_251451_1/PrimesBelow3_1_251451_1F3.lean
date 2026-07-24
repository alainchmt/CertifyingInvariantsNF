
import IdealArithmetic.Examples.NF3_1_251451_1.RI3_1_251451_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![114, 4, 3]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![114, 4, 3]] 
 ![![139, 0, 0], ![62, 1, 0], ![48, 0, 1]] where
  M :=![![![114, 4, 3], ![147, 6, 4], ![196, 3, 6]]]
  hmulB := by decide  
  f := ![![![24, -15, -2]], ![![10, -6, -1]], ![![3, -2, 0]]]
  g := ![![![-2, 4, 3], ![-3, 6, 4], ![-2, 3, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-31, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-31, 1, 0]] 
 ![![139, 0, 0], ![108, 1, 0], ![12, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-31, 1, 0], ![0, -31, 1], ![49, -36, -31]]]
  hmulB := by decide  
  f := ![![![404, -13, 0], ![1807, 0, 0]], ![![342, -11, 0], ![1530, 0, 0]], ![![38, -1, 0], ![170, 1, 0]]]
  g := ![![![1, 0, 0], ![-108, 139, 0], ![-12, 0, 139]], ![![-1, 1, 0], ![24, -31, 1], ![31, -36, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![114, 4, 3]] ![![139, 0, 0], ![-31, 1, 0]]
  ![![139, 0, 0], ![24, 31, 1]] where
 M := ![![![15846, 556, 417], ![-3387, -118, -89]]]
 hmul := by decide  
 g := ![![![![90, -27, 2], ![139, 0, 0]], ![![-33, -12, -1], ![50, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![24, 31, 1]] ![![139, 0, 0], ![-31, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-4309, 139, 0]], ![![3336, 4309, 139], ![-695, -973, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-31, 1, 0]]], ![![![24, 31, 1]], ![![-5, -7, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)


lemma PB142I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 141 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 141 (by omega)

def PB142I3 : PrimesBelowBoundCertificateInterval O 137 141 142 where
  m := 1
  g := ![3]
  P := ![139]
  hP := PB142I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N1
  β := ![I139N0, I139N1]
  Il := ![[I139N0, I139N1, I139N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
