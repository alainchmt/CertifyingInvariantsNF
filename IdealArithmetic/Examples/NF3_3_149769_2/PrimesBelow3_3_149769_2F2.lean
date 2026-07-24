
import IdealArithmetic.Examples.NF3_3_149769_2.RI3_3_149769_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![13, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![13, 1, 0]] 
 ![![83, 0, 0], ![13, 1, 0], ![80, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![13, 1, 0], ![0, 13, 1], ![559, 129, 13]]]
  hmulB := by decide  
  f := ![![![365, 28, 0], ![-2324, 0, 0]], ![![39, 3, 0], ![-248, 0, 0]], ![![354, 27, 0], ![-2254, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 83, 0], ![-80, 0, 83]], ![![0, 1, 0], ![-3, 13, 1], ![-26, 129, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-8, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-8, 1, 0]] 
 ![![83, 0, 0], ![75, 1, 0], ![19, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-8, 1, 0], ![0, -8, 1], ![559, 129, -8]]]
  hmulB := by decide  
  f := ![![![449, -56, 0], ![4648, 0, 0]], ![![409, -51, 0], ![4234, 0, 0]], ![![113, -14, 0], ![1170, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 83, 0], ![-19, 0, 83]], ![![-1, 1, 0], ![7, -8, 1], ![-108, 129, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-5, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-5, 1, 0]] 
 ![![83, 0, 0], ![78, 1, 0], ![58, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-5, 1, 0], ![0, -5, 1], ![559, 129, -5]]]
  hmulB := by decide  
  f := ![![![271, -54, 0], ![4482, 0, 0]], ![![256, -51, 0], ![4234, 0, 0]], ![![186, -37, 0], ![3076, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 83, 0], ![-58, 0, 83]], ![![-1, 1, 0], ![4, -5, 1], ![-111, 129, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![13, 1, 0]] ![![83, 0, 0], ![-8, 1, 0]]
  ![![83, 0, 0], ![-104, 5, 1]] where
 M := ![![![6889, 0, 0], ![-664, 83, 0]], ![![1079, 83, 0], ![-104, 5, 1]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![96, -4, -1], ![83, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-104, 5, 1]] ![![83, 0, 0], ![-5, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-415, 83, 0]], ![![-8632, 415, 83], ![1079, 0, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-5, 1, 0]]], ![![![-104, 5, 1]], ![![13, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)


lemma PB87I2_primes (p : ℕ) :
  p ∈ Set.range ![83] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 86 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 86 (by omega)

def PB87I2 : PrimesBelowBoundCertificateInterval O 79 86 87 where
  m := 1
  g := ![3]
  P := ![83]
  hP := PB87I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
  β := ![I83N0, I83N1, I83N2]
  Il := ![[I83N0, I83N1, I83N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
