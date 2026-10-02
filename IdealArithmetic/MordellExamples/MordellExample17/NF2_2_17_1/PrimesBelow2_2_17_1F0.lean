
import IdealArithmetic.MordellExamples.MordellExample17.NF2_2_17_1.RI2_2_17_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

namespace NF2_2_17_1

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1, 1]] 
 ![![2, 0], ![1, 1]] where
  M :=![![![1, 1], ![4, 2]]]
  hmulB := by decide  
  f := ![![![-2, 1]], ![![1, 0]]]
  g := ![![![0, 1], ![1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-2, 1]] 
 ![![2, 0], ![0, 1]] where
  M :=![![![-2, 1], ![4, -1]]]
  hmulB := by decide  
  f := ![![![1, 1]], ![![2, 1]]]
  g := ![![![-1, 1], ![2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1, 1]] ![![-2, 1]]
  ![![2, 0]] where
 M := ![![![2, 0]]]
 hmul := by decide  
 g := ![![![![1, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)


lemma PB3I0_primes (p : ℕ) :
  p ∈ Set.range ![2] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 2 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 2 (by omega)

def PB3I0 : PrimesBelowBoundCertificateInterval O 1 2 3 where
  m := 1
  g := ![2]
  P := ![2]
  hP := PB3I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
  β := ![I2N0, I2N1]
  Il := ![[I2N0, I2N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp

end

end NF2_2_17_1
