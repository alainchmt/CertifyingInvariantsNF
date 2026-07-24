
import IdealArithmetic.Examples.NF3_1_89240_1.RI3_1_89240_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6309694921, -531049979, 786727693]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![6309694921, -531049979, 786727693]] 
 ![![83, 0, 0], ![51, 1, 0], ![71, 0, 1]] where
  M :=![![![6309694921, -531049979, 786727693], ![-46692306152, 3929817291, -5821855218], ![59123095730, -4976043872, 7371794879]]]
  hmulB := by decide  
  f := ![![![-671307, -89755, 759]], ![![-415183, -66492, -8203]], ![![-511201, -75761, -5276]]]
  g := ![![![-270655691, -531049979, 786727693], ![2002876295, 3929817291, -5821855218], ![-2536097629, -4976043872, 7371794879]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-345, 29, -43]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-345, 29, -43]] 
 ![![83, 0, 0], ![53, 1, 0], ![65, 0, 1]] where
  M :=![![![-345, 29, -43], ![2552, -215, 318], ![-3230, 272, -403]]]
  hmulB := by decide  
  f := ![![![-149, 9, 23]], ![![-111, 4, 15]], ![![-113, 5, 16]]]
  g := ![![![11, 29, -43], ![-81, -215, 318], ![103, 272, -403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2631019, -82454, 215668]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-2631019, -82454, 215668]] 
 ![![83, 0, 0], ![61, 1, 0], ![31, 0, 1]] where
  M :=![![![-2631019, -82454, 215668], ![-12673652, -3094049, -1090968], ![12546380, -1427222, -2466111]]]
  hmulB := by decide  
  f := ![![![6073214742543, -511146830690, 757242035204]], ![![3921973103517, -330089451287, 489013318452]], ![![2953938391159, -248615652616, 368313391509]]]
  g := ![![![-51651, -82454, 215668], ![2528715, -3094049, -1090968], ![2121161, -1427222, -2466111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![6309694921, -531049979, 786727693]] ![![-345, 29, -43]]
  ![![-6073214742543, 511146830690, -757242035204]] where
 M := ![![![-6073214742543, 511146830690, -757242035204]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-6073214742543, 511146830690, -757242035204]] ![![-2631019, -82454, 215668]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB85I2_primes (p : ℕ) :
  p ∈ Set.range ![83] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 84 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 84 (by omega)

def PB85I2 : PrimesBelowBoundCertificateInterval O 79 84 85 where
  m := 1
  g := ![3]
  P := ![83]
  hP := PB85I2_primes
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
