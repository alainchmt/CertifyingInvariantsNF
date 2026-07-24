
import IdealArithmetic.Examples.NF3_1_252563_1.RI3_1_252563_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18298927258, 425143542, 471461883]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![18298927258, 425143542, 471461883]] 
 ![![139, 0, 0], ![43, 1, 0], ![97, 0, 1]] where
  M :=![![![18298927258, 425143542, 471461883], ![16501165905, 383375704, 425143542], ![14880023970, 345711309, 383375704]]]
  hmulB := by decide  
  f := ![![![-220862, 231279, 15132]], ![![-64514, 65821, 6345]], ![![-95891, 101979, 4834]]]
  g := ![![![-328878041, 425143542, 471461883], ![-296567719, 383375704, 425143542], ![-267431695, 345711309, 383375704]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3848364, -89410, -99151]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-3848364, -89410, -99151]] 
 ![![139, 0, 0], ![48, 1, 0], ![59, 0, 1]] where
  M :=![![![-3848364, -89410, -99151], ![-3470285, -80626, -89410], ![-3129350, -72705, -80626]]]
  hmulB := by decide  
  f := ![![![2174, -2795, 426]], ![![858, -1066, 127]], ![![219, -315, 80]]]
  g := ![![![45275, -89410, -99151], ![40827, -80626, -89410], ![36816, -72705, -80626]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![18298927258, 425143542, 471461883]] ![![-3848364, -89410, -99151]]
  ![![-73371671398521432, -1704662345558587, -1890381106426936]] where
 M := ![![![-73371671398521432, -1704662345558587, -1890381106426936]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-73371671398521432, -1704662345558587, -1890381106426936]] ![![-3848364, -89410, -99151]]
  ![![139, 0, 0]] where
 M := ![![![294192227113153445396143, 6835041404357578252462, 7579702318237969909838]]]
 hmul := by decide  
 g := ![![![![2116490842540672269037, 49172959743579699658, 54530232505309136042]]]]
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


lemma PB143I3_primes (p : ℕ) :
  p ∈ Set.range ![139] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 142 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 142 (by omega)

def PB143I3 : PrimesBelowBoundCertificateInterval O 137 142 143 where
  m := 1
  g := ![3]
  P := ![139]
  hP := PB143I3_primes
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
