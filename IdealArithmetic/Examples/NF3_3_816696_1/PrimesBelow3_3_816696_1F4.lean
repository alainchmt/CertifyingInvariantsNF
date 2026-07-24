
import IdealArithmetic.Examples.NF3_3_816696_1.RI3_3_816696_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21111, 702, -556]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![21111, 702, -556]] 
 ![![197, 0, 0], ![0, 197, 0], ![136, 127, 1]] where
  M :=![![![21111, 702, -556], ![-40178, -3499, 1550], ![31494, 9058, -2651]]]
  hmulB := by decide  
  f := ![![![24183, 16118, 4352]], ![![292874, 195201, 52706]], ![![212040, 141325, 38159]]]
  g := ![![![491, 362, -556], ![-1274, -1017, 1550], ![1990, 1755, -2651]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [26, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 196], [0, 1]]
 g := ![![[20, 144], [104], [126, 76], [173], [60], [23], [71, 1]], ![[0, 53], [104], [6, 121], [173], [60], [23], [142, 196]]]
 h' := ![![[71, 196], [64, 185], [73, 33], [67, 43], [25, 31], [3, 116], [124, 90], [0, 1]], ![[0, 1], [0, 12], [52, 164], [165, 154], [59, 166], [162, 81], [13, 107], [71, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [88, 164]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [26, 126, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![450, 342, 12]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -6, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24183, 16118, 4352]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![24183, 16118, 4352]] 
 ![![197, 0, 0], ![12, 1, 0], ![87, 0, 1]] where
  M :=![![![24183, 16118, 4352], ![292874, 195201, 52706], ![1287994, 858450, 231789]]]
  hmulB := by decide  
  f := ![![![21111, 702, -556]], ![![1082, 25, -26]], ![![9483, 356, -259]]]
  g := ![![![-2781, 16118, 4352], ![-33680, 195201, 52706], ![-148117, 858450, 231789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![21111, 702, -556]] ![![24183, 16118, 4352]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3129, -2082, -562]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-3129, -2082, -562]] 
 ![![199, 0, 0], ![21, 1, 0], ![125, 0, 1]] where
  M :=![![![-3129, -2082, -562], ![-37820, -25213, -6808], ![-166368, -110882, -29939]]]
  hmulB := by decide  
  f := ![![![32649, 17314, -4550]], ![![1735, 921, -242]], ![![25931, 13748, -3613]]]
  g := ![![![557, -2082, -562], ![6747, -25213, -6808], ![29671, -110882, -29939]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54, 2, -1]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![54, 2, -1]] 
 ![![199, 0, 0], ![157, 1, 0], ![61, 0, 1]] where
  M :=![![![54, 2, -1], ![-73, 9, 5], ![109, 48, 12]]]
  hmulB := by decide  
  f := ![![![-132, -72, 19]], ![![-97, -53, 14]], ![![-63, -34, 9]]]
  g := ![![![-1, 2, -1], ![-9, 9, 5], ![-41, 48, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-3129, -2082, -562]] ![![-3129, -2082, -562]]
  ![![182030697, 121323728, 32758472]] where
 M := ![![![182030697, 121323728, 32758472]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI199N1 : IdealMulLeCertificate' Table 
  ![![182030697, 121323728, 32758472]] ![![54, 2, -1]]
  ![![199, 0, 0]] where
 M := ![![![4543698942, 3028381602, 817689607]]]
 hmul := by decide  
 g := ![![![![22832658, 15217998, 4108993]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)


lemma PB201I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 200 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 200 (by omega)

def PB201I4 : PrimesBelowBoundCertificateInterval O 193 200 201 where
  m := 2
  g := ![2, 3]
  P := ![197, 199]
  hP := PB201I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N0, I199N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![199, 199, 199]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N0
      exact NI199N1
  β := ![I197N1, I199N0, I199N1]
  Il := ![[I197N1], [I199N0, I199N0, I199N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
