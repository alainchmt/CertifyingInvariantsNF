
import IdealArithmetic.Examples.NF3_1_110424_1.RI3_1_110424_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![5, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![5, 1, 0]] 
 ![![83, 0, 0], ![5, 1, 0], ![36, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![5, 1, 0], ![2, 7, 6], ![58, -10, 3]]]
  hmulB := by decide  
  f := ![![![5761, 20292, 17400], ![664, -240700, 0]], ![![343, 1217, 1044], ![84, -14442, 0]], ![![2497, 8801, 7547], ![317, -104400, 0]]]
  g := ![![![1, 0, 0], ![-5, 83, 0], ![-36, 0, 83]], ![![0, 1, 0], ![-3, 7, 6], ![0, -10, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![16, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![16, 1, 0]] 
 ![![83, 0, 0], ![16, 1, 0], ![63, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![16, 1, 0], ![2, 18, 6], ![58, -10, 14]]]
  hmulB := by decide  
  f := ![![![-1079, -10292, -3432], ![-332, 47476, 0]], ![![-220, -1980, -660], ![1, 9130, 0]], ![![-819, -7812, -2605], ![-252, 36036, 0]]]
  g := ![![![1, 0, 0], ![-16, 83, 0], ![-63, 0, 83]], ![![0, 1, 0], ![-8, 18, 6], ![-8, -10, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52595021382267, 4506280913501, 4063990937802]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![52595021382267, 4506280913501, 4063990937802]] 
 ![![83, 0, 0], ![62, 1, 0], ![3, 0, 1]] where
  M :=![![![52595021382267, 4506280913501, 4063990937802], ![244724036219518, 20967673831249, 18909703605402], ![90676673595374, 7769073056416, 7006541115047]]]
  hmulB := by decide  
  f := ![![![24344471, -3511915, -4642296]], ![![14856388, -1855363, -3609750]], ![![774925, -430921, 713519]]]
  g := ![![![-2879353832147, 4506280913501, 4063990937802], ![-13397600628122, 20967673831249, 18909703605402], ![-4964162400573, 7769073056416, 7006541115047]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![5, 1, 0]] ![![83, 0, 0], ![16, 1, 0]]
  ![![24344471, -3511915, -4642296]] where
 M := ![![![6889, 0, 0], ![1328, 83, 0]], ![![415, 83, 0], ![82, 23, 6]]]
 hmul := by decide  
 g := ![![![![4365386774728161, 374021315820583, 337311247837566]], ![![1086244378335790, 93068168447265, 83933558610234]]], ![![![507699143130853, 43499078398754, 39229658294412]], ![![126331381059844, 10823927365835, 9761562488124]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![24344471, -3511915, -4642296]] ![![52595021382267, 4506280913501, 4063990937802]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [33, 77, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 72, 86], [83, 16, 3], [0, 1]]
 g := ![![[71, 82, 5], [3, 10], [36, 34], [71, 81, 87], [80, 54, 1], []], ![[18, 12, 3, 14], [87, 16], [49, 68], [53, 78, 21, 24], [6, 77, 86, 33], [54, 9]], ![[20, 35, 31, 37], [22, 88], [41, 4], [20, 9, 35, 35], [55, 59, 26, 66], [48, 9]]]
 h' := ![![[60, 72, 86], [71, 70, 19], [9, 40, 30], [60, 58, 52], [30, 68, 40], [0, 0, 1], [0, 1]], ![[83, 16, 3], [9, 5, 5], [78, 3, 4], [87, 8, 35], [23, 81, 80], [38, 2, 16], [60, 72, 86]], ![[0, 1], [54, 14, 65], [54, 46, 55], [28, 23, 2], [2, 29, 58], [54, 87, 72], [83, 16, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 42], []]
 b := ![[], [35, 27, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [33, 77, 35, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8722, 1157, -6141]
  a := ![-1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![98, 13, -69]
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
  g := ![3, 1]
  P := ![83, 89]
  hP := PB95I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
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
    · exact ![83, 83, 83]
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
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
  β := ![I83N0, I83N1, I83N2]
  Il := ![[I83N0, I83N1, I83N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
