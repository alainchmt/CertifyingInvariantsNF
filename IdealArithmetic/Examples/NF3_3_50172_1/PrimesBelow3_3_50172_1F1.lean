
import IdealArithmetic.Examples.NF3_3_50172_1.RI3_3_50172_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -138, -57]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![47, -138, -57]] 
 ![![37, 0, 0], ![19, 1, 0], ![9, 0, 1]] where
  M :=![![![47, -138, -57], ![342, -1003, -414], ![714, -2094, -865]]]
  hmulB := by decide  
  f := ![![![-679, 12, 39]], ![![-355, 5, 21]], ![![-165, 6, 8]]]
  g := ![![![86, -138, -57], ![625, -1003, -414], ![1305, -2094, -865]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1269, 10, 79]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-1269, 10, 79]] 
 ![![37, 0, 0], ![35, 1, 0], ![24, 0, 1]] where
  M :=![![![-1269, 10, 79], ![-474, 5, 30], ![98, 2, -5]]]
  hmulB := by decide  
  f := ![![![85, -208, 95]], ![![65, -159, 73]], ![![94, -230, 105]]]
  g := ![![![-95, 10, 79], ![-37, 5, 30], ![4, 2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![47, -138, -57]] ![![47, -138, -57]]
  ![![-85685, 251286, 103758]] where
 M := ![![![-85685, 251286, 103758]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-85685, 251286, 103758]] ![![-1269, 10, 79]]
  ![![37, 0, 0]] where
 M := ![![![-207015, 607096, 250675]]]
 hmul := by decide  
 g := ![![![![-5595, 16408, 6775]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2075, 16, 129]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-2075, 16, 129]] 
 ![![41, 0, 0], ![0, 41, 0], ![30, 30, 1]] where
  M :=![![![-2075, 16, 129], ![-774, 5, 48], ![162, -2, -11]]]
  hmulB := by decide  
  f := ![![![-1, 2, -3]], ![![18, -47, 6]], ![![12, -32, 1]]]
  g := ![![![-145, -94, 129], ![-54, -35, 48], ![12, 8, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [20, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40], [0, 1]]
 g := ![![[4, 39], [4], [21], [10, 4], [1]], ![[0, 2], [4], [21], [18, 37], [1]]]
 h' := ![![[2, 40], [22, 30], [15, 39], [5, 12], [21, 2], [0, 1]], ![[0, 1], [0, 11], [11, 2], [29, 29], [25, 39], [2, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [14, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [20, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50, 196, 217]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-160, -154, 217]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -3]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-1, 2, -3]] 
 ![![41, 0, 0], ![33, 1, 0], ![36, 0, 1]] where
  M :=![![![-1, 2, -3], ![18, -47, 6], ![-18, 38, -49]]]
  hmulB := by decide  
  f := ![![![-2075, 16, 129]], ![![-1689, 13, 105]], ![![-1818, 14, 113]]]
  g := ![![![1, 2, -3], ![33, -47, 6], ![12, 38, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-2075, 16, 129]] ![![-1, 2, -3]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 72, 30]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-25, 72, 30]] 
 ![![43, 0, 0], ![0, 43, 0], ![35, 11, 1]] where
  M :=![![![-25, 72, 30], ![-180, 527, 216], ![-372, 1092, 455]]]
  hmulB := by decide  
  f := ![![![-91, 0, 6]], ![![-36, 5, 0]], ![![-83, 1, 5]]]
  g := ![![![-25, -6, 30], ![-180, -43, 216], ![-379, -91, 455]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 42], [0, 1]]
 g := ![![[0, 11], [], [41], [], [1]], ![[0, 32], [], [41], [], [1]]]
 h' := ![![[0, 42], [0, 21], [8], [0, 16], [39], [0, 1]], ![[0, 1], [0, 22], [8], [0, 27], [39], [0, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [0, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [4, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5, 109, 393]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-320, -98, 393]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, 0, 6]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-91, 0, 6]] 
 ![![43, 0, 0], ![10, 1, 0], ![35, 0, 1]] where
  M :=![![![-91, 0, 6], ![-36, 5, 0], ![12, -12, 5]]]
  hmulB := by decide  
  f := ![![![-25, 72, 30]], ![![-10, 29, 12]], ![![-29, 84, 35]]]
  g := ![![![-7, 0, 6], ![-2, 5, 0], ![-1, -12, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-25, 72, 30]] ![![-91, 0, 6]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 92, 43]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-31, 92, 43]] 
 ![![47, 0, 0], ![0, 47, 0], ![43, 24, 1]] where
  M :=![![![-31, 92, 43], ![-258, 749, 276], ![-466, 1386, 657]]]
  hmulB := by decide  
  f := ![![![-2331, 18, 145]], ![![-870, 7, 54]], ![![-2573, 20, 160]]]
  g := ![![![-40, -20, 43], ![-258, -125, 276], ![-611, -306, 657]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [32, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 46], [0, 1]]
 g := ![![[34, 25], [18, 16], [42, 6], [11, 2], [1]], ![[0, 22], [0, 31], [0, 41], [44, 45], [1]]]
 h' := ![![[40, 46], [35, 5], [19, 43], [24, 37], [15, 40], [0, 1]], ![[0, 1], [0, 42], [0, 4], [0, 10], [17, 7], [40, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [34, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [32, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3682, -2, 137]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -70, 137]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2331, 18, 145]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-2331, 18, 145]] 
 ![![47, 0, 0], ![22, 1, 0], ![35, 0, 1]] where
  M :=![![![-2331, 18, 145], ![-870, 7, 54], ![182, -2, -11]]]
  hmulB := by decide  
  f := ![![![-31, 92, 43]], ![![-20, 59, 26]], ![![-33, 98, 46]]]
  g := ![![![-166, 18, 145], ![-62, 7, 54], ![13, -2, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-31, 92, 43]] ![![-2331, 18, 145]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)


lemma PB50I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 49 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 49 (by omega)

def PB50I1 : PrimesBelowBoundCertificateInterval O 31 49 50 where
  m := 4
  g := ![3, 2, 2, 2]
  P := ![37, 41, 43, 47]
  hP := PB50I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
  β := ![I37N0, I37N1, I41N1, I43N1, I47N1]
  Il := ![[I37N0, I37N0, I37N1], [I41N1], [I43N1], [I47N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
