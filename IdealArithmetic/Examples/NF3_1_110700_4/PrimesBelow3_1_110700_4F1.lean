
import IdealArithmetic.Examples.NF3_1_110700_4.RI3_1_110700_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [3, 12, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 19, 32], [10, 17, 5], [0, 1]]
 g := ![![[8, 27, 28], [13, 27], [14, 26, 1], [23, 1], []], ![[7, 3, 30, 31], [7, 12], [13, 16, 19, 2], [10, 30], [15, 25]], ![[7, 5, 36, 18], [33, 1], [30, 3, 26, 24], [35, 28], [5, 25]]]
 h' := ![![[13, 19, 32], [23, 12, 19], [32, 1, 29], [5, 17, 36], [0, 0, 1], [0, 1]], ![[10, 17, 5], [19, 33, 4], [15, 31, 7], [28, 10, 9], [13, 17, 17], [13, 19, 32]], ![[0, 1], [19, 29, 14], [28, 5, 1], [16, 10, 29], [11, 20, 19], [10, 17, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 25], []]
 b := ![[], [9, 26, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [3, 12, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1073, -2812, -1258]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, -76, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀


def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![41, 0, 0], ![1, 1, 0], ![40, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![10, -30, 1]]]
  hmulB := by decide  
  f := ![![![31, -1, 1]], ![![1, 0, 0]], ![![30, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![0, -30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1, -2, 0]] 
 ![![41, 0, 0], ![20, 1, 0], ![10, 0, 1]] where
  M :=![![![1, -2, 0], ![0, 1, -2], ![-20, 60, 1]]]
  hmulB := by decide  
  f := ![![![121, 2, 4]], ![![60, 1, 2]], ![![30, 0, 1]]]
  g := ![![![1, -2, 0], ![0, 1, -2], ![-30, 60, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![1, -2, 0]]
  ![![1, -1, -2]] where
 M := ![![![1, -1, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![1, -1, -2]] ![![1, -2, 0]]
  ![![41, 0, 0]] where
 M := ![![![41, -123, 0]]]
 hmul := by decide  
 g := ![![![![1, -3, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![19, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![19, 1, 0]] 
 ![![43, 0, 0], ![19, 1, 0], ![26, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![19, 1, 0], ![0, 19, 1], ![10, -30, 19]]]
  hmulB := by decide  
  f := ![![![267, 14, 0], ![-602, 0, 0]], ![![95, 5, 0], ![-214, 0, 0]], ![![142, 7, 0], ![-320, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 43, 0], ![-26, 0, 43]], ![![0, 1, 0], ![-9, 19, 1], ![2, -30, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-10, 1, 0]] 
 ![![43, 0, 0], ![33, 1, 0], ![29, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-10, 1, 0], ![0, -10, 1], ![10, -30, -10]]]
  hmulB := by decide  
  f := ![![![171, -17, 0], ![731, 0, 0]], ![![141, -14, 0], ![603, 0, 0]], ![![133, -13, 0], ![569, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 43, 0], ![-29, 0, 43]], ![![-1, 1, 0], ![7, -10, 1], ![30, -30, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-9, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-9, 1, 0]] 
 ![![43, 0, 0], ![34, 1, 0], ![5, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-9, 1, 0], ![0, -9, 1], ![10, -30, -9]]]
  hmulB := by decide  
  f := ![![![271, -30, 0], ![1290, 0, 0]], ![![208, -23, 0], ![990, 0, 0]], ![![47, -5, 0], ![224, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 43, 0], ![-5, 0, 43]], ![![-1, 1, 0], ![7, -9, 1], ![25, -30, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![19, 1, 0]] ![![43, 0, 0], ![-10, 1, 0]]
  ![![43, 0, 0], ![25, 9, 1]] where
 M := ![![![1849, 0, 0], ![-430, 43, 0]], ![![817, 43, 0], ![-190, 9, 1]]]
 hmul := by decide  
 g := ![![![![18, -9, -1], ![43, 0, 0]], ![![-10, 1, 0], ![0, 0, 0]]], ![![![-6, -8, -1], ![43, 0, 0]], ![![-5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![25, 9, 1]] ![![43, 0, 0], ![-9, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-387, 43, 0]], ![![1075, 387, 43], ![-215, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-9, 1, 0]]], ![![![25, 9, 1]], ![![-5, -2, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [34, 21, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 17, 37], [10, 29, 10], [0, 1]]
 g := ![![[43, 33, 2], [6, 2, 17], [29, 33, 14], [4, 5, 1], []], ![[15, 40, 23, 17], [30, 14, 33, 28], [46, 36, 35, 3], [22, 24, 31, 3], [19, 6]], ![[38, 41, 44, 38], [8, 26, 0, 19], [31, 23, 18, 19], [23, 17, 32, 23], [46, 6]]]
 h' := ![![[42, 17, 37], [31, 42, 40], [1, 33, 8], [5, 28, 22], [0, 0, 1], [0, 1]], ![[10, 29, 10], [32, 15, 35], [38, 17, 43], [21, 14, 29], [37, 26, 29], [42, 17, 37]], ![[0, 1], [30, 37, 19], [40, 44, 43], [37, 5, 43], [40, 21, 17], [10, 29, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 30], []]
 b := ![[], [9, 35, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [34, 21, 42, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14194, -46530, 12126]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![302, -990, 258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![13, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![13, 1, 0]] 
 ![![53, 0, 0], ![13, 1, 0], ![43, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![13, 1, 0], ![0, 13, 1], ![10, -30, 13]]]
  hmulB := by decide  
  f := ![![![352, 27, 0], ![-1431, 0, 0]], ![![78, 6, 0], ![-317, 0, 0]], ![![290, 22, 0], ![-1179, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 53, 0], ![-43, 0, 53]], ![![0, 1, 0], ![-4, 13, 1], ![-3, -30, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-8, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-8, 1, 0]] 
 ![![53, 0, 0], ![45, 1, 0], ![42, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-8, 1, 0], ![0, -8, 1], ![10, -30, -8]]]
  hmulB := by decide  
  f := ![![![193, -24, 0], ![1272, 0, 0]], ![![169, -21, 0], ![1114, 0, 0]], ![![162, -20, 0], ![1068, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 53, 0], ![-42, 0, 53]], ![![-1, 1, 0], ![6, -8, 1], ![32, -30, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-5, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-5, 1, 0]] 
 ![![53, 0, 0], ![48, 1, 0], ![28, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-5, 1, 0], ![0, -5, 1], ![10, -30, -5]]]
  hmulB := by decide  
  f := ![![![181, -36, 0], ![1908, 0, 0]], ![![166, -33, 0], ![1750, 0, 0]], ![![96, -19, 0], ![1012, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 53, 0], ![-28, 0, 53]], ![![-1, 1, 0], ![4, -5, 1], ![30, -30, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![13, 1, 0]] ![![53, 0, 0], ![-8, 1, 0]]
  ![![53, 0, 0], ![2, 5, 1]] where
 M := ![![![2809, 0, 0], ![-424, 53, 0]], ![![689, 53, 0], ![-104, 5, 1]]]
 hmul := by decide  
 g := ![![![![51, -5, -1], ![53, 0, 0]], ![![-8, 1, 0], ![0, 0, 0]]], ![![![11, -4, -1], ![53, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![2, 5, 1]] ![![53, 0, 0], ![-5, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-265, 53, 0]], ![![106, 265, 53], ![0, -53, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-5, 1, 0]]], ![![![2, 5, 1]], ![![0, -1, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![19, -15, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![19, -15, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![19, 44, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![19, -15, 1], ![10, -11, -15], ![-150, 460, -11]]]
  hmulB := by decide  
  f := ![![![-18, 15, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -44, 59]], ![![0, -1, 1], ![5, 11, -15], ![1, 16, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [36, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 58], [0, 1]]
 g := ![![[28, 41], [44, 16], [3], [37, 3], [54, 1]], ![[0, 18], [23, 43], [3], [22, 56], [49, 58]]]
 h' := ![![[54, 58], [9, 49], [45, 4], [25, 11], [3, 48], [0, 1]], ![[0, 1], [0, 10], [25, 55], [29, 48], [58, 11], [54, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [5, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [36, 5, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3792, -53, 94]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, -71, 94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![15, 1, 0]] 
 ![![59, 0, 0], ![15, 1, 0], ![11, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![15, 1, 0], ![0, 15, 1], ![10, -30, 15]]]
  hmulB := by decide  
  f := ![![![31, 2, 0], ![-118, 0, 0]], ![![-15, -1, 0], ![60, 0, 0]], ![![-11, -1, 0], ![44, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 59, 0], ![-11, 0, 59]], ![![0, 1, 0], ![-4, 15, 1], ![5, -30, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![19, -15, 1]] ![![59, 0, 0], ![15, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![885, 59, 0]], ![![1121, -885, 59], ![295, -236, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![15, 1, 0]]], ![![![19, -15, 1]], ![![5, -4, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [7, 43, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 48, 57], [13, 12, 4], [0, 1]]
 g := ![![[28, 8, 52], [21, 27], [1, 27, 3], [19], [1]], ![[7, 31, 1, 56], [30, 58], [16, 13, 33, 56], [46, 3, 39, 4], [43, 39, 47, 58]], ![[51, 23, 43, 14], [53, 39], [55, 54, 47, 56], [39, 19, 25, 57], [20, 27, 27, 3]]]
 h' := ![![[48, 48, 57], [24, 35, 28], [54, 11, 37], [50, 25, 53], [54, 18], [0, 1]], ![[13, 12, 4], [21, 34, 13], [29, 13, 34], [49, 32, 48], [3, 10, 50], [48, 48, 57]], ![[0, 1], [59, 53, 20], [8, 37, 51], [7, 4, 21], [44, 33, 11], [13, 12, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 2], []]
 b := ![[], [36, 15, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [7, 43, 0, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10919, 41236, -24705]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-179, 676, -405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![47, 33, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![47, 33, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![47, 33, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![47, 33, 1], ![10, 17, 33], ![330, -980, 17]]]
  hmulB := by decide  
  f := ![![![-46, -33, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -33, 67]], ![![0, 0, 1], ![-23, -16, 33], ![-7, -23, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [35, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 66], [0, 1]]
 g := ![![[16, 23], [40, 24], [26], [21], [40], [1]], ![[0, 44], [0, 43], [26], [21], [40], [1]]]
 h' := ![![[43, 66], [7, 31], [25, 15], [8, 19], [26, 50], [32, 43], [0, 1]], ![[0, 1], [0, 36], [0, 52], [21, 48], [32, 17], [5, 24], [43, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [19, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [35, 24, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55, -74, -53]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 25, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-33, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-33, 1, 0]] 
 ![![67, 0, 0], ![34, 1, 0], ![50, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-33, 1, 0], ![0, -33, 1], ![10, -30, -33]]]
  hmulB := by decide  
  f := ![![![2212, -67, 0], ![4489, 0, 0]], ![![1156, -35, 0], ![2346, 0, 0]], ![![1700, -51, 0], ![3450, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 67, 0], ![-50, 0, 67]], ![![-1, 1, 0], ![16, -33, 1], ![40, -30, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![47, 33, 1]] ![![67, 0, 0], ![-33, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2211, 67, 0]], ![![3149, 2211, 67], ![-1541, -1072, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-33, 1, 0]]], ![![![47, 33, 1]], ![![-23, -16, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [64, 38, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 27, 58], [65, 43, 13], [0, 1]]
 g := ![![[13, 37, 36], [1, 19, 10], [30, 67, 43], [61, 43], [14, 1], []], ![[37, 67, 26, 10], [7, 68, 12, 30], [55, 69, 59, 60], [70, 27], [58, 3], [31, 27]], ![[70, 49, 2, 65], [28, 46, 6, 63], [14, 2, 54, 41], [40, 9], [38, 19], [5, 27]]]
 h' := ![![[20, 27, 58], [7, 33, 65], [68, 13, 9], [20, 21, 16], [27, 43, 16], [0, 0, 1], [0, 1]], ![[65, 43, 13], [18, 61, 23], [59, 34, 5], [17, 35, 60], [38, 61, 58], [49, 20, 43], [20, 27, 58]], ![[0, 1], [22, 48, 54], [61, 24, 57], [36, 15, 66], [53, 38, 68], [0, 51, 27], [65, 43, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 67], []]
 b := ![[], [24, 23, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [64, 38, 57, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74550, -209095, -11005]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1050, -2945, -155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [58, 48, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 56, 68], [8, 16, 5], [0, 1]]
 g := ![![[13, 0, 3], [17, 1], [71, 48], [10, 37, 48], [57, 1], []], ![[13, 33, 32, 47], [30, 24], [6, 32], [23, 67, 49, 28], [31, 37], [62, 25]], ![[66, 46, 32, 51], [47, 38], [39, 49], [24, 70, 22, 31], [21, 70], [52, 25]]]
 h' := ![![[49, 56, 68], [13, 51, 52], [59, 53, 1], [4, 5, 62], [52, 53, 62], [0, 0, 1], [0, 1]], ![[8, 16, 5], [13, 45, 66], [1, 15, 43], [35, 59, 18], [26, 46, 70], [46, 40, 16], [49, 56, 68]], ![[0, 1], [71, 50, 28], [13, 5, 29], [31, 9, 66], [25, 47, 14], [41, 33, 56], [8, 16, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 68], []]
 b := ![[], [51, 54, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [58, 48, 16, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3285, 10147, -292]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45, 139, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![43, -31, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![43, -31, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![43, 48, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![43, -31, 1], ![10, 13, -31], ![-310, 940, 13]]]
  hmulB := by decide  
  f := ![![![-42, 31, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -48, 79]], ![![0, -1, 1], ![17, 19, -31], ![-11, 4, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [72, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 78], [0, 1]]
 g := ![![[40, 45], [30, 18], [12, 62], [50, 9], [32], [1]], ![[0, 34], [14, 61], [71, 17], [42, 70], [32], [1]]]
 h' := ![![[43, 78], [52, 19], [5, 52], [34, 33], [36, 3], [7, 43], [0, 1]], ![[0, 1], [0, 60], [29, 27], [31, 46], [7, 76], [39, 36], [43, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [31, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [72, 36, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112, -44, -47]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27, 28, -47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![31, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![31, 1, 0]] 
 ![![79, 0, 0], ![31, 1, 0], ![66, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![31, 1, 0], ![0, 31, 1], ![10, -30, 31]]]
  hmulB := by decide  
  f := ![![![838, 27, 0], ![-2133, 0, 0]], ![![310, 10, 0], ![-789, 0, 0]], ![![726, 23, 0], ![-1848, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 79, 0], ![-66, 0, 79]], ![![0, 1, 0], ![-13, 31, 1], ![-14, -30, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![43, -31, 1]] ![![79, 0, 0], ![31, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2449, 79, 0]], ![![3397, -2449, 79], ![1343, -948, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![31, 1, 0]]], ![![![43, -31, 1]], ![![17, -12, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB95I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB95I1 : PrimesBelowBoundCertificateInterval O 31 79 95 where
  m := 11
  g := ![1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB95I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![389017]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N0, I41N1, I43N0, I43N1, I43N2, I53N0, I53N1, I53N2, I59N1, I67N1, I79N1]
  Il := ![[], [I41N0, I41N1, I41N1], [I43N0, I43N1, I43N2], [], [I53N0, I53N1, I53N2], [I59N1], [], [I67N1], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
