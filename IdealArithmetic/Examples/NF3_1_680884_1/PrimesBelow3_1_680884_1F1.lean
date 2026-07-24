
import IdealArithmetic.Examples.NF3_1_680884_1.RI3_1_680884_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![32, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![1, 14, 2], ![355, 73, 15]]]
  hmulB := by decide  
  f := ![![![179, 3467, 496], ![185, -9176, 0]], ![![65, 1300, 186], ![75, -3441, 0]], ![![148, 2998, 429], ![178, -7936, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-32, 0, 37]], ![![0, 1, 0], ![-7, 14, 2], ![-31, 73, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-13, 1, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-13, 1, 0], ![1, -13, 2], ![355, 73, -12]]]
  hmulB := by decide  
  f := ![![![-265, 4634, -714], ![259, 13209, 0]], ![![-178, 2999, -462], ![149, 8547, 0]], ![![-199, 3382, -521], ![173, 9639, 0]]]
  g := ![![![1, 0, 0], ![-24, 37, 0], ![-27, 0, 37]], ![![-1, 1, 0], ![7, -13, 2], ![-29, 73, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-2, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-2, 1, 0]] 
 ![![37, 0, 0], ![35, 1, 0], ![17, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-2, 1, 0], ![1, -2, 2], ![355, 73, -1]]]
  hmulB := by decide  
  f := ![![![-231, 467, -468], ![37, 8658, 0]], ![![-218, 441, -442], ![38, 8177, 0]], ![![-105, 214, -215], ![38, 3978, 0]]]
  g := ![![![1, 0, 0], ![-35, 37, 0], ![-17, 0, 37]], ![![-1, 1, 0], ![1, -2, 2], ![-59, 73, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![14, 1, 0]] ![![37, 0, 0], ![-13, 1, 0]]
  ![![37, 0, 0], ![-35, -18, 1]] where
 M := ![![![1369, 0, 0], ![-481, 37, 0]], ![![518, 37, 0], ![-181, 1, 2]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![22, 19, -1], ![37, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![32, 19, -1], ![39, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-35, -18, 1]] ![![37, 0, 0], ![-2, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-74, 37, 0]], ![![-1295, -666, 37], ![407, 74, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-2, 1, 0]]], ![![![-35, -18, 1]], ![![11, 2, -1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-35, -13, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-35, -13, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![6, 28, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-35, -13, 1], ![342, 38, -25], ![-4401, -735, 25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -28, 41]], ![![-1, -1, 1], ![12, 18, -25], ![-111, -35, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [8, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 40], [0, 1]]
 g := ![![[3, 36], [2], [31], [8, 2], [1]], ![[0, 5], [2], [31], [1, 39], [1]]]
 h' := ![![[17, 40], [20, 35], [35, 17], [18, 20], [33, 17], [0, 1]], ![[0, 1], [0, 6], [37, 24], [30, 21], [35, 24], [17, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [9, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [8, 24, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2262, 1126, 254]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, -146, 254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-16, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-16, 1, 0]] 
 ![![41, 0, 0], ![25, 1, 0], ![16, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-16, 1, 0], ![1, -16, 2], ![355, 73, -15]]]
  hmulB := by decide  
  f := ![![![-331, 7352, -920], ![328, 18860, 0]], ![![-199, 4475, -560], ![206, 11480, 0]], ![![-128, 2869, -359], ![131, 7360, 0]]]
  g := ![![![1, 0, 0], ![-25, 41, 0], ![-16, 0, 41]], ![![-1, 1, 0], ![9, -16, 2], ![-30, 73, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-35, -13, 1]] ![![41, 0, 0], ![-16, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-656, 41, 0]], ![![-1435, -533, 41], ![902, 246, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-16, 1, 0]]], ![![![-35, -13, 1]], ![![22, 6, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![12, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![12, 1, 0]] 
 ![![43, 0, 0], ![12, 1, 0], ![36, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![12, 1, 0], ![1, 12, 2], ![355, 73, 13]]]
  hmulB := by decide  
  f := ![![![-563, -7769, -1296], ![-301, 27864, 0]], ![![-156, -2158, -360], ![-85, 7740, 0]], ![![-468, -6504, -1085], ![-264, 23328, 0]]]
  g := ![![![1, 0, 0], ![-12, 43, 0], ![-36, 0, 43]], ![![0, 1, 0], ![-5, 12, 2], ![-23, 73, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![14, 1, 0]] 
 ![![43, 0, 0], ![14, 1, 0], ![10, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![14, 1, 0], ![1, 14, 2], ![355, 73, 15]]]
  hmulB := by decide  
  f := ![![![-171, -2798, -400], ![-86, 8600, 0]], ![![-65, -910, -130], ![1, 2795, 0]], ![![-44, -651, -93], ![-7, 2000, 0]]]
  g := ![![![1, 0, 0], ![-14, 43, 0], ![-10, 0, 43]], ![![0, 1, 0], ![-5, 14, 2], ![-19, 73, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![16, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![16, 1, 0]] 
 ![![43, 0, 0], ![16, 1, 0], ![23, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![16, 1, 0], ![1, 16, 2], ![355, 73, 17]]]
  hmulB := by decide  
  f := ![![![-901, -19022, -2380], ![-774, 51170, 0]], ![![-346, -7066, -884], ![-257, 19006, 0]], ![![-489, -10175, -1273], ![-395, 27370, 0]]]
  g := ![![![1, 0, 0], ![-16, 43, 0], ![-23, 0, 43]], ![![0, 1, 0], ![-7, 16, 2], ![-28, 73, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![12, 1, 0]] ![![43, 0, 0], ![14, 1, 0]]
  ![![43, 0, 0], ![-66, 13, 1]] where
 M := ![![![1849, 0, 0], ![602, 43, 0]], ![![516, 43, 0], ![169, 26, 2]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![7, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-66, 13, 1]] ![![43, 0, 0], ![16, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![688, 43, 0]], ![![-2838, 559, 43], ![-688, 215, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![16, 1, 0]]], ![![![-66, 13, 1]], ![![-16, 5, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-25, -1, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-25, -1, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![22, 46, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-25, -1, 1], ![354, 48, -1], ![-141, 141, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -46, 47]], ![![-1, -1, 1], ![8, 2, -1], ![-25, -43, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [29, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 46], [0, 1]]
 g := ![![[4, 36], [15, 2], [9, 2], [28, 14], [1]], ![[11, 11], [18, 45], [12, 45], [2, 33], [1]]]
 h' := ![![[25, 46], [35, 6], [21, 7], [34, 7], [18, 25], [0, 1]], ![[0, 1], [44, 41], [8, 40], [21, 40], [32, 22], [25, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [38, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [29, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1669, 3838, 1943]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-945, -1820, 1943]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![1, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![1, 1, 0]] 
 ![![47, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![1, 1, 0], ![1, 1, 2], ![355, 73, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![47, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, -1], ![23, 24, 0]]]
  g := ![![![1, 0, 0], ![-1, 47, 0], ![0, 0, 47]], ![![0, 1, 0], ![0, 1, 2], ![6, 73, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-25, -1, 1]] ![![47, 0, 0], ![1, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![47, 47, 0]], ![![-1175, -47, 47], ![329, 47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![1, 1, 0]]], ![![![-25, -1, 1]], ![![7, 1, 0]]]]
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
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [26, 13, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 27, 1], [11, 25, 52], [0, 1]]
 g := ![![[34, 3, 44], [10, 17], [8, 45, 25], [24, 42], [1]], ![[41, 2, 34, 17], [24, 36], [6, 30, 22, 29], [16, 4], [51, 30, 3, 1]], ![[12, 51, 8, 28], [38, 13], [29, 34, 37, 40], [49, 40], [33, 17, 47, 52]]]
 h' := ![![[17, 27, 1], [21, 3, 16], [4, 52, 21], [52, 14, 5], [27, 40, 28], [0, 1]], ![[11, 25, 52], [52, 0, 32], [27, 29, 47], [32, 38, 33], [36, 24, 51], [17, 27, 1]], ![[0, 1], [12, 50, 5], [24, 25, 38], [14, 1, 15], [49, 42, 27], [11, 25, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 28], []]
 b := ![[], [38, 10, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [26, 13, 25, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26141638963, -9066997419, -1703255276]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-493238471, -171075423, -32136892]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-28, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-28, 1, 0]] 
 ![![59, 0, 0], ![31, 1, 0], ![51, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-28, 1, 0], ![1, -28, 2], ![355, 73, -27]]]
  hmulB := by decide  
  f := ![![![353, -14554, 1040], ![-354, -30680, 0]], ![![190, -7641, 546], ![-176, -16107, 0]], ![![289, -12580, 899], ![-340, -26520, 0]]]
  g := ![![![1, 0, 0], ![-31, 59, 0], ![-51, 0, 59]], ![![-1, 1, 0], ![13, -28, 2], ![-9, 73, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-17, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-17, 1, 0]] 
 ![![59, 0, 0], ![42, 1, 0], ![33, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-17, 1, 0], ![1, -17, 2], ![355, 73, -16]]]
  hmulB := by decide  
  f := ![![![2349, -46828, 5512], ![-1416, -162604, 0]], ![![1673, -33320, 3922], ![-1002, -115699, 0]], ![![1315, -26192, 3083], ![-788, -90948, 0]]]
  g := ![![![1, 0, 0], ![-42, 59, 0], ![-33, 0, 59]], ![![-1, 1, 0], ![11, -17, 2], ![-37, 73, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-15, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-15, 1, 0]] 
 ![![59, 0, 0], ![44, 1, 0], ![6, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-15, 1, 0], ![1, -15, 2], ![355, 73, -14]]]
  hmulB := by decide  
  f := ![![![776, -13193, 1760], ![-413, -51920, 0]], ![![582, -9835, 1312], ![-294, -38704, 0]], ![![84, -1342, 179], ![-22, -5280, 0]]]
  g := ![![![1, 0, 0], ![-44, 59, 0], ![-6, 0, 59]], ![![-1, 1, 0], ![11, -15, 2], ![-47, 73, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-28, 1, 0]] ![![59, 0, 0], ![-17, 1, 0]]
  ![![59, 0, 0], ![-27, 7, 1]] where
 M := ![![![3481, 0, 0], ![-1003, 59, 0]], ![![-1652, 59, 0], ![477, -45, 2]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![10, -6, -1], ![59, 0, 0]]], ![![![-1, -6, -1], ![59, 0, 0]], ![![9, -1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-27, 7, 1]] ![![59, 0, 0], ![-15, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-885, 59, 0]], ![![-1593, 413, 59], ![767, -59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-15, 1, 0]]], ![![![-27, 7, 1]], ![![13, -1, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-70, -32, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-70, -32, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![52, 29, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-70, -32, 1], ![323, 3, -63], ![-11146, -2122, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -29, 61]], ![![-2, -1, 1], ![59, 30, -63], ![-158, -21, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [20, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 60], [0, 1]]
 g := ![![[56, 58], [22], [20, 22], [2, 27], [39, 1]], ![[0, 3], [22], [24, 39], [18, 34], [17, 60]]]
 h' := ![![[39, 60], [45, 27], [27, 49], [21, 12], [13, 37], [0, 1]], ![[0, 1], [0, 34], [47, 12], [1, 49], [53, 24], [39, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [54, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [20, 22, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1781, 4638, 1727]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1443, -745, 1727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![2, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![2, 1, 0]] 
 ![![61, 0, 0], ![2, 1, 0], ![29, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![2, 1, 0], ![1, 2, 2], ![355, 73, 3]]]
  hmulB := by decide  
  f := ![![![-1237, -2479, -2480], ![-61, 75640, 0]], ![![-40, -80, -80], ![1, 2440, 0]], ![![-589, -1179, -1179], ![-1, 35960, 0]]]
  g := ![![![1, 0, 0], ![-2, 61, 0], ![-29, 0, 61]], ![![0, 1, 0], ![-1, 2, 2], ![2, 73, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-70, -32, 1]] ![![61, 0, 0], ![2, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![122, 61, 0]], ![![-4270, -1952, 61], ![183, -61, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![2, 1, 0]]], ![![![-70, -32, 1]], ![![3, -1, -1]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![4, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![4, 1, 0]] 
 ![![67, 0, 0], ![4, 1, 0], ![26, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![4, 1, 0], ![1, 4, 2], ![355, 73, 5]]]
  hmulB := by decide  
  f := ![![![-526, -2108, -1054], ![0, 35309, 0]], ![![-31, -124, -62], ![1, 2077, 0]], ![![-204, -818, -409], ![-2, 13702, 0]]]
  g := ![![![1, 0, 0], ![-4, 67, 0], ![-26, 0, 67]], ![![0, 1, 0], ![-1, 4, 2], ![-1, 73, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![27, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![27, 1, 0]] 
 ![![67, 0, 0], ![27, 1, 0], ![38, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![27, 1, 0], ![1, 27, 2], ![355, 73, 28]]]
  hmulB := by decide  
  f := ![![![213, 8636, 640], ![268, -21440, 0]], ![![74, 3454, 256], ![135, -8576, 0]], ![![120, 4898, 363], ![154, -12160, 0]]]
  g := ![![![1, 0, 0], ![-27, 67, 0], ![-38, 0, 67]], ![![0, 1, 0], ![-12, 27, 2], ![-40, 73, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-32, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-32, 1, 0]] 
 ![![67, 0, 0], ![35, 1, 0], ![58, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-32, 1, 0], ![1, -32, 2], ![355, 73, -31]]]
  hmulB := by decide  
  f := ![![![-544, 28693, -1794], ![737, 60099, 0]], ![![-275, 14970, -936], ![403, 31356, 0]], ![![-480, 24839, -1553], ![619, 52026, 0]]]
  g := ![![![1, 0, 0], ![-35, 67, 0], ![-58, 0, 67]], ![![-1, 1, 0], ![15, -32, 2], ![-6, 73, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![4, 1, 0]] ![![67, 0, 0], ![27, 1, 0]]
  ![![67, 0, 0], ![-46, -18, 1]] where
 M := ![![![4489, 0, 0], ![1809, 67, 0]], ![![268, 67, 0], ![109, 31, 2]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![27, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-46, -18, 1]] ![![67, 0, 0], ![-32, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2144, 67, 0]], ![![-3082, -1206, 67], ![1809, 603, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-32, 1, 0]]], ![![![-46, -18, 1]], ![![27, 9, -1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [4, 20, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 45, 55], [62, 25, 16], [0, 1]]
 g := ![![[54, 45, 38], [50, 30, 6], [70, 26, 36], [41, 40], [59, 1], []], ![[11, 45, 14, 53], [7, 59, 60, 44], [59, 34, 10, 52], [68, 20], [28, 57], [32, 43]], ![[42, 9, 22, 40], [18, 20, 56, 40], [17, 60, 68, 45], [35, 43], [21, 37], [0, 43]]]
 h' := ![![[68, 45, 55], [13, 32, 40], [4, 16, 52], [10, 21, 65], [48, 23, 53], [0, 0, 1], [0, 1]], ![[62, 25, 16], [56, 50, 62], [16, 49, 50], [22, 53, 11], [62, 63, 34], [23, 54, 25], [68, 45, 55]], ![[0, 1], [54, 60, 40], [25, 6, 40], [45, 68, 66], [16, 56, 55], [10, 17, 45], [62, 25, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 40], []]
 b := ![[], [36, 53, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [4, 20, 12, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1029074, -308850, -50268]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14494, -4350, -708]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-55, -30, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-55, -30, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![18, 43, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-55, -30, 1], ![325, 18, -59], ![-10436, -1976, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -43, 73]], ![![-1, -1, 1], ![19, 35, -59], ![-140, -20, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [57, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 72], [0, 1]]
 g := ![![[19, 41], [54], [36], [31, 25], [71], [1]], ![[0, 32], [54], [36], [39, 48], [71], [1]]]
 h' := ![![[12, 72], [65, 25], [71, 28], [58, 67], [5, 68], [16, 12], [0, 1]], ![[0, 1], [0, 48], [42, 45], [59, 6], [18, 5], [14, 61], [12, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [52, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [57, 61, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42940, 11483, 1688]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![172, -837, 1688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-14, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-14, 1, 0]] 
 ![![73, 0, 0], ![59, 1, 0], ![12, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-14, 1, 0], ![1, -14, 2], ![355, 73, -13]]]
  hmulB := by decide  
  f := ![![![-1007, 15282, -2184], ![438, 79716, 0]], ![![-811, 12343, -1764], ![366, 64386, 0]], ![![-164, 2512, -359], ![80, 13104, 0]]]
  g := ![![![1, 0, 0], ![-59, 73, 0], ![-12, 0, 73]], ![![-1, 1, 0], ![11, -14, 2], ![-52, 73, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-55, -30, 1]] ![![73, 0, 0], ![-14, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1022, 73, 0]], ![![-4015, -2190, 73], ![1095, 438, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-14, 1, 0]]], ![![![-55, -30, 1]], ![![15, 6, -1]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-104, -7, 2]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-104, -7, 2]] 
 ![![79, 0, 0], ![0, 79, 0], ![27, 36, 1]] where
  M :=![![![-104, -7, 2], ![703, 42, -12], ![-2057, -83, 35]]]
  hmulB := by decide  
  f := ![![![6, 1, 0]], ![![1, 6, 2]], ![![7, 4, 1]]]
  g := ![![![-2, -1, 2], ![13, 6, -12], ![-38, -17, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [78, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 78], [0, 1]]
 g := ![![[66, 73], [28, 65], [13, 73], [59, 42], [11], [1]], ![[65, 6], [52, 14], [12, 6], [66, 37], [11], [1]]]
 h' := ![![[66, 78], [28, 28], [13, 67], [59, 51], [12, 68], [1, 66], [0, 1]], ![[0, 1], [59, 51], [11, 12], [28, 28], [76, 11], [12, 13], [66, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [36, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [78, 13, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4399, 639, 630]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-271, -279, 630]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![6, 1, 0]] 
 ![![79, 0, 0], ![6, 1, 0], ![22, 0, 1]] where
  M :=![![![6, 1, 0], ![1, 6, 2], ![355, 73, 7]]]
  hmulB := by decide  
  f := ![![![-104, -7, 2]], ![![1, 0, 0]], ![![-55, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 6, 2], ![-3, 73, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-104, -7, 2]] ![![6, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB234I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB234I1 : PrimesBelowBoundCertificateInterval O 31 79 234 where
  m := 11
  g := ![3, 2, 3, 2, 1, 3, 2, 3, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB234I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I43N0, I43N1, I43N2, I47N1, I59N0, I59N1, I59N2, I61N1, I67N0, I67N1, I67N2, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [], [I59N0, I59N1, I59N2], [I61N1], [I67N0, I67N1, I67N2], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
