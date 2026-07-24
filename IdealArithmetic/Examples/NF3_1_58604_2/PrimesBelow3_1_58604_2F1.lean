
import IdealArithmetic.Examples.NF3_1_58604_2.RI3_1_58604_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![3, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![3, 1, 0]] 
 ![![37, 0, 0], ![3, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![3, 1, 0], ![0, 3, 1], ![42, -14, 3]]]
  hmulB := by decide  
  f := ![![![64, 21, 0], ![-777, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![46, 15, 0], ![-558, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-1, 3, 1], ![0, -14, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![8, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![8, 1, 0]] 
 ![![37, 0, 0], ![8, 1, 0], ![10, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![8, 1, 0], ![0, 8, 1], ![42, -14, 8]]]
  hmulB := by decide  
  f := ![![![81, 10, 0], ![-370, 0, 0]], ![![8, 1, 0], ![-36, 0, 0]], ![![18, 2, 0], ![-82, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 37, 0], ![-10, 0, 37]], ![![0, 1, 0], ![-2, 8, 1], ![2, -14, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-11, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-11, 1, 0]] 
 ![![37, 0, 0], ![26, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-11, 1, 0], ![0, -11, 1], ![42, -14, -11]]]
  hmulB := by decide  
  f := ![![![342, -31, 0], ![1147, 0, 0]], ![![254, -23, 0], ![852, 0, 0]], ![![268, -24, 0], ![899, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 37, 0], ![-27, 0, 37]], ![![-1, 1, 0], ![7, -11, 1], ![19, -14, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![3, 1, 0]] ![![37, 0, 0], ![8, 1, 0]]
  ![![37, 0, 0], ![24, 11, 1]] where
 M := ![![![1369, 0, 0], ![296, 37, 0]], ![![111, 37, 0], ![24, 11, 1]]]
 hmul := by decide  
 g := ![![![![13, -11, -1], ![37, 0, 0]], ![![-16, -10, -1], ![37, 0, 0]]], ![![![-21, -10, -1], ![37, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![24, 11, 1]] ![![37, 0, 0], ![-11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-407, 37, 0]], ![![888, 407, 37], ![-222, -111, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-11, 1, 0]]], ![![![24, 11, 1]], ![![-6, -3, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-361, -42, -19]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-361, -42, -19]] 
 ![![41, 0, 0], ![0, 41, 0], ![19, 13, 1]] where
  M :=![![![-361, -42, -19], ![-798, -95, -42], ![-1764, -210, -95]]]
  hmulB := by decide  
  f := ![![![-5, 0, 1]], ![![42, -19, 0]], ![![11, -5, 0]]]
  g := ![![![0, 5, -19], ![0, 11, -42], ![1, 25, -95]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [10, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 40], [0, 1]]
 g := ![![[20, 37], [16], [10], [25, 25], [1]], ![[0, 4], [16], [10], [27, 16], [1]]]
 h' := ![![[5, 40], [8, 23], [39, 4], [37, 16], [31, 5], [0, 1]], ![[0, 1], [0, 18], [18, 37], [35, 25], [15, 36], [5, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [27, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [10, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![94, -22, -49]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 15, -49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, 1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-5, 0, 1]] 
 ![![41, 0, 0], ![28, 1, 0], ![36, 0, 1]] where
  M :=![![![-5, 0, 1], ![42, -19, 0], ![0, 42, -19]]]
  hmulB := by decide  
  f := ![![![-361, -42, -19]], ![![-266, -31, -14]], ![![-360, -42, -19]]]
  g := ![![![-1, 0, 1], ![14, -19, 0], ![-12, 42, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-361, -42, -19]] ![![-5, 0, 1]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![7, 6, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![7, 6, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![7, 6, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![7, 6, 1], ![42, -7, 6], ![252, -42, -7]]]
  hmulB := by decide  
  f := ![![![-6, -6, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -6, 43]], ![![0, 0, 1], ![0, -1, 6], ![7, 0, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [42, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 42], [0, 1]]
 g := ![![[33, 4], [14, 17], [17], [12, 14], [1]], ![[36, 39], [16, 26], [17], [1, 29], [1]]]
 h' := ![![[33, 42], [14, 41], [32, 19], [12, 24], [1, 33], [0, 1]], ![[0, 1], [34, 2], [14, 24], [30, 19], [15, 10], [33, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [9, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [42, 10, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-471, 530, -98]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 26, -98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-6, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-6, 1, 0]] 
 ![![43, 0, 0], ![37, 1, 0], ![7, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-6, 1, 0], ![0, -6, 1], ![42, -14, -6]]]
  hmulB := by decide  
  f := ![![![229, -38, 0], ![1634, 0, 0]], ![![199, -33, 0], ![1420, 0, 0]], ![![37, -6, 0], ![264, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 43, 0], ![-7, 0, 43]], ![![-1, 1, 0], ![5, -6, 1], ![14, -14, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![7, 6, 1]] ![![43, 0, 0], ![-6, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-258, 43, 0]], ![![301, 258, 43], ![0, -43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-6, 1, 0]]], ![![![7, 6, 1]], ![![0, -1, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![28, -22, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![28, -22, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![28, 25, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![28, -22, 1], ![42, 14, -22], ![-924, 350, 14]]]
  hmulB := by decide  
  f := ![![![-27, 22, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -25, 47]], ![![0, -1, 1], ![14, 12, -22], ![-28, 0, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [8, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 46], [0, 1]]
 g := ![![[8, 6], [33, 2], [25, 17], [12, 7], [1]], ![[0, 41], [46, 45], [18, 30], [34, 40], [1]]]
 h' := ![![[30, 46], [18, 37], [35, 7], [45, 39], [39, 30], [0, 1]], ![[0, 1], [0, 10], [10, 40], [40, 8], [46, 17], [30, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [27, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [8, 17, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2932, -41, 98]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, -53, 98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![22, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![22, 1, 0]] 
 ![![47, 0, 0], ![22, 1, 0], ![33, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![22, 1, 0], ![0, 22, 1], ![42, -14, 22]]]
  hmulB := by decide  
  f := ![![![243, 11, 0], ![-517, 0, 0]], ![![110, 5, 0], ![-234, 0, 0]], ![![165, 7, 0], ![-351, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 47, 0], ![-33, 0, 47]], ![![0, 1, 0], ![-11, 22, 1], ![-8, -14, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![28, -22, 1]] ![![47, 0, 0], ![22, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![1034, 47, 0]], ![![1316, -1034, 47], ![658, -470, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![22, 1, 0]]], ![![![28, -22, 1]], ![![14, -10, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![20, 18, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![20, 18, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![20, 18, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![20, 18, 1], ![42, 6, 18], ![756, -210, 6]]]
  hmulB := by decide  
  f := ![![![-19, -18, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -18, 53]], ![![0, 0, 1], ![-6, -6, 18], ![12, -6, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [15, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 52], [0, 1]]
 g := ![![[19, 46], [7], [4, 42], [37], [33, 1]], ![[0, 7], [7], [12, 11], [37], [13, 52]]]
 h' := ![![[33, 52], [50, 29], [46, 22], [34, 28], [35, 14], [0, 1]], ![[0, 1], [0, 24], [30, 31], [4, 25], [20, 39], [33, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [28, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [15, 20, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-216, 484, -191]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68, 74, -191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![47, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![0, -18, 1], ![42, -14, -18]]]
  hmulB := by decide  
  f := ![![![91, -5, 0], ![265, 0, 0]], ![![73, -4, 0], ![213, 0, 0]], ![![97, -5, 0], ![283, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-47, 0, 53]], ![![-1, 1, 0], ![11, -18, 1], ![26, -14, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![20, 18, 1]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![1060, 954, 53], ![-318, -318, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-18, 1, 0]]], ![![![20, 18, 1]], ![![-6, -6, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![31, 28, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![31, 28, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![31, 28, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![31, 28, 1], ![42, 17, 28], ![1176, -350, 17]]]
  hmulB := by decide  
  f := ![![![-30, -28, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -28, 59]], ![![0, 0, 1], ![-14, -13, 28], ![11, -14, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [6, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 58], [0, 1]]
 g := ![![[37, 21], [42, 25], [45], [5, 51], [14, 1]], ![[36, 38], [38, 34], [45], [11, 8], [28, 58]]]
 h' := ![![[14, 58], [43, 32], [40, 5], [29, 35], [34, 13], [0, 1]], ![[0, 1], [19, 27], [51, 54], [47, 24], [39, 46], [14, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [9, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [6, 45, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![90, -31, -58]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, 27, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-28, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-28, 1, 0]] 
 ![![59, 0, 0], ![31, 1, 0], ![42, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-28, 1, 0], ![0, -28, 1], ![42, -14, -28]]]
  hmulB := by decide  
  f := ![![![813, -29, 0], ![1711, 0, 0]], ![![449, -16, 0], ![945, 0, 0]], ![![630, -22, 0], ![1326, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 59, 0], ![-42, 0, 59]], ![![-1, 1, 0], ![14, -28, 1], ![28, -14, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![31, 28, 1]] ![![59, 0, 0], ![-28, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1652, 59, 0]], ![![1829, 1652, 59], ![-826, -767, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-28, 1, 0]]], ![![![31, 28, 1]], ![![-14, -13, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-8, 10, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-8, 10, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![53, 10, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-8, 10, 1], ![42, -22, 10], ![420, -98, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -10, 61]], ![![-1, 0, 1], ![-8, -2, 10], ![26, 2, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [26, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 60], [0, 1]]
 g := ![![[45, 4], [9], [6, 13], [22, 58], [50, 1]], ![[1, 57], [9], [46, 48], [55, 3], [39, 60]]]
 h' := ![![[50, 60], [7, 2], [27, 3], [38, 14], [42, 34], [0, 1]], ![[0, 1], [46, 59], [55, 58], [6, 47], [34, 27], [50, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [46, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [26, 11, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1634, -243, 360]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-286, -63, 360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-10, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-10, 1, 0]] 
 ![![61, 0, 0], ![51, 1, 0], ![22, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-10, 1, 0], ![0, -10, 1], ![42, -14, -10]]]
  hmulB := by decide  
  f := ![![![571, -57, 0], ![3477, 0, 0]], ![![481, -48, 0], ![2929, 0, 0]], ![![222, -22, 0], ![1352, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 61, 0], ![-22, 0, 61]], ![![-1, 1, 0], ![8, -10, 1], ![16, -14, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-8, 10, 1]] ![![61, 0, 0], ![-10, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-610, 61, 0]], ![![-488, 610, 61], ![122, -122, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-10, 1, 0]]], ![![![-8, 10, 1]], ![![2, -2, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [8, 44, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 50, 57], [28, 16, 10], [0, 1]]
 g := ![![[59, 6, 54], [24, 39, 60], [51, 35], [16, 15], [25, 1], []], ![[29, 46, 1, 63], [61, 40, 64, 38], [60, 22], [27, 64], [51, 55], [26, 33]], ![[37, 59], [34, 64, 11, 37], [30, 37], [1, 62], [6, 21], [6, 33]]]
 h' := ![![[64, 50, 57], [9, 12, 11], [43, 7, 44], [7, 42, 54], [1, 31, 45], [0, 0, 1], [0, 1]], ![[28, 16, 10], [62, 36, 56], [43, 37, 31], [56, 50, 42], [65, 65, 8], [2, 34, 16], [64, 50, 57]], ![[0, 1], [66, 19], [61, 23, 59], [57, 42, 38], [20, 38, 14], [66, 33, 50], [28, 16, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 38], []]
 b := ![[], [20, 15, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [8, 44, 42, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15745, 6231, 402]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-235, 93, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀



lemma PB69I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 68 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 68 (by omega)

def PB69I1 : PrimesBelowBoundCertificateInterval O 31 68 69 where
  m := 8
  g := ![3, 2, 2, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67]
  hP := PB69I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
  β := ![I37N0, I37N1, I37N2, I41N1, I43N1, I47N1, I53N1, I59N1, I61N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N1], [I47N1], [I53N1], [I59N1], [I61N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
