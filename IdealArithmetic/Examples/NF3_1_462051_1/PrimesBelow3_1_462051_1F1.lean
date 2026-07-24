
import IdealArithmetic.Examples.NF3_1_462051_1.RI3_1_462051_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-27, -3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-27, -3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![10, 34, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-27, -3, 1], ![155, 9, -3], ![-465, 47, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -34, 37]], ![![-1, -1, 1], ![5, 3, -3], ![-15, -7, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [29, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 36], [0, 1]]
 g := ![![[1, 3], [26], [24, 10], [27], [1]], ![[25, 34], [26], [30, 27], [27], [1]]]
 h' := ![![[8, 36], [35, 15], [7, 10], [21, 11], [8, 8], [0, 1]], ![[0, 1], [7, 22], [13, 27], [35, 26], [35, 29], [8, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [34, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [29, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![339, 198, 8]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, -2, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![3, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![3, 1, 0]] 
 ![![37, 0, 0], ![3, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![3, 1, 0], ![0, 3, 1], ![155, 36, 3]]]
  hmulB := by decide  
  f := ![![![64, 21, 0], ![-777, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![46, 15, 0], ![-558, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-1, 3, 1], ![-1, 36, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-27, -3, 1]] ![![37, 0, 0], ![3, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![111, 37, 0]], ![![-999, -111, 37], ![74, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![3, 1, 0]]], ![![![-27, -3, 1]], ![![2, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-28, -7, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-28, -7, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![13, 34, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-28, -7, 1], ![155, 8, -7], ![-1085, -97, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -34, 41]], ![![-1, -1, 1], ![6, 6, -7], ![-29, -9, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [30, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 40], [0, 1]]
 g := ![![[16, 33], [25], [10], [24, 21], [1]], ![[2, 8], [25], [10], [30, 20], [1]]]
 h' := ![![[12, 40], [31, 19], [24, 36], [18, 25], [11, 12], [0, 1]], ![[0, 1], [13, 22], [5, 5], [31, 16], [32, 29], [12, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [21, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [30, 29, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1858, 909, 409]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-175, -317, 409]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![7, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![7, 1, 0]] 
 ![![41, 0, 0], ![7, 1, 0], ![33, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![7, 1, 0], ![0, 7, 1], ![155, 36, 7]]]
  hmulB := by decide  
  f := ![![![29, 4, 0], ![-164, 0, 0]], ![![-7, -1, 0], ![42, 0, 0]], ![![23, 3, 0], ![-130, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 41, 0], ![-33, 0, 41]], ![![0, 1, 0], ![-2, 7, 1], ![-8, 36, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-28, -7, 1]] ![![41, 0, 0], ![7, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![287, 41, 0]], ![![-1148, -287, 41], ![-41, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![7, 1, 0]]], ![![![-28, -7, 1]], ![![-1, -1, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, -24, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, -24, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![24, 19, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, -24, 1], ![155, 17, -24], ![-3720, -709, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -19, 43]], ![![-1, -1, 1], ![17, 11, -24], ![-96, -24, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [41, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 42], [0, 1]]
 g := ![![[28, 21], [9, 11], [25], [13, 40], [1]], ![[0, 22], [23, 32], [25], [17, 3], [1]]]
 h' := ![![[13, 42], [18, 35], [38, 22], [26, 38], [2, 13], [0, 1]], ![[0, 1], [0, 8], [23, 21], [4, 5], [42, 30], [13, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [37, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [41, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1907, -15, 135]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31, -60, 135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![26, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![0, -19, 1], ![155, 36, -19]]]
  hmulB := by decide  
  f := ![![![761, -40, 0], ![1720, 0, 0]], ![![438, -23, 0], ![990, 0, 0]], ![![484, -25, 0], ![1094, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-26, 0, 43]], ![![-1, 1, 0], ![10, -19, 1], ![-5, 36, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-19, -24, 1]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![-817, -1032, 43], ![516, 473, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-19, 1, 0]]], ![![![-19, -24, 1]], ![![12, 11, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![22, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![22, 1, 0]] 
 ![![47, 0, 0], ![22, 1, 0], ![33, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![22, 1, 0], ![0, 22, 1], ![155, 36, 22]]]
  hmulB := by decide  
  f := ![![![243, 11, 0], ![-517, 0, 0]], ![![110, 5, 0], ![-234, 0, 0]], ![![165, 7, 0], ![-351, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 47, 0], ![-33, 0, 47]], ![![0, 1, 0], ![-11, 22, 1], ![-29, 36, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-18, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-18, 1, 0]] 
 ![![47, 0, 0], ![29, 1, 0], ![5, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-18, 1, 0], ![0, -18, 1], ![155, 36, -18]]]
  hmulB := by decide  
  f := ![![![757, -42, 0], ![1974, 0, 0]], ![![451, -25, 0], ![1176, 0, 0]], ![![79, -4, 0], ![206, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 47, 0], ![-5, 0, 47]], ![![-1, 1, 0], ![11, -18, 1], ![-17, 36, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-4, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-4, 1, 0]] 
 ![![47, 0, 0], ![43, 1, 0], ![31, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-4, 1, 0], ![0, -4, 1], ![155, 36, -4]]]
  hmulB := by decide  
  f := ![![![57, -14, 0], ![658, 0, 0]], ![![53, -13, 0], ![612, 0, 0]], ![![41, -10, 0], ![474, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 47, 0], ![-31, 0, 47]], ![![-1, 1, 0], ![3, -4, 1], ![-27, 36, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![22, 1, 0]] ![![47, 0, 0], ![-18, 1, 0]]
  ![![47, 0, 0], ![-20, 4, 1]] where
 M := ![![![2209, 0, 0], ![-846, 47, 0]], ![![1034, 47, 0], ![-396, 4, 1]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![2, -3, -1], ![47, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![12, -4, -1], ![48, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-20, 4, 1]] ![![47, 0, 0], ![-4, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-188, 47, 0]], ![![-940, 188, 47], ![235, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-4, 1, 0]]], ![![![-20, 4, 1]], ![![5, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-42, -10, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-42, -10, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![11, 43, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-42, -10, 1], ![155, -6, -10], ![-1550, -205, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -43, 53]], ![![-1, -1, 1], ![5, 8, -10], ![-28, 1, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [17, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 52], [0, 1]]
 g := ![![[38, 25], [25], [50, 43], [52], [43, 1]], ![[0, 28], [25], [44, 10], [52], [33, 52]]]
 h' := ![![[43, 52], [3, 48], [51, 5], [32, 34], [11, 30], [0, 1]], ![[0, 1], [0, 5], [1, 48], [10, 19], [29, 23], [43, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [3, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [17, 10, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-902, 1191, 289]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -212, 289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![10, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![10, 1, 0]] 
 ![![53, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![10, 1, 0], ![0, 10, 1], ![155, 36, 10]]]
  hmulB := by decide  
  f := ![![![141, 14, 0], ![-742, 0, 0]], ![![10, 1, 0], ![-52, 0, 0]], ![![2, 0, 0], ![-10, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 53, 0], ![-6, 0, 53]], ![![0, 1, 0], ![-2, 10, 1], ![-5, 36, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-42, -10, 1]] ![![53, 0, 0], ![10, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![530, 53, 0]], ![![-2226, -530, 53], ![-265, -106, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![10, 1, 0]]], ![![![-42, -10, 1]], ![![-5, -2, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-537, -196, -26]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-537, -196, -26]] 
 ![![59, 0, 0], ![0, 59, 0], ![32, 3, 1]] where
  M :=![![![-537, -196, -26], ![-4030, -1473, -196], ![-30380, -11086, -1473]]]
  hmulB := by decide  
  f := ![![![53, 8, -2]], ![![-310, -19, 8]], ![![34, 3, -1]]]
  g := ![![![5, -2, -26], ![38, -15, -196], ![284, -113, -1473]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [16, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 58], [0, 1]]
 g := ![![[48, 48], [12, 12], [20], [3, 48], [58, 1]], ![[0, 11], [0, 47], [20], [14, 11], [57, 58]]]
 h' := ![![[58, 58], [44, 44], [37, 37], [11, 16], [16, 44], [0, 1]], ![[0, 1], [0, 15], [0, 22], [54, 43], [31, 15], [58, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [15, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [16, 1, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![326, 226, 36]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, 2, 36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 8, -2]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![53, 8, -2]] 
 ![![59, 0, 0], ![56, 1, 0], ![50, 0, 1]] where
  M :=![![![53, 8, -2], ![-310, -19, 8], ![1240, -22, -19]]]
  hmulB := by decide  
  f := ![![![-537, -196, -26]], ![![-578, -211, -28]], ![![-970, -354, -47]]]
  g := ![![![-5, 8, -2], ![6, -19, 8], ![58, -22, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-537, -196, -26]] ![![53, 8, -2]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-9, -24, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-9, -24, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![52, 37, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-9, -24, 1], ![155, 27, -24], ![-3720, -709, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -37, 61]], ![![-1, -1, 1], ![23, 15, -24], ![-84, -28, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [1, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 60], [0, 1]]
 g := ![![[46, 1], [14], [11, 25], [12, 34], [15, 1]], ![[0, 60], [14], [20, 36], [34, 27], [30, 60]]]
 h' := ![![[15, 60], [46, 1], [50, 40], [49, 5], [46, 41], [0, 1]], ![[0, 1], [0, 60], [40, 21], [2, 56], [51, 20], [15, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [2, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [1, 46, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5938, 2435, 445]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-282, -230, 445]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![24, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![24, 1, 0]] 
 ![![61, 0, 0], ![24, 1, 0], ![34, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![24, 1, 0], ![0, 24, 1], ![155, 36, 24]]]
  hmulB := by decide  
  f := ![![![433, 18, 0], ![-1098, 0, 0]], ![![168, 7, 0], ![-426, 0, 0]], ![![250, 10, 0], ![-634, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 61, 0], ![-34, 0, 61]], ![![0, 1, 0], ![-10, 24, 1], ![-25, 36, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-9, -24, 1]] ![![61, 0, 0], ![24, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1464, 61, 0]], ![![-549, -1464, 61], ![-61, -549, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![24, 1, 0]]], ![![![-9, -24, 1]], ![![-1, -9, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-12, 15, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-12, 15, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![55, 15, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-12, 15, 1], ![155, 24, 15], ![2325, 695, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -15, 67]], ![![-1, 0, 1], ![-10, -3, 15], ![15, 5, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [59, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 66], [0, 1]]
 g := ![![[30, 25], [16, 15], [24], [15], [47], [1]], ![[0, 42], [65, 52], [24], [15], [47], [1]]]
 h' := ![![[39, 66], [61, 62], [51, 45], [23, 52], [38, 45], [8, 39], [0, 1]], ![[0, 1], [0, 5], [64, 22], [41, 15], [51, 22], [55, 28], [39, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [20, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [59, 28, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-898, 17, 19]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -4, 19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-15, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-15, 1, 0]] 
 ![![67, 0, 0], ![52, 1, 0], ![43, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-15, 1, 0], ![0, -15, 1], ![155, 36, -15]]]
  hmulB := by decide  
  f := ![![![196, -13, 0], ![871, 0, 0]], ![![166, -11, 0], ![738, 0, 0]], ![![124, -8, 0], ![551, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 67, 0], ![-43, 0, 67]], ![![-1, 1, 0], ![11, -15, 1], ![-16, 36, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-12, 15, 1]] ![![67, 0, 0], ![-15, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1005, 67, 0]], ![![-804, 1005, 67], ![335, -201, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-15, 1, 0]]], ![![![-12, 15, 1]], ![![5, -3, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-49, -22, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-49, -22, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![22, 49, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-49, -22, 1], ![155, -13, -22], ![-3410, -637, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -49, 71]], ![![-1, -1, 1], ![9, 15, -22], ![-44, 0, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [15, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 70], [0, 1]]
 g := ![![[44, 19], [52, 16], [34, 5], [38], [15], [1]], ![[0, 52], [0, 55], [0, 66], [38], [15], [1]]]
 h' := ![![[50, 70], [1, 44], [58, 67], [69, 54], [0, 31], [56, 50], [0, 1]], ![[0, 1], [0, 27], [0, 4], [0, 17], [59, 40], [0, 21], [50, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [62, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [15, 21, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![635, 785, 187]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49, -118, 187]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![22, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![22, 1, 0]] 
 ![![71, 0, 0], ![22, 1, 0], ![13, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![22, 1, 0], ![0, 22, 1], ![155, 36, 22]]]
  hmulB := by decide  
  f := ![![![573, 26, 0], ![-1846, 0, 0]], ![![154, 7, 0], ![-496, 0, 0]], ![![95, 4, 0], ![-306, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 71, 0], ![-13, 0, 71]], ![![0, 1, 0], ![-7, 22, 1], ![-13, 36, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-49, -22, 1]] ![![71, 0, 0], ![22, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1562, 71, 0]], ![![-3479, -1562, 71], ![-923, -497, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![22, 1, 0]]], ![![![-49, -22, 1]], ![![-13, -7, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-32, 2, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-32, 2, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![41, 2, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-32, 2, 1], ![155, 4, 2], ![310, 227, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -2, 73]], ![![-1, 0, 1], ![1, 0, 2], ![2, 3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [5, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 72], [0, 1]]
 g := ![![[41, 49], [6], [6], [30, 65], [50], [1]], ![[70, 24], [6], [6], [64, 8], [50], [1]]]
 h' := ![![[14, 72], [20, 66], [59, 58], [69, 58], [67, 49], [68, 14], [0, 1]], ![[0, 1], [68, 7], [68, 15], [5, 15], [23, 24], [45, 59], [14, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [54, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [5, 59, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6073, -1450, 370]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-291, -30, 370]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-2, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-2, 1, 0]] 
 ![![73, 0, 0], ![71, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-2, 1, 0], ![0, -2, 1], ![155, 36, -2]]]
  hmulB := by decide  
  f := ![![![79, -39, 0], ![2847, 0, 0]], ![![77, -38, 0], ![2775, 0, 0]], ![![75, -37, 0], ![2703, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 73, 0], ![-69, 0, 73]], ![![-1, 1, 0], ![1, -2, 1], ![-31, 36, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-32, 2, 1]] ![![73, 0, 0], ![-2, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-146, 73, 0]], ![![-2336, 146, 73], ![219, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-2, 1, 0]]], ![![![-32, 2, 1]], ![![3, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [41, 75, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 0, 12], [15, 78, 67], [0, 1]]
 g := ![![[15, 47, 11], [30, 27, 16], [36, 4, 4], [7, 48, 1], [32, 1], []], ![[32, 66, 25, 61], [4, 44, 64, 66], [28, 23, 42, 78], [33, 29, 75, 70], [19, 1], [26, 65]], ![[10, 2, 61, 67], [24, 40, 71, 51], [68, 40, 58, 51], [76, 72, 55, 8], [], [50, 65]]]
 h' := ![![[17, 0, 12], [34, 33, 66], [25, 31, 75], [29, 48, 2], [31, 8, 1], [0, 0, 1], [0, 1]], ![[15, 78, 67], [31, 34, 14], [26, 53, 60], [2, 13, 21], [22, 46, 16], [13, 46, 78], [17, 0, 12]], ![[0, 1], [1, 12, 78], [48, 74, 23], [22, 18, 56], [64, 25, 62], [71, 33], [15, 78, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 43], []]
 b := ![[], [27, 46, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [41, 75, 47, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8374, 13035, 5925]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-106, 165, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB193I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB193I1 : PrimesBelowBoundCertificateInterval O 31 79 193 where
  m := 11
  g := ![2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB193I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
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
      exact NI47N2
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
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N1, I47N0, I47N1, I47N2, I53N1, I59N1, I61N1, I67N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [I53N1], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
