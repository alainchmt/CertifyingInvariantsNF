
import IdealArithmetic.Examples.NF3_3_895700_1.RI3_3_895700_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![8, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![8, 1, 0]] 
 ![![37, 0, 0], ![8, 1, 0], ![24, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![8, 1, 0], ![1, 8, 2], ![-428, 86, 9]]]
  hmulB := by decide  
  f := ![![![-401, -3468, -868], ![-148, 16058, 0]], ![![-85, -743, -186], ![-36, 3441, 0]], ![![-256, -2249, -563], ![-115, 10416, 0]]]
  g := ![![![1, 0, 0], ![-8, 37, 0], ![-24, 0, 37]], ![![0, 1, 0], ![-3, 8, 2], ![-36, 86, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 1, 0]] 
 ![![37, 0, 0], ![13, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 1, 0], ![1, 13, 2], ![-428, 86, 14]]]
  hmulB := by decide  
  f := ![![![-254, -4155, -640], ![-185, 11840, 0]], ![![-99, -1455, -224], ![-36, 4144, 0]], ![![-185, -3032, -467], ![-136, 8640, 0]]]
  g := ![![![1, 0, 0], ![-13, 37, 0], ![-27, 0, 37]], ![![0, 1, 0], ![-6, 13, 2], ![-52, 86, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, 1, 0]] 
 ![![37, 0, 0], ![15, 1, 0], ![36, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, 1, 0], ![1, 15, 2], ![-428, 86, 16]]]
  hmulB := by decide  
  f := ![![![86, 1947, 260], ![111, -4810, 0]], ![![37, 779, 104], ![38, -1924, 0]], ![![78, 1894, 253], ![122, -4680, 0]]]
  g := ![![![1, 0, 0], ![-15, 37, 0], ![-36, 0, 37]], ![![0, 1, 0], ![-8, 15, 2], ![-62, 86, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![8, 1, 0]] ![![37, 0, 0], ![13, 1, 0]]
  ![![37, 0, 0], ![-40, -8, 1]] where
 M := ![![![1369, 0, 0], ![481, 37, 0]], ![![296, 37, 0], ![105, 21, 2]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![13, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-40, -8, 1]] ![![37, 0, 0], ![15, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![555, 37, 0]], ![![-1480, -296, 37], ![-1036, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![15, 1, 0]]], ![![![-40, -8, 1]], ![![-28, -2, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-72, 5, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-72, 5, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![10, 5, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-72, 5, 1], ![-423, 14, 11], ![-2311, 259, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -5, 41]], ![![-2, 0, 1], ![-13, -1, 11], ![-61, 4, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [26, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 40], [0, 1]]
 g := ![![[2, 23], [33], [10], [20, 39], [1]], ![[36, 18], [33], [10], [1, 2], [1]]]
 h' := ![![[30, 40], [2, 33], [32, 19], [13, 16], [15, 30], [0, 1]], ![[0, 1], [8, 8], [28, 22], [1, 25], [13, 11], [30, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [9, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [26, 11, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2379, -349, 332]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-139, -49, 332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-11, 1, 0]] 
 ![![41, 0, 0], ![30, 1, 0], ![22, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-11, 1, 0], ![1, -11, 2], ![-428, 86, -10]]]
  hmulB := by decide  
  f := ![![![-215, 2856, -520], ![164, 10660, 0]], ![![-156, 2087, -380], ![124, 7790, 0]], ![![-110, 1532, -279], ![108, 5720, 0]]]
  g := ![![![1, 0, 0], ![-30, 41, 0], ![-22, 0, 41]], ![![-1, 1, 0], ![7, -11, 2], ![-68, 86, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-72, 5, 1]] ![![41, 0, 0], ![-11, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-451, 41, 0]], ![![-2952, 205, 41], ![369, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-11, 1, 0]]], ![![![-72, 5, 1]], ![![9, -1, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [37, 10, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 13, 33], [19, 29, 10], [0, 1]]
 g := ![![[19, 27, 13], [17, 4, 24], [2, 14], [6, 4, 1], []], ![[40, 29, 3, 8], [2, 6, 0, 29], [12, 41], [33, 26, 4, 18], [11, 14]], ![[13, 18, 21, 14], [13, 23, 33, 25], [29, 31], [26, 7, 23, 13], [34, 14]]]
 h' := ![![[28, 13, 33], [16, 6, 23], [18, 9, 14], [36, 7, 33], [0, 0, 1], [0, 1]], ![[19, 29, 10], [40, 13, 5], [1, 12, 15], [31, 37, 27], [33, 14, 29], [28, 13, 33]], ![[0, 1], [10, 24, 15], [15, 22, 14], [23, 42, 26], [6, 29, 13], [19, 29, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 41], []]
 b := ![[], [21, 36, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [37, 10, 39, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13036654, -5052285, 1027614]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![303178, -117495, 23898]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [18, 24, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 44, 13], [3, 2, 34], [0, 1]]
 g := ![![[28, 8, 7], [43, 8, 24], [39, 16, 24], [44, 16, 1], []], ![[22, 37, 13, 23], [43, 22, 20, 26], [38, 8, 28, 43], [33, 33, 40, 5], [41, 28]], ![[34, 7, 35, 37], [9, 41, 34, 12], [25, 46, 5, 6], [18, 42, 21, 24], [20, 28]]]
 h' := ![![[13, 44, 13], [25, 8, 17], [3, 0, 27], [7, 19, 20], [0, 0, 1], [0, 1]], ![[3, 2, 34], [44, 3, 44], [9, 18, 7], [13, 19, 5], [42, 32, 2], [13, 44, 13]], ![[0, 1], [4, 36, 33], [20, 29, 13], [0, 9, 22], [25, 15, 44], [3, 2, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 18], []]
 b := ![[], [45, 44, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [18, 24, 31, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17183766820, 8674346602, -2093364302]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-365612060, 184560566, -44539666]
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


def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![6, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![6, 1, 0]] 
 ![![53, 0, 0], ![6, 1, 0], ![9, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![6, 1, 0], ![1, 6, 2], ![-428, 86, 7]]]
  hmulB := by decide  
  f := ![![![-161, -972, -324], ![0, 8586, 0]], ![![-18, -108, -36], ![1, 954, 0]], ![![-27, -165, -55], ![-3, 1458, 0]]]
  g := ![![![1, 0, 0], ![-6, 53, 0], ![-9, 0, 53]], ![![0, 1, 0], ![-1, 6, 2], ![-19, 86, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-13, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-13, 1, 0]] 
 ![![53, 0, 0], ![40, 1, 0], ![22, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-13, 1, 0], ![1, -13, 2], ![-428, 86, -12]]]
  hmulB := by decide  
  f := ![![![-86, 1299, -200], ![53, 5300, 0]], ![![-61, 974, -150], ![54, 3975, 0]], ![![-33, 539, -83], ![33, 2200, 0]]]
  g := ![![![1, 0, 0], ![-40, 53, 0], ![-22, 0, 53]], ![![-1, 1, 0], ![9, -13, 2], ![-68, 86, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![6, 1, 0]] ![![53, 0, 0], ![6, 1, 0]]
  ![![53, 0, 0], ![-61, 6, 1]] where
 M := ![![![2809, 0, 0], ![318, 53, 0]], ![![318, 53, 0], ![37, 12, 2]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![6, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-61, 6, 1]] ![![53, 0, 0], ![-13, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-689, 53, 0]], ![![-3233, 318, 53], ![371, -53, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-13, 1, 0]]], ![![![-61, 6, 1]], ![![7, -1, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [2, 47, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 27, 10], [53, 31, 49], [0, 1]]
 g := ![![[46, 41, 16], [9, 34, 25], [18, 53], [1, 43, 46], [1]], ![[3, 32, 4, 34], [55, 35, 57, 23], [5, 26], [36, 7, 19, 33], [45, 41, 16, 56]], ![[50, 44, 51, 27], [8, 8, 41, 29], [33, 25], [35, 55, 23, 41], [29, 20, 38, 3]]]
 h' := ![![[26, 27, 10], [41, 2, 4], [27, 36, 5], [57, 48, 42], [57, 12, 20], [0, 1]], ![[53, 31, 49], [0, 58, 26], [6, 33, 43], [4, 40, 12], [22, 49, 32], [26, 27, 10]], ![[0, 1], [48, 58, 29], [56, 49, 11], [57, 30, 5], [21, 57, 7], [53, 31, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 34], []]
 b := ![[], [55, 12, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [2, 47, 39, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10079147, 4054126, -832372]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-170833, 68714, -14108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-74, -14, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-74, -14, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![48, 47, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-74, -14, 1], ![-442, 12, -27], ![5821, -1375, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -47, 61]], ![![-2, -1, 1], ![14, 21, -27], ![97, -21, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [7, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 60], [0, 1]]
 g := ![![[54, 14], [41], [38, 12], [3, 42], [49, 1]], ![[8, 47], [41], [16, 49], [48, 19], [37, 60]]]
 h' := ![![[49, 60], [14, 21], [39, 23], [40, 16], [23, 15], [0, 1]], ![[0, 1], [6, 40], [7, 38], [31, 45], [26, 46], [49, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [2, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [7, 12, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2399, -350, 330]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-299, -260, 330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![27, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![27, 1, 0]] 
 ![![61, 0, 0], ![27, 1, 0], ![2, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![27, 1, 0], ![1, 27, 2], ![-428, 86, 28]]]
  hmulB := by decide  
  f := ![![![-792, -30875, -2288], ![-793, 69784, 0]], ![![-344, -13656, -1012], ![-365, 30866, 0]], ![![-45, -1013, -75], ![17, 2288, 0]]]
  g := ![![![1, 0, 0], ![-27, 61, 0], ![-2, 0, 61]], ![![0, 1, 0], ![-12, 27, 2], ![-46, 86, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-74, -14, 1]] ![![61, 0, 0], ![27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1647, 61, 0]], ![![-4514, -854, 61], ![-2440, -366, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![27, 1, 0]]], ![![![-74, -14, 1]], ![![-40, -6, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-80, -2, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-80, -2, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![54, 65, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-80, -2, 1], ![-430, 6, -3], ![685, -343, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -65, 67]], ![![-2, -1, 1], ![-4, 3, -3], ![7, -9, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [28, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 66], [0, 1]]
 g := ![![[27, 40], [46, 64], [1], [17], [26], [1]], ![[4, 27], [36, 3], [1], [17], [26], [1]]]
 h' := ![![[48, 66], [52, 43], [37, 8], [47, 1], [56, 34], [39, 48], [0, 1]], ![[0, 1], [39, 24], [19, 59], [28, 66], [13, 33], [65, 19], [48, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [1, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [28, 19, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49900, 8702, 1679]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2098, -1499, 1679]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![3, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![3, 1, 0]] 
 ![![67, 0, 0], ![3, 1, 0], ![63, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![3, 1, 0], ![1, 3, 2], ![-428, 86, 4]]]
  hmulB := by decide  
  f := ![![![-359, -1080, -720], ![0, 24120, 0]], ![![-16, -48, -32], ![1, 1072, 0]], ![![-339, -1016, -677], ![32, 22680, 0]]]
  g := ![![![1, 0, 0], ![-3, 67, 0], ![-63, 0, 67]], ![![0, 1, 0], ![-2, 3, 2], ![-14, 86, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-80, -2, 1]] ![![67, 0, 0], ![3, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![201, 67, 0]], ![![-5360, -134, 67], ![-670, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![3, 1, 0]]], ![![![-80, -2, 1]], ![![-10, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-80, 37, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-80, 37, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![62, 37, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-80, 37, 1], ![-391, 6, 75], ![-16007, 3011, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -37, 71]], ![![-2, 0, 1], ![-71, -39, 75], ![-263, 20, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [52, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 70], [0, 1]]
 g := ![![[35, 2], [16, 37], [63, 29], [24], [37], [1]], ![[16, 69], [55, 34], [36, 42], [24], [37], [1]]]
 h' := ![![[26, 70], [20, 12], [61, 26], [31, 61], [70, 33], [19, 26], [0, 1]], ![[0, 1], [48, 59], [27, 45], [55, 10], [5, 38], [56, 45], [26, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [4, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [52, 45, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6140, -2964, 651]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-482, -381, 651]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-4, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-4, 1, 0]] 
 ![![71, 0, 0], ![67, 1, 0], ![28, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-4, 1, 0], ![1, -4, 2], ![-428, 86, -3]]]
  hmulB := by decide  
  f := ![![![-260, 1059, -530], ![71, 18815, 0]], ![![-245, 999, -500], ![72, 17750, 0]], ![![-100, 417, -209], ![73, 7420, 0]]]
  g := ![![![1, 0, 0], ![-67, 71, 0], ![-28, 0, 71]], ![![-1, 1, 0], ![3, -4, 2], ![-86, 86, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-80, 37, 1]] ![![71, 0, 0], ![-4, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-284, 71, 0]], ![![-5680, 2627, 71], ![-71, -142, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-4, 1, 0]]], ![![![-80, 37, 1]], ![![-1, -2, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-93, -31, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-93, -31, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![53, 42, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-93, -31, 1], ![-459, -7, -61], ![13097, -2837, -38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -42, 73]], ![![-2, -1, 1], ![38, 35, -61], ![207, -17, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [66, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 72], [0, 1]]
 g := ![![[46, 24], [12], [1], [53, 54], [24], [1]], ![[36, 49], [12], [1], [67, 19], [24], [1]]]
 h' := ![![[30, 72], [35, 30], [43, 42], [6, 1], [71, 45], [7, 30], [0, 1]], ![[0, 1], [59, 43], [62, 31], [36, 72], [34, 28], [31, 43], [30, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [9, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [66, 43, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6003, -2001, 1574]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1225, -933, 1574]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-12, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-12, 1, 0]] 
 ![![73, 0, 0], ![61, 1, 0], ![38, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-12, 1, 0], ![1, -12, 2], ![-428, 86, -11]]]
  hmulB := by decide  
  f := ![![![-389, 4966, -828], ![146, 30222, 0]], ![![-320, 4138, -690], ![147, 25185, 0]], ![![-202, 2585, -431], ![79, 15732, 0]]]
  g := ![![![1, 0, 0], ![-61, 73, 0], ![-38, 0, 73]], ![![-1, 1, 0], ![9, -12, 2], ![-72, 86, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-93, -31, 1]] ![![73, 0, 0], ![-12, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-876, 73, 0]], ![![-6789, -2263, 73], ![657, 365, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-12, 1, 0]]], ![![![-93, -31, 1]], ![![9, 5, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![116, -7, -2]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![116, -7, -2]] 
 ![![79, 0, 0], ![0, 79, 0], ![21, 43, 1]] where
  M :=![![![116, -7, -2], ![849, -56, -16], ![3338, -260, -63]]]
  hmulB := by decide  
  f := ![![![8, -1, 0]], ![![-1, 8, -2]], ![![7, 3, -1]]]
  g := ![![![2, 1, -2], ![15, 8, -16], ![59, 31, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [56, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 78], [0, 1]]
 g := ![![[36, 67], [46, 25], [74, 21], [63, 55], [22], [1]], ![[54, 12], [48, 54], [3, 58], [20, 24], [22], [1]]]
 h' := ![![[38, 78], [31, 64], [43, 74], [27, 10], [8, 56], [23, 38], [0, 1]], ![[0, 1], [14, 15], [11, 5], [12, 69], [3, 23], [45, 41], [38, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [53, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [56, 41, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4399, -4275, 1995]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-586, -1140, 1995]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-8, 1, 0]] 
 ![![79, 0, 0], ![71, 1, 0], ![8, 0, 1]] where
  M :=![![![-8, 1, 0], ![1, -8, 2], ![-428, 86, -7]]]
  hmulB := by decide  
  f := ![![![-116, 7, 2]], ![![-115, 7, 2]], ![![-54, 4, 1]]]
  g := ![![![-1, 1, 0], ![7, -8, 2], ![-82, 86, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![116, -7, -2]] ![![-8, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB211I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB211I1 : PrimesBelowBoundCertificateInterval O 31 79 211 where
  m := 11
  g := ![3, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB211I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![79507]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
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
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I53N0, I53N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [], [], [I53N0, I53N0, I53N1], [], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
