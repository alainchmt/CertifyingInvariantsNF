
import IdealArithmetic.Examples.NF3_1_117288_3.RI3_1_117288_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![8, 17, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![8, 17, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![8, 17, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![8, 17, 1], ![62, -7, 17], ![1054, -193, -7]]]
  hmulB := by decide  
  f := ![![![-7, -17, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -17, 37]], ![![0, 0, 1], ![-2, -8, 17], ![30, -2, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [10, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 36], [0, 1]]
 g := ![![[33, 26], [7], [17, 16], [9], [1]], ![[0, 11], [7], [28, 21], [9], [1]]]
 h' := ![![[3, 36], [7, 10], [15, 28], [10, 4], [27, 3], [0, 1]], ![[0, 1], [0, 27], [25, 9], [22, 33], [36, 34], [3, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [19, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [10, 34, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![134, -2, -48]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 22, -48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-17, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-17, 1, 0]] 
 ![![37, 0, 0], ![20, 1, 0], ![7, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-17, 1, 0], ![0, -17, 1], ![62, -15, -17]]]
  hmulB := by decide  
  f := ![![![545, -32, 0], ![1184, 0, 0]], ![![290, -17, 0], ![630, 0, 0]], ![![127, -7, 0], ![276, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 37, 0], ![-7, 0, 37]], ![![-1, 1, 0], ![9, -17, 1], ![13, -15, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![8, 17, 1]] ![![37, 0, 0], ![-17, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-629, 37, 0]], ![![296, 629, 37], ![-74, -296, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-17, 1, 0]]], ![![![8, 17, 1]], ![![-2, -8, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, -11, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![13, -11, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![13, 30, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, -11, 1], ![62, -2, -11], ![-682, 227, -2]]]
  hmulB := by decide  
  f := ![![![-12, 11, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -30, 41]], ![![0, -1, 1], ![5, 8, -11], ![-16, 7, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40], [0, 1]]
 g := ![![[13, 21], [33], [9], [35, 20], [1]], ![[0, 20], [33], [9], [7, 21], [1]]]
 h' := ![![[15, 40], [25, 12], [3, 22], [12, 38], [39, 15], [0, 1]], ![[0, 1], [0, 29], [5, 19], [8, 3], [18, 26], [15, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [32, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-767, 690, -59]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, 60, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![11, 1, 0]] 
 ![![41, 0, 0], ![11, 1, 0], ![2, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![11, 1, 0], ![0, 11, 1], ![62, -15, 11]]]
  hmulB := by decide  
  f := ![![![122, 11, 0], ![-451, 0, 0]], ![![22, 2, 0], ![-81, 0, 0]], ![![-8, -1, 0], ![30, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 41, 0], ![-2, 0, 41]], ![![0, 1, 0], ![-3, 11, 1], ![5, -15, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![13, -11, 1]] ![![41, 0, 0], ![11, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![451, 41, 0]], ![![533, -451, 41], ![205, -123, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![11, 1, 0]]], ![![![13, -11, 1]], ![![5, -3, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [3, 16, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 35, 36], [22, 7, 7], [0, 1]]
 g := ![![[4, 30, 17], [8, 42, 6], [5, 35], [41, 10, 1], []], ![[15, 38, 11, 38], [19, 30, 11, 16], [28, 25], [21, 21, 24, 1], [0, 6]], ![[21, 35, 10, 7], [3, 2, 19, 34], [14, 41], [8, 0, 35, 18], [29, 6]]]
 h' := ![![[31, 35, 36], [19, 15, 24], [21, 11, 7], [6, 2, 32], [0, 0, 1], [0, 1]], ![[22, 7, 7], [27, 14, 20], [37, 12, 15], [32, 5, 38], [15, 2, 7], [31, 35, 36]], ![[0, 1], [30, 14, 42], [32, 20, 21], [26, 36, 16], [10, 41, 35], [22, 7, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 34], []]
 b := ![[], [28, 25, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [3, 16, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-114853, -4214, -5848]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2671, -98, -136]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [30, 8, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 15, 40], [45, 31, 7], [0, 1]]
 g := ![![[36, 45, 3], [13, 11, 7], [33, 15, 37], [40, 46, 1], []], ![[4, 24, 31, 35], [18, 39, 41, 19], [7, 33, 37, 38], [38, 31, 43, 41], [23, 2]], ![[12, 26, 38, 17], [3, 8, 26, 24], [45, 4, 22, 7], [21, 43, 3, 24], [9, 2]]]
 h' := ![![[1, 15, 40], [33, 45, 35], [44, 5, 30], [22, 39, 32], [0, 0, 1], [0, 1]], ![[45, 31, 7], [27, 0, 18], [12, 0, 2], [9, 35, 14], [16, 21, 31], [1, 15, 40]], ![[0, 1], [33, 2, 41], [44, 42, 15], [33, 20, 1], [16, 26, 15], [45, 31, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 1], []]
 b := ![[], [23, 33, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [30, 8, 1, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-130284, 58327, -4841]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2772, 1241, -103]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [13, 1, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12, 7], [27, 40, 46], [0, 1]]
 g := ![![[12, 6, 11], [11, 40], [11, 41, 29], [16, 52], [1]], ![[20, 16, 15, 40], [39, 6], [30, 34, 8, 25], [23, 40], [16, 49, 23, 25]], ![[35, 26, 21, 6], [1, 11], [20, 20, 24, 38], [13, 16], [7, 9, 42, 28]]]
 h' := ![![[3, 12, 7], [7, 46, 8], [16, 23, 26], [14, 23, 20], [40, 52, 30], [0, 1]], ![[27, 40, 46], [48, 47, 6], [48, 26, 35], [26, 47, 7], [31, 42, 27], [3, 12, 7]], ![[0, 1], [50, 13, 39], [13, 4, 45], [49, 36, 26], [35, 12, 49], [27, 40, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 32], []]
 b := ![[], [22, 12, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [13, 1, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1749, 1749, -689]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33, 33, -13]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [23, 43, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 7, 27], [42, 51, 32], [0, 1]]
 g := ![![[3, 29, 5], [10, 10, 27], [11, 28], [56, 44, 21], [1]], ![[45, 33, 18, 48], [48, 58, 8, 16], [24, 22], [48, 12, 5, 27], [57, 21, 0, 36]], ![[17, 28, 6, 8], [30, 40, 20, 2], [3, 15], [0, 23, 45, 13], [28, 3, 55, 23]]]
 h' := ![![[49, 7, 27], [6, 34, 51], [24, 4, 26], [10, 0, 38], [36, 16, 32], [0, 1]], ![[42, 51, 32], [21, 32, 38], [25, 19, 18], [20, 5, 50], [49, 51, 58], [49, 7, 27]], ![[0, 1], [6, 52, 29], [54, 36, 15], [8, 54, 30], [48, 51, 28], [42, 51, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 9], []]
 b := ![[], [11, 46, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [23, 43, 27, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![446866, -38114, -2006]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7574, -646, -34]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![21, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![21, 1, 0]] 
 ![![61, 0, 0], ![21, 1, 0], ![47, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![21, 1, 0], ![0, 21, 1], ![62, -15, 21]]]
  hmulB := by decide  
  f := ![![![421, 20, 0], ![-1220, 0, 0]], ![![147, 7, 0], ![-426, 0, 0]], ![![323, 15, 0], ![-936, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 61, 0], ![-47, 0, 61]], ![![0, 1, 0], ![-8, 21, 1], ![-10, -15, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-15, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-15, 1, 0]] 
 ![![61, 0, 0], ![46, 1, 0], ![19, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-15, 1, 0], ![0, -15, 1], ![62, -15, -15]]]
  hmulB := by decide  
  f := ![![![886, -59, 0], ![3599, 0, 0]], ![![676, -45, 0], ![2746, 0, 0]], ![![304, -20, 0], ![1235, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 61, 0], ![-19, 0, 61]], ![![-1, 1, 0], ![11, -15, 1], ![17, -15, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-6, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-6, 1, 0]] 
 ![![61, 0, 0], ![55, 1, 0], ![25, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-6, 1, 0], ![0, -6, 1], ![62, -15, -6]]]
  hmulB := by decide  
  f := ![![![319, -53, 0], ![3233, 0, 0]], ![![289, -48, 0], ![2929, 0, 0]], ![![139, -23, 0], ![1409, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 61, 0], ![-25, 0, 61]], ![![-1, 1, 0], ![5, -6, 1], ![17, -15, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![21, 1, 0]] ![![61, 0, 0], ![-15, 1, 0]]
  ![![61, 0, 0], ![-10, 6, 1]] where
 M := ![![![3721, 0, 0], ![-915, 61, 0]], ![![1281, 61, 0], ![-315, 6, 1]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![-5, -5, -1], ![61, 0, 0]]], ![![![21, 1, 0], ![0, 0, 0]], ![![-5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-10, 6, 1]] ![![61, 0, 0], ![-6, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-366, 61, 0]], ![![-610, 366, 61], ![122, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-6, 1, 0]]], ![![![-10, 6, 1]], ![![2, -1, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![3, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![3, 1, 0]] 
 ![![67, 0, 0], ![3, 1, 0], ![58, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![3, 1, 0], ![0, 3, 1], ![62, -15, 3]]]
  hmulB := by decide  
  f := ![![![124, 41, 0], ![-2747, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![106, 35, 0], ![-2348, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 67, 0], ![-58, 0, 67]], ![![0, 1, 0], ![-1, 3, 1], ![-1, -15, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![18, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![18, 1, 0]] 
 ![![67, 0, 0], ![18, 1, 0], ![11, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![18, 1, 0], ![0, 18, 1], ![62, -15, 18]]]
  hmulB := by decide  
  f := ![![![487, 27, 0], ![-1809, 0, 0]], ![![126, 7, 0], ![-468, 0, 0]], ![![59, 3, 0], ![-219, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 67, 0], ![-11, 0, 67]], ![![0, 1, 0], ![-5, 18, 1], ![2, -15, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-21, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-21, 1, 0]] 
 ![![67, 0, 0], ![46, 1, 0], ![28, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-21, 1, 0], ![0, -21, 1], ![62, -15, -21]]]
  hmulB := by decide  
  f := ![![![505, -24, 0], ![1608, 0, 0]], ![![358, -17, 0], ![1140, 0, 0]], ![![238, -11, 0], ![758, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 67, 0], ![-28, 0, 67]], ![![-1, 1, 0], ![14, -21, 1], ![20, -15, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![3, 1, 0]] ![![67, 0, 0], ![18, 1, 0]]
  ![![67, 0, 0], ![-13, 21, 1]] where
 M := ![![![4489, 0, 0], ![1206, 67, 0]], ![![201, 67, 0], ![54, 21, 1]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![18, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-13, 21, 1]] ![![67, 0, 0], ![-21, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1407, 67, 0]], ![![-871, 1407, 67], ![335, -469, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-21, 1, 0]]], ![![![-13, 21, 1]], ![![5, -7, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -2, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![5, -2, 0]] 
 ![![71, 0, 0], ![33, 1, 0], ![47, 0, 1]] where
  M :=![![![5, -2, 0], ![0, 5, -2], ![-124, 30, 5]]]
  hmulB := by decide  
  f := ![![![-85, -10, -4]], ![![-43, -5, -2]], ![![-65, -8, -3]]]
  g := ![![![1, -2, 0], ![-1, 5, -2], ![-19, 30, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-21, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-21, 1, 0]] 
 ![![71, 0, 0], ![50, 1, 0], ![56, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-21, 1, 0], ![0, -21, 1], ![62, -15, -21]]]
  hmulB := by decide  
  f := ![![![1135, -54, 0], ![3834, 0, 0]], ![![820, -39, 0], ![2770, 0, 0]], ![![910, -43, 0], ![3074, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 71, 0], ![-56, 0, 71]], ![![-1, 1, 0], ![14, -21, 1], ![28, -15, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-12, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-12, 1, 0]] 
 ![![71, 0, 0], ![59, 1, 0], ![69, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-12, 1, 0], ![0, -12, 1], ![62, -15, -12]]]
  hmulB := by decide  
  f := ![![![97, -8, 0], ![568, 0, 0]], ![![85, -7, 0], ![498, 0, 0]], ![![99, -8, 0], ![580, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 71, 0], ![-69, 0, 71]], ![![-1, 1, 0], ![9, -12, 1], ![25, -15, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![5, -2, 0]] ![![71, 0, 0], ![-21, 1, 0]]
  ![![71, 0, 0], ![17, 12, 1]] where
 M := ![![![355, -142, 0], ![-105, 47, -2]]]
 hmul := by decide  
 g := ![![![![-12, -14, -1], ![71, 0, 0]], ![![-18, -11, -1], ![69, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![17, 12, 1]] ![![71, 0, 0], ![-12, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-852, 71, 0]], ![![1207, 852, 71], ![-142, -142, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-12, 1, 0]]], ![![![17, 12, 1]], ![![-2, -2, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [50, 58, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 18, 19], [23, 54, 54], [0, 1]]
 g := ![![[70, 38, 25], [71, 8], [63, 54], [43, 48, 50], [27, 1], []], ![[33, 2, 14, 46], [50, 54], [34, 32], [45, 49, 33, 24], [67, 69], [65, 69]], ![[67, 55, 33, 16], [48, 69], [16, 72], [19, 27, 39, 61], [27, 32], [30, 69]]]
 h' := ![![[4, 18, 19], [24, 71, 68], [56, 69, 9], [40, 52, 28], [37, 63, 14], [0, 0, 1], [0, 1]], ![[23, 54, 54], [53, 12, 57], [61, 46, 45], [70, 54, 18], [54, 36, 55], [51, 5, 54], [4, 18, 19]], ![[0, 1], [15, 63, 21], [58, 31, 19], [36, 40, 27], [10, 47, 4], [51, 68, 18], [23, 54, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 8], []]
 b := ![[], [52, 23, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [50, 58, 46, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26499, 8249, 511]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-363, 113, 7]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-18, -21, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-18, -21, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![61, 58, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-18, -21, 1], ![62, -33, -21], ![-1302, 377, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -58, 79]], ![![-1, -1, 1], ![17, 15, -21], ![9, 29, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [48, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 78], [0, 1]]
 g := ![![[34, 8], [45, 23], [20, 26], [36, 18], [18], [1]], ![[13, 71], [34, 56], [11, 53], [48, 61], [18], [1]]]
 h' := ![![[27, 78], [52, 18], [67, 24], [10, 37], [18, 27], [31, 27], [0, 1]], ![[0, 1], [64, 61], [4, 55], [61, 42], [36, 52], [49, 52], [27, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [23, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [48, 52, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![296, 240, 45]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31, -30, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![21, 1, 0]] 
 ![![79, 0, 0], ![21, 1, 0], ![33, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![21, 1, 0], ![0, 21, 1], ![62, -15, 21]]]
  hmulB := by decide  
  f := ![![![799, 38, 0], ![-3002, 0, 0]], ![![189, 9, 0], ![-710, 0, 0]], ![![321, 15, 0], ![-1206, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 79, 0], ![-33, 0, 79]], ![![0, 1, 0], ![-6, 21, 1], ![-4, -15, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-18, -21, 1]] ![![79, 0, 0], ![21, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1659, 79, 0]], ![![-1422, -1659, 79], ![-316, -474, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![21, 1, 0]]], ![![![-18, -21, 1]], ![![-4, -6, 0]]]]
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


lemma PB97I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB97I1 : PrimesBelowBoundCertificateInterval O 31 79 97 where
  m := 11
  g := ![2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB97I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![148877]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
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
      exact NI37N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I79N1]
  Il := ![[I37N1], [I41N1], [], [], [], [], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
