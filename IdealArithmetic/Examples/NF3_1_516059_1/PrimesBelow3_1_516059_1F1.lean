
import IdealArithmetic.Examples.NF3_1_516059_1.RI3_1_516059_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![5, -2, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![5, -2, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![5, 35, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![5, -2, 1], ![56, -15, -11], ![-46, 48, -24]]]
  hmulB := by decide  
  f := ![![![-4, 2, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -35, 37]], ![![0, -1, 1], ![3, 10, -11], ![2, 24, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [13, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 36], [0, 1]]
 g := ![![[10, 26], [36], [1, 1], [28], [1]], ![[34, 11], [36], [19, 36], [28], [1]]]
 h' := ![![[18, 36], [34, 27], [24, 31], [27, 36], [24, 18], [0, 1]], ![[0, 1], [2, 10], [27, 6], [9, 1], [15, 19], [18, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [27, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [13, 19, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1313, 570, -1358]
  a := ![3, 2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![219, 1300, -1358]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![11, 1, 0]] 
 ![![37, 0, 0], ![11, 1, 0], ![24, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![11, 1, 0], ![-3, 8, 7], ![50, -26, 14]]]
  hmulB := by decide  
  f := ![![![2428, -6927, -6048], ![555, 31968, 0]], ![![713, -2053, -1792], ![186, 9472, 0]], ![![1577, -4493, -3923], ![353, 20736, 0]]]
  g := ![![![1, 0, 0], ![-11, 37, 0], ![-24, 0, 37]], ![![0, 1, 0], ![-7, 8, 7], ![0, -26, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![5, -2, 1]] ![![37, 0, 0], ![11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![407, 37, 0]], ![![185, -74, 37], ![111, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![11, 1, 0]]], ![![![5, -2, 1]], ![![3, -1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [20, 6, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 35, 12], [12, 5, 29], [0, 1]]
 g := ![![[6, 37, 21], [19, 21], [15, 37], [14, 15, 1], []], ![[10, 38, 33, 26], [24, 36], [18, 23], [31, 36, 22, 13], [7, 21]], ![[12, 0, 12, 6], [6, 36], [20, 18], [31, 35, 17, 19], [31, 21]]]
 h' := ![![[3, 35, 12], [14, 26, 12], [36, 26, 29], [7, 26, 18], [0, 0, 1], [0, 1]], ![[12, 5, 29], [37, 18, 3], [5, 39, 6], [23, 23, 33], [33, 35, 5], [3, 35, 12]], ![[0, 1], [26, 38, 26], [33, 17, 6], [33, 33, 31], [16, 6, 35], [12, 5, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 24], []]
 b := ![[], [32, 13, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [20, 6, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2580991, -3431044, 2302355]
  a := ![-7, -9, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![62951, -83684, 56155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-3, -20, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-3, -20, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![40, 23, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-3, -20, 1], ![110, 31, -137], ![-946, 516, -86]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -23, 43]], ![![-1, -1, 1], ![130, 74, -137], ![58, 58, -86]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [2, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 42], [0, 1]]
 g := ![![[37, 41], [36, 25], [14], [3, 15], [1]], ![[13, 2], [35, 18], [14], [11, 28], [1]]]
 h' := ![![[12, 42], [14, 16], [8, 5], [37, 10], [41, 12], [0, 1]], ![[0, 1], [34, 27], [25, 38], [28, 33], [13, 31], [12, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [14, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [2, 31, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1426718, 1803216, -2692194]
  a := ![131, 132, -327]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2537546, 1481946, -2692194]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![8, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![8, 1, 0]] 
 ![![43, 0, 0], ![8, 1, 0], ![0, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![8, 1, 0], ![-3, 5, 7], ![50, -26, 11]]]
  hmulB := by decide  
  f := ![![![-7, -1, 0], ![43, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-3, -5, -6], ![30, 37, 0]]]
  g := ![![![1, 0, 0], ![-8, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![-1, 5, 7], ![6, -26, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-3, -20, 1]] ![![43, 0, 0], ![8, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![344, 43, 0]], ![![-129, -860, 43], ![86, -129, -129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![8, 1, 0]]], ![![![-3, -20, 1]], ![![2, -3, -3]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [7, 43, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 41, 17], [22, 5, 30], [0, 1]]
 g := ![![[9, 31, 4], [39, 31, 16], [40, 12, 14], [40, 6, 1], []], ![[37, 40, 38, 27], [5, 14, 29, 25], [39, 21, 40, 17], [29, 42, 22, 2], [26, 7]], ![[11, 5, 28, 22], [20, 11, 12, 23], [45, 29, 15, 31], [7, 23, 29, 46], [13, 7]]]
 h' := ![![[31, 41, 17], [9, 37, 2], [2, 33, 4], [2, 24, 22], [0, 0, 1], [0, 1]], ![[22, 5, 30], [35, 37, 28], [5, 38, 17], [24, 26, 1], [27, 12, 5], [31, 41, 17]], ![[0, 1], [11, 20, 17], [44, 23, 26], [11, 44, 24], [17, 35, 41], [22, 5, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 33], []]
 b := ![[], [23, 34, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [7, 43, 41, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1547804, 3376480, -2800448]
  a := ![7, 8, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32932, 71840, -59584]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-4, 6, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-4, 6, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![49, 6, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-4, 6, 1], ![32, -48, 45], ![354, -160, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -6, 53]], ![![-1, 0, 1], ![-41, -6, 45], ![15, -2, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [29, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 52], [0, 1]]
 g := ![![[17, 11], [15], [43, 13], [13], [37, 1]], ![[0, 42], [15], [47, 40], [13], [21, 52]]]
 h' := ![![[37, 52], [31, 45], [25, 11], [4, 38], [40, 15], [0, 1]], ![[0, 1], [0, 8], [8, 42], [32, 15], [12, 38], [37, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [12, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [29, 16, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1320, 564, -1337]
  a := ![3, 2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1261, 162, -1337]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![8, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![8, 1, 0]] 
 ![![53, 0, 0], ![8, 1, 0], ![9, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![8, 1, 0], ![-3, 5, 7], ![50, -26, 11]]]
  hmulB := by decide  
  f := ![![![1297, -2203, -3080], ![159, 23320, 0]], ![![190, -331, -462], ![54, 3498, 0]], ![![213, -375, -523], ![75, 3960, 0]]]
  g := ![![![1, 0, 0], ![-8, 53, 0], ![-9, 0, 53]], ![![0, 1, 0], ![-2, 5, 7], ![3, -26, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-4, 6, 1]] ![![53, 0, 0], ![8, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![424, 53, 0]], ![![-212, 318, 53], ![0, 0, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![8, 1, 0]]], ![![![-4, 6, 1]], ![![0, 0, 1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![20, -24, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![20, -24, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![20, 35, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![20, -24, 1], ![122, 66, -165], ![-1146, 620, -75]]]
  hmulB := by decide  
  f := ![![![-19, 24, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -35, 59]], ![![0, -1, 1], ![58, 99, -165], ![6, 55, -75]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [56, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 58], [0, 1]]
 g := ![![[25, 17], [25, 29], [9], [52, 57], [16, 1]], ![[2, 42], [17, 30], [9], [20, 2], [32, 58]]]
 h' := ![![[16, 58], [16, 31], [55, 18], [38, 3], [48, 23], [0, 1]], ![[0, 1], [40, 28], [48, 41], [27, 56], [3, 36], [16, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [30, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [56, 43, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23854, -9438, -536]
  a := ![-5, 14, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![586, 158, -536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-12, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-12, 1, 0]] 
 ![![59, 0, 0], ![47, 1, 0], ![16, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-12, 1, 0], ![-3, -15, 7], ![50, -26, -9]]]
  hmulB := by decide  
  f := ![![![325, 1620, -756], ![0, 6372, 0]], ![![259, 1290, -602], ![1, 5074, 0]], ![![92, 439, -205], ![19, 1728, 0]]]
  g := ![![![1, 0, 0], ![-47, 59, 0], ![-16, 0, 59]], ![![-1, 1, 0], ![10, -15, 7], ![24, -26, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![20, -24, 1]] ![![59, 0, 0], ![-12, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-708, 59, 0]], ![![1180, -1416, 59], ![-118, 354, -177]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-12, 1, 0]]], ![![![20, -24, 1]], ![![-2, 6, -3]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [25, 32, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 4, 9], [2, 56, 52], [0, 1]]
 g := ![![[15, 42, 19], [20, 57], [60, 49, 34], [47, 44, 49], [1]], ![[29, 0, 51, 48], [49, 58], [14, 40, 32, 4], [46, 19, 13, 58], [32, 52, 17, 58]], ![[18, 57, 19, 4], [24, 22], [20, 40, 39, 60], [37, 42, 7, 14], [50, 10, 45, 3]]]
 h' := ![![[52, 4, 9], [3, 7, 43], [25, 39, 39], [45, 34, 41], [36, 29, 54], [0, 1]], ![[2, 56, 52], [29, 9, 31], [20, 4, 34], [48, 20, 40], [57, 51, 52], [52, 4, 9]], ![[0, 1], [15, 45, 48], [26, 18, 49], [43, 7, 41], [39, 42, 16], [2, 56, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 55], []]
 b := ![[], [44, 10, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [25, 32, 7, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1826523, 1845128, -1001132]
  a := ![5, 8, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29943, 30248, -16412]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![44, 9, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![44, 9, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![44, 9, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![44, 9, 1], ![23, -9, 66], ![504, -238, 48]]]
  hmulB := by decide  
  f := ![![![-43, -9, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -9, 67]], ![![0, 0, 1], ![-43, -9, 66], ![-24, -10, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [21, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 66], [0, 1]]
 g := ![![[24, 16], [38, 62], [56], [1], [19], [1]], ![[0, 51], [12, 5], [56], [1], [19], [1]]]
 h' := ![![[32, 66], [6, 4], [31, 14], [1, 49], [42, 1], [46, 32], [0, 1]], ![[0, 1], [0, 63], [10, 53], [28, 18], [7, 66], [65, 35], [32, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [16, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [21, 35, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3356, 2666, -4431]
  a := ![-6, -5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2960, 635, -4431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![1, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![1, 1, 0]] 
 ![![67, 0, 0], ![1, 1, 0], ![19, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![1, 1, 0], ![-3, -2, 7], ![50, -26, 4]]]
  hmulB := by decide  
  f := ![![![-2, -2, 7], ![0, -67, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, 2], ![29, -19, 0]]]
  g := ![![![1, 0, 0], ![-1, 67, 0], ![-19, 0, 67]], ![![0, 1, 0], ![-2, -2, 7], ![0, -26, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![44, 9, 1]] ![![67, 0, 0], ![1, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![67, 67, 0]], ![![2948, 603, 67], ![67, 0, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![1, 1, 0]]], ![![![44, 9, 1]], ![![1, 0, 1]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [31, 8, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 13, 2], [14, 57, 69], [0, 1]]
 g := ![![[47, 69, 40], [28, 65, 8], [54, 63, 3], [60, 8], [48, 1], []], ![[38, 16, 51, 4], [20, 65, 68, 24], [20, 60, 19, 4], [27, 48], [42, 54], [31, 4]], ![[32, 66, 65, 46], [10, 23, 46, 51], [46, 48, 3, 56], [33, 36], [54, 27], [35, 4]]]
 h' := ![![[34, 13, 2], [55, 10, 53], [30, 54, 24], [66, 48, 28], [3, 11, 24], [0, 0, 1], [0, 1]], ![[14, 57, 69], [9, 2, 59], [14, 68, 56], [58, 50, 59], [16, 6, 41], [53, 15, 57], [34, 13, 2]], ![[0, 1], [9, 59, 30], [40, 20, 62], [57, 44, 55], [50, 54, 6], [34, 56, 13], [14, 57, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 9], []]
 b := ![[], [60, 48, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [31, 8, 23, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![294011, 9384780, -10266600]
  a := ![10, 10, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4141, 132180, -144600]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![43, 36, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![43, 36, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![43, 36, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![43, 36, 1], ![-58, -91, 255], ![1854, -940, 128]]]
  hmulB := by decide  
  f := ![![![-42, -36, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -36, 73]], ![![0, 0, 1], ![-151, -127, 255], ![-50, -76, 128]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [7, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 72], [0, 1]]
 g := ![![[48, 36], [23], [25], [27, 61], [38], [1]], ![[70, 37], [23], [25], [44, 12], [38], [1]]]
 h' := ![![[29, 72], [10, 67], [68, 60], [30, 68], [2, 39], [66, 29], [0, 1]], ![[0, 1], [55, 6], [56, 13], [31, 5], [38, 34], [31, 44], [29, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [54, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [7, 44, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18429, 20976, -12752]
  a := ![-10, -20, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7259, 6576, -12752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-36, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-36, 1, 0]] 
 ![![73, 0, 0], ![37, 1, 0], ![18, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-36, 1, 0], ![-3, -39, 7], ![50, -26, -33]]]
  hmulB := by decide  
  f := ![![![187, 2418, -434], ![0, 4526, 0]], ![![94, 1209, -217], ![1, 2263, 0]], ![![54, 596, -107], ![16, 1116, 0]]]
  g := ![![![1, 0, 0], ![-37, 73, 0], ![-18, 0, 73]], ![![-1, 1, 0], ![18, -39, 7], ![22, -26, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![43, 36, 1]] ![![73, 0, 0], ![-36, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2628, 73, 0]], ![![3139, 2628, 73], ![-1606, -1387, 219]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-36, 1, 0]]], ![![![43, 36, 1]], ![![-22, -19, 3]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![28, 30, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![28, 30, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![28, 30, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![28, 30, 1], ![-40, -88, 213], ![1554, -784, 95]]]
  hmulB := by decide  
  f := ![![![-27, -30, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -30, 79]], ![![0, 0, 1], ![-76, -82, 213], ![-14, -46, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [29, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 78], [0, 1]]
 g := ![![[52, 4], [32, 31], [6, 22], [20, 19], [49], [1]], ![[24, 75], [52, 48], [10, 57], [45, 60], [49], [1]]]
 h' := ![![[72, 78], [20, 2], [63, 49], [52, 38], [52, 63], [50, 72], [0, 1]], ![[0, 1], [6, 77], [36, 30], [23, 41], [6, 16], [20, 7], [72, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [6, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [29, 7, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61903, 90414, -129564]
  a := ![-29, -30, 72]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46705, 50346, -129564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![24, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![24, 1, 0]] 
 ![![79, 0, 0], ![24, 1, 0], ![63, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![24, 1, 0], ![-3, 21, 7], ![50, -26, 27]]]
  hmulB := by decide  
  f := ![![![4417, -32940, -10976], ![948, 123872, 0]], ![![1332, -10000, -3332], ![317, 37604, 0]], ![![3513, -26269, -8753], ![787, 98784, 0]]]
  g := ![![![1, 0, 0], ![-24, 79, 0], ![-63, 0, 79]], ![![0, 1, 0], ![-12, 21, 7], ![-13, -26, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![28, 30, 1]] ![![79, 0, 0], ![24, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1896, 79, 0]], ![![2212, 2370, 79], ![632, 632, 237]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![24, 1, 0]]], ![![![28, 30, 1]], ![![8, 8, 3]]]]
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


lemma PB204I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB204I1 : PrimesBelowBoundCertificateInterval O 31 79 204 where
  m := 11
  g := ![2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB204I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I53N1, I59N1, I67N1, I73N1, I79N1]
  Il := ![[I37N1], [], [I43N1], [], [I53N1], [I59N1], [], [I67N1], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
