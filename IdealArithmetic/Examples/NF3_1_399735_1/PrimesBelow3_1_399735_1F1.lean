
import IdealArithmetic.Examples.NF3_1_399735_1.RI3_1_399735_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-63, -14, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-63, -14, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![11, 23, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-63, -14, 1], ![384, -1, -29], ![-5760, -910, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -23, 37]], ![![-2, -1, 1], ![19, 18, -29], ![-164, -42, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [19, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 36], [0, 1]]
 g := ![![[15, 21], [36], [33, 33], [10], [1]], ![[24, 16], [36], [26, 4], [10], [1]]]
 h' := ![![[11, 36], [23, 13], [2, 6], [23, 25], [18, 11], [0, 1]], ![[0, 1], [18, 24], [31, 31], [2, 12], [28, 26], [11, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [6, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [19, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1171, 2250, 611]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-150, -319, 611]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-8, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-8, 1, 0]] 
 ![![37, 0, 0], ![29, 1, 0], ![9, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-8, 1, 0], ![0, -7, 2], ![384, 76, -9]]]
  hmulB := by decide  
  f := ![![![145, -18, 0], ![666, 0, 0]], ![![121, -15, 0], ![556, 0, 0]], ![![37, -1, -1], ![170, 19, 0]]]
  g := ![![![1, 0, 0], ![-29, 37, 0], ![-9, 0, 37]], ![![-1, 1, 0], ![5, -7, 2], ![-47, 76, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-63, -14, 1]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![-2331, -518, 37], ![888, 111, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-8, 1, 0]]], ![![![-63, -14, 1]], ![![24, 3, -1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-54, -19, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-54, -19, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![28, 22, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-54, -19, 1], ![384, 3, -39], ![-7680, -1290, 42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -22, 41]], ![![-2, -1, 1], ![36, 21, -39], ![-216, -54, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [1, 11, 1] where
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
 g := ![![[11, 1], [9], [39], [3, 39], [1]], ![[0, 40], [9], [39], [25, 2], [1]]]
 h' := ![![[30, 40], [30, 40], [11, 38], [38, 11], [40, 30], [0, 1]], ![[0, 1], [0, 1], [3, 3], [40, 30], [38, 11], [30, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [36, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [1, 11, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3081, 3082, 1262]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-937, -602, 1262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-2, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-2, 1, 0]] 
 ![![41, 0, 0], ![39, 1, 0], ![40, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-2, 1, 0], ![0, -1, 2], ![384, 76, -3]]]
  hmulB := by decide  
  f := ![![![3, 19, -40], ![41, 820, 0]], ![![1, 19, -38], ![1, 779, 0]], ![![2, 19, -39], ![21, 800, 0]]]
  g := ![![![1, 0, 0], ![-39, 41, 0], ![-40, 0, 41]], ![![-1, 1, 0], ![-1, -1, 2], ![-60, 76, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-54, -19, 1]] ![![41, 0, 0], ![-2, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-82, 41, 0]], ![![-2214, -779, 41], ![492, 41, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-2, 1, 0]]], ![![![-54, -19, 1]], ![![12, 1, -1]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [7, 35, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 29, 36], [36, 13, 7], [0, 1]]
 g := ![![[36, 21, 14], [15, 34, 38], [18, 17], [9, 42, 1], []], ![[31, 5, 12, 9], [3, 39, 18, 23], [11, 25], [15, 7, 36, 21], [18, 6]], ![[5, 40, 25, 19], [29, 12, 8, 19], [6, 24], [20, 23, 22, 39], [4, 6]]]
 h' := ![![[6, 29, 36], [24, 9, 33], [16, 4, 9], [23, 36, 19], [0, 0, 1], [0, 1]], ![[36, 13, 7], [32, 18, 22], [4, 38, 3], [34, 5, 38], [39, 20, 13], [6, 29, 36]], ![[0, 1], [9, 16, 31], [5, 1, 31], [41, 2, 29], [21, 23, 29], [36, 13, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 38], []]
 b := ![[], [39, 18, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [7, 35, 1, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-216505, -52976, -32293]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5035, -1232, -751]
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


def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![2, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![2, 1, 0]] 
 ![![47, 0, 0], ![2, 1, 0], ![44, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![2, 1, 0], ![0, 3, 2], ![384, 76, 1]]]
  hmulB := by decide  
  f := ![![![45, 22, 0], ![-1034, 0, 0]], ![![-2, -1, 0], ![48, 0, 0]], ![![40, 18, -1], ![-918, 24, 0]]]
  g := ![![![1, 0, 0], ![-2, 47, 0], ![-44, 0, 47]], ![![0, 1, 0], ![-2, 3, 2], ![4, 76, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-4, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-4, 1, 0]] 
 ![![47, 0, 0], ![43, 1, 0], ![41, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-4, 1, 0], ![0, -3, 2], ![384, 76, -5]]]
  hmulB := by decide  
  f := ![![![57, -14, 0], ![658, 0, 0]], ![![53, -13, 0], ![612, 0, 0]], ![![55, -12, -1], ![636, 24, 0]]]
  g := ![![![1, 0, 0], ![-43, 47, 0], ![-41, 0, 47]], ![![-1, 1, 0], ![1, -3, 2], ![-57, 76, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![2, 1, 0]] ![![47, 0, 0], ![2, 1, 0]]
  ![![47, 0, 0], ![-45, -21, 1]] where
 M := ![![![2209, 0, 0], ![94, 47, 0]], ![![94, 47, 0], ![4, 5, 2]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![2, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-45, -21, 1]] ![![47, 0, 0], ![-4, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-188, 47, 0]], ![![-2115, -987, 47], ![564, 94, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-4, 1, 0]]], ![![![-45, -21, 1]], ![![12, 2, -1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [31, 16, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 4, 2], [11, 48, 51], [0, 1]]
 g := ![![[1, 28, 1], [20, 49], [50, 47, 28], [7, 29], [1]], ![[23, 52, 29, 41], [27, 24], [38, 26, 26, 45], [39, 13], [23, 34, 47, 8]], ![[2, 5, 46, 50], [43, 46], [4, 34, 30, 45], [2, 25], [42, 18, 47, 45]]]
 h' := ![![[22, 4, 2], [26, 29, 52], [40, 26, 7], [2, 34, 44], [22, 37, 33], [0, 1]], ![[11, 48, 51], [51, 47, 10], [27, 4, 17], [3, 45, 7], [24, 40, 15], [22, 4, 2]], ![[0, 1], [7, 30, 44], [42, 23, 29], [37, 27, 2], [29, 29, 5], [11, 48, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 45], []]
 b := ![[], [32, 52, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [31, 16, 20, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8158396, -3689330, -674001]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-153932, -69610, -12717]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![86422925, -3457034, -382658]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![86422925, -3457034, -382658]] 
 ![![59, 0, 0], ![19, 1, 0], ![46, 0, 1]] where
  M :=![![![86422925, -3457034, -382658], ![-146940672, 53883883, -6531410], ![-1180560384, -321663916, 60415293]]]
  hmulB := by decide  
  f := ![![![1154491661821159, 331944992789690, 43198405338954]], ![![652941173301023, 187736785141957, 24431547147128]], ![![2779411966522982, 799149890551544, 103999161452929]]]
  g := ![![![2876421, -3457034, -382658], ![-14750671, 53883883, -6531410], ![36473738, -321663916, 60415293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5342179171810643075037522313738505, -1536009037839735739540186320522514, -199891977472716145966536111719434]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-5342179171810643075037522313738505, -1536009037839735739540186320522514, -199891977472716145966536111719434]] 
 ![![59, 0, 0], ![49, 1, 0], ![14, 0, 1]] where
  M :=![![![-5342179171810643075037522313738505, -1536009037839735739540186320522514, -199891977472716145966536111719434], ![-76758519349523000051149866900262656, -22069978497576805908034453124938003, -2872126098206755333113836529325594], ![-513068951180935523932281680180382720, -147520051406618202683900721564503900, -19197852399370050574920616595612409]]]
  hmulB := by decide  
  f := ![![![-5482191713759662627, -249444485496516374, 94400254866826986]], ![![-3938605018734947561, -182711807096722549, 68344462078214620]], ![![-3538763801562019102, -134107871952459624, 56909762112171347]]]
  g := ![![![1232555107914481935694290050100623, -1536009037839735739540186320522514, -199891977472716145966536111719434], ![17709833769603984137392068603936573, -22069978497576805908034453124938003, -2872126098206755333113836529325594], ![118375991548043001959792242522353934, -147520051406618202683900721564503900, -19197852399370050574920616595612409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54782844527, -2503263604, 944915060]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-54782844527, -2503263604, 944915060]] 
 ![![59, 0, 0], ![50, 1, 0], ![23, 0, 1]] where
  M :=![![![-54782844527, -2503263604, 944915060], ![362847383040, 14527436429, -5951442268], ![-1324100606976, -44731114664, 20478878697]]]
  hmulB := by decide  
  f := ![![![-31290961901785635061, -8996927796330604148, -1170835355836893132]], ![![-34138116470010995182, -9815555365394073299, -1277369288621507996]], ![![-63134095269333129433, -18152618587044260220, -2362331689646514307]]]
  g := ![![![824530327, -2503263604, 944915060], ![-3841377394, 14527436429, -5951442268], ![7482049427, -44731114664, 20478878697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![86422925, -3457034, -382658]] ![![-5342179171810643075037522313738505, -1536009037839735739540186320522514, -199891977472716145966536111719434]]
  ![![-31290961901785635061, -8996927796330604148, -1170835355836893132]] where
 M := ![![![-31290961901785635061, -8996927796330604148, -1170835355836893132]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-31290961901785635061, -8996927796330604148, -1170835355836893132]] ![![-54782844527, -2503263604, 944915060]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1308270381474413045405755712519472655, 376160189550820583204976063717601444, 48952449030882975482382831660264858]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![1308270381474413045405755712519472655, 376160189550820583204976063717601444, 48952449030882975482382831660264858]] 
 ![![61, 0, 0], ![0, 61, 0], ![8, 55, 1]] where
  M :=![![![1308270381474413045405755712519472655, 376160189550820583204976063717601444, 48952449030882975482382831660264858], ![18797740427859062585235007357541705472, 5404816697372339765271826982417203307, 703367930070758190927569295774938030], ![125647772359656041365475801110017249024, 36126851556618342547865136918218497876, 4701448767301581574344257686642265277]]]
  hmulB := by decide  
  f := ![![![2825127795736869619, 434865697440396420, -94474603867458526]], ![![-36278247885104073984, -3920076400749581937, 964205998748251366]], ![![-29007146485452669064, -3174173318882333119, 776905749192070879]]]
  g := ![![![15027062118481135107322837036677931, -37970893559799066693870158649130586, 48952449030882975482382831660264858], ![215914704709721263242859885103970512, -545580646828186241569581709593514563, 703367930070758190927569295774938030], ![1443216101987596537224946551096379128, -3646767715491289246574902227001739219, 4701448767301581574344257686642265277]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [4, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 60], [0, 1]]
 g := ![![[53, 46], [12], [59, 16], [58, 45], [32, 1]], ![[0, 15], [12], [22, 45], [34, 16], [3, 60]]]
 h' := ![![[32, 60], [16, 30], [8, 16], [12, 4], [55, 44], [0, 1]], ![[0, 1], [0, 31], [32, 45], [18, 57], [60, 17], [32, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [1, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [4, 29, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1156, 2244, 602]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, -506, 602]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2825127795736869619, 434865697440396420, -94474603867458526]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![2825127795736869619, 434865697440396420, -94474603867458526]] 
 ![![61, 0, 0], ![13, 1, 0], ![31, 0, 1]] where
  M :=![![![2825127795736869619, 434865697440396420, -94474603867458526], ![-36278247885104073984, -3920076400749581937, 964205998748251366], ![203266675702216299264, 18500704009881514916, -4884282399497833303]]]
  hmulB := by decide  
  f := ![![![1308270381474413045405755712519472655, 376160189550820583204976063717601444, 48952449030882975482382831660264858]], ![![586971399787318560254259534758931967, 168768838713655858146500259192557739, 21963110942167817577025346022268544]], ![![2724658265333817143820561118001981989, 783406843158914436511793358909248240, 101950404709163177283575827346073375]]]
  g := ![![![1648958178736565, 434865697440396420, -94474603867458526], ![-249305584205824609, -3920076400749581937, 964205998748251366], ![1871643900953925209, 18500704009881514916, -4884282399497833303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![1308270381474413045405755712519472655, 376160189550820583204976063717601444, 48952449030882975482382831660264858]] ![![2825127795736869619, 434865697440396420, -94474603867458526]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [7, 46, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 22, 45], [27, 44, 22], [0, 1]]
 g := ![![[23, 36, 1], [44, 39, 64], [23, 9], [41, 39], [0, 1], []], ![[62, 1, 13, 7], [56, 29, 35, 5], [62, 9], [43, 36], [18, 60], [37, 15]], ![[60, 61, 59, 4], [20, 55, 20, 35], [36, 36], [50, 59], [58, 15], [60, 15]]]
 h' := ![![[40, 22, 45], [27, 49, 66], [66, 52, 59], [48, 52, 64], [0, 60, 21], [0, 0, 1], [0, 1]], ![[27, 44, 22], [43, 53, 17], [61, 46, 45], [48, 12, 64], [9, 65, 6], [1, 20, 44], [40, 22, 45]], ![[0, 1], [36, 32, 51], [3, 36, 30], [56, 3, 6], [2, 9, 40], [41, 47, 22], [27, 44, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 54], []]
 b := ![[], [42, 62, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [7, 46, 0, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1053125430, 378264044, 59996691]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15718290, 5645732, 895473]
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

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![667, -140, 14]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![667, -140, 14]] 
 ![![71, 0, 0], ![0, 71, 0], ![2, 61, 1]] where
  M :=![![![667, -140, 14], ![5376, 1591, -294], ![-59136, -8484, 1885]]]
  hmulB := by decide  
  f := ![![![7109, 2044, 266]], ![![102144, 29369, 3822]], ![![97574, 28055, 3651]]]
  g := ![![![9, -14, 14], ![84, 275, -294], ![-886, -1739, 1885]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [42, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 70], [0, 1]]
 g := ![![[55, 20], [60, 40], [60, 64], [64], [24], [1]], ![[5, 51], [31, 31], [42, 7], [64], [24], [1]]]
 h' := ![![[33, 70], [36, 34], [36, 18], [67, 8], [46, 8], [29, 33], [0, 1]], ![[0, 1], [22, 37], [62, 53], [47, 63], [26, 63], [53, 38], [33, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [19, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [42, 38, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1157, 534, 117]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, -93, 117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7109, -2044, -266]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-7109, -2044, -266]] 
 ![![71, 0, 0], ![21, 1, 0], ![53, 0, 1]] where
  M :=![![![-7109, -2044, -266], ![-102144, -29369, -3822], ![-682752, -196308, -25547]]]
  hmulB := by decide  
  f := ![![![-667, 140, -14]], ![![-273, 19, 0]], ![![335, 224, -37]]]
  g := ![![![703, -2044, -266], ![10101, -29369, -3822], ![67517, -196308, -25547]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![667, -140, 14]] ![![-7109, -2044, -266]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15326636133321053049217, -4406788103380493333676, -573487242970165773792]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-15326636133321053049217, -4406788103380493333676, -573487242970165773792]] 
 ![![73, 0, 0], ![0, 73, 0], ![32, 43, 1]] where
  M :=![![![-15326636133321053049217, -4406788103380493333676, -573487242970165773792], ![-220219101300543657136128, -63318454702434145191085, -8240088963790820893560], ![-1471987530397565782995456, -423232931274323022523344, -55078365738643324297525]]]
  hmulB := by decide  
  f := ![![![-1311047647945, -71479691076, 24344733120]], ![![9348377518080, 467672378099, -167304115272]], ![![4427809995232, 221084856473, -79179027445]]]
  g := ![![![41437748516770571399, 277440593758036095060, -573487242970165773792], ![595393774530994677504, 3986374941651659633315, -8240088963790820893560], ![3979728400534528692128, 26645709527223834551647, -55078365738643324297525]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [55, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 72], [0, 1]]
 g := ![![[10, 4], [23], [55], [13, 23], [61], [1]], ![[0, 69], [23], [55], [65, 50], [61], [1]]]
 h' := ![![[34, 72], [68, 71], [47, 60], [15, 37], [35, 13], [18, 34], [0, 1]], ![[0, 1], [0, 2], [43, 13], [32, 36], [39, 60], [6, 39], [34, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [3, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [55, 39, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1975, 6256, 2108]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-897, -1156, 2108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1311047647945, -71479691076, 24344733120]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-1311047647945, -71479691076, 24344733120]] 
 ![![73, 0, 0], ![61, 1, 0], ![7, 0, 1]] where
  M :=![![![-1311047647945, -71479691076, 24344733120], ![9348377518080, 467672378099, -167304115272], ![-36796578891264, -1683367621296, 634976493371]]]
  hmulB := by decide  
  f := ![![![-15326636133321053049217, -4406788103380493333676, -573487242970165773792]], ![![-15823889115522299906005, -4549760671351290938977, -592093298424259357464]], ![![-21633890182613878826575, -6220280109561458573412, -809490088211431297453]]]
  g := ![![![39435621587, -71479691076, 24344733120], ![-246691900535, 467672378099, -167304115272], ![841698774715, -1683367621296, 634976493371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-15326636133321053049217, -4406788103380493333676, -573487242970165773792]] ![![-1311047647945, -71479691076, 24344733120]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [32, 50, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 78, 20], [59, 0, 59], [0, 1]]
 g := ![![[18, 8, 72], [57, 71, 46], [45, 78, 32], [5, 38, 8], [36, 1], []], ![[49, 5, 51, 18], [50, 58, 62, 5], [0, 30, 74, 10], [6, 36, 58, 64], [], [61, 5]], ![[61, 71, 66, 7], [5, 59, 61, 48], [5, 74, 63, 59], [68, 11, 36, 78], [28, 1], [22, 5]]]
 h' := ![![[56, 78, 20], [72, 21, 25], [61, 77, 21], [77, 18, 36], [33, 64, 61], [0, 0, 1], [0, 1]], ![[59, 0, 59], [38, 37, 25], [7, 76, 39], [22, 75, 44], [1, 8, 16], [78, 75], [56, 78, 20]], ![[0, 1], [31, 21, 29], [37, 5, 19], [70, 65, 78], [38, 7, 2], [12, 4, 78], [59, 0, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 71], []]
 b := ![[], [27, 73, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [32, 50, 43, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30755016, -9837080, -1404304]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-389304, -124520, -17776]
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



lemma PB179I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB179I1 : PrimesBelowBoundCertificateInterval O 31 79 179 where
  m := 11
  g := ![2, 2, 1, 3, 1, 3, 2, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB179I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
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
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![300763]
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
  β := ![I37N1, I41N1, I47N0, I47N1, I59N0, I59N1, I59N2, I61N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [], [I47N0, I47N0, I47N1], [], [I59N0, I59N1, I59N2], [I61N1], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
