
import IdealArithmetic.Examples.NF3_1_387731_1.RI3_1_387731_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![25, 3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![25, 3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![25, 3, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![25, 3, 1], ![4, -1, 12], ![11, -86, -4]]]
  hmulB := by decide  
  f := ![![![-24, -3, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -3, 37]], ![![0, 0, 1], ![-8, -1, 12], ![3, -2, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [32, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 36], [0, 1]]
 g := ![![[6, 36], [27], [23, 36], [12], [1]], ![[13, 1], [27], [30, 1], [12], [1]]]
 h' := ![![[30, 36], [3, 6], [4, 29], [11, 31], [5, 30], [0, 1]], ![[0, 1], [35, 31], [23, 8], [16, 6], [17, 7], [30, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [31, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [32, 7, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95, -773, -1454]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![985, 97, -1454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, 1, 0]] 
 ![![37, 0, 0], ![25, 1, 0], ![4, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, 1, 0], ![0, -11, 4], ![4, -29, -12]]]
  hmulB := by decide  
  f := ![![![433, -36, 0], ![1332, 0, 0]], ![![301, -25, 0], ![926, 0, 0]], ![![52, 4, -3], ![160, 28, 0]]]
  g := ![![![1, 0, 0], ![-25, 37, 0], ![-4, 0, 37]], ![![-1, 1, 0], ![7, -11, 4], ![21, -29, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![25, 3, 1]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-444, 37, 0]], ![![925, 111, 37], ![-296, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-12, 1, 0]]], ![![![25, 3, 1]], ![![-8, -1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![27, -3, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![27, -3, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![27, 38, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![27, -3, 1], ![4, -5, -12], ![-13, 88, -2]]]
  hmulB := by decide  
  f := ![![![-26, 3, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -38, 41]], ![![0, -1, 1], ![8, 11, -12], ![1, 4, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [40, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 40], [0, 1]]
 g := ![![[3, 40], [23], [32], [33, 9], [1]], ![[0, 1], [23], [32], [19, 32], [1]]]
 h' := ![![[3, 40], [14, 9], [14, 33], [33, 27], [1, 3], [0, 1]], ![[0, 1], [0, 32], [31, 8], [32, 14], [10, 38], [3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [16, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [40, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15, -275, -824]
  a := ![-1, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![543, 757, -824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![2, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![0, 13, 4], ![4, -29, 12]]]
  hmulB := by decide  
  f := ![![![193, 16, 0], ![-656, 0, 0]], ![![60, 5, 0], ![-204, 0, 0]], ![![10, -9, -3], ![-34, 31, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-2, 0, 41]], ![![0, 1, 0], ![-4, 13, 4], ![8, -29, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![27, -3, 1]] ![![41, 0, 0], ![12, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![492, 41, 0]], ![![1107, -123, 41], ![328, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![12, 1, 0]]], ![![![27, -3, 1]], ![![8, -1, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5881, 7, 203]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![5881, 7, 203]] 
 ![![43, 0, 0], ![24, 1, 0], ![22, 0, 1]] where
  M :=![![![5881, 7, 203], ![812, 1, 28], ![-175, 0, -6]]]
  hmulB := by decide  
  f := ![![![-6, 42, -7]], ![![-4, 29, 0]], ![![1, -7, 1]]]
  g := ![![![29, 7, 203], ![4, 1, 28], ![-1, 0, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -427, -133]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![55, -427, -133]] 
 ![![43, 0, 0], ![37, 1, 0], ![14, 0, 1]] where
  M :=![![![55, -427, -133], ![-532, 3485, -1708], ![-1575, 12250, 3912]]]
  hmulB := by decide  
  f := ![![![-34556320, -41174, -1192821]], ![![-29845468, -35561, -1030211]], ![![-11226985, -13377, -387535]]]
  g := ![![![412, -427, -133], ![-2455, 3485, -1708], ![-11851, 12250, 3912]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![5881, 7, 203]] ![![5881, 7, 203]]
  ![![34556320, 41174, 1192821]] where
 M := ![![![34556320, 41174, 1192821]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![34556320, 41174, 1192821]] ![![55, -427, -133]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, 16, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, 16, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![3, 16, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, 16, 1], ![4, -10, 64], ![63, -463, -26]]]
  hmulB := by decide  
  f := ![![![-2, -16, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -16, 47]], ![![0, 0, 1], ![-4, -22, 64], ![3, -1, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [37, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[28, 14], [5, 28], [25, 1], [46, 4], [1]], ![[0, 33], [43, 19], [23, 46], [38, 43], [1]]]
 h' := ![![[45, 46], [3, 25], [15, 13], [37, 1], [10, 45], [0, 1]], ![[0, 1], [0, 22], [36, 34], [35, 46], [14, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [32, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [37, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4004, 1, 97]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![79, -33, 97]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-17, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-17, 1, 0]] 
 ![![47, 0, 0], ![30, 1, 0], ![26, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-17, 1, 0], ![0, -16, 4], ![4, -29, -17]]]
  hmulB := by decide  
  f := ![![![18, 527, -132], ![47, 1551, 0]], ![![18, 335, -84], ![48, 987, 0]], ![![19, 291, -73], ![51, 858, 0]]]
  g := ![![![1, 0, 0], ![-30, 47, 0], ![-26, 0, 47]], ![![-1, 1, 0], ![8, -16, 4], ![28, -29, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![3, 16, 1]] ![![47, 0, 0], ![-17, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-799, 47, 0]], ![![141, 752, 47], ![-47, -282, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-17, 1, 0]]], ![![![3, 16, 1]], ![![-1, -6, 1]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [13, 18, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 46, 24], [45, 6, 29], [0, 1]]
 g := ![![[4, 23, 16], [4, 24], [36, 8, 16], [15, 49], [1]], ![[30, 52, 5, 17], [25, 40], [13, 12, 20, 28], [13, 9], [51, 26, 51, 44]], ![[26, 25, 33, 17], [28, 28], [42, 50, 42, 7], [19, 16], [15, 9, 23, 9]]]
 h' := ![![[1, 46, 24], [29, 50, 4], [9, 30, 17], [27, 38, 49], [40, 35, 46], [0, 1]], ![[45, 6, 29], [8, 5, 5], [42, 40, 27], [30, 15, 40], [27, 48, 3], [1, 46, 24]], ![[0, 1], [17, 51, 44], [40, 36, 9], [24, 0, 17], [35, 23, 4], [45, 6, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 9], []]
 b := ![[], [34, 5, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [13, 18, 7, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32860, -372484, -625453]
  a := ![1, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![620, -7028, -11801]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![18, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![18, 1, 0]] 
 ![![59, 0, 0], ![18, 1, 0], ![3, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![18, 1, 0], ![0, 19, 4], ![4, -29, 18]]]
  hmulB := by decide  
  f := ![![![271, 15, 0], ![-885, 0, 0]], ![![90, 5, 0], ![-294, 0, 0]], ![![15, -4, -1], ![-49, 15, 0]]]
  g := ![![![1, 0, 0], ![-18, 59, 0], ![-3, 0, 59]], ![![0, 1, 0], ![-6, 19, 4], ![8, -29, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1805281, 2151, 62315]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1805281, 2151, 62315]] 
 ![![59, 0, 0], ![19, 1, 0], ![23, 0, 1]] where
  M :=![![![1805281, 2151, 62315], ![249260, 297, 8604], ![-53711, -64, -1854]]]
  hmulB := by decide  
  f := ![![![18, -206, -351]], ![![-18, 103, -127]], ![![-1, 15, 36]]]
  g := ![![![5613, 2151, 62315], ![775, 297, 8604], ![-167, -64, -1854]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![21, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![21, 1, 0]] 
 ![![59, 0, 0], ![21, 1, 0], ![32, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![21, 1, 0], ![0, 22, 4], ![4, -29, 21]]]
  hmulB := by decide  
  f := ![![![400, 19, 0], ![-1121, 0, 0]], ![![126, 6, 0], ![-353, 0, 0]], ![![202, 4, -1], ![-566, 15, 0]]]
  g := ![![![1, 0, 0], ![-21, 59, 0], ![-32, 0, 59]], ![![0, 1, 0], ![-10, 22, 4], ![-1, -29, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![18, 1, 0]] ![![1805281, 2151, 62315]]
  ![![59, 0, 0], ![-3, -20, 1]] where
 M := ![![![106511579, 126909, 3676585]], ![![32744318, 39015, 1130274]]]
 hmul := by decide  
 g := ![![![![1801123, -25569, 63701], ![-81774, 0, 0]]], ![![![553711, -7855, 19583], ![-25123, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-3, -20, 1]] ![![59, 0, 0], ![21, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1239, 59, 0]], ![![-177, -1180, 59], ![-59, -472, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![21, 1, 0]]], ![![![-3, -20, 1]], ![![-1, -8, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![7, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![7, 1, 0]] 
 ![![61, 0, 0], ![7, 1, 0], ![47, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![7, 1, 0], ![0, 8, 4], ![4, -29, 7]]]
  hmulB := by decide  
  f := ![![![218, 31, 0], ![-1891, 0, 0]], ![![14, 2, 0], ![-121, 0, 0]], ![![162, 17, -3], ![-1405, 46, 0]]]
  g := ![![![1, 0, 0], ![-7, 61, 0], ![-47, 0, 61]], ![![0, 1, 0], ![-4, 8, 4], ![-2, -29, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![17, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![0, 21, 4], ![4, -29, 20]]]
  hmulB := by decide  
  f := ![![![761, 38, 0], ![-2318, 0, 0]], ![![220, 11, 0], ![-670, 0, 0]], ![![197, -6, -3], ![-600, 46, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-17, 0, 61]], ![![0, 1, 0], ![-8, 21, 4], ![4, -29, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 16, 7]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-2, 16, 7]] 
 ![![61, 0, 0], ![33, 1, 0], ![55, 0, 1]] where
  M :=![![![-2, 16, 7], ![28, -189, 64], ![57, -457, -205]]]
  hmulB := by decide  
  f := ![![![67993, 81, 2347]], ![![36937, 44, 1275]], ![![61272, 73, 2115]]]
  g := ![![![-15, 16, 7], ![45, -189, 64], ![433, -457, -205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![7, 1, 0]] ![![61, 0, 0], ![20, 1, 0]]
  ![![67993, 81, 2347]] where
 M := ![![![3721, 0, 0], ![1220, 61, 0]], ![![427, 61, 0], ![140, 28, 4]]]
 hmul := by decide  
 g := ![![![![-122, 976, 427]], ![![-12, 131, 204]]], ![![![14, -77, 113]], ![![12, -80, 32]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![67993, 81, 2347]] ![![-2, 16, 7]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![1, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![1, 1, 0]] 
 ![![67, 0, 0], ![1, 1, 0], ![33, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![1, 1, 0], ![0, 2, 4], ![4, -29, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![67, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![33, 17, 0]]]
  g := ![![![1, 0, 0], ![-1, 67, 0], ![-33, 0, 67]], ![![0, 1, 0], ![-2, 2, 4], ![0, -29, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![32, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![32, 1, 0]] 
 ![![67, 0, 0], ![32, 1, 0], ![4, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![32, 1, 0], ![0, 33, 4], ![4, -29, 32]]]
  hmulB := by decide  
  f := ![![![257, 8, 0], ![-536, 0, 0]], ![![96, 3, 0], ![-200, 0, 0]], ![![-20, -9, -1], ![42, 17, 0]]]
  g := ![![![1, 0, 0], ![-32, 67, 0], ![-4, 0, 67]], ![![0, 1, 0], ![-16, 33, 4], ![12, -29, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![33, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![33, 1, 0]] 
 ![![67, 0, 0], ![33, 1, 0], ![21, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![33, 1, 0], ![0, 34, 4], ![4, -29, 33]]]
  hmulB := by decide  
  f := ![![![2080, 63, 0], ![-4221, 0, 0]], ![![990, 30, 0], ![-2009, 0, 0]], ![![648, 11, -1], ![-1315, 17, 0]]]
  g := ![![![1, 0, 0], ![-33, 67, 0], ![-21, 0, 67]], ![![0, 1, 0], ![-18, 34, 4], ![4, -29, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![1, 1, 0]] ![![67, 0, 0], ![32, 1, 0]]
  ![![67, 0, 0], ![8, -25, 1]] where
 M := ![![![4489, 0, 0], ![2144, 67, 0]], ![![67, 67, 0], ![32, 34, 4]]]
 hmul := by decide  
 g := ![![![![59, 25, -1], ![67, 0, 0]], ![![24, 26, -1], ![67, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![0, 2, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![8, -25, 1]] ![![67, 0, 0], ![33, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2211, 67, 0]], ![![536, -1675, 67], ![268, -871, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![33, 1, 0]]], ![![![8, -25, 1]], ![![4, -13, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 56, -9]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-8, 56, -9]] 
 ![![71, 0, 0], ![31, 1, 0], ![36, 0, 1]] where
  M :=![![![-8, 56, -9], ![-36, 309, 224], ![233, -1633, 253]]]
  hmulB := by decide  
  f := ![![![-443969, -529, -15325]], ![![-194709, -232, -6721]], ![![-224925, -268, -7764]]]
  g := ![![![-20, 56, -9], ![-249, 309, 224], ![588, -1633, 253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-16, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-16, 1, 0]] 
 ![![71, 0, 0], ![55, 1, 0], ![11, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-16, 1, 0], ![0, -15, 4], ![4, -29, -16]]]
  hmulB := by decide  
  f := ![![![705, -44, 0], ![3124, 0, 0]], ![![561, -35, 0], ![2486, 0, 0]], ![![125, -4, -1], ![554, 18, 0]]]
  g := ![![![1, 0, 0], ![-55, 71, 0], ![-11, 0, 71]], ![![-1, 1, 0], ![11, -15, 4], ![25, -29, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-8, 56, -9]] ![![71, 0, 0], ![-16, 1, 0]]
  ![![71, 0, 0], ![18, 4, 1]] where
 M := ![![![-568, 3976, -639], ![92, -587, 368]]]
 hmul := by decide  
 g := ![![![![-26, 52, -10], ![71, 0, 0]], ![![-2, -9, 5], ![13, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![18, 4, 1]] ![![71, 0, 0], ![-16, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1136, 71, 0]], ![![1278, 284, 71], ![-284, -71, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-16, 1, 0]]], ![![![18, 4, 1]], ![![-4, -1, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![274, -2120, -629]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![274, -2120, -629]] 
 ![![73, 0, 0], ![0, 73, 0], ![15, 39, 1]] where
  M :=![![![274, -2120, -629], ![-2516, 16395, -8480], ![-7851, 60851, 18515]]]
  hmulB := by decide  
  f := ![![![11226985, 13377, 387535]], ![![1550140, 1847, 53508]], ![![3130496, 3730, 108059]]]
  g := ![![![133, 307, -629], ![1708, 4755, -8480], ![-3912, -9058, 18515]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [25, 39, 1] where
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
 g := ![![[22, 38], [72], [72], [59, 8], [61], [1]], ![[0, 35], [72], [72], [39, 65], [61], [1]]]
 h' := ![![[34, 72], [37, 44], [31, 46], [58, 46], [49, 9], [48, 34], [0, 1]], ![[0, 1], [0, 29], [62, 27], [16, 27], [63, 64], [36, 39], [34, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [1, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [25, 39, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![88, -837, -1678]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![346, 885, -1678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11226985, 13377, 387535]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![11226985, 13377, 387535]] 
 ![![73, 0, 0], ![63, 1, 0], ![14, 0, 1]] where
  M :=![![![11226985, 13377, 387535], ![1550140, 1847, 53508], ![-334027, -398, -11530]]]
  hmulB := by decide  
  f := ![![![274, -2120, -629]], ![![202, -1605, -659]], ![![-55, 427, 133]]]
  g := ![![![67928, 13377, 387535], ![9379, 1847, 53508], ![-2021, -398, -11530]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![274, -2120, -629]] ![![11226985, 13377, 387535]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [14, 33, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 55], [49, 23], [0, 1]]
 g := ![![[74, 3, 65], [63, 68, 50], [65, 71, 36], [3, 48, 11], [40, 1], []], ![[19, 42, 73], [25, 60, 44], [51, 23, 38], [67, 45, 16], [31, 55], []], ![[24, 34, 20], [47, 30, 64], [78, 64, 5], [10, 65, 52], [10, 23], []]]
 h' := ![![[70, 55], [66, 72, 67], [38, 47, 45], [37, 68, 73], [72, 9, 66], [0, 0, 1], [0, 1]], ![[49, 23], [26, 40, 40], [21, 63, 8], [45, 42, 20], [44, 14, 17], [2, 37, 23], [70, 55]], ![[0, 1], [62, 46, 51], [23, 48, 26], [23, 48, 65], [31, 56, 75], [31, 42, 55], [49, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30], []]
 b := ![[], [29, 47, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [14, 33, 39, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18026062, 169050204, 178639856]
  a := ![1, 20, 61]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-228178, 2139876, 2261264]
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



lemma PB177I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB177I1 : PrimesBelowBoundCertificateInterval O 31 79 177 where
  m := 11
  g := ![2, 2, 3, 2, 1, 3, 3, 3, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB177I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N1]
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
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
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
      exact NI43N0
      exact NI43N1
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
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N0, I43N1, I47N1, I59N0, I59N1, I59N2, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2, I71N0, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [I43N0, I43N0, I43N1], [I47N1], [], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
