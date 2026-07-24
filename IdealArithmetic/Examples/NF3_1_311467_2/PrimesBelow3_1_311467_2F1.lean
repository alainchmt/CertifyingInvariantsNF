
import IdealArithmetic.Examples.NF3_1_311467_2.RI3_1_311467_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [36, 13, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 24, 23], [35, 12, 14], [0, 1]]
 g := ![![[25], [22, 12], [14, 26, 4], [23, 1], []], ![[1, 22, 33, 35], [8, 25], [18, 36, 12, 35], [8, 33], [25, 11]], ![[35, 27, 30, 2], [3, 33], [7, 16, 18, 19], [24, 21], [34, 11]]]
 h' := ![![[25, 24, 23], [33, 32], [14, 3, 7], [23, 35, 35], [0, 0, 1], [0, 1]], ![[35, 12, 14], [19, 28, 33], [14, 21, 5], [5, 30, 4], [21, 35, 12], [25, 24, 23]], ![[0, 1], [6, 14, 4], [15, 13, 25], [25, 9, 35], [1, 2, 24], [35, 12, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 8], []]
 b := ![[], [20, 14, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [36, 13, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2220, 5476, -888]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![60, 148, -24]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [2, 17, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 19, 17], [34, 21, 24], [0, 1]]
 g := ![![[12, 12, 23], [30, 23], [15, 4], [1, 10, 1], []], ![[21, 40, 27, 30], [35, 2], [16, 5], [33, 23, 25, 35], [10, 2]], ![[12, 0, 21, 34], [18, 10], [2, 39], [40, 16, 39, 13], [3, 2]]]
 h' := ![![[17, 19, 17], [1, 12, 8], [15, 8, 8], [39, 4, 2], [0, 0, 1], [0, 1]], ![[34, 21, 24], [20, 27, 3], [7, 33, 17], [30, 36, 28], [23, 21, 21], [17, 19, 17]], ![[0, 1], [15, 2, 30], [16, 0, 16], [15, 1, 11], [2, 20, 19], [34, 21, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 7], []]
 b := ![[], [38, 27, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [2, 17, 31, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![776007, -437429, 61049]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18927, -10669, 1489]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![19, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![19, 1, 0]] 
 ![![43, 0, 0], ![19, 1, 0], ![26, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![19, 1, 0], ![0, 19, 1], ![-168, 43, 20]]]
  hmulB := by decide  
  f := ![![![267, 14, 0], ![-602, 0, 0]], ![![95, 5, 0], ![-214, 0, 0]], ![![142, 7, 0], ![-320, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 43, 0], ![-26, 0, 43]], ![![0, 1, 0], ![-9, 19, 1], ![-35, 43, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-18, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-18, 1, 0]] 
 ![![43, 0, 0], ![25, 1, 0], ![20, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-18, 1, 0], ![0, -18, 1], ![-168, 43, -17]]]
  hmulB := by decide  
  f := ![![![361, -20, 0], ![860, 0, 0]], ![![199, -11, 0], ![474, 0, 0]], ![![188, -10, 0], ![448, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 43, 0], ![-20, 0, 43]], ![![-1, 1, 0], ![10, -18, 1], ![-21, 43, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-2, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-2, 1, 0]] 
 ![![43, 0, 0], ![41, 1, 0], ![39, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-2, 1, 0], ![0, -2, 1], ![-168, 43, -1]]]
  hmulB := by decide  
  f := ![![![49, -24, 0], ![1032, 0, 0]], ![![47, -23, 0], ![990, 0, 0]], ![![45, -22, 0], ![948, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 43, 0], ![-39, 0, 43]], ![![-1, 1, 0], ![1, -2, 1], ![-44, 43, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![19, 1, 0]] ![![43, 0, 0], ![-18, 1, 0]]
  ![![43, 0, 0], ![-41, 1, 1]] where
 M := ![![![1849, 0, 0], ![-774, 43, 0]], ![![817, 43, 0], ![-342, 1, 1]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![23, 0, -1], ![43, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![34, -1, -1], ![44, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-41, 1, 1]] ![![43, 0, 0], ![-2, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-86, 43, 0]], ![![-1763, 43, 43], ![-86, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-2, 1, 0]]], ![![![-41, 1, 1]], ![![-2, 0, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [8, 20, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 6, 44], [19, 40, 3], [0, 1]]
 g := ![![[43, 38, 2], [33, 11, 32], [9, 4, 6], [43, 4, 1], []], ![[30, 33, 33, 19], [29, 14, 35, 31], [17, 4, 27, 22], [27, 6, 26, 41], [0, 9]], ![[13, 6, 0, 9], [17, 8, 34, 9], [21, 38, 28, 18], [1, 16, 40, 14], [41, 9]]]
 h' := ![![[32, 6, 44], [18, 18, 40], [22, 13, 19], [32, 1, 37], [0, 0, 1], [0, 1]], ![[19, 40, 3], [6, 39, 42], [13, 37, 16], [23, 35, 20], [37, 30, 40], [32, 6, 44]], ![[0, 1], [35, 37, 12], [3, 44, 12], [3, 11, 37], [33, 17, 6], [19, 40, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 29], []]
 b := ![[], [14, 13, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [8, 20, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-147768, 54708, -15228]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3144, 1164, -324]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 4, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-23, 4, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![30, 4, 1]] where
  M :=![![![-23, 4, 1], ![-168, 20, 5], ![-840, 47, 25]]]
  hmulB := by decide  
  f := ![![![5, -1, 0]], ![![0, 5, -1]], ![![6, -1, 0]]]
  g := ![![![-1, 0, 1], ![-6, 0, 5], ![-30, -1, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [33, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 52], [0, 1]]
 g := ![![[33, 24], [28], [], [10], [24, 1]], ![[26, 29], [28], [], [10], [48, 52]]]
 h' := ![![[24, 52], [30, 36], [0, 9], [50], [3, 13], [0, 1]], ![[0, 1], [46, 17], [4, 44], [50], [50, 40], [24, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [33, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [33, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-441, -1352, 298]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177, -48, 298]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-5, 1, 0]] 
 ![![53, 0, 0], ![48, 1, 0], ![28, 0, 1]] where
  M :=![![![-5, 1, 0], ![0, -5, 1], ![-168, 43, -4]]]
  hmulB := by decide  
  f := ![![![23, -4, -1]], ![![24, -4, -1]], ![![28, -3, -1]]]
  g := ![![![-1, 1, 0], ![4, -5, 1], ![-40, 43, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-23, 4, 1]] ![![-5, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [7, 7, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 42, 54], [45, 16, 5], [0, 1]]
 g := ![![[19, 2, 48], [20, 25, 7], [3, 25], [11, 30, 15], [1]], ![[33, 26, 31, 47], [28, 39, 8, 37], [38, 3], [53, 18, 8, 18], [11, 12, 49, 52]], ![[15, 10, 43, 45], [42, 24, 8, 20], [52, 20], [38, 24, 0, 36], [36, 24, 53, 7]]]
 h' := ![![[44, 42, 54], [37, 44, 44], [8, 53, 40], [41, 57, 54], [52, 52, 30], [0, 1]], ![[45, 16, 5], [31, 26, 12], [6, 44, 21], [53, 56, 48], [29, 46, 43], [44, 42, 54]], ![[0, 1], [50, 48, 3], [47, 21, 57], [23, 5, 16], [13, 20, 45], [45, 16, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 17], []]
 b := ![[], [48, 22, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [7, 7, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5369, 4897, -177]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91, 83, -3]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [7, 28, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 0, 42], [28, 60, 19], [0, 1]]
 g := ![![[32, 24, 48], [45, 34], [32, 10, 16], [20, 56, 47], [1]], ![[19, 39, 30, 9], [49, 19], [30, 44, 31, 9], [14, 51, 5, 1], [15, 41, 46, 34]], ![[13, 44, 45, 1], [16, 4], [21, 54, 56, 45], [50, 57, 50, 1], [23, 16, 30, 27]]]
 h' := ![![[20, 0, 42], [24, 28, 29], [20, 29, 41], [43, 12, 4], [54, 33, 48], [0, 1]], ![[28, 60, 19], [26, 24, 49], [53, 15, 18], [2, 58, 12], [26, 25, 57], [20, 0, 42]], ![[0, 1], [7, 9, 44], [34, 17, 2], [14, 52, 45], [14, 3, 17], [28, 60, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 14], []]
 b := ![[], [52, 53, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [7, 28, 13, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1846775, 272182, 58682]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30275, 4462, 962]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [26, 50, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6, 53], [43, 60, 14], [0, 1]]
 g := ![![[5, 2, 24], [30, 41, 35], [65, 54], [64, 24], [47, 1], []], ![[56, 13, 33, 3], [9, 24, 41, 57], [35, 6], [2, 36], [49, 49], [66, 62]], ![[66, 19, 51, 49], [7, 0, 25, 25], [18, 24], [22, 14], [28, 36], [38, 62]]]
 h' := ![![[4, 6, 53], [24, 42, 52], [53, 5, 54], [66, 49, 11], [51, 36, 15], [0, 0, 1], [0, 1]], ![[43, 60, 14], [31, 48, 53], [63, 14, 21], [54, 55, 41], [21, 18, 61], [42, 27, 60], [4, 6, 53]], ![[0, 1], [37, 44, 29], [63, 48, 59], [53, 30, 15], [42, 13, 58], [57, 40, 6], [43, 60, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 34], []]
 b := ![[], [9, 50, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [26, 50, 20, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65861, 24455, -2747]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-983, 365, -41]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [67, 34, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 36, 1], [1, 34, 70], [0, 1]]
 g := ![![[8, 13, 45], [67, 33, 27], [34, 11, 4], [29, 29], [33, 1], []], ![[62, 68, 16, 29], [39, 56, 11, 5], [7, 56, 17, 45], [56, 24], [44, 20], [34, 1]], ![[41, 3, 58, 42], [51, 2, 6, 55], [41, 24, 43, 13], [50, 32], [10, 18], [36, 1]]]
 h' := ![![[32, 36, 1], [55, 20, 20], [65, 33, 58], [3, 48, 69], [61, 18, 61], [0, 0, 1], [0, 1]], ![[1, 34, 70], [39, 46, 61], [28, 57, 17], [0, 63, 51], [42, 62, 33], [24, 16, 34], [32, 36, 1]], ![[0, 1], [64, 5, 61], [59, 52, 67], [45, 31, 22], [49, 62, 48], [3, 55, 36], [1, 34, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 36], []]
 b := ![[], [17, 58, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [67, 34, 38, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32021, -79449, 19383]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-451, -1119, 273]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [6, 49, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 39, 59], [44, 33, 14], [0, 1]]
 g := ![![[52, 55, 50], [56, 23], [2, 16], [28, 2, 37], [24, 1], []], ![[10, 64, 15, 39], [29, 48], [59, 61], [9, 16, 46, 7], [61, 67], [35, 50]], ![[40, 8, 4, 13], [13, 65], [42, 57], [50, 29, 20, 13], [67, 61], [7, 50]]]
 h' := ![![[53, 39, 59], [17, 66, 14], [34, 9, 13], [51, 7, 4], [2, 59, 16], [0, 0, 1], [0, 1]], ![[44, 33, 14], [43, 47, 49], [61, 12, 11], [14, 62, 34], [37, 70, 67], [44, 2, 33], [53, 39, 59]], ![[0, 1], [18, 33, 10], [13, 52, 49], [51, 4, 35], [52, 17, 63], [69, 71, 39], [44, 33, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 66], []]
 b := ![[], [32, 40, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [6, 49, 49, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1396052, -536550, 61758]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19124, -7350, 846]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4871, 1889, -220]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-4871, 1889, -220]] 
 ![![79, 0, 0], ![0, 79, 0], ![62, 60, 1]] where
  M :=![![![-4871, 1889, -220], ![36960, -14331, 1669], ![-280392, 108727, -12662]]]
  hmulB := by decide  
  f := ![![![79, 18, 1]], ![![-168, 122, 19]], ![![-106, 115, 17]]]
  g := ![![![111, 191, -220], ![-842, -1449, 1669], ![6388, 10993, -12662]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [43, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 78], [0, 1]]
 g := ![![[77, 32], [73, 4], [25, 52], [46, 10], [49], [1]], ![[64, 47], [22, 75], [73, 27], [37, 69], [49], [1]]]
 h' := ![![[7, 78], [21, 36], [31, 2], [76, 17], [58, 57], [36, 7], [0, 1]], ![[0, 1], [36, 43], [45, 77], [37, 62], [62, 22], [6, 72], [7, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [16, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [43, 72, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1316, -309, 141]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94, -111, 141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 18, 1]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 18, 1]] 
 ![![79, 0, 0], ![18, 1, 0], ![71, 0, 1]] where
  M :=![![![79, 18, 1], ![-168, 122, 19], ![-3192, 649, 141]]]
  hmulB := by decide  
  f := ![![![-4871, 1889, -220]], ![![-642, 249, -29]], ![![-7927, 3074, -358]]]
  g := ![![![-4, 18, 1], ![-47, 122, 19], ![-315, 649, 141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-4871, 1889, -220]] ![![79, 18, 1]]
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


lemma PB158I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB158I1 : PrimesBelowBoundCertificateInterval O 31 79 158 where
  m := 11
  g := ![1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB158I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
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
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
  β := ![I43N0, I43N1, I43N2, I53N1, I79N1]
  Il := ![[], [], [I43N0, I43N1, I43N2], [], [I53N1], [], [], [], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
