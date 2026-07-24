
import IdealArithmetic.Examples.NF3_1_112887_1.RI3_1_112887_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-17, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-17, 1, 0]] 
 ![![37, 0, 0], ![20, 1, 0], ![7, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-17, 1, 0], ![0, -17, 1], ![53, -21, -17]]]
  hmulB := by decide  
  f := ![![![545, -32, 0], ![1184, 0, 0]], ![![290, -17, 0], ![630, 0, 0]], ![![127, -7, 0], ![276, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 37, 0], ![-7, 0, 37]], ![![-1, 1, 0], ![9, -17, 1], ![16, -21, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![37, 0, 0], ![34, 1, 0], ![28, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 1], ![53, -21, -3]]]
  hmulB := by decide  
  f := ![![![-30, -3, -1]], ![![-29, -3, -1]], ![![-27, -2, -1]]]
  g := ![![![-1, 1, 0], ![2, -3, 1], ![23, -21, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-17, 1, 0]] ![![37, 0, 0], ![-17, 1, 0]]
  ![![30, 3, 1]] where
 M := ![![![1369, 0, 0], ![-629, 37, 0]], ![![-629, 37, 0], ![289, -34, 1]]]
 hmul := by decide  
 g := ![![![![111, -37, 0]], ![![-51, 20, -1]]], ![![![-51, 20, -1]], ![![22, -10, 1]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![30, 3, 1]] ![![-3, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![1, 12, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![1, 12, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![1, 12, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![1, 12, 1], ![53, -20, 12], ![636, -199, -20]]]
  hmulB := by decide  
  f := ![![![0, 4, 0], ![-12, 1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -12, 41]], ![![0, 0, 1], ![1, -4, 12], ![16, 1, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [31, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 40], [0, 1]]
 g := ![![[28, 4], [31], [36], [9, 8], [1]], ![[0, 37], [31], [36], [35, 33], [1]]]
 h' := ![![[34, 40], [14, 2], [14, 21], [8, 35], [10, 34], [0, 1]], ![[0, 1], [0, 39], [31, 20], [9, 6], [18, 7], [34, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [40, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [31, 7, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![137, 4, -27]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 8, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-12, 1, 0]] 
 ![![41, 0, 0], ![29, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-12, 1, 0], ![0, -12, 1], ![53, -21, -12]]]
  hmulB := by decide  
  f := ![![![361, -30, 0], ![1230, 0, 0]], ![![253, -21, 0], ![862, 0, 0]], ![![196, -16, 0], ![668, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 41, 0], ![-20, 0, 41]], ![![-1, 1, 0], ![8, -12, 1], ![22, -21, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![1, 12, 1]] ![![41, 0, 0], ![-12, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-492, 41, 0]], ![![41, 492, 41], ![41, -164, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-12, 1, 0]]], ![![![1, 12, 1]], ![![1, -4, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [16, 16, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 0, 14], [37, 42, 29], [0, 1]]
 g := ![![[5, 31, 14], [20, 11, 24], [21, 41], [27, 0, 1], []], ![[36, 39, 24, 15], [39, 21, 23, 1], [34, 15], [23, 18, 2, 14], [0, 24]], ![[12, 23, 40, 39], [38, 29, 31, 28], [5, 10], [41, 3], [28, 24]]]
 h' := ![![[6, 0, 14], [24, 35, 33], [12, 5, 14], [41, 41, 27], [0, 0, 1], [0, 1]], ![[37, 42, 29], [3, 13, 27], [30, 42, 13], [12, 38, 31], [36, 3, 42], [6, 0, 14]], ![[0, 1], [21, 38, 26], [19, 39, 16], [23, 7, 28], [18, 40], [37, 42, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26], []]
 b := ![[], [24, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [16, 16, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![137428, -84065, 8901]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3196, -1955, 207]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-18, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-18, 1, 0]] 
 ![![47, 0, 0], ![29, 1, 0], ![5, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-18, 1, 0], ![0, -18, 1], ![53, -21, -18]]]
  hmulB := by decide  
  f := ![![![757, -42, 0], ![1974, 0, 0]], ![![451, -25, 0], ![1176, 0, 0]], ![![79, -4, 0], ![206, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 47, 0], ![-5, 0, 47]], ![![-1, 1, 0], ![11, -18, 1], ![16, -21, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-17, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-17, 1, 0]] 
 ![![47, 0, 0], ![30, 1, 0], ![40, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-17, 1, 0], ![0, -17, 1], ![53, -21, -17]]]
  hmulB := by decide  
  f := ![![![715, -42, 0], ![1974, 0, 0]], ![![460, -27, 0], ![1270, 0, 0]], ![![602, -35, 0], ![1662, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 47, 0], ![-40, 0, 47]], ![![-1, 1, 0], ![10, -17, 1], ![29, -21, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-12, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-12, 1, 0]] 
 ![![47, 0, 0], ![35, 1, 0], ![44, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-12, 1, 0], ![0, -12, 1], ![53, -21, -12]]]
  hmulB := by decide  
  f := ![![![73, -6, 0], ![282, 0, 0]], ![![61, -5, 0], ![236, 0, 0]], ![![76, -6, 0], ![294, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 47, 0], ![-44, 0, 47]], ![![-1, 1, 0], ![8, -12, 1], ![28, -21, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-18, 1, 0]] ![![47, 0, 0], ![-17, 1, 0]]
  ![![47, 0, 0], ![24, 12, 1]] where
 M := ![![![2209, 0, 0], ![-799, 47, 0]], ![![-846, 47, 0], ![306, -35, 1]]]
 hmul := by decide  
 g := ![![![![23, -12, -1], ![47, 0, 0]], ![![-17, 1, 0], ![0, 0, 0]]], ![![![-18, 1, 0], ![0, 0, 0]], ![![-18, -13, -1], ![48, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![24, 12, 1]] ![![47, 0, 0], ![-12, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-564, 47, 0]], ![![1128, 564, 47], ![-235, -141, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-12, 1, 0]]], ![![![24, 12, 1]], ![![-5, -3, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 0, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![21, 0, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![21, 0, 1]] where
  M :=![![![21, 0, 1], ![53, 0, 0], ![0, 53, 0]]]
  hmulB := by decide  
  f := ![![![0, 1, 0]], ![![0, 0, 1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [15, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 52], [0, 1]]
 g := ![![[34, 46], [7], [49, 42], [37], [20, 1]], ![[0, 7], [7], [41, 11], [37], [40, 52]]]
 h' := ![![[20, 52], [50, 24], [7, 22], [34, 25], [18, 14], [0, 1]], ![[0, 1], [0, 29], [23, 31], [4, 28], [33, 39], [20, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [25, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [15, 33, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1893, 0, 75]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 0, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![53, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![53, -21, 0]]]
  hmulB := by decide  
  f := ![![![21, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, -21, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![21, 0, 1]] ![![0, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 5, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-13, 5, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![46, 5, 1]] where
  M :=![![![-13, 5, 1], ![53, -34, 5], ![265, -52, -34]]]
  hmulB := by decide  
  f := ![![![24, 2, 1]], ![![53, 3, 2]], ![![25, 2, 1]]]
  g := ![![![-1, 0, 1], ![-3, -1, 5], ![31, 2, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [35, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 58], [0, 1]]
 g := ![![[23, 27], [8, 53], [25], [50, 49], [21, 1]], ![[0, 32], [0, 6], [25], [17, 10], [42, 58]]]
 h' := ![![[21, 58], [15, 33], [56, 17], [20, 5], [32, 52], [0, 1]], ![[0, 1], [0, 26], [0, 42], [7, 54], [3, 7], [21, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [33, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [35, 38, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-244, 643, -308]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![236, 37, -308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 2, 1]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![24, 2, 1]] 
 ![![59, 0, 0], ![54, 1, 0], ![34, 0, 1]] where
  M :=![![![24, 2, 1], ![53, 3, 2], ![106, 11, 3]]]
  hmulB := by decide  
  f := ![![![-13, 5, 1]], ![![-11, 4, 1]], ![![-3, 2, 0]]]
  g := ![![![-2, 2, 1], ![-3, 3, 2], ![-10, 11, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-13, 5, 1]] ![![24, 2, 1]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![17, -22, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![17, -22, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![17, 39, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![17, -22, 1], ![53, -4, -22], ![-1166, 515, -4]]]
  hmulB := by decide  
  f := ![![![-16, 22, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -39, 61]], ![![0, -1, 1], ![7, 14, -22], ![-18, 11, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [9, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 60], [0, 1]]
 g := ![![[5, 34], [49], [8, 42], [12, 9], [16, 1]], ![[0, 27], [49], [9, 19], [34, 52], [32, 60]]]
 h' := ![![[16, 60], [46, 20], [50, 7], [14, 46], [39, 3], [0, 1]], ![[0, 1], [0, 41], [40, 54], [18, 15], [26, 58], [16, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [40, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [9, 45, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![115, -34, -65]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20, 41, -65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![22, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![22, 1, 0]] 
 ![![61, 0, 0], ![22, 1, 0], ![4, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![22, 1, 0], ![0, 22, 1], ![53, -21, 22]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-1037, 0, 0]], ![![110, 5, 0], ![-304, 0, 0]], ![![8, 0, 0], ![-22, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 61, 0], ![-4, 0, 61]], ![![0, 1, 0], ![-8, 22, 1], ![7, -21, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![17, -22, 1]] ![![61, 0, 0], ![22, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1342, 61, 0]], ![![1037, -1342, 61], ![427, -488, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![22, 1, 0]]], ![![![17, -22, 1]], ![![7, -8, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 8, -2]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-7, 8, -2]] 
 ![![67, 0, 0], ![0, 67, 0], ![37, 63, 1]] where
  M :=![![![-7, 8, -2], ![-106, 35, 8], ![424, -274, 35]]]
  hmulB := by decide  
  f := ![![![51, 4, 2]], ![![106, 9, 4]], ![![131, 11, 5]]]
  g := ![![![1, 2, -2], ![-6, -7, 8], ![-13, -37, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [3, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 66], [0, 1]]
 g := ![![[38, 16], [5, 40], [33], [6], [65], [1]], ![[23, 51], [1, 27], [33], [6], [65], [1]]]
 h' := ![![[20, 66], [52, 63], [4, 43], [6, 10], [15, 41], [64, 20], [0, 1]], ![[0, 1], [39, 4], [60, 24], [5, 57], [31, 26], [62, 47], [20, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [56, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [3, 47, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2065, 186, 389]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-184, -363, 389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, -4, -2]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-51, -4, -2]] 
 ![![67, 0, 0], ![4, 1, 0], ![51, 0, 1]] where
  M :=![![![-51, -4, -2], ![-106, -9, -4], ![-212, -22, -9]]]
  hmulB := by decide  
  f := ![![![7, -8, 2]], ![![2, -1, 0]], ![![-1, -2, 1]]]
  g := ![![![1, -4, -2], ![2, -9, -4], ![5, -22, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-7, 8, -2]] ![![-51, -4, -2]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [28, 32, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 32, 23], [63, 38, 48], [0, 1]]
 g := ![![[11, 13, 4], [42, 38, 40], [69, 50, 25], [6, 4], [39, 1], []], ![[44, 18, 69, 44], [41, 14, 57, 51], [7, 35, 51, 63], [0, 48], [24, 24], [22, 32]], ![[29, 46, 64, 4], [55, 48, 27, 36], [69, 14, 39, 30], [25, 30], [21, 30], [68, 32]]]
 h' := ![![[47, 32, 23], [31, 18, 69], [56, 62, 53], [64, 14, 5], [44, 2, 69], [0, 0, 1], [0, 1]], ![[63, 38, 48], [34, 32, 54], [69, 70, 32], [25, 33, 15], [5, 17, 41], [31, 59, 38], [47, 32, 23]], ![[0, 1], [17, 21, 19], [20, 10, 57], [53, 24, 51], [16, 52, 32], [6, 12, 32], [63, 38, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 26], []]
 b := ![[], [52, 64, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [28, 32, 32, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20590, 9301, 284]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-290, 131, 4]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![13, -24, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![13, -24, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![13, 49, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![13, -24, 1], ![53, -8, -24], ![-1272, 557, -8]]]
  hmulB := by decide  
  f := ![![![-12, 24, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -49, 73]], ![![0, -1, 1], ![5, 16, -24], ![-16, 13, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [72, 44, 1] where
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
 g := ![![[29, 72], [69], [27], [64, 64], [38], [1]], ![[0, 1], [69], [27], [22, 9], [38], [1]]]
 h' := ![![[29, 72], [53, 46], [35, 19], [64, 10], [39, 65], [1, 29], [0, 1]], ![[0, 1], [0, 27], [2, 54], [62, 63], [26, 8], [39, 44], [29, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [65, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [72, 44, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![284, 172, 5]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -1, 5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![24, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![24, 1, 0]] 
 ![![73, 0, 0], ![24, 1, 0], ![8, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![24, 1, 0], ![0, 24, 1], ![53, -21, 24]]]
  hmulB := by decide  
  f := ![![![721, 30, 0], ![-2190, 0, 0]], ![![216, 9, 0], ![-656, 0, 0]], ![![56, 2, 0], ![-170, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 73, 0], ![-8, 0, 73]], ![![0, 1, 0], ![-8, 24, 1], ![5, -21, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![13, -24, 1]] ![![73, 0, 0], ![24, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1752, 73, 0]], ![![949, -1752, 73], ![365, -584, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![24, 1, 0]]], ![![![13, -24, 1]], ![![5, -8, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![6, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![6, 1, 0]] 
 ![![79, 0, 0], ![6, 1, 0], ![43, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![6, 1, 0], ![0, 6, 1], ![53, -21, 6]]]
  hmulB := by decide  
  f := ![![![337, 56, 0], ![-4424, 0, 0]], ![![18, 3, 0], ![-236, 0, 0]], ![![181, 30, 0], ![-2376, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 79, 0], ![-43, 0, 79]], ![![0, 1, 0], ![-1, 6, 1], ![-1, -21, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![27, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![27, 1, 0]] 
 ![![79, 0, 0], ![27, 1, 0], ![61, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![27, 1, 0], ![0, 27, 1], ![53, -21, 27]]]
  hmulB := by decide  
  f := ![![![730, 27, 0], ![-2133, 0, 0]], ![![216, 8, 0], ![-631, 0, 0]], ![![550, 20, 0], ![-1607, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 79, 0], ![-61, 0, 79]], ![![0, 1, 0], ![-10, 27, 1], ![-13, -21, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-33, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-33, 1, 0]] 
 ![![79, 0, 0], ![46, 1, 0], ![17, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-33, 1, 0], ![0, -33, 1], ![53, -21, -33]]]
  hmulB := by decide  
  f := ![![![661, -20, 0], ![1580, 0, 0]], ![![430, -13, 0], ![1028, 0, 0]], ![![179, -5, 0], ![428, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 79, 0], ![-17, 0, 79]], ![![-1, 1, 0], ![19, -33, 1], ![20, -21, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![6, 1, 0]] ![![79, 0, 0], ![27, 1, 0]]
  ![![79, 0, 0], ![4, 33, 1]] where
 M := ![![![6241, 0, 0], ![2133, 79, 0]], ![![474, 79, 0], ![162, 33, 1]]]
 hmul := by decide  
 g := ![![![![75, -33, -1], ![79, 0, 0]], ![![23, -32, -1], ![79, 0, 0]]], ![![![2, -32, -1], ![79, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![4, 33, 1]] ![![79, 0, 0], ![-33, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2607, 79, 0]], ![![316, 2607, 79], ![-79, -1106, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-33, 1, 0]]], ![![![4, 33, 1]], ![![-1, -14, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB96I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB96I1 : PrimesBelowBoundCertificateInterval O 31 79 96 where
  m := 11
  g := ![3, 2, 1, 3, 2, 2, 2, 2, 1, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB96I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N0, I37N1, I41N1, I47N0, I47N1, I47N2, I53N1, I59N1, I61N1, I67N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N0, I37N1], [I41N1], [], [I47N0, I47N1, I47N2], [I53N1], [I59N1], [I61N1], [I67N1], [], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
