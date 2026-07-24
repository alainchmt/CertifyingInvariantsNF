
import IdealArithmetic.Examples.NF3_1_677484_9.RI3_1_677484_9
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-41, 17, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-41, 17, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![33, 17, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-41, 17, 1], ![258, -5, 102], ![4386, 655, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -17, 37]], ![![-2, 0, 1], ![-84, -47, 102], ![123, 20, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[30, 21], [9], [19, 7], [33], [1]], ![[0, 16], [9], [9, 30], [33], [1]]]
 h' := ![![[25, 36], [29, 24], [22, 3], [21, 28], [7, 25], [0, 1]], ![[0, 1], [0, 13], [23, 34], [18, 9], [3, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [18, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [30, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![546, 103, 30]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -11, 30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![9, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![9, 1, 0]] 
 ![![37, 0, 0], ![9, 1, 0], ![5, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![9, 1, 0], ![0, 9, 6], ![258, 36, 9]]]
  hmulB := by decide  
  f := ![![![172, 19, 0], ![-703, 0, 0]], ![![36, 4, 0], ![-147, 0, 0]], ![![14, -6, -5], ![-57, 31, 0]]]
  g := ![![![1, 0, 0], ![-9, 37, 0], ![-5, 0, 37]], ![![0, 1, 0], ![-3, 9, 6], ![-3, 36, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-41, 17, 1]] ![![37, 0, 0], ![9, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![333, 37, 0]], ![![-1517, 629, 37], ![-111, 148, 111]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![9, 1, 0]]], ![![![-41, 17, 1]], ![![-3, 4, 3]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-20, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-20, 1, 0]] 
 ![![41, 0, 0], ![21, 1, 0], ![29, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-20, 1, 0], ![0, -20, 6], ![258, 36, -20]]]
  hmulB := by decide  
  f := ![![![821, -41, 0], ![1681, 0, 0]], ![![441, -22, 0], ![903, 0, 0]], ![![609, -27, -1], ![1247, 7, 0]]]
  g := ![![![1, 0, 0], ![-21, 41, 0], ![-29, 0, 41]], ![![-1, 1, 0], ![6, -20, 6], ![2, 36, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-1, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-1, 1, 0]] 
 ![![41, 0, 0], ![40, 1, 0], ![34, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-1, 1, 0], ![0, -1, 6], ![258, 36, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![123, 0, 0]], ![![2, -1, 0], ![42, 0, 0]], ![![2, -1, -1], ![48, 7, 0]]]
  g := ![![![1, 0, 0], ![-40, 41, 0], ![-34, 0, 41]], ![![-1, 1, 0], ![-4, -1, 6], ![-28, 36, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-20, 1, 0]] ![![41, 0, 0], ![-20, 1, 0]]
  ![![41, 0, 0], ![-29, 7, 1]] where
 M := ![![![1681, 0, 0], ![-820, 41, 0]], ![![-820, 41, 0], ![400, -40, 6]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![9, -6, -1], ![41, 0, 0]]], ![![![9, -6, -1], ![41, 0, 0]], ![![14, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-29, 7, 1]] ![![41, 0, 0], ![-1, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-41, 41, 0]], ![![-1189, 287, 41], ![287, 0, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-1, 1, 0]]], ![![![-29, 7, 1]], ![![7, 0, 1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![0, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![0, 1, 0]] 
 ![![43, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![0, 0, 6], ![258, 36, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -5], ![0, 36, 0]]]
  g := ![![![1, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![0, 0, 6], ![6, 36, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2178541, 428790, 147391]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![2178541, 428790, 147391]] 
 ![![43, 0, 0], ![1, 1, 0], ![7, 0, 1]] where
  M :=![![![2178541, 428790, 147391], ![38026878, 7484617, 2572740], ![110627820, 21774253, 7484617]]]
  hmulB := by decide  
  f := ![![![-26531, 493, 353]], ![![1501, -310, 77]], ![![-1361, 846, -264]]]
  g := ![![![16698, 428790, 147391], ![291467, 7484617, 2572740], ![847936, 21774253, 7484617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-1, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-1, 1, 0]] 
 ![![43, 0, 0], ![42, 1, 0], ![7, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-1, 1, 0], ![0, -1, 6], ![258, 36, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![129, 0, 0]], ![![2, -1, 0], ![44, 0, 0]], ![![2, -1, -5], ![79, 36, 0]]]
  g := ![![![1, 0, 0], ![-42, 43, 0], ![-7, 0, 43]], ![![-1, 1, 0], ![0, -1, 6], ![-29, 36, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![0, 1, 0]] ![![2178541, 428790, 147391]]
  ![![43, 0, 0], ![-43, -7, 1]] where
 M := ![![![93677263, 18437970, 6337813]], ![![38026878, 7484617, 2572740]]]
 hmul := by decide  
 g := ![![![![1071076, 248505, 173146], ![-1107465, 0, 0]]], ![![![434788, 100877, 70286], ![-449558, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-43, -7, 1]] ![![43, 0, 0], ![-1, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-43, 43, 0]], ![![-1849, -301, 43], ![301, 0, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-1, 1, 0]]], ![![![-43, -7, 1]], ![![7, 0, -1]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [12, 22, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 7, 42], [31, 39, 5], [0, 1]]
 g := ![![[24], [37, 7, 12], [20, 45, 6], [39, 25, 1], []], ![[17, 40, 16, 8], [45, 21, 24, 14], [18, 35, 26, 16], [22, 29, 34, 9], [38, 25]], ![[43, 20, 17, 39], [1, 35, 17, 19], [41, 22, 42, 44], [0, 32, 0, 10], [28, 25]]]
 h' := ![![[41, 7, 42], [26, 20], [42, 11, 23], [2, 17, 37], [0, 0, 1], [0, 1]], ![[31, 39, 5], [0, 46, 41], [45, 29, 43], [11, 5, 42], [3, 2, 39], [41, 7, 42]], ![[0, 1], [35, 28, 6], [0, 7, 28], [13, 25, 15], [14, 45, 7], [31, 39, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 17], []]
 b := ![[], [29, 29, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [12, 22, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-273211, 20351, 35391]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5813, 433, 753]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [34, 38, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 14, 36], [24, 38, 17], [0, 1]]
 g := ![![[49, 9, 11], [8, 4], [28, 30, 28], [31, 1], [1]], ![[24, 17, 41, 25], [28, 36], [26, 14, 16, 28], [30, 25], [1, 0, 17, 16]], ![[35, 49, 31, 6], [34, 11], [30, 52, 17, 6], [6, 16], [25, 48, 17, 37]]]
 h' := ![![[30, 14, 36], [50, 33, 8], [2, 52, 51], [49, 47, 44], [19, 15, 1], [0, 1]], ![[24, 38, 17], [9, 50, 8], [31, 36, 47], [2, 35, 25], [42, 26, 48], [30, 14, 36]], ![[0, 1], [1, 23, 37], [16, 18, 8], [23, 24, 37], [42, 12, 4], [24, 38, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 18], []]
 b := ![[], [34, 10, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [34, 38, 52, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39008, 9964, -12720]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![736, 188, -240]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-3, 25, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-3, 25, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![56, 25, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-3, 25, 1], ![258, 33, 150], ![6450, 943, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -25, 59]], ![![-1, 0, 1], ![-138, -63, 150], ![78, 2, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [40, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 58], [0, 1]]
 g := ![![[14, 9], [5, 20], [35], [44, 35], [30, 1]], ![[48, 50], [15, 39], [35], [32, 24], [1, 58]]]
 h' := ![![[30, 58], [36, 3], [57, 16], [10, 25], [39, 34], [0, 1]], ![[0, 1], [8, 56], [6, 43], [52, 34], [56, 25], [30, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [12, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [40, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1478, 202, 237]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-250, -97, 237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![27, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![27, 1, 0]] 
 ![![59, 0, 0], ![27, 1, 0], ![26, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![27, 1, 0], ![0, 27, 6], ![258, 36, 27]]]
  hmulB := by decide  
  f := ![![![514, 19, 0], ![-1121, 0, 0]], ![![216, 8, 0], ![-471, 0, 0]], ![![178, 2, -1], ![-388, 10, 0]]]
  g := ![![![1, 0, 0], ![-27, 59, 0], ![-26, 0, 59]], ![![0, 1, 0], ![-15, 27, 6], ![-24, 36, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-3, 25, 1]] ![![59, 0, 0], ![27, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1593, 59, 0]], ![![-177, 1475, 59], ![177, 708, 177]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![27, 1, 0]]], ![![![-3, 25, 1]], ![![3, 12, 3]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-311, 12, 2]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-311, 12, 2]] 
 ![![61, 0, 0], ![0, 61, 0], ![58, 6, 1]] where
  M :=![![![-311, 12, 2], ![516, -239, 72], ![3096, 518, -239]]]
  hmulB := by decide  
  f := ![![![325, 64, 22]], ![![5676, 1117, 384]], ![![1138, 224, 77]]]
  g := ![![![-7, 0, 2], ![-60, -11, 72], ![278, 32, -239]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [38, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 60], [0, 1]]
 g := ![![[37, 47], [12], [3, 15], [15, 48], [58, 1]], ![[18, 14], [12], [19, 46], [54, 13], [55, 60]]]
 h' := ![![[58, 60], [35, 13], [8, 45], [40, 25], [53, 32], [0, 1]], ![[0, 1], [57, 48], [56, 16], [26, 36], [18, 29], [58, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [35, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [38, 3, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![554, 112, 39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -2, 39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-325, -64, -22]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-325, -64, -22]] 
 ![![61, 0, 0], ![25, 1, 0], ![28, 0, 1]] where
  M :=![![![-325, -64, -22], ![-5676, -1117, -384], ![-16512, -3250, -1117]]]
  hmulB := by decide  
  f := ![![![311, -12, -2]], ![![119, -1, -2]], ![![92, -14, 3]]]
  g := ![![![31, -64, -22], ![541, -1117, -384], ![1574, -3250, -1117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-311, 12, 2]] ![![-325, -64, -22]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-12, 2, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-12, 2, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![55, 2, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-12, 2, 1], ![258, 24, 12], ![516, 115, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -2, 67]], ![![-1, 0, 1], ![-6, 0, 12], ![-12, 1, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [25, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 66], [0, 1]]
 g := ![![[50, 59], [10, 56], [55], [37], [60], [1]], ![[0, 8], [25, 11], [55], [37], [60], [1]]]
 h' := ![![[23, 66], [18, 40], [2, 49], [29, 16], [63, 29], [42, 23], [0, 1]], ![[0, 1], [0, 27], [57, 18], [62, 51], [60, 38], [35, 44], [23, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [48, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [25, 44, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9874, 2285, 2248]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1698, -33, 2248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-12, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-12, 1, 0]] 
 ![![67, 0, 0], ![55, 1, 0], ![43, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-12, 1, 0], ![0, -12, 6], ![258, 36, -12]]]
  hmulB := by decide  
  f := ![![![409, -34, 0], ![2278, 0, 0]], ![![349, -29, 0], ![1944, 0, 0]], ![![265, -12, -5], ![1476, 56, 0]]]
  g := ![![![1, 0, 0], ![-55, 67, 0], ![-43, 0, 67]], ![![-1, 1, 0], ![6, -12, 6], ![-18, 36, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-12, 2, 1]] ![![67, 0, 0], ![-12, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-804, 67, 0]], ![![-804, 134, 67], ![402, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-12, 1, 0]]], ![![![-12, 2, 1]], ![![6, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-35, 15, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-35, 15, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![36, 15, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-35, 15, 1], ![258, 1, 90], ![3870, 583, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -15, 71]], ![![-1, 0, 1], ![-42, -19, 90], ![54, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [25, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 70], [0, 1]]
 g := ![![[62, 54], [16, 15], [8, 5], [64], [2], [1]], ![[0, 17], [54, 56], [68, 66], [64], [2], [1]]]
 h' := ![![[12, 70], [26, 57], [13, 21], [11, 17], [7, 63], [46, 12], [0, 1]], ![[0, 1], [0, 14], [52, 50], [2, 54], [53, 8], [48, 59], [12, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [39, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [25, 59, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1581, -2, 33]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, -7, 33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-19, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-19, 1, 0]] 
 ![![71, 0, 0], ![52, 1, 0], ![70, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-19, 1, 0], ![0, -19, 6], ![258, 36, -19]]]
  hmulB := by decide  
  f := ![![![400, -21, 0], ![1491, 0, 0]], ![![324, -17, 0], ![1208, 0, 0]], ![![404, -18, -1], ![1506, 12, 0]]]
  g := ![![![1, 0, 0], ![-52, 71, 0], ![-70, 0, 71]], ![![-1, 1, 0], ![8, -19, 6], ![-4, 36, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-35, 15, 1]] ![![71, 0, 0], ![-19, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1349, 71, 0]], ![![-2485, 1065, 71], ![923, -284, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-19, 1, 0]]], ![![![-35, 15, 1]], ![![13, -4, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-30, 1, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-30, 1, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![43, 1, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-30, 1, 1], ![258, 6, 6], ![258, 79, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -1, 73]], ![![-1, 0, 1], ![0, 0, 6], ![0, 1, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [57, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 72], [0, 1]]
 g := ![![[17, 41], [36], [6], [39, 19], [35], [1]], ![[0, 32], [36], [6], [24, 54], [35], [1]]]
 h' := ![![[53, 72], [62, 25], [17, 67], [40, 58], [13, 47], [16, 53], [0, 1]], ![[0, 1], [0, 48], [64, 6], [48, 15], [22, 26], [51, 20], [53, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [61, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [57, 20, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1089, 336, 190]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-97, 2, 190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-6, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-6, 1, 0]] 
 ![![73, 0, 0], ![67, 1, 0], ![67, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-6, 1, 0], ![0, -6, 6], ![258, 36, -6]]]
  hmulB := by decide  
  f := ![![![379, -63, 0], ![4599, 0, 0]], ![![349, -58, 0], ![4235, 0, 0]], ![![349, -53, -5], ![4235, 61, 0]]]
  g := ![![![1, 0, 0], ![-67, 73, 0], ![-67, 0, 73]], ![![-1, 1, 0], ![0, -6, 6], ![-24, 36, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-30, 1, 1]] ![![73, 0, 0], ![-6, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-438, 73, 0]], ![![-2190, 73, 73], ![438, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-6, 1, 0]]], ![![![-30, 1, 1]], ![![6, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [1, 47, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 29, 52], [3, 49, 27], [0, 1]]
 g := ![![[11], [54, 34, 44], [49, 54, 2], [44, 10, 52], [71, 1], []], ![[3, 14, 33, 26], [5, 57, 14, 52], [0, 64, 49, 23], [64, 43, 78, 32], [46, 31], [28, 18]], ![[35, 4, 5, 53], [3, 36, 4, 12], [19, 37, 5, 34], [65, 19, 67, 77], [50, 51], [53, 18]]]
 h' := ![![[68, 29, 52], [25, 66], [30, 53, 26], [35, 40, 70], [8, 59, 17], [0, 0, 1], [0, 1]], ![[3, 49, 27], [10, 18, 35], [48, 35, 1], [22, 27, 59], [71, 24, 30], [14, 3, 49], [68, 29, 52]], ![[0, 1], [65, 74, 44], [72, 70, 52], [77, 12, 29], [69, 75, 32], [35, 76, 29], [3, 49, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 10], []]
 b := ![[], [14, 74, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [1, 47, 8, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2718153, -210614, 119606]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34407, -2666, 1514]
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



lemma PB233I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB233I1 : PrimesBelowBoundCertificateInterval O 31 79 233 where
  m := 11
  g := ![2, 3, 3, 1, 1, 2, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB233I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0]
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
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![148877]
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
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
  β := ![I37N1, I41N0, I41N1, I43N0, I43N1, I43N2, I59N1, I61N1, I67N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N0, I41N0, I41N1], [I43N0, I43N1, I43N2], [], [], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
