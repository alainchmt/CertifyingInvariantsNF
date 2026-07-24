
import IdealArithmetic.Examples.NF3_1_410700_2.RI3_1_410700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![22, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![0, 13, 3], ![201, 41, 12]]]
  hmulB := by decide  
  f := ![![![265, 22, 0], ![-814, 0, 0]], ![![84, 7, 0], ![-258, 0, 0]], ![![142, 3, -2], ![-436, 25, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-22, 0, 37]], ![![0, 1, 0], ![-6, 13, 3], ![-15, 41, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![12, 1, 0]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0], ![-26, -4, 1]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![444, 37, 0], ![144, 25, 3]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![12, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![6, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-26, -4, 1]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![-962, -148, 37], ![-111, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![12, 1, 0]]], ![![![-26, -4, 1]], ![![-3, -1, 0]]]]
 hle2 := by decide  

def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-39, 13, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-39, 13, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![2, 13, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-39, 13, 1], ![201, 15, 39], ![2546, 600, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -13, 41]], ![![-1, 0, 1], ![3, -12, 39], ![62, 14, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [15, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 40], [0, 1]]
 g := ![![[38, 37], [10], [8], [26, 16], [1]], ![[22, 4], [10], [8], [8, 25], [1]]]
 h' := ![![[4, 40], [22, 18], [34, 25], [20, 7], [26, 4], [0, 1]], ![[0, 1], [12, 23], [11, 16], [7, 34], [1, 37], [4, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [26, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [15, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2360, 2425, 852]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, -211, 852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![2, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![2, 1, 0]] 
 ![![41, 0, 0], ![2, 1, 0], ![39, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![2, 1, 0], ![0, 3, 3], ![201, 41, 2]]]
  hmulB := by decide  
  f := ![![![39, 19, 0], ![-779, 0, 0]], ![![-2, -1, 0], ![42, 0, 0]], ![![37, 17, -1], ![-739, 14, 0]]]
  g := ![![![1, 0, 0], ![-2, 41, 0], ![-39, 0, 41]], ![![0, 1, 0], ![-3, 3, 3], ![1, 41, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-39, 13, 1]] ![![41, 0, 0], ![2, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![82, 41, 0]], ![![-1599, 533, 41], ![123, 41, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![2, 1, 0]]], ![![![-39, 13, 1]], ![![3, 1, 1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, 1, 0]] 
 ![![43, 0, 0], ![10, 1, 0], ![35, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, 1, 0], ![0, 11, 3], ![201, 41, 10]]]
  hmulB := by decide  
  f := ![![![111, 11, 0], ![-473, 0, 0]], ![![10, 1, 0], ![-42, 0, 0]], ![![95, 2, -2], ![-405, 29, 0]]]
  g := ![![![1, 0, 0], ![-10, 43, 0], ![-35, 0, 43]], ![![0, 1, 0], ![-5, 11, 3], ![-13, 41, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-6, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-6, 1, 0]] 
 ![![43, 0, 0], ![37, 1, 0], ![33, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-6, 1, 0], ![0, -5, 3], ![201, 41, -6]]]
  hmulB := by decide  
  f := ![![![229, -38, 0], ![1634, 0, 0]], ![![199, -33, 0], ![1420, 0, 0]], ![![171, -25, -2], ![1220, 29, 0]]]
  g := ![![![1, 0, 0], ![-37, 43, 0], ![-33, 0, 43]], ![![-1, 1, 0], ![2, -5, 3], ![-26, 41, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-5, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-5, 1, 0]] 
 ![![43, 0, 0], ![38, 1, 0], ![22, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-5, 1, 0], ![0, -4, 3], ![201, 41, -5]]]
  hmulB := by decide  
  f := ![![![141, -28, 0], ![1204, 0, 0]], ![![126, -25, 0], ![1076, 0, 0]], ![![74, -12, -2], ![632, 29, 0]]]
  g := ![![![1, 0, 0], ![-38, 43, 0], ![-22, 0, 43]], ![![-1, 1, 0], ![2, -4, 3], ![-29, 41, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![10, 1, 0]] ![![43, 0, 0], ![-6, 1, 0]]
  ![![43, 0, 0], ![-20, 16, 1]] where
 M := ![![![1849, 0, 0], ![-258, 43, 0]], ![![430, 43, 0], ![-60, 5, 3]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![14, -15, -1], ![43, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![0, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-20, 16, 1]] ![![43, 0, 0], ![-5, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-215, 43, 0]], ![![-860, 688, 43], ![301, -43, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-5, 1, 0]]], ![![![-20, 16, 1]], ![![7, -1, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-8, 21, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-8, 21, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![39, 21, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-8, 21, 1], ![201, 54, 63], ![4154, 928, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -21, 47]], ![![-1, 0, 1], ![-48, -27, 63], ![61, 5, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [36, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 46], [0, 1]]
 g := ![![[25, 17], [35, 37], [35, 9], [20, 2], [1]], ![[0, 30], [11, 10], [19, 38], [6, 45], [1]]]
 h' := ![![[40, 46], [9, 8], [9, 32], [32, 3], [11, 40], [0, 1]], ![[0, 1], [0, 39], [20, 15], [11, 44], [13, 7], [40, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [7, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [36, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![365, 2091, 1053]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-866, -426, 1053]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-16, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-16, 1, 0]] 
 ![![47, 0, 0], ![31, 1, 0], ![14, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-16, 1, 0], ![0, -15, 3], ![201, 41, -16]]]
  hmulB := by decide  
  f := ![![![241, -15, 0], ![705, 0, 0]], ![![161, -10, 0], ![471, 0, 0]], ![![82, 0, -1], ![240, 16, 0]]]
  g := ![![![1, 0, 0], ![-31, 47, 0], ![-14, 0, 47]], ![![-1, 1, 0], ![9, -15, 3], ![-18, 41, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-8, 21, 1]] ![![47, 0, 0], ![-16, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-752, 47, 0]], ![![-376, 987, 47], ![329, -282, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-16, 1, 0]]], ![![![-8, 21, 1]], ![![7, -6, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-39, 1, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-39, 1, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![14, 1, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-39, 1, 1], ![201, 3, 3], ![134, 108, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -1, 53]], ![![-1, 0, 1], ![3, 0, 3], ![2, 2, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [45, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 52], [0, 1]]
 g := ![![[27, 11], [10], [8, 46], [46], [4, 1]], ![[18, 42], [10], [33, 7], [46], [8, 52]]]
 h' := ![![[4, 52], [42, 8], [11, 13], [14, 24], [32, 24], [0, 1]], ![[0, 1], [21, 45], [10, 40], [4, 29], [22, 29], [4, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [31, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [45, 49, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![938, 67, 120]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -1, 120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-3, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-3, 1, 0]] 
 ![![53, 0, 0], ![50, 1, 0], ![51, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-3, 1, 0], ![0, -2, 3], ![201, 41, -3]]]
  hmulB := by decide  
  f := ![![![61, -20, 0], ![1060, 0, 0]], ![![58, -19, 0], ![1008, 0, 0]], ![![57, -18, -1], ![990, 18, 0]]]
  g := ![![![1, 0, 0], ![-50, 53, 0], ![-51, 0, 53]], ![![-1, 1, 0], ![-1, -2, 3], ![-32, 41, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-39, 1, 1]] ![![53, 0, 0], ![-3, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-159, 53, 0]], ![![-2067, 53, 53], ![318, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-3, 1, 0]]], ![![![-39, 1, 1]], ![![6, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-17, 3, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-17, 3, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![42, 3, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-17, 3, 1], ![201, 27, 9], ![536, 190, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -3, 59]], ![![-1, 0, 1], ![-3, 0, 9], ![-8, 2, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [56, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 58], [0, 1]]
 g := ![![[28, 19], [1, 27], [12], [28, 28], [25, 1]], ![[31, 40], [27, 32], [12], [20, 31], [50, 58]]]
 h' := ![![[25, 58], [3, 14], [12, 26], [25, 37], [16, 38], [0, 1]], ![[0, 1], [58, 45], [13, 33], [6, 22], [22, 21], [25, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [52, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [56, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2436, 4363, 1769]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1218, -16, 1769]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-9, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-9, 1, 0]] 
 ![![59, 0, 0], ![50, 1, 0], ![35, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-9, 1, 0], ![0, -8, 3], ![201, 41, -9]]]
  hmulB := by decide  
  f := ![![![451, -50, 0], ![2950, 0, 0]], ![![370, -41, 0], ![2420, 0, 0]], ![![259, -26, -1], ![1694, 20, 0]]]
  g := ![![![1, 0, 0], ![-50, 59, 0], ![-35, 0, 59]], ![![-1, 1, 0], ![5, -8, 3], ![-26, 41, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-17, 3, 1]] ![![59, 0, 0], ![-9, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-531, 59, 0]], ![![-1003, 177, 59], ![354, 0, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-9, 1, 0]]], ![![![-17, 3, 1]], ![![6, 0, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [42, 12, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 10, 41], [1, 50, 20], [0, 1]]
 g := ![![[20, 48, 52], [1, 5], [33, 56, 4], [51, 26, 42], [1]], ![[3, 7, 56, 3], [50, 27], [33, 40, 26, 42], [57, 56, 35, 45], [44, 27, 31, 52]], ![[0, 45, 37, 56], [49, 60], [32, 49], [49, 16, 22, 45], [43, 13, 50, 9]]]
 h' := ![![[14, 10, 41], [3, 0, 28], [17, 46, 35], [54, 60, 2], [19, 49, 15], [0, 1]], ![[1, 50, 20], [22, 9, 58], [29, 29, 37], [37, 56, 59], [42, 9, 14], [14, 10, 41]], ![[0, 1], [0, 52, 36], [44, 47, 50], [31, 6], [25, 3, 32], [1, 50, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 3], []]
 b := ![[], [13, 38, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [42, 12, 46, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2473062, -839482, -191662]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40542, -13762, -3142]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![0, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![0, 1, 0]] 
 ![![67, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![0, 1, 0], ![0, 1, 3], ![201, 41, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -2], ![22, 45, 0]]]
  g := ![![![1, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![0, 1, 0], ![0, 1, 3], ![3, 41, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![7, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![7, 1, 0]] 
 ![![67, 0, 0], ![7, 1, 0], ![26, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![7, 1, 0], ![0, 8, 3], ![201, 41, 7]]]
  hmulB := by decide  
  f := ![![![281, 40, 0], ![-2680, 0, 0]], ![![21, 3, 0], ![-200, 0, 0]], ![![108, 10, -2], ![-1030, 45, 0]]]
  g := ![![![1, 0, 0], ![-7, 67, 0], ![-26, 0, 67]], ![![0, 1, 0], ![-2, 8, 3], ![-4, 41, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-8, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-8, 1, 0]] 
 ![![67, 0, 0], ![59, 1, 0], ![26, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-8, 1, 0], ![0, -7, 3], ![201, 41, -8]]]
  hmulB := by decide  
  f := ![![![369, -46, 0], ![3082, 0, 0]], ![![329, -41, 0], ![2748, 0, 0]], ![![158, -15, -2], ![1320, 45, 0]]]
  g := ![![![1, 0, 0], ![-59, 67, 0], ![-26, 0, 67]], ![![-1, 1, 0], ![5, -7, 3], ![-30, 41, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![0, 1, 0]] ![![67, 0, 0], ![7, 1, 0]]
  ![![67, 0, 0], ![0, 25, 1]] where
 M := ![![![4489, 0, 0], ![469, 67, 0]], ![![0, 67, 0], ![0, 8, 3]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![7, -24, -1], ![67, 0, 0]]], ![![![0, -24, -1], ![67, 0, 0]], ![![0, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![0, 25, 1]] ![![67, 0, 0], ![-8, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-536, 67, 0]], ![![0, 1675, 67], ![201, -134, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-8, 1, 0]]], ![![![0, 25, 1]], ![![3, -2, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-44, 13, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-44, 13, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![27, 13, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-44, 13, 1], ![201, 10, 39], ![2546, 600, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -13, 71]], ![![-1, 0, 1], ![-12, -7, 39], ![37, 9, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [45, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 70], [0, 1]]
 g := ![![[53, 30], [8, 54], [16, 60], [40], [60], [1]], ![[0, 41], [12, 17], [52, 11], [40], [60], [1]]]
 h' := ![![[29, 70], [66, 32], [61, 14], [64, 42], [35, 53], [26, 29], [0, 1]], ![[0, 1], [0, 39], [41, 57], [4, 29], [10, 18], [15, 42], [29, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [11, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [45, 42, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![217101, 181147, 71925]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24294, -10618, 71925]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![32, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![32, 1, 0]] 
 ![![71, 0, 0], ![32, 1, 0], ![3, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![32, 1, 0], ![0, 33, 3], ![201, 41, 32]]]
  hmulB := by decide  
  f := ![![![385, 12, 0], ![-852, 0, 0]], ![![160, 5, 0], ![-354, 0, 0]], ![![-27, -12, -1], ![60, 24, 0]]]
  g := ![![![1, 0, 0], ![-32, 71, 0], ![-3, 0, 71]], ![![0, 1, 0], ![-15, 33, 3], ![-17, 41, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-44, 13, 1]] ![![71, 0, 0], ![32, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2272, 71, 0]], ![![-3124, 923, 71], ![-1207, 426, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![32, 1, 0]]], ![![![-44, 13, 1]], ![![-17, 6, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [54, 60, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 0, 32], [35, 72, 41], [0, 1]]
 g := ![![[61, 26, 54], [2, 3], [19, 48], [36, 51, 2], [26, 1], []], ![[16, 14, 9, 55], [11, 64], [54, 67], [0, 66, 62, 1], [58, 1], [52, 2]], ![[61, 41, 45, 49], [17, 38], [2, 38], [42, 23, 33, 65], [], [43, 2]]]
 h' := ![![[64, 0, 32], [63, 51, 28], [68, 47, 52], [27, 47, 11], [56, 65, 32], [0, 0, 1], [0, 1]], ![[35, 72, 41], [44, 63, 71], [45, 44, 65], [48, 43, 33], [26, 72, 4], [47, 57, 72], [64, 0, 32]], ![[0, 1], [40, 32, 47], [3, 55, 29], [44, 56, 29], [4, 9, 37], [71, 16], [35, 72, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 2], []]
 b := ![[], [48, 43, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [54, 60, 47, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![818914, 297110, 75555]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11218, 4070, 1035]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [6, 28, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 62, 7], [66, 16, 72], [0, 1]]
 g := ![![[46, 4, 21], [74, 73, 16], [20, 5, 1], [70, 7, 21], [27, 1], []], ![[1, 58, 64, 75], [76, 22, 32, 69], [23, 77, 41, 56], [0, 25, 1, 66], [55, 19], [58, 49]], ![[65, 78, 75, 67], [32, 32, 60, 1], [2, 60, 13, 1], [19, 25, 70, 8], [78, 52], [72, 49]]]
 h' := ![![[40, 62, 7], [30, 40, 69], [38, 35, 75], [54, 68, 1], [75, 28, 69], [0, 0, 1], [0, 1]], ![[66, 16, 72], [12, 26, 41], [64, 35, 23], [76, 69, 18], [51, 72, 36], [67, 40, 16], [40, 62, 7]], ![[0, 1], [7, 13, 48], [3, 9, 60], [13, 21, 60], [50, 58, 53], [53, 39, 62], [66, 16, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 5], []]
 b := ![[], [50, 68, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [6, 28, 52, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10530463, 4162668, 1106869]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![133297, 52692, 14011]
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



lemma PB182I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB182I1 : PrimesBelowBoundCertificateInterval O 31 79 182 where
  m := 11
  g := ![3, 2, 3, 2, 2, 2, 1, 3, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB182I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N0
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I41N1, I43N0, I43N1, I43N2, I47N1, I53N1, I59N1, I67N0, I67N1, I67N2, I71N1]
  Il := ![[I37N0, I37N0, I37N0], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [I59N1], [], [I67N0, I67N1, I67N2], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
