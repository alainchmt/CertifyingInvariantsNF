
import IdealArithmetic.Examples.NF3_1_796835_2.RI3_1_796835_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [14, 31, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 29, 20], [26, 7, 17], [0, 1]]
 g := ![![[5, 26, 30], [29, 16], [5, 8, 28], [30, 1], []], ![[16, 25, 24, 20], [22, 27], [22, 13, 12, 19], [13, 12], [25, 30]], ![[22, 19, 14, 32], [19, 16], [3, 8, 9, 2], [17, 27], [28, 30]]]
 h' := ![![[4, 29, 20], [17, 17, 20], [4, 13, 4], [24, 18, 18], [0, 0, 1], [0, 1]], ![[26, 7, 17], [28, 29, 36], [15, 3, 29], [4, 23, 5], [36, 36, 7], [4, 29, 20]], ![[0, 1], [34, 28, 18], [35, 21, 4], [17, 33, 14], [25, 1, 29], [26, 7, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 29], []]
 b := ![[], [32, 19, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [14, 31, 7, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10209151, -2713617, -997335]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-275923, -73341, -26955]
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


def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![7, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![7, 1, 0]] 
 ![![41, 0, 0], ![7, 1, 0], ![10, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![7, 1, 0], ![3, 11, 9], ![-141, -20, 4]]]
  hmulB := by decide  
  f := ![![![-107, -396, -324], ![0, 1476, 0]], ![![-18, -66, -54], ![1, 246, 0]], ![![-29, -97, -79], ![17, 360, 0]]]
  g := ![![![1, 0, 0], ![-7, 41, 0], ![-10, 0, 41]], ![![0, 1, 0], ![-4, 11, 9], ![-1, -20, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-4, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-4, 1, 0]] 
 ![![41, 0, 0], ![37, 1, 0], ![14, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-4, 1, 0], ![3, 0, 9], ![-141, -20, -7]]]
  hmulB := by decide  
  f := ![![![-771, -2, -2340], ![82, 10660, 0]], ![![-693, -2, -2106], ![83, 9594, 0]], ![![-262, -1, -799], ![41, 3640, 0]]]
  g := ![![![1, 0, 0], ![-37, 41, 0], ![-14, 0, 41]], ![![-1, 1, 0], ![-3, 0, 9], ![17, -20, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![7, 1, 0]] ![![41, 0, 0], ![-4, 1, 0]]
  ![![41, 0, 0], ![20, 19, 1]] where
 M := ![![![1681, 0, 0], ![-164, 41, 0]], ![![287, 41, 0], ![-25, 7, 9]]]
 hmul := by decide  
 g := ![![![![21, -19, -1], ![41, 0, 0]], ![![-4, 1, 0], ![0, 0, 0]]], ![![![-13, -18, -1], ![41, 0, 0]], ![![-5, -4, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![20, 19, 1]] ![![41, 0, 0], ![-4, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-164, 41, 0]], ![![820, 779, 41], ![-164, 0, 164]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-4, 1, 0]]], ![![![20, 19, 1]], ![![-4, 0, 4]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-21, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-21, 1, 0]] 
 ![![43, 0, 0], ![22, 1, 0], ![18, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-21, 1, 0], ![3, -17, 9], ![-141, -20, -24]]]
  hmulB := by decide  
  f := ![![![-47, 508, -270], ![86, 1290, 0]], ![![-23, 254, -135], ![44, 645, 0]], ![![-27, 213, -113], ![21, 540, 0]]]
  g := ![![![1, 0, 0], ![-22, 43, 0], ![-18, 0, 43]], ![![-1, 1, 0], ![5, -17, 9], ![17, -20, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-16, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-16, 1, 0]] 
 ![![43, 0, 0], ![27, 1, 0], ![22, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-16, 1, 0], ![3, -12, 9], ![-141, -20, -19]]]
  hmulB := by decide  
  f := ![![![-111, 574, -432], ![86, 2064, 0]], ![![-73, 359, -270], ![44, 1290, 0]], ![![-62, 294, -221], ![30, 1056, 0]]]
  g := ![![![1, 0, 0], ![-27, 43, 0], ![-22, 0, 43]], ![![-1, 1, 0], ![3, -12, 9], ![19, -20, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-7, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-7, 1, 0]] 
 ![![43, 0, 0], ![36, 1, 0], ![41, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-7, 1, 0], ![3, -3, 9], ![-141, -20, -10]]]
  hmulB := by decide  
  f := ![![![-709, 734, -2214], ![172, 10578, 0]], ![![-593, 612, -1845], ![130, 8815, 0]], ![![-677, 700, -2111], ![158, 10086, 0]]]
  g := ![![![1, 0, 0], ![-36, 43, 0], ![-41, 0, 43]], ![![-1, 1, 0], ![-6, -3, 9], ![23, -20, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-21, 1, 0]] ![![43, 0, 0], ![-16, 1, 0]]
  ![![43, 0, 0], ![9, -18, 1]] where
 M := ![![![1849, 0, 0], ![-688, 43, 0]], ![![-903, 43, 0], ![339, -33, 9]]]
 hmul := by decide  
 g := ![![![![34, 18, -1], ![43, 0, 0]], ![![-16, 1, 0], ![0, 0, 0]]], ![![![-21, 1, 0], ![0, 0, 0]], ![![6, 3, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![9, -18, 1]] ![![43, 0, 0], ![-7, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-301, 43, 0]], ![![387, -774, 43], ![-258, 43, -172]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-7, 1, 0]]], ![![![9, -18, 1]], ![![-6, 1, -4]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [31, 1, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 24, 4], [2, 22, 43], [0, 1]]
 g := ![![[20, 13, 8], [34, 46, 3], [27, 44, 21], [1, 40, 1], []], ![[20, 28, 22, 42], [33, 35, 20, 4], [31, 24, 37, 3], [9, 7, 8, 9], [33, 16]], ![[22, 10, 33, 46], [18, 5, 30, 29], [21, 25, 38, 23], [6, 38, 46, 46], [41, 16]]]
 h' := ![![[38, 24, 4], [27, 31, 14], [9, 40, 12], [16, 28, 16], [0, 0, 1], [0, 1]], ![[2, 22, 43], [2, 27, 9], [1, 3, 1], [14, 7, 41], [45, 26, 22], [38, 24, 4]], ![[0, 1], [23, 36, 24], [19, 4, 34], [10, 12, 37], [2, 21, 24], [2, 22, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 26], []]
 b := ![[], [46, 27, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [31, 1, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5261039, 1580845, 703825]
  a := ![4, 5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![111937, 33635, 14975]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1436913, -20876, 61342]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![1436913, -20876, 61342]] 
 ![![53, 0, 0], ![0, 53, 0], ![9, 23, 1]] where
  M :=![![![1436913, -20876, 61342], ![-8711850, 126569, -371910], ![9261742, -134558, 395385]]]
  hmulB := by decide  
  f := ![![![345, 8, -46]], ![![6510, 1297, 210]], ![![2773, 569, 105]]]
  g := ![![![16695, -27014, 61342], ![-101220, 163783, -371910], ![107609, -174121, 395385]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [16, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 52], [0, 1]]
 g := ![![[31, 10], [6], [3, 17], [40], [34, 1]], ![[0, 43], [6], [51, 36], [40], [15, 52]]]
 h' := ![![[34, 52], [35, 13], [5, 18], [33, 21], [39, 27], [0, 1]], ![[0, 1], [0, 40], [34, 35], [5, 32], [3, 26], [34, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [11, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [16, 19, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-617966, -470934, -307422]
  a := ![-65, -65, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40544, 124524, -307422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-345, -8, 46]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-345, -8, 46]] 
 ![![53, 0, 0], ![8, 1, 0], ![25, 0, 1]] where
  M :=![![![-345, -8, 46], ![-6510, -1297, -210], ![5866, -254, -1149]]]
  hmulB := by decide  
  f := ![![![-1436913, 20876, -61342]], ![![-52518, 763, -2242]], ![![-852539, 12386, -36395]]]
  g := ![![![-27, -8, 46], ![172, -1297, -210], ![691, -254, -1149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![1436913, -20876, 61342]] ![![-345, -8, 46]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [6, 34, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 9, 18], [58, 49, 41], [0, 1]]
 g := ![![[51, 44, 7], [49, 5, 21], [21, 7], [32, 32, 26], [1]], ![[40, 45, 16, 34], [37, 4, 26, 24], [50, 48], [4, 37, 30, 2], [1, 52, 6, 50]], ![[21, 17, 22, 5], [38, 48], [6, 35], [6, 11, 13, 35], [40, 43, 25, 9]]]
 h' := ![![[48, 9, 18], [1, 22, 19], [40, 43, 27], [44, 54, 19], [53, 25, 47], [0, 1]], ![[58, 49, 41], [15, 20, 29], [55, 44, 32], [1, 13, 15], [20, 30, 39], [48, 9, 18]], ![[0, 1], [46, 17, 11], [27, 31], [57, 51, 25], [54, 4, 32], [58, 49, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 28], []]
 b := ![[], [28, 50, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [6, 34, 12, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18390477, -5321092, -2219816]
  a := ![-6, -8, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-311703, -90188, -37624]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![1, -23, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![1, -23, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![1, 38, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![1, -23, 1], ![-210, -111, -210], ![3346, 451, 52]]]
  hmulB := by decide  
  f := ![![![0, 23, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -38, 61]], ![![0, -1, 1], ![0, 129, -210], ![54, -25, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [11, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 60], [0, 1]]
 g := ![![[18, 48], [56], [22, 49], [24, 46], [46, 1]], ![[30, 13], [56], [19, 12], [5, 15], [31, 60]]]
 h' := ![![[46, 60], [59, 29], [2, 19], [41, 7], [43, 31], [0, 1]], ![[0, 1], [51, 32], [22, 42], [58, 54], [5, 30], [46, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [38, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [11, 15, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6327, -6064, -4314]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, 2588, -4314]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![27, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![27, 1, 0]] 
 ![![61, 0, 0], ![27, 1, 0], ![9, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![27, 1, 0], ![3, 31, 9], ![-141, -20, 24]]]
  hmulB := by decide  
  f := ![![![2392, 32213, 9360], ![1647, -63440, 0]], ![![1056, 14248, 4140], ![733, -28060, 0]], ![![333, 4752, 1381], ![288, -9360, 0]]]
  g := ![![![1, 0, 0], ![-27, 61, 0], ![-9, 0, 61]], ![![0, 1, 0], ![-15, 31, 9], ![3, -20, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![1, -23, 1]] ![![61, 0, 0], ![27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1647, 61, 0]], ![![61, -1403, 61], ![-183, -732, -183]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![27, 1, 0]]], ![![![1, -23, 1]], ![![-3, -12, -3]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![11, 24, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![11, 24, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![11, 24, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![11, 24, 1], ![-69, 87, 213], ![-3281, -489, -79]]]
  hmulB := by decide  
  f := ![![![-10, -24, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -24, 67]], ![![0, 0, 1], ![-36, -75, 213], ![-36, 21, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [35, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 66], [0, 1]]
 g := ![![[64, 23], [41, 47], [9], [26], [37], [1]], ![[0, 44], [18, 20], [9], [26], [37], [1]]]
 h' := ![![[38, 66], [39, 36], [49, 28], [37, 3], [64, 19], [32, 38], [0, 1]], ![[0, 1], [0, 31], [41, 39], [17, 64], [49, 48], [2, 29], [38, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [25, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [35, 29, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-561576, -428243, -279029]
  a := ![42, 62, 125]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37429, 93559, -279029]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-12, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-12, 1, 0]] 
 ![![67, 0, 0], ![55, 1, 0], ![12, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-12, 1, 0], ![3, -8, 9], ![-141, -20, -15]]]
  hmulB := by decide  
  f := ![![![1696, -4675, 5265], ![-335, -39195, 0]], ![![1393, -3836, 4320], ![-267, -32160, 0]], ![![312, -838, 943], ![-14, -7020, 0]]]
  g := ![![![1, 0, 0], ![-55, 67, 0], ![-12, 0, 67]], ![![-1, 1, 0], ![5, -8, 9], ![17, -20, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![11, 24, 1]] ![![67, 0, 0], ![-12, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-804, 67, 0]], ![![737, 1608, 67], ![-201, -201, 201]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-12, 1, 0]]], ![![![11, 24, 1]], ![![-3, -3, 3]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-3, 5, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-3, 5, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![68, 5, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-3, 5, 1], ![-126, -3, 42], ![-602, -109, -36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -5, 71]], ![![-1, 0, 1], ![-42, -3, 42], ![26, 1, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [9, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 70], [0, 1]]
 g := ![![[43, 8], [38, 50], [47, 57], [60], [30], [1]], ![[0, 63], [0, 21], [69, 14], [60], [30], [1]]]
 h' := ![![[39, 70], [13, 47], [3, 60], [36, 25], [24, 42], [62, 39], [0, 1]], ![[0, 1], [0, 24], [0, 11], [17, 46], [29, 29], [21, 32], [39, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [29, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [9, 32, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2724, -1353, -654]
  a := ![2, 4, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![588, 27, -654]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![29, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![29, 1, 0]] 
 ![![71, 0, 0], ![29, 1, 0], ![36, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![29, 1, 0], ![3, 33, 9], ![-141, -20, 26]]]
  hmulB := by decide  
  f := ![![![3895, 53328, 14553], ![2343, -114807, 0]], ![![1574, 21766, 5940], ![995, -46860, 0]], ![![1959, 27039, 7379], ![1227, -58212, 0]]]
  g := ![![![1, 0, 0], ![-29, 71, 0], ![-36, 0, 71]], ![![0, 1, 0], ![-18, 33, 9], ![-7, -20, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-3, 5, 1]] ![![71, 0, 0], ![29, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2059, 71, 0]], ![![-213, 355, 71], ![-213, 142, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![29, 1, 0]]], ![![![-3, 5, 1]], ![![-3, 2, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10122581101040705122802843586317285117551548613735, 147064582620537408528941334421005273515457410589, -432134294769546162265155866393391277452123926808]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-10122581101040705122802843586317285117551548613735, 147064582620537408528941334421005273515457410589, -432134294769546162265155866393391277452123926808]] 
 ![![73, 0, 0], ![0, 73, 0], ![37, 53, 1]] where
  M :=![![![-10122581101040705122802843586317285117551548613735, 147064582620537408528941334421005273515457410589, -432134294769546162265155866393391277452123926808], ![61372129310367621104973801164731185941295845911695, -891636875167632243383960920765438474447240435219, 2619984127893475163555939608969221293995488475725], ![-65245938510759029315891782391881045143248259354273, 947917000515167289807576109120416026759967129492, -2785357543050486427616861994499257943959690162958]]]
  hmulB := by decide  
  f := ![![![245759142117525559194026, 178948199271176174540538, 130195309807988138862999]], ![![-17820694085112799056061245, -1642354256957532519903802, 1219947864016621154275845]], ![![-12975688732049903651895808, -1166772794786453723801087, 915614551007351956857386]]]
  g := ![![![80361476786746614808327718770386193810644338057, 315755920622006630254550715798229355869561993581, -432134294769546162265155866393391277452123926808], ![-487223060571109040364328279001780848445715447810, -1914394461007148163176010413645673521317919584228, 2619984127893475163555939608969221293995488475725], ![517976583316561212410028923350568476483017488701, 2035231051810834903472620024898371055570185558442, -2785357543050486427616861994499257943959690162958]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [6, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 72], [0, 1]]
 g := ![![[55, 61], [37], [70], [47, 12], [57], [1]], ![[0, 12], [37], [70], [29, 61], [57], [1]]]
 h' := ![![[35, 72], [51, 34], [45, 16], [10, 17], [59, 42], [67, 35], [0, 1]], ![[0, 1], [0, 39], [21, 57], [21, 56], [69, 31], [51, 38], [35, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [63, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [6, 38, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14383, -14666, -9567]
  a := ![8, 11, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4652, 6745, -9567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6712672441999829123168899722, 97524175019906194378836588, -286564853646303106560471749]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-6712672441999829123168899722, 97524175019906194378836588, -286564853646303106560471749]] 
 ![![73, 0, 0], ![37, 1, 0], ![67, 0, 1]] where
  M :=![![![-6712672441999829123168899722, 97524175019906194378836588, -286564853646303106560471749], ![40698216889188456608163026373, -591278668994142214444118390, 1737412136118065069090944539], ![-43267088603375993383144549055, 628600182418604071467513981, -1847077601426091788216918004]]]
  hmulB := by decide  
  f := ![![![226350779606199, 10947101892417, -24820045628822]], ![![163115706640692, 16049080407832, -10210378552715]], ![![151582139274190, 10108139720589, -14009215916210]]]
  g := ![![![121627099678985614032407585, 97524175019906194378836588, -286564853646303106560471749], ![-737412129834775905294491470, -591278668994142214444118390, 1737412136118065069090944539], ![783957588255942544973848492, 628600182418604071467513981, -1847077601426091788216918004]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-10122581101040705122802843586317285117551548613735, 147064582620537408528941334421005273515457410589, -432134294769546162265155866393391277452123926808]] ![![-6712672441999829123168899722, 97524175019906194378836588, -286564853646303106560471749]]
  ![![73, 0, 0]] where
 M := ![![![92632030299424188718264502562615324055881264123827206548991620521957608911807, -1345792218140610434592873675757531822389162571876442638406350484179213670538, 3954473339057512036737062864465454175857161022770884225931022389797564647218]]]
 hmul := by decide  
 g := ![![![![1268931921909920393400883596748155124053168001696263103410844116739145327559, -18435509837542608693053064051473038662865240710636200526114390194235803706, 54170867658322082695028258417334988710372068805080605834671539586268008866]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [3, 1, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 59, 4], [50, 19, 75], [0, 1]]
 g := ![![[2, 53, 38], [68, 17, 36], [29, 7, 73], [54, 58, 20], [44, 1], []], ![[25, 4, 58, 11], [13, 50, 14, 44], [14, 39, 52, 64], [37, 5], [59, 45], [70, 16]], ![[54, 29, 38, 57], [4, 30, 8, 57], [77, 54, 16, 12], [56, 0, 30, 78], [44, 5], [78, 16]]]
 h' := ![![[73, 59, 4], [33, 24, 14], [71, 45, 73], [75, 53, 51], [26, 32, 39], [0, 0, 1], [0, 1]], ![[50, 19, 75], [60, 43, 46], [55, 27, 66], [47, 27, 75], [0, 10], [63, 43, 19], [73, 59, 4]], ![[0, 1], [14, 12, 19], [22, 7, 19], [28, 78, 32], [19, 37, 40], [54, 36, 59], [50, 19, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 43], []]
 b := ![[], [78, 73, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [3, 1, 35, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3370377, -896255, -321135]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42663, -11345, -4065]
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



lemma PB253I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB253I1 : PrimesBelowBoundCertificateInterval O 31 79 253 where
  m := 11
  g := ![1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB253I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
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
  β := ![I41N0, I41N1, I43N0, I43N1, I43N2, I53N1, I61N1, I67N1, I71N1, I73N1]
  Il := ![[], [I41N0, I41N1, I41N1], [I43N0, I43N1, I43N2], [], [I53N1], [], [I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
