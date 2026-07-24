
import IdealArithmetic.Examples.NF3_1_205556_1.RI3_1_205556_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![3, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![3, 1, 0]] 
 ![![37, 0, 0], ![3, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![3, 1, 0], ![0, 3, 1], ![284, 79, 3]]]
  hmulB := by decide  
  f := ![![![64, 21, 0], ![-777, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![46, 15, 0], ![-558, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-1, 3, 1], ![-1, 79, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![7, 1, 0]] 
 ![![37, 0, 0], ![7, 1, 0], ![25, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![7, 1, 0], ![0, 7, 1], ![284, 79, 7]]]
  hmulB := by decide  
  f := ![![![85, 12, 0], ![-444, 0, 0]], ![![7, 1, 0], ![-36, 0, 0]], ![![51, 7, 0], ![-266, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 37, 0], ![-25, 0, 37]], ![![0, 1, 0], ![-2, 7, 1], ![-12, 79, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-503353, -63890, 10916]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-503353, -63890, 10916]] 
 ![![37, 0, 0], ![27, 1, 0], ![11, 0, 1]] where
  M :=![![![-503353, -63890, 10916], ![3100144, 359011, -63890], ![-18144760, -1947166, 359011]]]
  hmulB := by decide  
  f := ![![![-4484462381, -1681948734, -162968024]], ![![-4523335219, -1696528435, -164380686]], ![![-14243311531, -5342116348, -517610393]]]
  g := ![![![29773, -63890, 10916], ![-159199, 359011, -63890], ![823773, -1947166, 359011]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![3, 1, 0]] ![![37, 0, 0], ![7, 1, 0]]
  ![![-4484462381, -1681948734, -162968024]] where
 M := ![![![1369, 0, 0], ![259, 37, 0]], ![![111, 37, 0], ![21, 10, 1]]]
 hmul := by decide  
 g := ![![![![-18624061, -2363930, 403892]], ![![-423327, -88219, 12522]]], ![![![1590085, 167341, -31142]], ![![61791, 8142, -1369]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-4484462381, -1681948734, -162968024]] ![![-503353, -63890, 10916]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10209, -3829, -371]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-10209, -3829, -371]] 
 ![![41, 0, 0], ![8, 1, 0], ![18, 0, 1]] where
  M :=![![![-10209, -3829, -371], ![-105364, -39518, -3829], ![-1087436, -407855, -39518]]]
  hmulB := by decide  
  f := ![![![4471, 217, -63]], ![![436, 30, -7]], ![![3466, 77, -40]]]
  g := ![![![661, -3829, -371], ![6822, -39518, -3829], ![70408, -407855, -39518]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![16, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![16, 1, 0]] 
 ![![41, 0, 0], ![16, 1, 0], ![31, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![16, 1, 0], ![0, 16, 1], ![284, 79, 16]]]
  hmulB := by decide  
  f := ![![![193, 12, 0], ![-492, 0, 0]], ![![48, 3, 0], ![-122, 0, 0]], ![![135, 8, 0], ![-344, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 41, 0], ![-31, 0, 41]], ![![0, 1, 0], ![-7, 16, 1], ![-36, 79, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![17, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![17, 1, 0]] 
 ![![41, 0, 0], ![17, 1, 0], ![39, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![17, 1, 0], ![0, 17, 1], ![284, 79, 17]]]
  hmulB := by decide  
  f := ![![![222, 13, 0], ![-533, 0, 0]], ![![102, 6, 0], ![-245, 0, 0]], ![![212, 12, 0], ![-509, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 41, 0], ![-39, 0, 41]], ![![0, 1, 0], ![-8, 17, 1], ![-42, 79, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-10209, -3829, -371]] ![![41, 0, 0], ![16, 1, 0]]
  ![![41, 0, 0], ![-36, -17, 1]] where
 M := ![![![-418569, -156989, -15211], ![-268708, -100782, -9765]]]
 hmul := by decide  
 g := ![![![![-5421, -1568, -504], ![5453, 0, 0]], ![![-3464, -999, -324], ![3519, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-36, -17, 1]] ![![41, 0, 0], ![17, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![697, 41, 0]], ![![-1476, -697, 41], ![-328, -246, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![17, 1, 0]]], ![![![-36, -17, 1]], ![![-8, -6, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-62, -24, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-62, -24, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![24, 19, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-62, -24, 1], ![284, 17, -24], ![-6816, -1612, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -19, 43]], ![![-2, -1, 1], ![20, 11, -24], ![-168, -45, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [15, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 42], [0, 1]]
 g := ![![[11, 23], [26, 40], [38], [4, 6], [1]], ![[0, 20], [5, 3], [38], [3, 37], [1]]]
 h' := ![![[7, 42], [40, 25], [20, 13], [26, 34], [28, 7], [0, 1]], ![[0, 1], [0, 18], [25, 30], [6, 9], [34, 36], [7, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [15, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [15, 36, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![583, 406, 44]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -10, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![26, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![0, -19, 1], ![284, 79, -19]]]
  hmulB := by decide  
  f := ![![![761, -40, 0], ![1720, 0, 0]], ![![438, -23, 0], ![990, 0, 0]], ![![484, -25, 0], ![1094, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-26, 0, 43]], ![![-1, 1, 0], ![10, -19, 1], ![-26, 79, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-62, -24, 1]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![-2666, -1032, 43], ![1462, 473, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-19, 1, 0]]], ![![![-62, -24, 1]], ![![34, 11, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, -17, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![69, -17, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![22, 30, 1]] where
  M :=![![![69, -17, 1], ![284, 148, -17], ![-4828, -1059, 148]]]
  hmulB := by decide  
  f := ![![![83, 31, 3]], ![![852, 320, 31]], ![![770, 289, 28]]]
  g := ![![![1, -1, 1], ![14, 14, -17], ![-172, -117, 148]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [43, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 46], [0, 1]]
 g := ![![[22, 17], [46, 21], [6, 25], [18, 36], [1]], ![[14, 30], [14, 26], [44, 22], [37, 11], [1]]]
 h' := ![![[41, 46], [43, 8], [24, 31], [25, 5], [4, 41], [0, 1]], ![[0, 1], [42, 39], [26, 16], [42, 42], [40, 6], [41, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [27, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [43, 6, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3370, 1600, 727]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-412, -430, 727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 31, 3]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![83, 31, 3]] 
 ![![47, 0, 0], ![17, 1, 0], ![40, 0, 1]] where
  M :=![![![83, 31, 3], ![852, 320, 31], ![8804, 3301, 320]]]
  hmulB := by decide  
  f := ![![![69, -17, 1]], ![![31, -3, 0]], ![![-44, -37, 4]]]
  g := ![![![-12, 31, 3], ![-124, 320, 31], ![-1279, 3301, 320]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![69, -17, 1]] ![![83, 31, 3]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![445, 166, 16]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![445, 166, 16]] 
 ![![53, 0, 0], ![0, 53, 0], ![51, 17, 1]] where
  M :=![![![445, 166, 16], ![4544, 1709, 166], ![47144, 17658, 1709]]]
  hmulB := by decide  
  f := ![![![-199, -22, 4]], ![![1136, 117, -22]], ![![55, 5, -1]]]
  g := ![![![-7, -2, 16], ![-74, -21, 166], ![-755, -215, 1709]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [1, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 52], [0, 1]]
 g := ![![[14, 1], [10], [17, 24], [24], [39, 1]], ![[0, 52], [10], [52, 29], [24], [25, 52]]]
 h' := ![![[39, 52], [14, 1], [36, 13], [13, 36], [14, 36], [0, 1]], ![[0, 1], [0, 52], [13, 40], [39, 17], [40, 17], [39, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [6, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [1, 14, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2633, 12, 194]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-137, -62, 194]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, -22, 4]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-199, -22, 4]] 
 ![![53, 0, 0], ![36, 1, 0], ![29, 0, 1]] where
  M :=![![![-199, -22, 4], ![1136, 117, -22], ![-6248, -602, 117]]]
  hmulB := by decide  
  f := ![![![445, 166, 16]], ![![388, 145, 14]], ![![1133, 424, 41]]]
  g := ![![![9, -22, 4], ![-46, 117, -22], ![227, -602, 117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![445, 166, 16]] ![![-199, -22, 4]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-331, -124, -12]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-331, -124, -12]] 
 ![![59, 0, 0], ![39, 1, 0], ![13, 0, 1]] where
  M :=![![![-331, -124, -12], ![-3408, -1279, -124], ![-35216, -13204, -1279]]]
  hmulB := by decide  
  f := ![![![1455, 148, -28]], ![![827, 85, -16]], ![![1033, 96, -19]]]
  g := ![![![79, -124, -12], ![815, -1279, -124], ![8413, -13204, -1279]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4013, -24, 40]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-4013, -24, 40]] 
 ![![59, 0, 0], ![40, 1, 0], ![52, 0, 1]] where
  M :=![![![-4013, -24, 40], ![11360, -853, -24], ![-6816, 9464, -853]]]
  hmulB := by decide  
  f := ![![![954745, 358088, 34696]], ![![814296, 305411, 29592]], ![![2565148, 962088, 93219]]]
  g := ![![![-87, -24, 40], ![792, -853, -24], ![-5780, 9464, -853]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-331, -124, -12]] ![![-331, -124, -12]]
  ![![954745, 358088, 34696]] where
 M := ![![![954745, 358088, 34696]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI59N1 : IdealMulLeCertificate' Table 
  ![![954745, 358088, 34696]] ![![-4013, -24, 40]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [7, 56, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 17, 53], [22, 43, 8], [0, 1]]
 g := ![![[53, 28, 5], [23, 52], [24, 9, 5], [47, 20, 45], [1]], ![[47, 40, 8, 54], [34, 42], [35, 28, 10, 24], [24, 9, 29, 33], [12, 32, 50, 37]], ![[54, 30, 52, 59], [38, 47], [12, 26, 13, 24], [18, 1, 56, 33], [23, 15, 2, 24]]]
 h' := ![![[56, 17, 53], [3, 14, 35], [15, 23, 33], [37, 22, 26], [54, 5, 17], [0, 1]], ![[22, 43, 8], [53, 18, 51], [48, 18, 15], [51, 45, 27], [35, 13, 20], [56, 17, 53]], ![[0, 1], [42, 29, 36], [53, 20, 13], [58, 55, 8], [56, 43, 24], [22, 43, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 53], []]
 b := ![[], [37, 51, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [7, 56, 44, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1651636, -947513, -128527]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27076, -15533, -2107]
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


def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![132607, 15038, -2702]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![132607, 15038, -2702]] 
 ![![67, 0, 0], ![2, 1, 0], ![63, 0, 1]] where
  M :=![![![132607, 15038, -2702], ![-767368, -80851, 15038], ![4270792, 420634, -80851]]]
  hmulB := by decide  
  f := ![![![211390109, 79284270, 7682042]], ![![38872838, 14579701, 1412662]], ![![534840441, 200598004, 19436419]]]
  g := ![![![4071, 15038, -2702], ![-23180, -80851, 15038], ![127211, 420634, -80851]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3185, 290, -58]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![3185, 290, -58]] 
 ![![67, 0, 0], ![63, 1, 0], ![51, 0, 1]] where
  M :=![![![3185, 290, -58], ![-16472, -1397, 290], ![82360, 6438, -1397]]]
  hmulB := by decide  
  f := ![![![-84589, -31726, -3074]], ![![-92569, -34719, -3364]], ![![-198869, -74588, -7227]]]
  g := ![![![-181, 290, -58], ![847, -1397, 290], ![-3761, 6438, -1397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![132607, 15038, -2702]] ![![132607, 15038, -2702]]
  ![![-5494743519, -358246340, 86296732]] where
 M := ![![![-5494743519, -358246340, 86296732]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-5494743519, -358246340, 86296732]] ![![3185, 290, -58]]
  ![![67, 0, 0]] where
 M := ![![![-4492325548015, -537427122914, 94247150898]]]
 hmul := by decide  
 g := ![![![![-67049635045, -8021300342, 1406673894]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5751, -2157, -209]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-5751, -2157, -209]] 
 ![![71, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-5751, -2157, -209], ![-59356, -22262, -2157], ![-612588, -229759, -22262]]]
  hmulB := by decide  
  f := ![![![-6481, -497, 109]], ![![436, 30, -7]], ![![-1988, -117, 30]]]
  g := ![![![-81, -2157, -209], ![-836, -22262, -2157], ![-8628, -229759, -22262]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![24, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![24, 1, 0]] 
 ![![71, 0, 0], ![24, 1, 0], ![63, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![24, 1, 0], ![0, 24, 1], ![284, 79, 24]]]
  hmulB := by decide  
  f := ![![![25, 1, 0], ![-71, 0, 0]], ![![-24, -1, 0], ![72, 0, 0]], ![![33, 1, 0], ![-95, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 71, 0], ![-63, 0, 71]], ![![0, 1, 0], ![-9, 24, 1], ![-44, 79, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-24, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-24, 1, 0]] 
 ![![71, 0, 0], ![47, 1, 0], ![63, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-24, 1, 0], ![0, -24, 1], ![284, 79, -24]]]
  hmulB := by decide  
  f := ![![![121, -5, 0], ![355, 0, 0]], ![![97, -4, 0], ![285, 0, 0]], ![![129, -5, 0], ![379, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 71, 0], ![-63, 0, 71]], ![![-1, 1, 0], ![15, -24, 1], ![-27, 79, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-5751, -2157, -209]] ![![71, 0, 0], ![24, 1, 0]]
  ![![71, 0, 0], ![-71, 24, 1]] where
 M := ![![![-408321, -153147, -14839], ![-197380, -74030, -7173]]]
 hmul := by decide  
 g := ![![![![-3337, -2973, -243], ![2414, 0, 0]], ![![-1575, -1450, -118], ![1205, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-71, 24, 1]] ![![71, 0, 0], ![-24, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1704, 71, 0]], ![![-5041, 1704, 71], ![1988, -568, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-24, 1, 0]]], ![![![-71, 24, 1]], ![![28, -8, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [31, 54, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 47, 21], [56, 25, 52], [0, 1]]
 g := ![![[54, 10, 8], [57, 37], [48, 55], [3, 63, 70], [61, 1], []], ![[48, 72, 52, 30], [47, 67], [31, 41], [10, 71, 67, 13], [2, 41], [40, 3]], ![[24, 32, 55, 63], [23, 65], [2, 48], [33, 29, 55, 53], [58, 19], [9, 3]]]
 h' := ![![[5, 47, 21], [34, 59, 64], [7, 14, 57], [53, 51, 37], [7, 33, 17], [0, 0, 1], [0, 1]], ![[56, 25, 52], [22, 59, 65], [26, 59, 40], [29, 9, 25], [30, 2, 23], [26, 42, 25], [5, 47, 21]], ![[0, 1], [36, 28, 17], [47, 0, 49], [67, 13, 11], [54, 38, 33], [10, 31, 47], [56, 25, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 24], []]
 b := ![[], [60, 42, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [31, 54, 12, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141401, -59276, -6424]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1937, -812, -88]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [21, 10, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 13, 54], [54, 65, 25], [0, 1]]
 g := ![![[25, 26, 46], [76, 8, 4], [34, 78, 36], [30, 26, 1], [3, 1], []], ![[32, 66, 22, 69], [69, 21, 4, 12], [42, 51, 49, 37], [78, 15, 65, 17], [7, 38], [40, 72]], ![[35, 16, 38, 13], [64, 49, 29, 25], [29, 21, 20, 22], [57, 35, 0, 22], [7, 11], [69, 72]]]
 h' := ![![[28, 13, 54], [63, 29, 58], [76, 1, 77], [2, 42, 73], [16, 28, 78], [0, 0, 1], [0, 1]], ![[54, 65, 25], [76, 40, 43], [58, 11, 3], [13, 66, 61], [66, 47, 25], [23, 1, 65], [28, 13, 54]], ![[0, 1], [52, 10, 57], [40, 67, 78], [25, 50, 24], [61, 4, 55], [45, 78, 13], [54, 65, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 42], []]
 b := ![[], [25, 39, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [21, 10, 76, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4160140, 1512771, 142911]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![52660, 19149, 1809]
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



lemma PB129I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB129I1 : PrimesBelowBoundCertificateInterval O 31 79 129 where
  m := 11
  g := ![3, 3, 2, 2, 2, 3, 1, 3, 3, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB129I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
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
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
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
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N0
      exact NI67N1
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
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I41N2, I43N1, I47N1, I53N1, I59N0, I59N1, I67N0, I67N1, I71N0, I71N1, I71N2]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [I53N1], [I59N0, I59N0, I59N1], [], [I67N0, I67N0, I67N1], [I71N0, I71N1, I71N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
