
import IdealArithmetic.Examples.NF5_1_607500000_4.RI5_1_607500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![5, -3, 0, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![5, -3, 0, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![5, -3, 0, 0, 1], ![2, 3, 0, 0, -2], ![-4, 6, -3, 0, 4], ![4, -6, 6, -3, -4], ![-2, 6, -1, 1, -2]]]
  hmulB := by decide  
  f := ![![![-2, 6, 0, 0, -3], ![2, -2, 0, 0, 0]], ![![-1, -1, 0, 0, 1], ![0, 1, 0, 0, 0]], ![![7, 15, 2, 0, -13], ![2, -10, 1, 0, 0]], ![![-74, -90, -12, 2, 86], ![-4, 70, -6, 1, 0]], ![![-1, 3, 0, 0, -1], ![1, -1, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![2, -3, 0, 0, 1], ![2, 3, 0, 0, -2], ![-4, 6, -3, 0, 4], ![4, -6, 6, -3, -4], ![0, 6, -1, 1, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-8, 9, 1, 0, -3], ![-6, -2, 1, 3, 6], ![18, -42, -1, 6, 42], ![26, -24, 16, -1, -6], ![2, -12, -2, 6, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2494, 1243, -433, -1374, -3040], ![17, 872, 21, 0, 1]], ![![119, 52, -20, -63, -138], ![2, 40, 1, 0, 0]], ![![-114, -62, 20, 65, 144], ![0, -41, -1, 0, 0]], ![![-2365, -1193, 411, 1308, 2898], ![-14, -830, -20, 0, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-4, 9, 1, 0, -3], ![-3, -2, 1, 3, 6], ![9, -42, -1, 6, 42], ![13, -24, 16, -1, -6], ![1, -12, -2, 6, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 2, 3, 0], ![2, -8, -6, 2, 18], ![2, -2, 3, 0, -1]]]
  hmulB := by decide  
  f := ![![![-2, 1, -3, 0, 1], ![2, 0, 0, 0, 2]], ![![-2, 1, -4, 0, 1], ![1, 2, 0, 0, 2]], ![![0, 0, 1, 0, 0], ![1, -1, 0, 0, 0]], ![![0, 0, 1, 2, 0], ![0, 0, -1, 0, 0]], ![![0, 0, -3, 0, 1], ![-1, 3, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 0, 2, 3, 0], ![-1, -8, -6, 2, 18], ![1, -2, 3, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![5, -3, 0, 0, 1]] ![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]]
  ![![74, -93, 12, 21, 80]] where
 M := ![![![4, 0, 0, 0, 0], ![-16, 18, 2, 0, -6]], ![![10, -6, 0, 0, 2], ![-20, 39, 0, -3, -16]]]
 hmul := by decide  
 g := ![![![![140, -114, -4, 4, 46]], ![![-156, 504, 1, -47, -257]]], ![![![206, -267, -5, 17, 122]], ![![275, 363, -14, -58, -229]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![74, -93, 12, 21, 80]] ![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]]
  ![![2, 0, 0, 0, 0], ![-6, 0, 1, 1, 2]] where
 M := ![![![148, -186, 24, 42, 160], ![888, -1116, 145, 252, 958]]]
 hmul := by decide  
 g := ![![![![-262, 33, 54, 42, 80], ![-98, 14, 0, 0, 0]], ![![-1551, 171, 324, 256, 496], ![-584, 81, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-6, 0, 1, 1, 2]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0], ![-8, 12, 0, -1, -6]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![-12, 0, 2, 2, 4], ![0, -18, 2, 5, 16]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![2, -12, 1, 2, 8], ![2, 0, 0, 0, 0]], ![![-4, -3, 1, 2, 5], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-8, 12, 0, -1, -6]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![-16, 24, 0, -2, -12], ![-22, 24, 0, -2, -12]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![-8, 12, 0, -1, -6]], ![![-11, 12, 0, -1, -6]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 3, 0], ![2, -8, -6, 1, 18], ![2, -2, 3, 0, -2]]]
  hmulB := by decide  
  f := ![![![-27, 122, 0, -18, -332], ![42, 360, 0, 54, -12]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![-14, 63, 0, -9, -172], ![23, 186, 0, 28, -6]], ![![-18, 81, 0, -12, -221], ![29, 240, 0, 36, -8]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![-2, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-2, 0, 1, 3, 0], ![-12, -8, -6, 1, 18], ![2, -2, 3, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-5, 0, 1, 1, 2]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-5, 0, 1, 1, 2]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-5, 0, 1, 1, 2], ![6, -17, 1, 4, 14], ![36, -54, 2, 7, 44], ![22, -18, 12, 2, -2], ![14, -24, -1, 6, 23]]]
  hmulB := by decide  
  f := ![![![-14341, 37692, -2086, -8581, -30880], ![-234, 6282, 111, 0, 12]], ![![-14345, 37698, -2086, -8582, -30884], ![-235, 6283, 111, 0, 12]], ![![-14093, 37044, -2050, -8434, -30350], ![-229, 6174, 109, 0, 12]], ![![-2450, 6444, -357, -1467, -5280], ![-39, 1074, 19, 0, 2]], ![![-9559, 25128, -1391, -5721, -20587], ![-155, 4188, 74, 0, 8]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![-4, 0, 1, 1, 2], ![2, -17, 1, 4, 14], ![15, -54, 2, 7, 44], ![12, -18, 12, 2, -2], ![4, -24, -1, 6, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![-8, 12, 0, -1, -6]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![0, 3, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![59, 24, 0, 4, 0], ![-24, 0, 0, 0, 36]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-8, 12, 0, -1, -6]] ![![3, 0, 0, 0, 0], ![-5, 0, 1, 1, 2]]
  ![![3, 0, 0, 0, 0], ![5, -3, 0, 0, 1]] where
 M := ![![![9, 0, 0, 0, 0], ![-15, 0, 3, 3, 6]], ![![-24, 36, 0, -3, -18], ![6, -42, -2, 2, 16]]]
 hmul := by decide  
 g := ![![![![-2, 3, 0, 0, -1], ![3, 0, 0, 0, 0]], ![![-2, 3, 0, 2, 1], ![-3, 0, 0, 0, -3]]], ![![![-3, 9, 0, -1, -5], ![-3, 0, 0, 0, 0]], ![![-10, -10, 0, 0, 4], ![8, 0, 0, 0, 2]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![5, -3, 0, 0, 1]] ![![3, 0, 0, 0, 0], ![-5, 0, 1, 1, 2]]
  ![![3, 0, 0, 0, 0], ![7, -15, 1, 2, 9]] where
 M := ![![![9, 0, 0, 0, 0], ![-15, 0, 3, 3, 6]], ![![15, -9, 0, 0, 3], ![-29, 27, 1, -1, -9]]]
 hmul := by decide  
 g := ![![![![-4, 15, -1, -2, -9], ![3, 0, 0, 0, 0]], ![![-5, 0, 1, 1, 2], ![0, 0, 0, 0, 0]]], ![![![-2, 12, -1, -2, -8], ![3, 0, 0, 0, 0]], ![![-12, 14, 0, -1, -6], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![7, -15, 1, 2, 9]] ![![3, 0, 0, 0, 0], ![-5, 0, 1, 1, 2]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-15, 0, 3, 3, 6]], ![![21, -45, 3, 6, 27], ![81, -51, 9, 12, 51]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![-5, 0, 1, 1, 2]]], ![![![7, -15, 1, 2, 9]], ![![27, -17, 3, 4, 17]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 9, -1, -2, -8]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-7, 9, -1, -2, -8]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-7, 9, -1, -2, -8], ![-20, 25, -4, -5, -20], ![-50, 60, -9, -17, -50], ![-28, 42, 4, -9, -52], ![-30, 36, -8, -7, -25]]]
  hmulB := by decide  
  f := ![![![79, 9, -3, -6, -14]], ![![-8, 31, 0, -3, -16]], ![![-38, 48, 1, -3, -22]], ![![-4, -6, 0, 1, 4]], ![![46, 36, -2, -7, -25]]]
  g := ![![![5, 9, -1, -2, -8], ![12, 25, -4, -5, -20], ![30, 60, -9, -17, -50], ![36, 42, 4, -9, -52], ![14, 36, -8, -7, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-7, 9, -1, -2, -8]] ![![-7, 9, -1, -2, -8]]
  ![![215, -270, 36, 60, 230]] where
 M := ![![![215, -270, 36, 60, 230]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![215, -270, 36, 60, 230]] ![![-7, 9, -1, -2, -8]]
  ![![-6485, 8145, -1059, -1842, -6990]] where
 M := ![![![-6485, 8145, -1059, -1842, -6990]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-6485, 8145, -1059, -1842, -6990]] ![![-7, 9, -1, -2, -8]]
  ![![196721, -247284, 31988, 55756, 212464]] where
 M := ![![![196721, -247284, 31988, 55756, 212464]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![196721, -247284, 31988, 55756, 212464]] ![![-7, 9, -1, -2, -8]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-5965855, 7498125, -972165, -1689870, -6438400]]]
 hmul := by decide  
 g := ![![![![-1193171, 1499625, -194433, -337974, -1287680]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [5, 6, 0, 3, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 5, 5, 4, 2], [0, 0, 1, 2], [3, 5, 4, 2, 5], [2, 3, 4, 6], [0, 1]]
 g := ![![[6, 3, 1], []], ![[2, 4, 0, 1, 3, 2, 5, 2], [6, 0, 2, 3, 2, 5, 2, 1]], ![[5, 0, 5, 5, 3, 4, 2], [3, 2, 6, 1, 1]], ![[2, 0, 1, 2, 1, 4, 2, 3], [5, 3, 1, 1, 4, 6, 0, 6]], ![[3, 1, 3, 0, 3, 5, 3], [4, 0, 5, 2, 6]]]
 h' := ![![[5, 5, 5, 4, 2], [0, 0, 0, 1], [0, 1]], ![[0, 0, 1, 2], [4, 3, 5, 3, 6], [5, 5, 5, 4, 2]], ![[3, 5, 4, 2, 5], [6, 0, 0, 6, 6], [0, 0, 1, 2]], ![[2, 3, 4, 6], [2, 6, 2, 2, 4], [3, 5, 4, 2, 5]], ![[0, 1], [2, 5, 0, 2, 5], [2, 3, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 2, 3, 5], [], [], []]
 b := ![[], [0, 0, 3, 4, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [5, 6, 0, 3, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141156122351811, 2952051098116358, 2667790493813186, 498522705717554, -7489654334570184]
  a := ![-21, 83, 59, -22, -189]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20165160335973, 421721585445194, 381112927687598, 71217529388222, -1069950619224312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-10, 14, 0, -1, -7]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-10, 14, 0, -1, -7]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![2, 9, 6, 1, 0], ![9, 3, 7, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-10, 14, 0, -1, -7], ![-16, 12, -1, -1, -4], ![-10, 0, 5, -4, -10], ![-6, 14, -2, 5, -14], ![-10, 2, -2, -2, 3]]]
  hmulB := by decide  
  f := ![![![57, -16, 6, 2, -4], ![-44, 66, 0, 0, 0]], ![![-12, -3, -2, 0, 6], ![22, -22, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 1], ![5, -6, 0, 0, 0]], ![![47, -19, 5, 2, 1], ![-26, 48, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-2, -9, -6, 11, 0], ![-9, -3, -7, 0, 11]], ![![5, 4, 5, -1, -7], ![2, 3, 3, -1, -4], ![8, 6, 9, -4, -10], ![10, 1, 6, 5, -14], ![-3, 1, -1, -2, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 10, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 0, 6], [4, 10, 5], [0, 1]]
 g := ![![[6, 6, 9], [1, 0, 1], []], ![[6, 1, 4, 10], [5, 10, 2, 6], [0, 3]], ![[2, 2, 5, 4], [2, 9], [1, 3]]]
 h' := ![![[7, 0, 6], [3, 1, 3], [0, 0, 1], [0, 1]], ![[4, 10, 5], [3, 5, 3], [5, 9, 10], [7, 0, 6]], ![[0, 1], [9, 5, 5], [8, 2], [4, 10, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6], []]
 b := ![[], [9, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 10, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24395218, 63916684, 116890815, -2318181, -265198827]
  a := ![16, -125, -44, 15, 141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![219620093, 80034254, 180653790, -2318181, -265198827]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![0, -2, 0, 0, 1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![0, -2, 0, 0, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![2, 5, 1, 0, 0], ![7, 9, 0, 1, 0], ![0, 9, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![0, -2, 0, 0, 1], ![2, -2, 1, 0, -2], ![-4, 6, -7, 3, 4], ![6, -14, 0, -7, 14], ![0, 4, 2, 1, -9]]]
  hmulB := by decide  
  f := ![![![-2387, 2246, -924, -162, 2405], ![-187, 14322, 594, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-398, 375, -154, -27, 401], ![-31, 2388, 99, 0, 0]], ![![-1519, 1431, -588, -103, 1530], ![-114, 9114, 378, 0, 0]], ![![0, 1, 0, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -5, 11, 0, 0], ![-7, -9, 0, 11, 0], ![0, -9, 0, 0, 11]], ![![0, -1, 0, 0, 1], ![0, 1, 1, 0, -2], ![-1, -2, -7, 3, 4], ![5, -7, 0, -7, 14], ![-1, 6, 2, 1, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[8, 1], [0, 9], [1]], ![[5, 10], [6, 2], [1]]]
 h' := ![![[8, 10], [0, 10], [1, 8], [0, 1]], ![[0, 1], [3, 1], [10, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [4, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [10, 3, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17350, -27166, 9736, -11256, 9568]
  a := ![-7, 26, 20, -8, -64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6970, -5514, 9736, -11256, 9568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-10, 14, 0, -1, -7]] ![![11, 0, 0, 0, 0], ![0, -2, 0, 0, 1]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![0, -22, 0, 0, 11]], ![![-110, 154, 0, -11, -77], ![22, -22, 0, 0, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![0, -2, 0, 0, 1]]], ![![![-10, 14, 0, -1, -7]], ![![2, -2, 0, 0, 1]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![8, -6, 0, 0, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![8, -6, 0, 0, 1]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![7, 2, 1, 0, 0], ![6, 9, 0, 1, 0], ![8, 7, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![8, -6, 0, 0, 1], ![2, 6, -3, 0, -2], ![-4, 6, -3, -9, 4], ![-2, 18, 24, -3, -58], ![-8, 12, -10, 1, 7]]]
  hmulB := by decide  
  f := ![![![14389, 30012, -16341, -99, -10383], ![-5785, -70668, -143, 0, 0]], ![![146816, 306109, -166686, -990, -105920], ![-59072, -720876, -1430, 0, 0]], ![![29203, 60902, -33161, -198, -21072], ![-11744, -143412, -286, 0, 0]], ![![108286, 225771, -122940, -731, -78121], ![-43571, -531684, -1056, 0, 0]], ![![87912, 183295, -99810, -594, -63423], ![-35372, -431652, -858, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-7, -2, 13, 0, 0], ![-6, -9, 0, 13, 0], ![-8, -7, 0, 0, 13]], ![![0, -1, 0, 0, 1], ![3, 2, -3, 0, -2], ![3, 5, -3, -9, 4], ![24, 31, 24, -3, -58], ![0, -2, -10, 1, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12], [0, 1]]
 g := ![![[7, 12], [1], [12, 1]], ![[8, 1], [1], [11, 12]]]
 h' := ![![[12, 12], [2, 8], [2, 12], [0, 1]], ![[0, 1], [7, 5], [3, 1], [12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![185136, -267260, 127348, -116702, 39916]
  a := ![22, -68, -62, 21, 197]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25032, 19150, 127348, -116702, 39916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![10, -5, 0, 0, 1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![10, -5, 0, 0, 1]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![2, 1, 1, 0, 0], ![3, 0, 0, 1, 0], ![10, 8, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![10, -5, 0, 0, 1], ![2, 8, -2, 0, -2], ![-4, 6, 0, -6, 4], ![0, 10, 18, 0, -40], ![-6, 10, -7, 1, 7]]]
  hmulB := by decide  
  f := ![![![-57709, -160965, 42120, 420, 40253], ![20631, 273780, 910, 0, 0]], ![![-40254, -112278, 29380, 294, 28077], ![14391, 190970, 637, 0, 0]], ![![-11540, -32162, 8417, 84, 8043], ![4133, 54710, 182, 0, 0]], ![![-13319, -37145, 9720, 97, 9289], ![4763, 63180, 210, 0, 0]], ![![-69164, -192913, 50480, 504, 48242], ![24727, 328120, 1092, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -1, 13, 0, 0], ![-3, 0, 0, 13, 0], ![-10, -8, 0, 0, 13]], ![![0, -1, 0, 0, 1], ![2, 2, -2, 0, -2], ![-2, -2, 0, -6, 4], ![28, 24, 18, 0, -40], ![-5, -3, -7, 1, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12], [0, 1]]
 g := ![![[6, 9], [9], [3, 1]], ![[7, 4], [9], [6, 12]]]
 h' := ![![[3, 12], [10, 10], [8, 3], [0, 1]], ![[0, 1], [1, 3], [4, 10], [3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [5, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [6, 10, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142036, -203386, 102432, -93725, 19951]
  a := ![-20, 79, 57, -18, -179]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1449, -35802, 102432, -93725, 19951]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 0, -2, 3, 0], ![2, -8, -6, -2, 18], ![2, -2, 3, 0, -5]]]
  hmulB := by decide  
  f := ![![![-1504, 711, 2104, -2938, -396], ![-6331, 208, 12922, 286, 0]], ![![-1516, 715, 2076, -2896, -396], ![-6382, 208, 12740, 286, 0]], ![![-756, 357, 1024, -1427, -198], ![-3182, 105, 6279, 143, 0]], ![![-750, 356, 1057, -1477, -198], ![-3157, 109, 6496, 143, 0]], ![![-1274, 603, 1780, -2486, -335], ![-5363, 180, 10934, 242, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 13, 0, 0, 0], ![-4, 0, 13, 0, 0], ![-7, 0, 0, 13, 0], ![-11, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0], ![2, -3, 1, 0, 0], ![-1, 0, -2, 3, 0], ![-6, -8, -6, -2, 18], ![5, -2, 3, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![8, -6, 0, 0, 1]] ![![13, 0, 0, 0, 0], ![10, -5, 0, 0, 1]]
  ![![13, 0, 0, 0, 0], ![-37, 65, 1, -5, -31]] where
 M := ![![![169, 0, 0, 0, 0], ![130, -65, 0, 0, 13]], ![![104, -78, 0, 0, 13], ![62, -78, 5, 1, 27]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![10, -5, 0, 0, 1], ![0, 0, 0, 0, 0]]], ![![![8, -6, 0, 0, 1], ![0, 0, 0, 0, 0]], ![![19, -31, 0, 2, 14], ![5, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-37, 65, 1, -5, -31]] ![![13, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![-39, 13, 0, 0, 0]], ![![-481, 845, 13, -65, -403], ![39, -130, 0, 13, 65]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![-3, 1, 0, 0, 0]]], ![![![-37, 65, 1, -5, -31]], ![![3, -10, 0, 1, 5]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![0, 0, 0, 0, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![0, 0, 0, 0, 1]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![12, 5, 1, 0, 0], ![10, 11, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![0, 0, 0, 0, 1], ![2, -2, 3, 0, -2], ![-4, 6, -5, 9, 4], ![10, -30, -12, -5, 50], ![4, 0, 8, 1, -13]]]
  hmulB := by decide  
  f := ![![![-8721, 8466, -13211, -1152, 8691], ![527, 78489, 2176, 0, 0]], ![![544, -527, 824, 72, -543], ![-17, -4896, -136, 0, 0]], ![![-5996, 5821, -9083, -792, 5976], ![352, 53964, 1496, 0, 0]], ![![-4778, 4639, -7238, -631, 4762], ![282, 43002, 1192, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-12, -5, 17, 0, 0], ![-10, -11, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![0, 0, 0, 0, 1], ![-2, -1, 3, 0, -2], ![-2, -4, -5, 9, 4], ![12, 5, -12, -5, 50], ![-6, -3, 8, 1, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [8, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 16], [0, 1]]
 g := ![![[13, 15], [15], [4], [1]], ![[0, 2], [15], [4], [1]]]
 h' := ![![[15, 16], [3, 10], [15, 7], [9, 15], [0, 1]], ![[0, 1], [0, 7], [1, 10], [13, 2], [15, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [11, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [8, 2, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86936, -165552, 14528, -55252, 136752]
  a := ![-18, 72, 48, -28, -162]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27360, 21740, 14528, -55252, 136752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![2, 5, 0, 0, 1]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![2, 5, 0, 0, 1]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![5, 14, 1, 0, 0], ![9, 11, 0, 1, 0], ![2, 5, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![2, 5, 0, 0, 1], ![2, 0, 8, 0, -2], ![-4, 6, 2, 24, 4], ![20, -70, -42, 2, 140], ![14, -10, 23, 1, -21]]]
  hmulB := by decide  
  f := ![![![-43689, 929, -175032, 1056, 44089], ![-2261, 372130, -748, 0, 0]], ![![-131742, 2808, -527816, 3168, 132951], ![-6851, 1122170, -2244, 0, 0]], ![![-120697, 2573, -483565, 2904, 121805], ![-6277, 1028090, -2057, 0, 0]], ![![-108375, 2307, -434192, 2609, 109368], ![-5624, 923120, -1848, 0, 0]], ![![-43888, 934, -175832, 1056, 44290], ![-2277, 373830, -748, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-5, -14, 17, 0, 0], ![-9, -11, 0, 17, 0], ![-2, -5, 0, 0, 17]], ![![0, 0, 0, 0, 1], ![-2, -6, 8, 0, -2], ![-14, -18, 2, 24, 4], ![-4, -12, -42, 2, 140], ![-4, -14, 23, 1, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 16], [0, 1]]
 g := ![![[1, 1], [15], [8], [1]], ![[13, 16], [15], [8], [1]]]
 h' := ![![[12, 16], [14, 16], [2, 10], [12, 12], [0, 1]], ![[0, 1], [2, 1], [3, 7], [3, 5], [12, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [16, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![173419, -264444, 102954, -109140, 79420]
  a := ![24, -84, -61, 25, 203]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28357, -53080, 102954, -109140, 79420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, 61, 1, -4, -28]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-45, 61, 1, -4, -28]] 
 ![![17, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-45, 61, 1, -4, -28], ![-64, 43, 2, -1, -16], ![-34, -24, 3, 5, 14], ![24, -26, -4, 3, 16], ![-34, 4, 2, 1, 1]]]
  hmulB := by decide  
  f := ![![![1737, -2183, 283, 492, 1874]], ![![1811, -2276, 295, 513, 1954]], ![![2087, -2623, 340, 591, 2252]], ![![1458, -1832, 238, 413, 1572]], ![![1020, -1282, 166, 289, 1101]]]
  g := ![![![-45, 61, 1, -4, -28], ![-37, 43, 2, -1, -16], ![9, -24, 3, 5, 14], ![20, -26, -4, 3, 16], ![-8, 4, 2, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![0, 0, 0, 0, 1]] ![![17, 0, 0, 0, 0], ![2, 5, 0, 0, 1]]
  ![![1737, -2183, 283, 492, 1874]] where
 M := ![![![289, 0, 0, 0, 0], ![34, 85, 0, 0, 17]], ![![0, 0, 0, 0, 17], ![14, -10, 23, 1, -21]]]
 hmul := by decide  
 g := ![![![![-765, 1037, 17, -68, -476]], ![![-444, 341, 14, -12, -135]]], ![![![-34, 4, 2, 1, 1]], ![![-2, -14, 1, 3, 5]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![1737, -2183, 283, 492, 1874]] ![![-45, 61, 1, -4, -28]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [10, 16, 16, 12, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 14, 9, 7, 10], [5, 11, 17, 10, 9], [8, 10, 15, 7, 15], [2, 2, 16, 14, 4], [0, 1]]
 g := ![![[4, 10, 10, 9, 9], [16, 7, 5, 13, 1], [], []], ![[0, 18, 4, 9, 18, 14], [16, 2, 8, 2, 15, 5, 11, 8], [4, 2, 10, 17], [14, 3, 15, 5]], ![[6, 18, 13, 0, 15, 14, 15, 17], [6, 7, 2, 2, 12, 14, 13, 6], [13, 6], [6, 16, 17, 5]], ![[0, 8, 16, 12, 8, 4, 5, 10], [1, 14, 13, 2, 6, 14, 13, 2], [18, 2, 6, 1], [8, 3, 0, 16]], ![[6, 8, 15, 0, 5, 10, 16, 11], [10, 13, 18, 4, 9, 16, 15, 9], [0, 11, 17, 6], [9, 17, 16, 16]]]
 h' := ![![[17, 14, 9, 7, 10], [11, 16, 0, 18, 16], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[5, 11, 17, 10, 9], [8, 6, 6, 16], [7, 9, 6, 18, 15], [16, 13, 4, 3, 6], [17, 14, 9, 7, 10]], ![[8, 10, 15, 7, 15], [14, 7, 3, 10, 17], [12, 15, 18, 5, 8], [3, 6, 16, 14], [5, 11, 17, 10, 9]], ![[2, 2, 16, 14, 4], [9, 15, 9, 5, 11], [0, 8, 0, 0, 3], [3, 2, 12, 13, 18], [8, 10, 15, 7, 15]], ![[0, 1], [7, 13, 1, 8, 13], [5, 6, 14, 15, 11], [9, 17, 5, 8, 14], [2, 2, 16, 14, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 4, 7, 7], [], [], []]
 b := ![[], [2, 18, 7, 3, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [10, 16, 16, 12, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![465514886842, -1339056834728, -326049815932, -425053712171, 1862112818599]
  a := ![4, -20, -12, 3, 37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24500783518, -70476675512, -17160516628, -22371248009, 98005937821]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![48, -16, 0, -1, 4]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![48, -16, 0, -1, 4]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![22, 9, 12, 1, 0], ![6, 4, 3, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![48, -16, 0, -1, 4], ![6, 48, 2, -1, -26], ![-54, 66, -22, 5, 34], ![44, -76, 46, -22, -4], ![-26, 62, -4, 9, -22]]]
  hmulB := by decide  
  f := ![![![1309, 4064, 180, -106, -2276], ![-368, -2070, 0, 0, 0]], ![![-132, -255, -12, 8, 148], ![46, 138, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![1238, 3775, 168, -99, -2116], ![-352, -1926, 0, 0, 0]], ![![306, 1020, 45, -26, -569], ![-82, -516, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-22, -9, -12, 23, 0], ![-6, -4, -3, 0, 23]], ![![2, -1, 0, -1, 4], ![8, 7, 4, -1, -26], ![-16, -5, -8, 5, 34], ![24, 6, 14, -22, -4], ![-4, 3, -2, 9, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [20, 15, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 14, 11], [9, 8, 12], [0, 1]]
 g := ![![[4, 1, 1], [17, 9, 12], [12, 21, 1], []], ![[17, 15, 19, 19], [9, 18, 18, 15], [5, 21, 22, 14], [20, 6]], ![[19, 13, 5, 6], [18, 4, 4, 4], [6, 16, 18, 6], [19, 6]]]
 h' := ![![[12, 14, 11], [5, 10, 22], [13, 21, 9], [0, 0, 1], [0, 1]], ![[9, 8, 12], [13, 17, 10], [8, 21, 4], [20, 8, 8], [12, 14, 11]], ![[0, 1], [3, 19, 14], [18, 4, 10], [0, 15, 14], [9, 8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 16], []]
 b := ![[], [12, 10, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [20, 15, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22491742, 945434207, 901686451, 151806777, -2480268312]
  a := ![28, -109, -78, 24, 249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![500842132, 413054194, 283513481, 151806777, -2480268312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![7, 2, 0, 0, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![7, 2, 0, 0, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![17, 11, 1, 0, 0], ![1, 0, 0, 1, 0], ![7, 2, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![7, 2, 0, 0, 1], ![2, 5, 5, 0, -2], ![-4, 6, 4, 15, 4], ![14, -46, -24, 4, 86], ![8, -4, 14, 1, -10]]]
  hmulB := by decide  
  f := ![![![352269, 997484, 1013012, -1680, -413484], ![175996, -4661916, 2576, 0, 0]], ![![285593, 808674, 821261, -1365, -335217], ![142669, -3779475, 2093, 0, 0]], ![![396009, 1121324, 1138778, -1890, -464818], ![197828, -5240697, 2898, 0, 0]], ![![15313, 43368, 44044, -73, -17978], ![7662, -202692, 112, 0, 0]], ![![132048, 373902, 379722, -630, -154992], ![65965, -1747494, 966, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-17, -11, 23, 0, 0], ![-1, 0, 0, 23, 0], ![-7, -2, 0, 0, 23]], ![![0, 0, 0, 0, 1], ![-3, -2, 5, 0, -2], ![-5, -2, 4, 15, 4], ![-8, 2, -24, 4, 86], ![-7, -6, 14, 1, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [22, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 22], [0, 1]]
 g := ![![[16, 16], [7, 16], [11, 3], [1]], ![[19, 7], [10, 7], [13, 20], [1]]]
 h' := ![![[16, 22], [7, 19], [11, 19], [1, 16], [0, 1]], ![[0, 1], [12, 4], [16, 4], [4, 7], [16, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [22, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [22, 7, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51134, -74082, 35612, -33326, 10272]
  a := ![12, -46, -34, 11, 107]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25776, -21146, 35612, -33326, 10272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![48, -16, 0, -1, 4]] ![![23, 0, 0, 0, 0], ![7, 2, 0, 0, 1]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![161, 46, 0, 0, 23]], ![![1104, -368, 0, -23, 92], ![322, 46, 0, 0, -46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![7, 2, 0, 0, 1]]], ![![![48, -16, 0, -1, 4]], ![![14, 2, 0, 0, -2]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB1535I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1535I0 : PrimesBelowBoundCertificateInterval O 1 23 1535 where
  m := 9
  g := ![5, 5, 5, 1, 2, 3, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1535I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![1331, 121]
    · exact ![169, 169, 13]
    · exact ![289, 289, 17]
    · exact ![2476099]
    · exact ![12167, 529]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N0, I11N1, I13N0, I13N1, I13N2, I17N0, I17N1, I17N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N0, I11N1], [I13N0, I13N1, I13N2], [I17N0, I17N1, I17N2], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
