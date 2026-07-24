
import IdealArithmetic.Examples.NF5_3_18225000000_2.RI5_3_18225000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![12, -1, -1, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![12, -1, -1, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![12, -1, -1, 0, 1], ![-72, -3, 2, 0, 0], ![0, -33, -3, 6, 0], ![36, -4, -10, -3, 12], ![-96, -6, 4, 0, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 5, 2, 0, -3], ![6, 1, 0, 0, 0]], ![![48, 143, 56, -3, -83], ![166, 29, 1, 0, 0]], ![![1146, 3211, 1249, -64, -1871], ![3730, 654, 22, 1, 0]], ![![-54, -147, -57, 3, 86], ![-171, -30, -1, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![6, -1, -1, 0, 1], ![-36, -3, 2, 0, 0], ![0, -33, -3, 6, 0], ![18, -4, -10, -3, 12], ![-48, -6, 4, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![7, -3, -1, 0, 2], ![-144, -20, 2, 6, 0], ![0, -81, -14, 6, 36], ![-360, -73, -2, 19, 12], ![-120, -42, -2, 6, 13]]]
  hmulB := by decide  
  f := ![![![-41, -63, -8, 6, 24], ![12, 0, -2, 0, 0]], ![![14, 35, 5, -3, -14], ![-4, 0, 1, 0, 0]], ![![-17, -33, -4, 3, 13], ![5, 0, -1, 0, 0]], ![![4867, 9424, 1287, -851, -3718], ![-1442, 0, 287, -1, 0]], ![![30542, 59082, 8067, -5340, -23305], ![-9052, 0, 1800, -6, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![4, -3, -1, 0, 2], ![-73, -20, 2, 6, 0], ![7, -81, -14, 6, 36], ![-179, -73, -2, 19, 12], ![-59, -42, -2, 6, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-17, -4, 0, 1, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-17, -4, 0, 1, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-17, -4, 0, 1, 1], ![-72, -33, -2, 6, 12], ![-432, -123, -3, 30, 36], ![-396, -149, -6, 30, 54], ![-276, -89, -2, 21, 28]]]
  hmulB := by decide  
  f := ![![![-1038, 5202, 678, -544, -2573], ![-3094, 670, 4, 0, 2]], ![![2, 9, 1, -1, -4], ![-4, 1, 0, 0, 0]], ![![-184, 955, 125, -100, -472], ![-568, 123, 1, 0, 0]], ![![528, -2599, -339, 272, 1286], ![1548, -335, -2, 0, -1]], ![![-519, 2601, 339, -272, -1286], ![-1547, 335, 2, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![-9, -4, 0, 1, 1], ![-42, -33, -2, 6, 12], ![-234, -123, -3, 30, 36], ![-225, -149, -6, 30, 54], ![-152, -89, -2, 21, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![12, -1, -1, 0, 1]] ![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]]
  ![![2, 0, 0, 0, 0], ![-18, -4, 0, 1, 1]] where
 M := ![![![4, 0, 0, 0, 0], ![14, -6, -2, 0, 4]], ![![24, -2, -2, 0, 2], ![108, 23, -2, -6, 1]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![493, -8144, -1217, 1793, 3651], ![14590, 0, -602, -4, 0]]], ![![![246, -4060, -607, 894, 1820], ![7270, 0, -300, -2, 0]], ![![837, -13798, -2062, 3038, 6189], ![24721, 0, -1020, -7, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-18, -4, 0, 1, 1]] ![![2, 0, 0, 0, 0], ![7, -3, -1, 0, 2]]
  ![![2, 0, 0, 0, 0], ![-6, -2, 0, 0, 1]] where
 M := ![![![4, 0, 0, 0, 0], ![14, -6, -2, 0, 4]], ![![-36, -8, 0, 2, 2], ![-30, 19, 6, 1, -11]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-179, 124, 23, 63, -165], ![334, 0, 0, -6, 0]]], ![![![-240, 174, 32, 85, -226], ![454, 0, 0, -8, 0]], ![![576, -392, -73, -199, 523], ![-1057, 0, 0, 19, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-6, -2, 0, 0, 1]] ![![2, 0, 0, 0, 0], ![-17, -4, 0, 1, 1]]
  ![![2, 0, 0, 0, 0], ![-12, -3, 0, 1, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-34, -8, 0, 2, 2]], ![![-12, -4, 0, 0, 2], ![-30, 1, 2, 3, -2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![7, 2, 0, -1, 1], ![4, 0, 0, 0, 0]]], ![![![6, 1, 0, -1, 1], ![2, 0, 0, 0, 0]], ![![3, 5, 1, 0, -1], ![3, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-12, -3, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![-17, -4, 0, 1, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-34, -8, 0, 2, 2]], ![![-24, -6, 0, 2, 0], ![24, -2, 0, 0, 6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![-17, -4, 0, 1, 1]]], ![![![-12, -3, 0, 1, 0]], ![![12, -1, 0, 0, 3]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![6, 1, 0, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![6, 1, 0, -1, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![6, 1, 0, -1, 1], ![-72, -2, 4, 6, -12], ![432, 30, -20, -24, 36], ![-396, 7, 24, 13, -42], ![156, 5, -6, -3, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![954, -430, -240, 225, 111], ![1731, 160, -4, 0, 0]], ![![462, -211, -117, 111, 53], ![849, 78, -2, 0, 0]], ![![22854, -10261, -5736, 5372, 2649], ![41385, 3824, -98, -2, 0]], ![![-11672, 5237, 2928, -2741, -1353], ![-21122, -1952, 50, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![2, 1, 0, -1, 1], ![-24, -2, 4, 6, -12], ![144, 30, -20, -24, 36], ![-132, 7, 24, 13, -42], ![52, 5, -6, -3, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-11, -3, 0, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-11, -3, 0, 1, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-11, -3, 0, 1, 0], ![0, -15, -4, 0, 12], ![-432, -78, 9, 24, 0], ![0, -76, -16, 9, 42], ![-180, -41, 0, 9, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-154, -31, 0, 8, 4], ![-42, -8, 0, 2, 0]], ![![0, 10, 3, 0, -8], ![0, 2, 0, 0, 0]], ![![4, 1, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![15830, 3958, 136, -952, -727], ![4350, 758, 0, -164, -2]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-4, -3, 0, 1, 0], ![0, -15, -4, 0, 12], ![-152, -78, 9, 24, 0], ![-3, -76, -16, 9, 42], ![-63, -41, 0, 9, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![6, 1, 0, -1, 1]] ![![3, 0, 0, 0, 0], ![6, 1, 0, -1, 1]]
  ![![3, 0, 0, 0, 0], ![-12, -3, 0, 1, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![18, 3, 0, -3, 3]], ![![18, 3, 0, -3, 3], ![516, 2, -26, -16, 39]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-1182, -326, -8, 110, 1], ![-405, 0, 3, 0, 0]]], ![![![-1182, -326, -8, 110, 1], ![-405, 0, 3, 0, 0]], ![![-11124, -3098, -82, 1048, 9], ![-3832, 1, 28, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-12, -3, 0, 1, 0]] ![![3, 0, 0, 0, 0], ![-11, -3, 0, 1, 0]]
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-33, -9, 0, 3, 0]], ![![-36, -9, 0, 3, 0], ![132, 5, -4, -3, 6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-11, -3, 0, 1, 0], ![0, 0, 0, 0, 0]]], ![![![-12, -3, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![44, 2, -2, -1, 2], ![-1, 1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![-11, -3, 0, 1, 0]]
  ![![3, 0, 0, 0, 0], ![18, 0, -1, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-33, -9, 0, 3, 0]], ![![0, 3, 0, 0, 0], ![0, -15, -4, 0, 12]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-11, -3, 0, 1, 0], ![0, 0, 0, 0, 0]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-6, -5, -1, 0, 4], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![18, 0, -1, 0, 0]] ![![3, 0, 0, 0, 0], ![-11, -3, 0, 1, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-33, -9, 0, 3, 0]], ![![54, 0, -3, 0, 0], ![234, 24, -9, -6, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![-11, -3, 0, 1, 0]]], ![![![18, 0, -1, 0, 0]], ![![78, 8, -3, -2, 0]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![-2, 1, 0, 0, 0], ![0, -2, 2, 0, 0], ![0, 3, -2, 6, 0], ![0, -4, 2, -2, 12], ![-72, -12, 4, 6, -2]]]
  hmulB := by decide  
  f := ![![![7, 3, -4, 12, 0], ![15, 0, -10, 0, 0]], ![![1, 6, -4, 12, 0], ![1, 0, -10, 0, 0]], ![![5, 0, -1, 6, 0], ![11, -2, -5, 0, 0]], ![![2, 2, -2, 5, 0], ![4, 1, -4, 0, 0]], ![![16, -26, 10, -44, 5], ![40, 13, 36, -2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 5, 0, 0, 0], ![-3, 0, 5, 0, 0], ![-2, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![-1, 1, 0, 0, 0], ![0, -2, 2, 0, 0], ![-3, 3, -2, 6, 0], ![2, -4, 2, -2, 12], ![-12, -12, 4, 6, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-6, -2, 0, 0, 1]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![-10, 5, 0, 0, 0], ![4, -4, 2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1181, 152, 0, -240, 284], ![-1420, 200, 0, 0, 0]], ![![-590, -75, 0, 120, -142], ![710, -100, 0, 0, 0]]], ![![![-590, -75, 0, 120, -142], ![710, -100, 0, 0, 0]], ![![-4246, -514, 10, 864, -1049], ![5101, -720, 4, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-6, -2, 0, 0, 1]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![6, -2, -1, 0, 2]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![-30, -10, 0, 0, 5], ![-60, -14, 0, 6, -2]]]
 hmul := by decide  
 g := ![![![![4391, 2678, 469, -360, -1418], ![3545, 300, 0, 0, 0]], ![![-2054, -1247, -218, 168, 660], ![-1650, -140, 0, 0, 0]]], ![![![-4692, -2856, -499, 384, 1511], ![-3775, -320, 0, 0, 0]], ![![-9732, -5926, -1036, 798, 3134], ![-7836, -664, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![6, -2, -1, 0, 2]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-36, -7, 1, 1, 1]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![30, -10, -5, 0, 10], ![-156, -17, 6, 6, -4]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![34, 8, -1, -1, -1], ![5, 0, 0, 0, 0]]], ![![![6, -2, -1, 0, 2], ![0, 0, 0, 0, 0]], ![![12, 5, 0, 0, -2], ![6, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-36, -7, 1, 1, 1]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![-180, -35, 5, 5, 5], ![0, -35, -10, 10, 10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![-36, -7, 1, 1, 1]], ![![0, -7, -2, 2, 2]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 16, 2, -2, -4]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![41, 16, 2, -2, -4]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![2, 3, 3, 4, 1]] where
  M :=![![![41, 16, 2, -2, -4], ![288, 103, 12, -12, -24], ![864, 330, 43, -36, -72], ![720, 282, 44, -23, -60], ![312, 118, 20, -6, -19]]]
  hmulB := by decide  
  f := ![![![47, 0, -2, -2, 4]], ![![-288, 1, 12, 12, -24]], ![![864, -6, -35, -36, 72]], ![![-720, 6, 28, 31, -60]], ![![-134, 1, 5, 6, -11]]]
  g := ![![![7, 4, 2, 2, -4], ![48, 25, 12, 12, -24], ![144, 78, 37, 36, -72], ![120, 66, 32, 31, -60], ![50, 25, 11, 10, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [3, 5, 5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 5, 6, 5], [2, 6], [3, 2, 1, 2], [0, 1]]
 g := ![![[5, 4, 4, 1], []], ![[6, 6, 6, 0, 5, 3], [4, 3, 0, 2, 5, 6]], ![[2, 3, 3, 6], []], ![[1, 4, 2, 1, 0, 4], [4, 5, 3, 5, 2, 1]]]
 h' := ![![[6, 5, 6, 5], [0, 0, 0, 1], [0, 1]], ![[2, 6], [1, 0, 6, 4], [6, 5, 6, 5]], ![[3, 2, 1, 2], [1, 2, 6, 6], [2, 6]], ![[0, 1], [1, 5, 2, 3], [3, 2, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5], []]
 b := ![[], [], [0, 5, 3, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [3, 5, 5, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-995009215545, -323471011888, -417998934, 83517126318, 119151792542]
  a := ![0, 10, -9, -3, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-176187542947, -97275198502, -51124768080, -56155720550, 119151792542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 0, 2, 2, -4]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-47, 0, 2, 2, -4]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-47, 0, 2, 2, -4], ![288, -1, -12, -12, 24], ![-864, 6, 35, 36, -72], ![720, -6, -28, -31, 60], ![-120, 2, 4, 6, -11]]]
  hmulB := by decide  
  f := ![![![-41, -16, -2, 2, 4]], ![![-47, -17, -2, 2, 4]], ![![-141, -54, -7, 6, 12]], ![![-138, -54, -8, 5, 12]], ![![-68, -26, -4, 2, 5]]]
  g := ![![![-7, 0, 2, 2, -4], ![43, -1, -12, -12, 24], ![-129, 6, 35, 36, -72], ![108, -6, -28, -31, 60], ![-18, 2, 4, 6, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![41, 16, 2, -2, -4]] ![![-47, 0, 2, 2, -4]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-39, -8, 1, 1, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-39, -8, 1, 1, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![5, 3, 1, 1, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-39, -8, 1, 1, 1], ![-72, -52, -10, 12, 12], ![-432, -147, -16, 6, 72], ![-828, -202, 6, 50, 6], ![12, -83, -24, 9, 42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![4, 1, 0, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-5, -3, -1, -1, 11]], ![![-4, -1, 0, 0, 1], ![-12, -8, -2, 0, 12], ![-72, -33, -8, -6, 72], ![-78, -20, 0, 4, 6], ![-18, -19, -6, -3, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [7, 4, 0, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1, 8, 4], [7, 3, 10, 2], [7, 6, 4, 5], [0, 1]]
 g := ![![[0, 0, 6, 4], [3, 1], []], ![[10, 3, 1, 8, 8, 5], [9, 0, 7, 9, 4, 4], [1, 2, 5]], ![[10, 6, 0, 10, 5, 2], [1, 3, 1, 4, 9, 10], [4, 8, 4]], ![[4, 7, 9, 9, 5, 5], [8, 3, 4, 6, 0, 4], [3, 5, 3]]]
 h' := ![![[0, 1, 8, 4], [1, 3, 7, 9], [0, 0, 1], [0, 1]], ![[7, 3, 10, 2], [3, 2, 1, 2], [4, 4, 2, 10], [0, 1, 8, 4]], ![[7, 6, 4, 5], [0, 2, 0, 10], [10, 3, 1, 7], [7, 3, 10, 2]], ![[0, 1], [9, 4, 3, 1], [6, 4, 7, 5], [7, 6, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 1, 7], []]
 b := ![[], [], [6, 4, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [7, 4, 0, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50407246513596140, -16324209415271080, -7753827122134, 4230799122321426, 6002455483202767]
  a := ![3, 122, -124, -66, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7310865811782725, -3121052351352671, -546382664574991, -161059669171031, 6002455483202767]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![0, -1, 2, 0, 0], ![0, 3, -1, 6, 0], ![0, -4, 2, -1, 12], ![-72, -12, 4, 6, -1]]]
  hmulB := by decide  
  f := ![![![4, 73416, -22881, 148302, -864], ![33, -10824, -271755, 792, 0]], ![![2, 73418, -22881, 148302, -864], ![12, -10824, -271755, 792, 0]], ![![2, 40760, -12703, 82336, -480], ![17, -6011, -150876, 440, 0]], ![![2, 32632, -10171, 65917, -384], ![17, -4806, -120789, 352, 0]], ![![2, 13347, -4160, 26964, -157], ![20, -1969, -49410, 144, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 11, 0, 0, 0], ![-5, 0, 11, 0, 0], ![-5, 0, 0, 11, 0], ![-2, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![0, -1, 2, 0, 0], ![-5, 3, -1, 6, 0], ![1, -4, 2, -1, 12], ![0, -12, 4, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-39, -8, 1, 1, 1]] ![![11, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![-11, 11, 0, 0, 0]], ![![-429, -88, 11, 11, 11], ![-33, -44, -11, 11, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![-39, -8, 1, 1, 1]], ![![-3, -4, -1, 1, 1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [11, 10, 6, 9, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 0, 0, 10, 1], [2, 11, 12, 4, 6], [7, 9, 8, 10, 6], [5, 5, 6, 2], [0, 1]]
 g := ![![[12, 6, 12, 5, 12], [12, 1], []], ![[1, 4, 12, 8, 1, 10], [5, 4, 6, 1], [2, 8, 11, 10, 3, 2, 3, 1]], ![[7, 2, 0, 10, 11, 7, 4, 11], [11, 9, 11, 1], [9, 12, 8, 10, 4, 9, 8, 8]], ![[10, 3, 8, 1, 3, 1, 7, 7], [0, 12, 11, 1], [6, 6, 8, 12, 6, 12, 6, 8]], ![[12, 11, 9, 3, 7, 11, 8], [9, 6, 0, 9], [0, 2, 10, 12, 8]]]
 h' := ![![[11, 0, 0, 10, 1], [11, 12, 9, 3, 5], [0, 0, 0, 1], [0, 1]], ![[2, 11, 12, 4, 6], [0, 3, 11, 6], [9, 9, 8, 3, 12], [11, 0, 0, 10, 1]], ![[7, 9, 8, 10, 6], [9, 12, 10, 6, 11], [0, 1, 10, 7, 12], [2, 11, 12, 4, 6]], ![[5, 5, 6, 2], [3, 6, 10, 10, 8], [4, 1, 2, 7, 12], [7, 9, 8, 10, 6]], ![[0, 1], [4, 6, 12, 1, 2], [8, 2, 6, 8, 3], [5, 5, 6, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 7, 1], [], [], []]
 b := ![[], [11, 8, 2, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [11, 10, 6, 9, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2214988493317886, 718900092750580, 3373912310769, -182703181798332, -260062120060470]
  a := ![1, 9, -9, -5, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![170383730255222, 55300007134660, 259531716213, -14054090907564, -20004778466190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [8, 15, 11, 16, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 8, 2, 0, 1], [5, 9, 8, 2, 4], [10, 4, 7, 5, 4], [3, 12, 0, 10, 8], [0, 1]]
 g := ![![[14, 12, 4, 2, 1], [7, 14, 8, 1], [], []], ![[4, 5, 0, 2, 16, 16, 4, 8], [7, 0, 16, 4], [3, 8, 10, 1], [4, 1, 8, 1]], ![[10, 2, 2, 16, 0, 11, 15, 15], [15, 3, 8, 1], [4, 15, 0, 8], [15, 12, 8, 16]], ![[13, 5, 6, 3, 14, 0, 13, 1], [2, 10, 3, 13], [6, 6, 13, 1], [11, 13, 15, 16]], ![[12, 2, 3, 10, 2, 15, 4, 2], [10, 15, 1, 2], [7, 10, 2, 8], [8, 15, 9, 13]]]
 h' := ![![[7, 8, 2, 0, 1], [12, 4, 6, 14, 1], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[5, 9, 8, 2, 4], [10, 10, 6, 11, 5], [10, 10, 3, 4, 15], [0, 10, 3, 16, 16], [7, 8, 2, 0, 1]], ![[10, 4, 7, 5, 4], [16, 6, 7, 6, 12], [0, 3, 14, 0, 16], [7, 7, 7, 3, 12], [5, 9, 8, 2, 4]], ![[3, 12, 0, 10, 8], [3, 14, 13, 15, 8], [11, 1, 11, 16, 8], [12, 15, 9, 11, 1], [10, 4, 7, 5, 4]], ![[0, 1], [7, 0, 2, 5, 8], [11, 3, 6, 14, 11], [13, 2, 14, 4, 5], [3, 12, 0, 10, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 2, 5, 16], [], [], []]
 b := ![[], [12, 4, 1, 4, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [8, 15, 11, 16, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6964431534194913768, -2262716151541434761, -11231533272338438, 574371002635297519, 818588043749081850]
  a := ![1, -52, 48, 17, 191]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-409672443187936104, -133100950090672633, -660678427784614, 33786529566782207, 48152237867593050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![31, -20, -7, 1, 13]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![31, -20, -7, 1, 13]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![17, 16, 17, 3, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![31, -20, -7, 1, 13], ![-936, -150, 14, 36, 12], ![-432, -591, -90, 78, 216], ![-2124, -526, -34, 108, 150], ![-1140, -323, 0, 57, 76]]]
  hmulB := by decide  
  f := ![![![-30, 20, 7, -1, -13], ![19, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-4, 4, 2, 0, -2], ![3, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-17, -16, -17, -3, 19]], ![![-10, -12, -12, -2, 13], ![-60, -18, -10, 0, 12], ![-216, -213, -198, -30, 216], ![-246, -154, -136, -18, 150], ![-128, -81, -68, -9, 76]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [6, 6, 14, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 15, 11, 7], [15, 7, 7, 5], [2, 15, 1, 7], [0, 1]]
 g := ![![[9, 5, 5, 4], [6, 10, 11, 1], [1], []], ![[9, 12, 12, 8, 18, 11], [5, 18, 7, 2, 4, 6], [5, 0, 5], [0, 13, 11]], ![[9, 12, 6, 8, 4, 5], [14, 5, 5, 1, 9, 5], [1], [16, 0, 6]], ![[3, 1, 17, 9, 0, 4], [3, 17, 2, 5, 1, 7], [5, 0, 5], [6, 6, 11]]]
 h' := ![![[3, 15, 11, 7], [2, 16, 14, 17], [13, 13, 5, 1], [0, 0, 1], [0, 1]], ![[15, 7, 7, 5], [2, 14, 16, 8], [13, 15, 11, 16], [9, 12, 14, 10], [3, 15, 11, 7]], ![[2, 15, 1, 7], [10, 2, 16, 18], [10, 13, 13, 1], [15, 0, 18], [15, 7, 7, 5]], ![[0, 1], [16, 6, 11, 14], [6, 16, 9, 1], [6, 7, 5, 9], [2, 15, 1, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 17, 8], []]
 b := ![[], [], [15, 11, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [6, 6, 14, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2659569273147, -903719510800, -7285897218, 225441200478, 342545773809]
  a := ![-1, 21, -14, 4, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-446465654100, -336023783776, -306871792209, -42220848471, 342545773809]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![2, 1, 0, 0, 0], ![0, 2, 2, 0, 0], ![0, 3, 2, 6, 0], ![0, -4, 2, 2, 12], ![-72, -12, 4, 6, 2]]]
  hmulB := by decide  
  f := ![![![13, -21, -18, -54, 0], ![-114, 0, 171, 0, 0]], ![![-2, -4, -2, -6, 0], ![20, 0, 19, 0, 0]], ![![11, -20, -17, -48, 0], ![-96, 10, 152, 0, 0]], ![![2, -8, -6, -17, 0], ![-16, 3, 54, 0, 0]], ![![-4, -8, -6, -16, -5], ![38, 1, 48, 8, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 19, 0, 0, 0], ![-17, 0, 19, 0, 0], ![-6, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![0, 1, 0, 0, 0], ![-2, 2, 2, 0, 0], ![-4, 3, 2, 6, 0], ![-2, -4, 2, 2, 12], ![-8, -12, 4, 6, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![31, -20, -7, 1, 13]] ![![19, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![361, 0, 0, 0, 0], ![38, 19, 0, 0, 0]], ![![589, -380, -133, 19, 247], ![-874, -190, 0, 38, 38]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0]], ![![2, 1, 0, 0, 0]]], ![![![31, -20, -7, 1, 13]], ![![-46, -10, 0, 2, 2]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-36, -24, -1, 0, 10]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-36, -24, -1, 0, 10]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![2, 6, 22, 1, 0], ![1, 16, 16, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-36, -24, -1, 0, 10], ![-720, -159, -8, 54, 0], ![0, -480, -105, -24, 324], ![-3528, -605, 52, 192, -48], ![48, -270, -70, 24, 138]]]
  hmulB := by decide  
  f := ![![![4681, -2016, -62, -864, 1900], ![-4370, 368, 0, 0, 0]], ![![-288, 130, 4, 54, -120], ![276, -23, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![346, -132, -3, -61, 130], ![-299, 26, 0, 0, 0]], ![![11, 8, 1, 0, -3], ![7, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-2, -6, -22, 23, 0], ![-1, -16, -16, 0, 23]], ![![-2, -8, -7, 0, 10], ![-36, -21, -52, 54, 0], ![-12, -240, -207, -24, 324], ![-168, -43, -148, 192, -48], ![-6, -114, -122, 24, 138]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [12, 19, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 11, 15], [10, 11, 8], [0, 1]]
 g := ![![[22, 22, 9], [9, 9, 4], [5, 22, 1], []], ![[11, 11, 12, 22], [4, 15, 5, 10], [4, 18, 17, 21], [13, 18]], ![[20, 9, 7, 18], [21, 10, 0, 9], [5, 4, 13, 2], [20, 18]]]
 h' := ![![[12, 11, 15], [7, 9, 3], [9, 9, 2], [0, 0, 1], [0, 1]], ![[10, 11, 8], [10, 8, 7], [1, 0, 19], [11, 8, 11], [12, 11, 15]], ![[0, 1], [22, 6, 13], [3, 14, 2], [21, 15, 11], [10, 11, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 13], []]
 b := ![[], [15, 20, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [12, 19, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![331158252, -6119100, -13530192, -10910420, 24221094]
  a := ![0, -20, 8, -20, 30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14293826, -14269308, -7001672, -10910420, 24221094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![0, -3, 0, 0, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![0, -3, 0, 0, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![9, 3, 1, 0, 0], ![14, 22, 0, 1, 0], ![0, 20, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![0, -3, 0, 0, 1], ![-72, -12, -2, 6, 0], ![0, -51, -6, -6, 36], ![-396, -65, 6, 27, -12], ![48, -24, -10, 0, 21]]]
  hmulB := by decide  
  f := ![![![1081, 3375, 414, 294, -2281], ![-529, 345, 1472, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![423, 1314, 161, 114, -887], ![-191, 135, 572, 0, 0]], ![![658, 2057, 252, 179, -1389], ![-309, 210, 896, 0, 0]], ![![0, 1, 0, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-9, -3, 23, 0, 0], ![-14, -22, 0, 23, 0], ![0, -20, 0, 0, 23]], ![![0, -1, 0, 0, 1], ![-6, -6, -2, 6, 0], ![6, -27, -6, -6, 36], ![-36, -19, 6, 27, -12], ![6, -18, -10, 0, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [18, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 22], [0, 1]]
 g := ![![[2, 9], [6, 4], [19, 8], [1]], ![[0, 14], [0, 19], [7, 15], [1]]]
 h' := ![![[10, 22], [7, 20], [3, 2], [5, 10], [0, 1]], ![[0, 1], [0, 3], [0, 21], [13, 13], [10, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [2, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [18, 13, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-280972, -196526, -10350, 48947, 110580]
  a := ![13, 18, -13, 1, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37960, -150170, -10350, 48947, 110580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-36, -24, -1, 0, 10]] ![![23, 0, 0, 0, 0], ![0, -3, 0, 0, 1]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![0, -69, 0, 0, 23]], ![![-828, -552, -23, 0, 230], ![2208, 207, -46, -138, 138]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![0, -3, 0, 0, 1]]], ![![![-36, -24, -1, 0, 10]], ![![96, 9, -2, -6, 6]]]]
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


lemma PB6601I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB6601I0 : PrimesBelowBoundCertificateInterval O 1 23 6601 where
  m := 9
  g := ![5, 5, 5, 2, 2, 1, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB6601I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
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
    · exact ![2401, 7]
    · exact ![14641, 11]
    · exact ![371293]
    · exact ![1419857]
    · exact ![130321, 19]
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
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I11N1, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N1], [], [], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
