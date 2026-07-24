
import IdealArithmetic.Examples.NF5_1_67500000_3.RI5_1_67500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![3, -1, -2, 3, 6], ![-6, -1, 2, -1, -3]]]
  hmulB := by decide  
  f := ![![![28, -10, -13, 22, 45], ![8, -6, 0, -14, 2]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![2, 0, 0, 2, 3], ![-1, -2, 0, -1, 0]], ![![14, -6, -7, 11, 23], ![6, -2, 0, -7, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-1, 1, 0, 2, 0], ![-3, -1, -2, 3, 6], ![-1, -1, 2, -1, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, -98, -4, 17, 69]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![239, -98, -4, 17, 69]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![239, -98, -4, 17, 69], ![-363, 149, 6, -26, -105], ![552, -226, -9, 39, 159], ![-237, 98, 4, -17, -69], ![183, -75, -3, 13, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 1, 0]], ![![2, 0, -1, 2, 3]], ![![-13, -4, 3, 0, 0]], ![![-1, -5, -1, 2, -3]], ![![0, 1, -1, 0, 5]]]
  g := ![![![162, -98, -4, 17, 69], ![-246, 149, 6, -26, -105], ![374, -226, -9, 39, 159], ![-161, 98, 4, -17, -69], ![124, -75, -3, 13, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 0, 1, 1, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 0, 1, 1, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 0, 1, 1, 1], ![-3, 0, 0, 4, 3], ![-6, -10, -2, 9, 15], ![-30, -16, 1, 2, 3], ![10, -1, -4, 3, 4]]]
  hmulB := by decide  
  f := ![![![4, 0, 0, -4, -3], ![0, 2, 0, 0, 0]], ![![-47, -35, -21, 47, 62], ![24, -13, -7, 0, -1]], ![![11, 5, 3, -11, -12], ![-3, 4, 1, 0, 0]], ![![-9, -5, -3, 9, 10], ![4, -3, -1, 0, 0]], ![![2, 0, 0, -2, -1], ![0, 1, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![-1, 0, 1, 1, 1], ![-5, 0, 0, 4, 3], ![-9, -10, -2, 9, 15], ![-10, -16, 1, 2, 3], ![4, -1, -4, 3, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![239, -98, -4, 17, 69]]
  ![![2, 0, 0, 0, 0], ![3, -1, 0, 0, 1]] where
 M := ![![![478, -196, -8, 34, 138]], ![![-363, 149, 6, -26, -105]]]
 hmul := by decide  
 g := ![![![![729, -823, 0, 350, -558], ![1230, 666, 0, 0, -674]]], ![![![-556, 626, 0, -266, 423], ![-933, -506, 0, 0, 512]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![3, -1, 0, 0, 1]] ![![239, -98, -4, 17, 69]]
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 1, 1]] where
 M := ![![![478, -196, -8, 34, 138]], ![![1263, -518, -21, 90, 365]]]
 hmul := by decide  
 g := ![![![![956, 484, -243, -357, -544], ![-208, 478, 0, 0, 0]]], ![![![2526, 1279, -642, -943, -1437], ![-550, 1263, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 1, 1]] ![![2, 0, 0, 0, 0], ![1, 0, 1, 1, 1]]
  ![![2, 0, 0, 0, 0], ![3, -1, 1, 1, 2]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 0, 2, 2, 2]], ![![0, 2, 0, 2, 2], ![-23, -17, -3, 9, 10]]]
 hmul := by decide  
 g := ![![![![-1, 1, -1, -1, -2], ![2, 0, 0, 0, 0]], ![![-2, 1, 0, 0, -1], ![2, 0, 0, 0, 0]]], ![![![0, 1, 0, 1, 1], ![0, 0, 0, 0, 0]], ![![-10, -9, -1, 5, 6], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![3, -1, 1, 1, 2]] ![![2, 0, 0, 0, 0], ![1, 0, 1, 1, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 0, 2, 2, 2]], ![![6, -2, 2, 2, 4], ![-10, -28, -6, 16, 26]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![1, 0, 1, 1, 1]]], ![![![3, -1, 1, 1, 2]], ![![-5, -14, -3, 8, 13]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![4, -1, 0, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![4, -1, 0, 0, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![4, -1, 0, 0, 1], ![-6, 3, 1, -1, -3], ![15, -1, -1, 2, 3], ![-3, 3, 0, 1, 3], ![1, -2, 1, 0, -2]]]
  hmulB := by decide  
  f := ![![![-129, -99, 0, -30, 47], ![-123, 96, 96, -6, 0]], ![![-52, -39, 0, -12, 18], ![-48, 38, 38, -2, 0]], ![![-48, -38, 0, -11, 18], ![-45, 37, 36, -2, 0]], ![![23, 19, 0, 6, -9], ![24, -18, -18, 1, 0]], ![![-43, -33, 0, -10, 16], ![-41, 32, 32, -2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![1, -1, 0, 0, 1], ![-1, 3, 1, -1, -3], ![4, -1, -1, 2, 3], ![-2, 3, 0, 1, 3], ![1, -2, 1, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![2, -1, 0, 0, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![2, -1, 0, 0, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![2, -1, 0, 0, 1], ![-6, 1, 1, -1, -3], ![15, -1, -3, 2, 3], ![-3, 3, 0, -1, 3], ![1, -2, 1, 0, -4]]]
  hmulB := by decide  
  f := ![![![-1529, -26, 396, -390, -702], ![-1242, -1098, 30, -12, 0]], ![![-259, -4, 67, -66, -119], ![-210, -186, 5, -2, 0]], ![![-347, -6, 90, -88, -160], ![-279, -248, 7, -2, 0]], ![![300, 6, -78, 77, 138], ![246, 216, -6, 2, 0]], ![![-1020, -17, 264, -260, -468], ![-827, -732, 20, -8, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, -1, 0, 0, 1], ![0, 1, 1, -1, -3], ![3, -1, -3, 2, 3], ![-3, 3, 0, -1, 3], ![3, -2, 1, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![3, -1, -2, 2, 6], ![-6, -1, 2, -1, -4]]]
  hmulB := by decide  
  f := ![![![56, -36, 1, -12, 16], ![93, -3, 24, 0, 12]], ![![54, -34, 1, -12, 16], ![88, -3, 24, 0, 12]], ![![28, -18, 1, -6, 8], ![46, -2, 12, 0, 6]], ![![0, 0, 0, -1, 0], ![0, 2, 2, 0, 0]], ![![38, -25, 1, -8, 11], ![64, -3, 16, 0, 8]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![-1, -1, -2, 2, 6], ![0, -1, 2, -1, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![4, -1, 0, 0, 1]] ![![3, 0, 0, 0, 0], ![2, -1, 0, 0, 1]]
  ![![-5109, 2095, 85, -364, -1476]] where
 M := ![![![9, 0, 0, 0, 0], ![6, -3, 0, 0, 3]], ![![12, -3, 0, 0, 3], ![15, -7, 0, 1, 3]]]
 hmul := by decide  
 g := ![![![![129, 15, -45, 30, 36]], ![![-187, -17, 62, -45, -35]]], ![![![-101, -7, 32, -25, -11]], ![![128, 3, -38, 32, -5]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-5109, 2095, 85, -364, -1476]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![-3, 0, 0, 1, 0]] where
 M := ![![![-15327, 6285, 255, -1092, -4428], ![12873, -5279, -214, 918, 3720]]]
 hmul := by decide  
 g := ![![![![-11346, 18855, 8465, -15045, -26616], ![6333, 12570, 0, 0, 0]], ![![9533, -15837, -7110, 12636, 22356], ![-5316, -10558, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-3, 0, 0, 1, 0]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![3, -1, 1, -1, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![-9, 0, 0, 3, 0], ![6, -4, -2, 2, 6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-3, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![1, -1, -1, 1, 2], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![3, -1, 1, -1, 0]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![9, -3, 3, -3, 0], ![-6, 6, 0, 0, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![3, -1, 1, -1, 0]], ![![-2, 2, 0, 0, -2]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N2, I3N2, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
    exact isPrimeI3N2
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1501, -288, 584, -346, -822]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-1501, -288, 584, -346, -822]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1501, -288, 584, -346, -822], ![3894, 251, -1240, 952, 390], ![516, 1312, -873, -14, 4542], ![-15594, -2568, 5832, -3641, -7050], ![14598, 2062, -5270, 3446, 5399]]]
  hmulB := by decide  
  f := ![![![-77537, 31820, 1292, -5538, -22422]], ![![-38446, 15799, 644, -2752, -11130]], ![![-97840, 40164, 1635, -6982, -28290]], ![![15438, -6324, -252, 1111, 4470]], ![![-11886, 4874, 198, -846, -3433]]]
  g := ![![![-537, -288, 584, -346, -822], ![1570, 251, -1240, 952, 390], ![-248, 1312, -873, -14, 4542], ![-5730, -2568, 5832, -3641, -7050], ![5486, 2062, -5270, 3446, 5399]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-1501, -288, 584, -346, -822]] ![![-1501, -288, 584, -346, -822]]
  ![![-5171159, 319772, 1284772, -1335832, 1775352]] where
 M := ![![![-5171159, 319772, 1284772, -1335832, 1775352]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-5171159, 319772, 1284772, -1335832, 1775352]] ![![-1501, -288, 584, -346, -822]]
  ![![56417596883, 10346369828, -21684757356, 13057284454, 29213579250]] where
 M := ![![![56417596883, 10346369828, -21684757356, 13057284454, 29213579250]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![56417596883, 10346369828, -21684757356, 13057284454, 29213579250]] ![![-1501, -288, 584, -346, -822]]
  ![![167261152508977, -15394436790920, -38756308547032, 43761263556208, -75162089345808]] where
 M := ![![![167261152508977, -15394436790920, -38756308547032, 43761263556208, -75162089345808]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![167261152508977, -15394436790920, -38756308547032, 43761263556208, -75162089345808]] ![![-1501, -288, 584, -346, -822]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-2110632506155698205, -370246645414210520, 801923771959755520, -490328594767211130, -1033840679580741030]]]
 hmul := by decide  
 g := ![![![![-422126501231139641, -74049329082842104, 160384754391951104, -98065718953442226, -206768135916148206]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![0, -1, 0, 1, 2]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![0, -1, 0, 1, 2]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![5, 4, 1, 1, 0], ![1, 1, 3, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![0, -1, 0, 1, 2], ![-9, -3, 1, 1, 0], ![3, -9, -5, 5, 6], ![-6, -5, -4, -1, 6], ![-4, -3, 2, -1, -6]]]
  hmulB := by decide  
  f := ![![![28, 9, -3, -3, 0], ![0, 21, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![20, 7, -2, -2, 0], ![0, 15, 0, 0, 0]], ![![4, 2, 0, -1, -1], ![4, 3, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-5, -4, -1, 7, 0], ![-1, -1, -3, 0, 7]], ![![-1, -1, -1, 1, 2], ![-2, -1, 0, 1, 0], ![-4, -5, -4, 5, 6], ![-1, -1, -3, -1, 6], ![1, 1, 3, -1, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 6, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [3, 2], [0, 1]]
 g := ![![[3, 2, 4], [1]], ![[2, 2, 1], [1]], ![[3, 3, 2], [1]]]
 h' := ![![[2, 4], [3, 1, 5], [0, 1]], ![[3, 2], [4, 0, 3], [2, 4]], ![[0, 1], [2, 6, 6], [3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [5, 1, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 6, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-114573, -154720, -110948, 126016, 339346]
  a := ![-17, 4, 8, -20, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-154857, -142590, -179286, 126016, 339346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![3, -1, -2, 4, 6], ![-6, -1, 2, -1, -2]]]
  hmulB := by decide  
  f := ![![![140, -324, -415, -672, 144], ![-469, -119, 2688, -168, 0]], ![![22, -56, -70, -112, 24], ![-69, -14, 448, -28, 0]], ![![116, -270, -345, -560, 120], ![-386, -104, 2240, -140, 0]], ![![0, -1, -1, -1, 0], ![0, 3, 4, 0, 0]], ![![100, -231, -296, -480, 103], ![-335, -88, 1920, -120, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-2, -1, -2, 4, 6], ![-1, -1, 2, -1, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 1, -3, 2, 0], ![3, -1, -2, 0, 6], ![-6, -1, 2, -1, -6]]]
  hmulB := by decide  
  f := ![![![-1118, 619, -898, 630, -72], ![-2527, -161, -2205, 84, 0]], ![![-842, 467, -676, 474, -54], ![-1903, -119, -1659, 63, 0]], ![![-838, 466, -676, 474, -54], ![-1894, -118, -1659, 63, 0]], ![![-274, 154, -224, 157, -18], ![-619, -37, -549, 21, 0]], ![![-638, 353, -513, 360, -41], ![-1442, -93, -1260, 48, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 7, 0, 0, 0], ![-5, 0, 7, 0, 0], ![-2, 0, 0, 7, 0], ![-4, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![1, -3, 1, 0, 0], ![1, 1, -3, 2, 0], ![-1, -1, -2, 0, 6], ![2, -1, 2, -1, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![0, -1, 0, 1, 2]] ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0], ![-2, 3, 1, 2, 2]] where
 M := ![![![49, 0, 0, 0, 0], ![7, 7, 0, 0, 0]], ![![0, -7, 0, 7, 14], ![-9, -4, 1, 2, 2]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![3, -2, -1, -2, -2], ![7, 0, 0, 0, 0]]], ![![![0, -1, 0, 1, 2], ![0, 0, 0, 0, 0]], ![![-1, -1, 0, 0, 0], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![-2, 3, 1, 2, 2]] ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![49, 0, 0, 0, 0], ![-21, 7, 0, 0, 0]], ![![-14, 21, 7, 14, 14], ![0, -14, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0]], ![![-3, 1, 0, 0, 0]]], ![![![-2, 3, 1, 2, 2]], ![![0, -2, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1361080908, 558099480, 22623862, -97020637, -393261782]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-1361080908, 558099480, 22623862, -97020637, -393261782]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![6, 0, 4, 1, 0], ![6, 7, 7, 0, 1]] where
  M :=![![![-1361080908, 558099480, 22623862, -97020637, -393261782], ![2068508781, -848174627, -34382810, 147447595, 597661524], ![-3143626359, 1289016852, 52253231, -224084359, -908299002], ![1354516077, -555407570, -22514812, 96552396, 391364664], ![-1042930040, 427644592, 17335578, -74342250, -301337457]]]
  hmulB := by decide  
  f := ![![![1538934, 236266, -566036, 361209, 635492]], ![![-2729325, -23803, 784832, -683937, 260778]], ![![-3616479, -1521334, 1865627, -742925, -4885956]], ![![879621, -246984, -111802, 248340, -978282]], ![![-4388420, -983517, 1785797, -996062, -2899983]]]
  g := ![![![143692146, 300993814, 287594444, -97020637, -393261782], ![-218376903, -457436845, -437073078, 147447595, 597661524], ![331879437, 695191806, 664243971, -224084359, -908299002], ![-142998753, -299541838, -286207004, 96552396, 391364664], ![110104382, 230636981, 220369707, -74342250, -301337457]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [7, 8, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 5, 6], [9, 5, 5], [0, 1]]
 g := ![![[5, 0, 5], [8, 7, 1], []], ![[4, 6, 3, 2], [4, 9, 7, 7], [4, 3]], ![[2, 6, 0, 4], [8, 9, 8, 4], [5, 3]]]
 h' := ![![[9, 5, 6], [10, 8, 4], [0, 0, 1], [0, 1]], ![[9, 5, 5], [8, 1, 2], [9, 4, 5], [9, 5, 6]], ![[0, 1], [2, 2, 5], [2, 7, 5], [9, 5, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6], []]
 b := ![[], [4, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [7, 8, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21960036, -107109722, -56978583, 120884080, 145003885]
  a := ![-110, -4, 57, -173, -223]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-147026166, -102012447, -141412918, 120884080, 145003885]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1538934, 236266, -566036, 361209, 635492]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![1538934, 236266, -566036, 361209, 635492]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![10, 3, 1, 0, 0], ![7, 1, 0, 1, 0], ![6, 1, 0, 0, 1]] where
  M :=![![![1538934, 236266, -566036, 361209, 635492], ![-2729325, -23803, 784832, -683937, 260778], ![-3616479, -1521334, 1865627, -742925, -4885956], ![14908143, 1950916, -5296114, 3536186, 4969770], ![-13085596, -1420324, 4486770, -3135902, -3336519]]]
  hmulB := by decide  
  f := ![![![-1361080908, 558099480, 22623862, -97020637, -393261782]], ![![2068508781, -848174627, -34382810, 147447595, 597661524]], ![![-958991736, 393226161, 15940311, -68358904, -277084750]], ![![-554958318, 227555833, 9224492, -39558588, -160346026]], ![![-649173337, 266187895, 10790540, -46274407, -187567875]]]
  g := ![![![77989, 85243, -566036, 361209, 635492], ![-668614, -177740, 784832, -683937, 260778], ![1113042, -135394, 1865627, -742925, -4885956], ![1208851, 848482, -5296114, 3536186, 4969770], ![-1452988, -764383, 4486770, -3135902, -3336519]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [7, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[10, 4], [3, 5], [1]], ![[5, 7], [5, 6], [1]]]
 h' := ![![[7, 10], [1, 2], [4, 7], [0, 1]], ![[0, 1], [4, 9], [9, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [7, 4, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1300, -735, -111, -341, 137]
  a := ![-9, 1, 5, -13, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![125, -18, -111, -341, 137]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-1361080908, 558099480, 22623862, -97020637, -393261782]] ![![1538934, 236266, -566036, 361209, 635492]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [9, 0, 6, 9, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 11, 11, 12, 6], [10, 1, 1, 9, 3], [1, 0, 10, 12, 1], [4, 0, 4, 6, 3], [0, 1]]
 g := ![![[10, 9, 10], [3, 1], []], ![[0, 12, 5, 3, 2, 9, 11, 8], [8, 10, 7, 1], [3, 12, 7, 8, 11, 11, 7, 8]], ![[10, 0, 7, 1, 10, 11, 9, 4], [0, 2, 6, 12], [10, 9, 9, 8, 7, 3, 12, 1]], ![[2, 12, 10, 9, 9, 9], [6, 8, 1, 10], [1, 2, 9, 2, 5, 11, 0, 1]], ![[1, 8, 5, 11, 0, 10], [5, 9, 1, 4], [7, 1, 10, 12, 0, 8, 9, 1]]]
 h' := ![![[1, 11, 11, 12, 6], [12, 4, 8, 6], [0, 0, 0, 1], [0, 1]], ![[10, 1, 1, 9, 3], [6, 1, 2, 7, 6], [0, 3, 3, 11, 12], [1, 11, 11, 12, 6]], ![[1, 0, 10, 12, 1], [0, 8, 2, 8, 7], [0, 11, 7, 10, 5], [10, 1, 1, 9, 3]], ![[4, 0, 4, 6, 3], [10, 8, 8, 10], [5, 8, 8, 10, 7], [1, 0, 10, 12, 1]], ![[0, 1], [8, 5, 6, 8], [1, 4, 8, 7, 2], [4, 0, 4, 6, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4, 4, 3], [], [], []]
 b := ![[], [4, 2, 6, 4, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [9, 0, 6, 9, 10, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31254181491, -1694844521682, -1551461778672, 776428508154, 2364151720164]
  a := ![62, -8, -30, 80, 123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2404167807, -130372655514, -119343213744, 59725269858, 181857824628]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![10, -6, 0, 0, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![10, -6, 0, 0, 1]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![16, 11, 1, 0, 0], ![14, 16, 0, 1, 0], ![10, 11, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![10, -6, 0, 0, 1], ![-6, 9, -4, -1, -3], ![15, -6, 5, -8, 3], ![-18, 8, 10, -8, -27], ![31, 3, -9, 5, 19]]]
  hmulB := by decide  
  f := ![![![660853, -1490778, 811478, 201704, 552783], ![947427, 3446104, -2142, 0, 0]], ![![1100832, -2483297, 1351738, 335992, 920811], ![1578195, 5740424, -3570, 0, 0]], ![![1329974, -3000191, 1633097, 405928, 1112475], ![1906677, 6935272, -4312, 0, 0]], ![![1580322, -3564928, 1940500, 482337, 1321880], ![2265572, 8240720, -5124, 0, 0]], ![![1101046, -2483771, 1351994, 336056, 920986], ![1578485, 5741512, -3570, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-16, -11, 17, 0, 0], ![-14, -16, 0, 17, 0], ![-10, -11, 0, 0, 17]], ![![0, -1, 0, 0, 1], ![6, 6, -4, -1, -3], ![1, 2, 5, -8, 3], ![12, 19, 10, -8, -27], ![-5, -11, -9, 5, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [8, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[10, 15], [2], [8], [1]], ![[0, 2], [2], [8], [1]]]
 h' := ![![[5, 16], [1, 10], [0, 11], [9, 5], [0, 1]], ![[0, 1], [0, 7], [4, 6], [0, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [8, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16368, -3637, 4731, -5471, -6477]
  a := ![-30, 11, 15, -27, -59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2900, 6065, 4731, -5471, -6477]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![10, -1, 0, 0, 1]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![10, -1, 0, 0, 1]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![12, 2, 1, 0, 0], ![5, 13, 0, 1, 0], ![10, 16, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![10, -1, 0, 0, 1], ![-6, 9, 1, -1, -3], ![15, -1, 5, 2, 3], ![-3, 3, 0, 7, 3], ![1, -2, 1, 0, 4]]]
  hmulB := by decide  
  f := ![![![609141, -1286966, -145010, 146354, 411530], ![458252, 2481490, -3264, 0, 0]], ![![266370, -562766, -63410, 63998, 179955], ![200379, 1085110, -1428, 0, 0]], ![![459086, -969925, -109287, 110300, 310151], ![345353, 1870180, -2460, 0, 0]], ![![382855, -808870, -91140, 91985, 258651], ![288009, 1559640, -2052, 0, 0]], ![![609020, -1286701, -144980, 146324, 411446], ![458151, 2480980, -3264, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-12, -2, 17, 0, 0], ![-5, -13, 0, 17, 0], ![-10, -16, 0, 0, 17]], ![![0, -1, 0, 0, 1], ![1, 4, 1, -1, -3], ![-5, -5, 5, 2, 3], ![-4, -8, 0, 7, 3], ![-3, -4, 1, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 16], [0, 1]]
 g := ![![[1, 1], [1], [1], [1]], ![[0, 16], [1], [1], [1]]]
 h' := ![![[16, 16], [16, 16], [0, 1], [16, 16], [0, 1]], ![[0, 1], [0, 1], [16, 16], [0, 1], [16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [6, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8165, -3848, 4544, -1458, -8772]
  a := ![18, -16, -8, -2, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1901, 8610, 4544, -1458, -8772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58, -25, -1, 5, 18]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![58, -25, -1, 5, 18]] 
 ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![58, -25, -1, 5, 18], ![-93, 34, 1, -5, -24], ![129, -63, -4, 11, 42], ![-63, 19, -1, -6, -18], ![45, -19, -1, 3, 13]]]
  hmulB := by decide  
  f := ![![![62, 5, -21, 15, 12]], ![![13, 2, -5, 3, 6]], ![![-17, -4, 7, -4, -12]], ![![79, 6, -26, 19, 12]], ![![9, 2, -4, 2, 7]]]
  g := ![![![-4, -25, -1, 5, 18], ![3, 34, 1, -5, -24], ![-8, -63, -4, 11, 42], ![6, 19, -1, -6, -18], ![-2, -19, -1, 3, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![10, -6, 0, 0, 1]] ![![17, 0, 0, 0, 0], ![10, -1, 0, 0, 1]]
  ![![62, 5, -21, 15, 12]] where
 M := ![![![289, 0, 0, 0, 0], ![170, -17, 0, 0, 17]], ![![170, -102, 0, 0, 17], ![137, -66, -5, 6, 32]]]
 hmul := by decide  
 g := ![![![![986, -425, -17, 85, 306]], ![![718, -303, -12, 58, 217]]], ![![![1183, -473, -17, 83, 337]], ![![853, -344, -13, 60, 244]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![62, 5, -21, 15, 12]] ![![58, -25, -1, 5, 18]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11792473, 30054, -3350646, 2963036, -1382340]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![11792473, 30054, -3350646, 2963036, -1382340]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![13, 10, 1, 0, 0], ![11, 14, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![11792473, 30054, -3350646, 2963036, -1382340], ![17183148, 6861131, -8660698, 3570156, 21925236], ![-120840948, -16972942, 43571291, -28536164, -44354772], ![81668496, -5619926, -19974730, 21159353, -30038952], ![-43528314, 10043038, 6740246, -12050298, 40758757]]]
  hmulB := by decide  
  f := ![![![449270044579, -184219347682, -7467765878, 32024899908, 129809159916]], ![![-682780259772, 279968218877, 11349172334, -48669991948, -197278080300]], ![![2650867777, -1086965594, -44062679, 188959392, 765924480]], ![![-266529274237, 109288054486, 4430249176, -18998759003, -77009232180]], ![![183639163705, -75299671896, -3052449852, 13090180190, 53059503649]]]
  g := ![![![1707045, -418210, -3350646, 2963036, -1382340], ![-3314534, 2288733, -8660698, 3570156, 21925236], ![-3309817, -2798924, 43571291, -28536164, -44354772], ![16782093, -5373872, -19974730, 21159353, -30038952], ![-14942607, 5860250, 6740246, -12050298, 40758757]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 18], [0, 1]]
 g := ![![[3, 11], [2, 1], [4], [1]], ![[0, 8], [0, 18], [4], [1]]]
 h' := ![![[17, 18], [5, 12], [2, 1], [12, 17], [0, 1]], ![[0, 1], [0, 7], [0, 18], [16, 2], [17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [8, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [7, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3538, -7853, -3432, 3477, 4123]
  a := ![16, 8, -1, 30, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1370, -1169, -3432, 3477, 4123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![9, -6, 0, 0, 1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![9, -6, 0, 0, 1]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![14, 11, 1, 0, 0], ![18, 4, 0, 1, 0], ![9, 13, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![9, -6, 0, 0, 1], ![-6, 8, -4, -1, -3], ![15, -6, 4, -8, 3], ![-18, 8, 10, -9, -27], ![31, 3, -9, 5, 18]]]
  hmulB := by decide  
  f := ![![![1512442, -2508294, 1501152, 373992, 1043577], ![1563453, 7127736, -2736, 0, 0]], ![![2267592, -3760663, 2250664, 560722, 1564626], ![2344068, 10686550, -4104, 0, 0]], ![![2420621, -4014449, 2402547, 598562, 1670213], ![2502247, 11407718, -4380, 0, 0]], ![![1910229, -3167998, 1895968, 472355, 1318047], ![1974651, 9002392, -3456, 0, 0]], ![![2267934, -3761227, 2251000, 560806, 1564860], ![2344411, 10688146, -4104, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-14, -11, 19, 0, 0], ![-18, -4, 0, 19, 0], ![-9, -13, 0, 0, 19]], ![![0, -1, 0, 0, 1], ![5, 5, -4, -1, -3], ![4, -3, 4, -8, 3], ![13, 15, 10, -9, -27], ![-5, -8, -9, 5, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [14, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 18], [0, 1]]
 g := ![![[9, 9], [2, 6], [11], [1]], ![[15, 10], [6, 13], [11], [1]]]
 h' := ![![[7, 18], [10, 3], [4, 14], [5, 7], [0, 1]], ![[0, 1], [12, 16], [7, 5], [16, 12], [7, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [18, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [14, 12, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![93, -475, -141, 151, -9]
  a := ![0, -4, 0, -6, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30, 31, -141, 151, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 1, -2, 2, 0], ![3, -1, -2, 1, 6], ![-6, -1, 2, -1, -5]]]
  hmulB := by decide  
  f := ![![![2925, -7304, 11846, -11932, 144], ![27094, 1178, 113582, -456, 0]], ![![2919, -7294, 11832, -11918, 144], ![27038, 1178, 113449, -456, 0]], ![![2433, -6079, 9862, -9934, 120], ![22536, 989, 94563, -380, 0]], ![![2436, -6086, 9873, -9945, 120], ![22564, 989, 94668, -380, 0]], ![![1848, -4614, 7482, -7536, 91], ![17118, 738, 71736, -288, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-17, 19, 0, 0, 0], ![-15, 0, 19, 0, 0], ![-16, 0, 0, 19, 0], ![-12, 0, 0, 0, 19]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-1, 1, -2, 2, 0], ![-2, -1, -2, 1, 6], ![3, -1, 2, -1, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![11792473, 30054, -3350646, 2963036, -1382340]] ![![19, 0, 0, 0, 0], ![9, -6, 0, 0, 1]]
  ![![19, 0, 0, 0, 0], ![-2, -2, 1, -9, -7]] where
 M := ![![![224056987, 571026, -63662274, 56297684, -26264460], ![-40494945, -30853262, 28548620, -6803910, -103233719]]]
 hmul := by decide  
 g := ![![![![11616527, -145892, -3262673, 2171279, -1998151], ![-1671487, 0, 0, 0, 0]], ![![-1930235, -1422778, 1402020, 546750, -4729581], ![1910240, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![-2, -2, 1, -9, -7]] ![![19, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![361, 0, 0, 0, 0], ![-38, 19, 0, 0, 0]], ![![-38, -38, 19, -171, -133], ![19, 19, 0, 0, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![-2, -2, 1, -9, -7]], ![![1, 1, 0, 0, -1]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-5, -6, 0, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-5, -6, 0, 1, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![18, 17, 0, 1, 0], ![3, 2, 14, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-5, -6, 0, 1, 0], ![3, -6, -8, 3, 6], ![-27, -14, 0, -13, 0], ![-21, -4, 10, -21, -42], ![36, 8, -14, 6, 22]]]
  hmulB := by decide  
  f := ![![![436, -774, -1080, 399, 810], ![138, -3105, 0, 0, 0]], ![![-27, 55, 72, -27, -54], ![0, 207, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![318, -569, -792, 293, 594], ![93, -2277, 0, 0, 0]], ![![58, -92, -134, 49, 101], ![34, -387, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-18, -17, 0, 23, 0], ![-3, -2, -14, 0, 23]], ![![-1, -1, 0, 1, 0], ![-3, -3, -4, 3, 6], ![9, 9, 0, -13, 0], ![21, 19, 26, -21, -42], ![-6, -6, -14, 6, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [1, 14, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 20, 7], [6, 2, 16], [0, 1]]
 g := ![![[17, 11, 8], [4, 18, 6], [15, 12, 1], []], ![[7, 15, 15, 20], [2, 0, 12, 15], [15, 9, 20, 5], [17, 3]], ![[3, 5, 3, 1], [18, 12, 14, 6], [16, 20, 17, 6], [8, 3]]]
 h' := ![![[6, 20, 7], [19, 13, 10], [8, 8, 11], [0, 0, 1], [0, 1]], ![[6, 2, 16], [11, 20, 19], [12, 11, 9], [19, 22, 2], [6, 20, 7]], ![[0, 1], [9, 13, 17], [19, 4, 3], [5, 1, 20], [6, 2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 4], []]
 b := ![[], [0, 20, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [1, 14, 11, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2701267, 492590, -562310, 335150, -291900]
  a := ![30, -11, -10, 25, 57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-106771, -200920, 153230, 335150, -291900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![5, 4, 0, 0, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![5, 4, 0, 0, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![13, 0, 1, 0, 0], ![0, 7, 0, 1, 0], ![5, 4, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![5, 4, 0, 0, 1], ![-6, 4, 6, -1, -3], ![15, 4, 0, 12, 3], ![12, -2, -10, 17, 33], ![-29, -7, 11, -5, -16]]]
  hmulB := by decide  
  f := ![![![1293998, -909516, -1325352, 222188, 656405], ![151685, 5080516, -2484, 0, 0]], ![![862039, -605899, -882924, 148018, 437285], ![101039, 3384542, -1656, 0, 0]], ![![726706, -510780, -744313, 124780, 368635], ![85180, 2853200, -1395, 0, 0]], ![![262356, -184407, -268716, 45049, 133086], ![30768, 1030078, -504, 0, 0]], ![![431222, -303096, -441672, 74044, 218746], ![50555, 1693076, -828, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-13, 0, 23, 0, 0], ![0, -7, 0, 23, 0], ![-5, -4, 0, 0, 23]], ![![0, 0, 0, 0, 1], ![-3, 1, 6, -1, -3], ![0, -4, 0, 12, 3], ![-1, -11, -10, 17, 33], ![-4, 4, 11, -5, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 22], [0, 1]]
 g := ![![[7, 8], [1, 6], [19, 4], [1]], ![[0, 15], [13, 17], [4, 19], [1]]]
 h' := ![![[2, 22], [20, 13], [12, 12], [20, 2], [0, 1]], ![[0, 1], [0, 10], [13, 11], [1, 21], [2, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [17, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [3, 21, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6194, -1981, 1213, -1633, -846]
  a := ![20, -6, -10, 20, 39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-771, 558, 1213, -1633, -846]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-5, -6, 0, 1, 0]] ![![23, 0, 0, 0, 0], ![5, 4, 0, 0, 1]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![115, 92, 0, 0, 23]], ![![-115, -138, 0, 23, 0], ![23, -46, -46, 23, 46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![5, 4, 0, 0, 1]]], ![![![-5, -6, 0, 1, 0]], ![![1, -2, -2, 1, 2]]]]
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


lemma PB512I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB512I0 : PrimesBelowBoundCertificateInterval O 1 23 512 where
  m := 9
  g := ![5, 5, 5, 3, 2, 1, 3, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB512I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N2, I3N2, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![343, 7, 7]
    · exact ![1331, 121]
    · exact ![371293]
    · exact ![289, 289, 17]
    · exact ![361, 361, 19]
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
      exact NI3N1
      exact NI3N2
      exact NI3N2
      exact NI3N2
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
      exact NI7N2
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
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I7N2, I11N1, I17N0, I17N1, I17N2, I19N0, I19N1, I19N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N2, I3N2, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N1], [], [I17N0, I17N1, I17N2], [I19N0, I19N1, I19N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
