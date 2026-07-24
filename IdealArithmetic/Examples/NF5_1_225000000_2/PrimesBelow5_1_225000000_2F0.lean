
import IdealArithmetic.Examples.NF5_1_225000000_2.RI5_1_225000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 2, -3, -1, -3]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![0, 2, -3, -1, -3]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 2, -3, -1, -3], ![-6, 5, -6, -2, -6], ![-12, 4, -11, -4, -12], ![-9, 2, -11, -2, -9], ![6, -4, 7, 2, 8]]]
  hmulB := by decide  
  f := ![![![346, -34, 47, 17, 54], ![-194, 76, 18, 2, 0]], ![![-3, 1, 0, 0, 0], ![2, -1, 0, 0, 0]], ![![18, -2, 3, 1, 3], ![-10, 4, 1, 0, 0]], ![![155, -17, 24, 9, 27], ![-85, 34, 8, 1, 0]], ![![173, -18, 25, 9, 29], ![-96, 38, 9, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![2, 2, -3, -1, -3], ![1, 5, -6, -2, -6], ![2, 4, -11, -4, -12], ![1, 2, -11, -2, -9], ![-2, -4, 7, 2, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-7, 10, -4, -1, -5], ![-6, 7, -2, 0, -2], ![0, 2, 3, 0, 4], ![3, -12, 6, -1, -3], ![6, -6, 0, 2, 3]]]
  hmulB := by decide  
  f := ![![![15, -8, -4, -2, -5], ![-8, 12, 0, 0, -2]], ![![4, -6, 3, 1, 4], ![2, -1, 0, 0, 0]], ![![1, -2, 4, 1, 5], ![2, -2, -1, 0, 0]], ![![11, -9, 0, 0, 0], ![-3, 6, 0, 0, -1]], ![![0, -6, 6, 2, 8], ![6, -6, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-3, 10, -4, -1, -5], ![-3, 7, -2, 0, -2], ![0, 2, 3, 0, 4], ![2, -12, 6, -1, -3], ![2, -6, 0, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![6, 7, 2, 3, 12], ![0, -5, 2, -2, -1]]]
  hmulB := by decide  
  f := ![![![-24, -24, 2, -20, -73], ![-22, -24, 0, 12, -2]], ![![-24, -24, 1, -20, -73], ![-23, -22, 0, 12, -2]], ![![-28, -28, 1, -23, -85], ![-27, -25, 0, 14, -2]], ![![2, 2, 1, 2, 6], ![3, 0, 0, -1, 0]], ![![-12, -12, 1, -10, -36], ![-11, -12, 0, 6, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-2, 1, 1, 2, 0], ![-9, 7, 2, 3, 12], ![3, -5, 2, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 2, -3, -1, -3]] ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]]
  ![![2, 0, 0, 0, 0], ![-1, 8, -3, -1, -4]] where
 M := ![![![4, 0, 0, 0, 0], ![-14, 20, -8, -2, -10]], ![![0, 4, -6, -2, -6], ![-33, 38, -19, -5, -22]]]
 hmul := by decide  
 g := ![![![![-115, 24, 35, 35, 28], ![54, -48, -4, 0, 0]], ![![122, -44, -36, -40, -33], ![-54, 52, 6, 0, 0]]], ![![![-185, 36, 53, 54, 41], ![86, -76, -6, 0, 0]], ![![304, -94, -95, -100, -85], ![-139, 130, 14, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-1, 8, -3, -1, -4]] ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]]
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-14, 20, -8, -2, -10]], ![![-2, 16, -6, -2, -8], ![-68, 76, -27, -6, -32]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-7, 8, 0, -1, -5], ![4, -8, 0, 0, 0]]], ![![![-1, 6, 0, -1, -4], ![4, -6, 0, 0, 0]], ![![-34, 30, 0, -3, -16], ![16, -27, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0], ![-8, 13, -7, -2, -8]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![0, 2, 0, 0, 0], ![0, 1, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![9, -12, 7, 2, 8], ![2, 0, 0, 0, 0]]], ![![![8, -12, 7, 2, 8], ![2, 0, 0, 0, 0]], ![![4, -6, 4, 1, 4], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-8, 13, -7, -2, -8]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![-16, 26, -14, -4, -16], ![-20, 24, -14, -4, -16]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![-8, 13, -7, -2, -8]], ![![-10, 12, -7, -2, -8]]]]
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
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![6, 7, 2, 2, 12], ![0, -5, 2, -2, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![1, 0, 2, 0, 0]], ![![0, -3, 2, 0, -1], ![1, -2, -2, 0, -2]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![2, 7, 2, 2, 12], ![0, -5, 2, -2, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-7, 10, -4, -1, -5], ![-6, 7, -2, 0, -2], ![0, 2, 3, 0, 4], ![3, -12, 6, -1, -3], ![6, -6, 0, 2, 3]]]
  hmulB := by decide  
  f := ![![![249, -156, -150, -108, -296], ![-318, 492, 66, -6, 0]], ![![161, -99, -99, -71, -195], ![-209, 322, 43, -4, 0]], ![![167, -104, -102, -73, -201], ![-215, 332, 45, -4, 0]], ![![-79, 46, 56, 38, 107], ![111, -168, -24, 2, 0]], ![![166, -104, -100, -72, -197], ![-212, 328, 44, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![-3, 10, -4, -1, -5], ![-4, 7, -2, 0, -2], ![-6, 2, 3, 0, 4], ![7, -12, 6, -1, -3], ![4, -6, 0, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-1, 10, -6, -2, -7]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-1, 10, -6, -2, -7]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 10, -6, -2, -7], ![-12, 14, -8, -2, -10], ![-12, 16, -10, 0, -4], ![6, -8, 8, -5, 9], ![6, -20, 8, 2, 2]]]
  hmulB := by decide  
  f := ![![![-32467, 916, 622, 2440, -688], ![12612, -8946, -219, 0, 6]], ![![-43307, 1215, 834, 3256, -913], ![16825, -11933, -292, 0, 8]], ![![-21644, 604, 419, 1628, -454], ![8410, -5964, -146, 0, 4]], ![![-10539, 294, 204, 793, -221], ![4095, -2904, -71, 0, 2]], ![![10685, -306, -202, -802, 230], ![-4149, 2944, 72, 0, -2]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-3, 10, -6, -2, -7], ![-8, 14, -8, -2, -10], ![-8, 16, -10, 0, -4], ![2, -8, 8, -5, 9], ![10, -20, 8, 2, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![0, 1, -3, -1, -3]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![0, 3, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![264, -125, 90, 26, 70], ![-210, 120, 0, 0, -12]]], ![![![264, -125, 90, 26, 70], ![-210, 120, 0, 0, -12]], ![![4, -3, 4, 1, 3], ![-1, 2, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, -3, -1, -3]] ![![3, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]]
  ![![3, 0, 0, 0, 0], ![-9, 9, -4, -1, -5]] where
 M := ![![![9, 0, 0, 0, 0], ![-21, 30, -12, -3, -15]], ![![0, 3, -9, -3, -9], ![-27, 31, -17, -5, -20]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, -3, -6, 6, 10], ![21, -30, 0, 0, 0]]], ![![![3, -3, -2, 0, 0], ![3, -3, 0, 0, 0]], ![![-2, -7, -6, 6, 11], ![23, -31, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-9, 9, -4, -1, -5]] ![![3, 0, 0, 0, 0], ![-1, 10, -6, -2, -7]]
  ![![3, 0, 0, 0, 0], ![15, -14, 8, 2, 9]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 30, -18, -6, -21]], ![![-27, 27, -12, -3, -15], ![-87, 80, -26, -5, -30]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-1, 10, -6, -2, -7], ![0, 0, 0, 0, 0]]], ![![![-9, 9, -4, -1, -5], ![0, 0, 0, 0, 0]], ![![-9, 8, 2, 1, 2], ![-4, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![15, -14, 8, 2, 9]] ![![3, 0, 0, 0, 0], ![-1, 10, -6, -2, -7]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 30, -18, -6, -21]], ![![45, -42, 24, 6, 27], ![123, -114, 30, 6, 39]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![-1, 10, -6, -2, -7]]], ![![![15, -14, 8, 2, 9]], ![![41, -38, 10, 2, 13]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N2, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![6, 7, 2, 3, 12], ![0, -5, 2, -2, -1]]]
  hmulB := by decide  
  f := ![![![46, 15, -26, -60, 48], ![-105, -10, 180, -20, 0]], ![![10, 2, -7, -15, 12], ![-19, 0, 45, -5, 0]], ![![34, 10, -20, -45, 36], ![-76, -4, 135, -15, 0]], ![![0, -1, -1, -1, 0], ![0, 2, 3, 0, 0]], ![![26, 7, -16, -36, 29], ![-55, -4, 108, -12, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 5, 0, 0, 0], ![-4, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![-3, 0, 0, 0, 5]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-9, 7, 2, 3, 12], ![0, -5, 2, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![0, 1, -3, -1, -3]] where
 M := ![![![25, 0, 0, 0, 0], ![5, 5, 0, 0, 0]], ![![5, 5, 0, 0, 0], ![1, 2, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![6125, -3924, 3972, 1044, 3012], ![-5180, 4900, 100, 0, 0]], ![![2425, -1553, 1574, 414, 1194], ![-2050, 1940, 40, 0, 0]]], ![![![2425, -1553, 1574, 414, 1194], ![-2050, 1940, 40, 0, 0]], ![![605, -388, 395, 104, 300], ![-508, 484, 10, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![0, 1, -3, -1, -3]] ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-8, 8, -4, -1, -5]] where
 M := ![![![25, 0, 0, 0, 0], ![5, 5, 0, 0, 0]], ![![0, 5, -15, -5, -15], ![-6, 6, -10, -3, -9]]]
 hmul := by decide  
 g := ![![![![23, -18, 24, -9, -15], ![-45, 75, 0, 0, 0]], ![![11, -9, 8, -1, 1], ![-5, 15, 0, 0, 0]]], ![![![10, -9, 5, -2, -2], ![-5, 15, 0, 0, 0]], ![![2, -2, -2, 1, 3], ![8, -8, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-8, 8, -4, -1, -5]] ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-1, 1, 3, 1, 2]] where
 M := ![![![25, 0, 0, 0, 0], ![5, 5, 0, 0, 0]], ![![-40, 40, -20, -5, -25], ![-14, 14, -8, -1, -7]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-8, 8, -4, -1, -5], ![0, 0, 0, 0, 0]], ![![-2, 2, -4, -1, -3], ![4, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-1, 1, 3, 1, 2]] ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![5, 5, 0, 0, 0]], ![![-5, 5, 15, 5, 10], ![5, 0, 10, 5, 10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![-1, 1, 3, 1, 2]], ![![1, 0, 2, 1, 2]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [3, 2, 4, 1, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 3, 6, 2, 4], [4, 3, 6, 4, 1], [0, 0, 6, 3, 1], [2, 0, 3, 5, 1], [0, 1]]
 g := ![![[0, 6, 1], []], ![[1, 4, 6, 0, 4, 5, 4, 2], [2, 4, 2, 2, 3, 2, 4, 1]], ![[0, 0, 3, 0, 0, 5, 5, 4], [5, 6, 5, 1, 1, 5, 4, 1]], ![[4, 2, 1, 2, 0, 2], [6, 6, 3, 1, 3, 1, 1, 1]], ![[0, 2, 1, 6, 6, 2], [5, 6, 2, 3, 2, 6, 0, 1]]]
 h' := ![![[0, 3, 6, 2, 4], [0, 0, 0, 1], [0, 1]], ![[4, 3, 6, 4, 1], [1, 5, 6, 6, 2], [0, 3, 6, 2, 4]], ![[0, 0, 6, 3, 1], [0, 4, 6, 0, 5], [4, 3, 6, 4, 1]], ![[2, 0, 3, 5, 1], [3, 5, 4, 3], [0, 0, 6, 3, 1]], ![[0, 1], [0, 0, 5, 4], [2, 0, 3, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 4, 5, 3], [], [], []]
 b := ![[], [3, 1, 2, 1, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [3, 2, 4, 1, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42830575638067, -84321936270936, 97557342145088, -55928065645788, 31948693197568]
  a := ![-31, -39, -13, -15, -62]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6118653662581, -12045990895848, 13936763163584, -7989723663684, 4564099028224]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [10, 4, 8, 9, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 3, 7], [7, 4, 10, 8, 2], [5, 4, 1, 1, 3], [3, 10, 4, 2, 6], [0, 1]]
 g := ![![[8, 1, 6, 5, 1], [1], []], ![[0, 9, 3, 0, 1, 8], [5, 3, 9, 1, 0, 10], []], ![[5, 2, 9, 4, 7, 2, 7, 7], [1, 1, 5, 4, 8, 2, 5, 8], [1, 5, 3, 4]], ![[0, 3, 9, 6, 4, 9, 6, 4], [3, 2, 2, 1, 9, 4, 2, 1], [2, 7, 4, 9]], ![[2, 9, 5, 8, 7, 1, 0, 10], [1, 6, 1, 8, 10, 5, 1, 6], [9, 8, 5, 3]]]
 h' := ![![[8, 3, 7], [1, 7, 3, 2, 1], [0, 0, 1], [0, 1]], ![[7, 4, 10, 8, 2], [4, 10, 10, 6, 3], [9, 4, 0, 9, 5], [8, 3, 7]], ![[5, 4, 1, 1, 3], [0, 1, 8, 5, 3], [6, 2, 10, 3, 9], [7, 4, 10, 8, 2]], ![[3, 10, 4, 2, 6], [7, 5, 1, 7, 7], [5, 6, 8, 3, 9], [5, 4, 1, 1, 3]], ![[0, 1], [5, 10, 0, 2, 8], [7, 10, 3, 7, 10], [3, 10, 4, 2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 7], [], [], []]
 b := ![[], [2, 8, 8, 7, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [10, 4, 8, 9, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22185104067411384, -44488447703458220, 1475103141266568, -5492098014531546, -56432745381635612]
  a := ![49, -6, 20, -43, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2016827642491944, -4044404336678020, 134100285569688, -499281637684686, -5130249580148692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 161051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-12, 15, -4, -1, -5]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-12, 15, -4, -1, -5]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![3, 12, 1, 0, 0], ![8, 8, 0, 1, 0], ![1, 4, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-12, 15, -4, -1, -5], ![-6, 2, 3, 0, -2], ![0, 7, -2, 10, 4], ![33, 23, 16, 4, 57], ![6, -31, 10, -8, -12]]]
  hmulB := by decide  
  f := ![![![-27491, -3723, 25828, 2065, -7603], ![15925, -91416, -1092, 0, 0]], ![![-11544, -1560, 10842, 864, -3194], ![6682, -38376, -455, 0, 0]], ![![-16821, -2278, 15803, 1261, -4653], ![9743, -55932, -665, 0, 0]], ![![-24016, -3258, 22568, 1803, -6642], ![13918, -79872, -952, 0, 0]], ![![-5663, -771, 5324, 425, -1566], ![3285, -18840, -224, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -12, 13, 0, 0], ![-8, -8, 0, 13, 0], ![-1, -4, 0, 0, 13]], ![![1, 7, -4, -1, -5], ![-1, -2, 3, 0, -2], ![-6, -5, -2, 10, 4], ![-8, -33, 16, 4, 57], ![4, -3, 10, -8, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[4, 12], [3], [4, 1]], ![[0, 1], [3], [8, 12]]]
 h' := ![![[4, 12], [6, 5], [4, 4], [0, 1]], ![[0, 1], [0, 8], [7, 9], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [8, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [12, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![88, 842, -444, 414, 448]
  a := ![-2, -6, -1, -4, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-180, 82, -444, 414, 448]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-9, 7, -4, -1, -5]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-9, 7, -4, -1, -5]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![6, 11, 1, 0, 0], ![6, 8, 0, 1, 0], ![1, 9, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-9, 7, -4, -1, -5], ![-6, 5, -5, 0, -2], ![0, -1, 1, -6, 4], ![-15, -33, 0, -9, -39], ![6, 9, -6, 8, 7]]]
  hmulB := by decide  
  f := ![![![595, -548, 770, -170, 114], ![-962, 2730, -208, 0, 0]], ![![309, -288, 406, -111, 73], ![-507, 1430, -156, 0, 0]], ![![531, -492, 693, -171, 113], ![-867, 2450, -226, 0, 0]], ![![462, -428, 604, -147, 96], ![-760, 2140, -192, 0, 0]], ![![259, -241, 340, -90, 59], ![-426, 1200, -124, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-6, -11, 13, 0, 0], ![-6, -8, 0, 13, 0], ![-1, -9, 0, 0, 13]], ![![2, 8, -4, -1, -5], ![2, 6, -5, 0, -2], ![2, 0, 1, -6, 4], ![6, 30, 0, -9, -39], ![-1, -4, -6, 8, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[2, 1], [1], [9, 1]], ![[11, 12], [1], [5, 12]]]
 h' := ![![[9, 12], [10, 12], [8, 1], [0, 1]], ![[0, 1], [1, 1], [4, 12], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![98657, 85002, 59019, -5234, 193455]
  a := ![53, 81, 22, 38, 105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32116, -174110, 59019, -5234, 193455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![3, 1, 0, 0, 0], ![0, 3, 1, 0, 0], ![0, 1, 3, 2, 0], ![6, 7, 2, 5, 12], ![0, -5, 2, -2, 1]]]
  hmulB := by decide  
  f := ![![![-62198, -92222, -237063, -159640, 720], ![271089, -35451, 1039610, -780, 0]], ![![-15558, -23063, -59282, -39921, 180], ![67809, -8866, 259974, -195, 0]], ![![-20732, -30737, -79010, -53206, 240], ![90360, -11816, 346489, -260, 0]], ![![-57018, -84539, -217310, -146338, 660], ![248512, -32495, 952985, -715, 0]], ![![-23926, -35471, -91178, -61400, 277], ![104281, -13636, 399850, -300, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 13, 0, 0, 0], ![-4, 0, 13, 0, 0], ![-12, 0, 0, 13, 0], ![-5, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![-1, 3, 1, 0, 0], ![-3, 1, 3, 2, 0], ![-11, 7, 2, 5, 12], ![2, -5, 2, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-12, 15, -4, -1, -5]] ![![13, 0, 0, 0, 0], ![-9, 7, -4, -1, -5]]
  ![![13, 0, 0, 0, 0], ![-35, 38, -10, -2, -15]] where
 M := ![![![169, 0, 0, 0, 0], ![-117, 91, -52, -13, -65]], ![![-156, 195, -52, -13, -65], ![3, -17, -1, 5, 18]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![26, -31, 6, 1, 10], ![13, 0, 0, 0, 0]]], ![![![23, -23, 6, 1, 10], ![13, 0, 0, 0, 0]], ![![11, -13, 3, 1, 6], ![4, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-35, 38, -10, -2, -15]] ![![13, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![39, 13, 0, 0, 0]], ![![-455, 494, -130, -26, -195], ![-117, 130, -26, 0, -39]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![3, 1, 0, 0, 0]]], ![![![-35, 38, -10, -2, -15]], ![![-9, 10, -2, 0, -3]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-6, 3, -4, -1, -5]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-6, 3, -4, -1, -5]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![2, 6, 1, 0, 0], ![11, 9, 0, 1, 0], ![11, 3, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-6, 3, -4, -1, -5], ![-6, 8, -9, 0, -2], ![0, -5, 4, -14, 4], ![-39, -61, -8, -14, -87], ![6, 29, -14, 16, 18]]]
  hmulB := by decide  
  f := ![![![-293, 512, -558, 63, -47], ![357, -1190, 51, 0, 0]], ![![-3480, 5871, -6434, 454, -534], ![3910, -13770, 272, 0, 0]], ![![-1250, 2111, -2313, 166, -192], ![1408, -4950, 101, 0, 0]], ![![-2033, 3440, -3768, 281, -314], ![2298, -8060, 177, 0, 0]], ![![-803, 1367, -1496, 121, -124], ![923, -3200, 81, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -6, 17, 0, 0], ![-11, -9, 0, 17, 0], ![-11, -3, 0, 0, 17]], ![![4, 3, -4, -1, -5], ![2, 4, -9, 0, -2], ![6, 5, 4, -14, 4], ![64, 22, -8, -14, -87], ![-20, -5, -14, 16, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [11, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 16], [0, 1]]
 g := ![![[6, 2], [4], [4], [1]], ![[10, 15], [4], [4], [1]]]
 h' := ![![[2, 16], [3, 6], [9, 15], [6, 2], [0, 1]], ![[0, 1], [15, 11], [5, 2], [10, 15], [2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [11, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [11, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![88250, -159561, 192421, -106889, 70964]
  a := ![-63, -71, -26, -17, -125]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5799, -33234, 192421, -106889, 70964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-3, 6, -4, -1, -5]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-3, 6, -4, -1, -5]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![5, 10, 1, 0, 0], ![9, 4, 0, 1, 0], ![5, 7, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-3, 6, -4, -1, -5], ![-6, 11, -6, 0, -2], ![0, -2, 7, -8, 4], ![-21, -40, -2, -5, -51], ![6, 14, -8, 10, 15]]]
  hmulB := by decide  
  f := ![![![-242, 501, -453, 285, -129], ![357, -867, 561, 0, 0]], ![![-1605, 3210, -2633, 1447, -687], ![2159, -5627, 2805, 0, 0]], ![![-1007, 2019, -1669, 930, -436], ![1378, -3543, 1804, 0, 0]], ![![-504, 1017, -857, 492, -227], ![707, -1783, 957, 0, 0]], ![![-731, 1467, -1216, 680, -319], ![1000, -2572, 1320, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-5, -10, 17, 0, 0], ![-9, -4, 0, 17, 0], ![-5, -7, 0, 0, 17]], ![![3, 5, -4, -1, -5], ![2, 5, -6, 0, -2], ![1, -4, 7, -8, 4], ![17, 21, -2, -5, -51], ![-7, -3, -8, 10, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [7, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 16], [0, 1]]
 g := ![![[12, 8], [16], [1], [1]], ![[3, 9], [16], [1], [1]]]
 h' := ![![[1, 16], [3, 12], [8, 4], [10, 1], [0, 1]], ![[0, 1], [15, 5], [12, 13], [11, 16], [1, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [7, 16, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-773, -158704, 92656, -61552, -73120]
  a := ![38, 36, 16, -4, 76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26795, -19248, 92656, -61552, -73120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![6, 7, 2, 3, 12], ![0, -5, 2, -2, -1]]]
  hmulB := by decide  
  f := ![![![192, -223, -398, -816, 192], ![-1615, -34, 7344, -272, 0]], ![![12, -14, -25, -51, 12], ![-101, 0, 459, -17, 0]], ![![180, -209, -373, -765, 180], ![-1514, -33, 6885, -255, 0]], ![![0, -1, -1, -1, 0], ![0, 8, 9, 0, 0]], ![![112, -132, -234, -480, 113], ![-934, -22, 4320, -160, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 17, 0, 0, 0], ![-16, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![-10, 0, 0, 0, 17]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-9, 7, 2, 3, 12], ![-1, -5, 2, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![-6, 3, -4, -1, -5]] ![![17, 0, 0, 0, 0], ![-3, 6, -4, -1, -5]]
  ![![17, 0, 0, 0, 0], ![-18, 18, 6, 3, 2]] where
 M := ![![![289, 0, 0, 0, 0], ![-51, 102, -68, -17, -85]], ![![-102, 51, -68, -17, -85], ![-9, -25, 20, -7, -16]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![15, -12, -10, -4, -7], ![17, 0, 0, 0, 0]]], ![![![12, -15, -10, -4, -7], ![17, 0, 0, 0, 0]], ![![9, -11, -2, -2, -2], ![9, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![-18, 18, 6, 3, 2]] ![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![289, 0, 0, 0, 0], ![17, 17, 0, 0, 0]], ![![-306, 306, 102, 51, 34], ![0, 17, 34, 17, 34]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![-18, 18, 6, 3, 2]], ![![0, 1, 2, 1, 2]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-8, 18, -4, -1, -5]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-8, 18, -4, -1, -5]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![18, 5, 1, 0, 0], ![12, 16, 0, 1, 0], ![0, 12, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-8, 18, -4, -1, -5], ![-6, 6, 6, 0, -2], ![0, 10, 2, 16, 4], ![51, 44, 22, 14, 93], ![6, -46, 16, -14, -14]]]
  hmulB := by decide  
  f := ![![![-79331, 49632, 117702, 6285, -18279], ![60135, -331398, -3705, 0, 0]], ![![-86006, 53797, 127598, 6791, -19823], ![65189, -359271, -3990, 0, 0]], ![![-97464, 60971, 144607, 7716, -22458], ![73884, -407151, -4545, 0, 0]], ![![-122532, 76654, 181788, 9688, -28239], ![92871, -511848, -5700, 0, 0]], ![![-54320, 33978, 80588, 4289, -12520], ![41171, -226908, -2520, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-18, -5, 19, 0, 0], ![-12, -16, 0, 19, 0], ![0, -12, 0, 0, 19]], ![![4, 6, -4, -1, -5], ![-6, 0, 6, 0, -2], ![-12, -16, 2, 16, 4], ![-27, -74, 22, 14, 93], ![-6, 14, 16, -14, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [4, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 18], [0, 1]]
 g := ![![[16, 5], [8, 4], [11], [1]], ![[0, 14], [18, 15], [11], [1]]]
 h' := ![![[12, 18], [6, 9], [10, 17], [15, 12], [0, 1]], ![[0, 1], [0, 10], [5, 2], [7, 7], [12, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [9, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [4, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![229114, 148013, 166429, -38448, 429942]
  a := ![89, 109, 35, 54, 165]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-121328, -275172, 166429, -38448, 429942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-14, 4, -4, -1, -5]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-14, 4, -4, -1, -5]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![8, 11, 1, 0, 0], ![13, 1, 0, 1, 0], ![9, 13, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-14, 4, -4, -1, -5], ![-6, 0, -8, 0, -2], ![0, -4, -4, -12, 4], ![-33, -54, -6, -20, -75], ![6, 24, -12, 14, 8]]]
  hmulB := by decide  
  f := ![![![-30639, -7472, -69744, 3688, -10104], ![38152, -186048, 2660, 0, 0]], ![![-22574, -5523, -51420, 2681, -7431], ![28139, -137142, 1900, 0, 0]], ![![-25850, -6315, -58865, 3091, -8517], ![32209, -157014, 2210, 0, 0]], ![![-22145, -5405, -50424, 2665, -7302], ![27594, -134514, 1920, 0, 0]], ![![-29963, -7317, -68220, 3581, -9872], ![37319, -181962, 2560, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-8, -11, 19, 0, 0], ![-13, -1, 0, 19, 0], ![-9, -13, 0, 0, 19]], ![![4, 6, -4, -1, -5], ![4, 6, -8, 0, -2], ![8, 0, -4, -12, 4], ![50, 53, -6, -20, -75], ![-8, 2, -12, 14, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [1, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18], [0, 1]]
 g := ![![[8, 1], [11, 4], [7], [1]], ![[0, 18], [17, 15], [7], [1]]]
 h' := ![![[11, 18], [8, 1], [13, 17], [18, 11], [0, 1]], ![[0, 1], [0, 18], [10, 2], [6, 8], [11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [10, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [1, 8, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-788, -11506, 5895, -4050, -6497]
  a := ![9, 7, 4, -2, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3325, 640, 5895, -4050, -6497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![3, 1, 0, 0, 0], ![0, 3, 1, 0, 0], ![0, 1, 3, 2, 0], ![6, 7, 2, 5, 12], ![0, -5, 2, -2, 1]]]
  hmulB := by decide  
  f := ![![![28, 5, -12, -8, 0], ![-171, 0, 76, 0, 0]], ![![0, -2, -6, -4, 0], ![1, 0, 38, 0, 0]], ![![10, 1, -6, -4, 0], ![-60, 1, 38, 0, 0]], ![![18, 2, -8, -5, 0], ![-110, 8, 48, 0, 0]], ![![-30, 66, 252, 168, -5], ![174, 44, -1616, 8, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 19, 0, 0, 0], ![-10, 0, 19, 0, 0], ![-12, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![0, 1, 0, 0, 0], ![-1, 3, 1, 0, 0], ![-3, 1, 3, 2, 0], ![-5, 7, 2, 5, 12], ![1, -5, 2, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![-8, 18, -4, -1, -5]] ![![19, 0, 0, 0, 0], ![-14, 4, -4, -1, -5]]
  ![![19, 0, 0, 0, 0], ![59, -56, 5, -1, 12]] where
 M := ![![![361, 0, 0, 0, 0], ![-266, 76, -76, -19, -95]], ![![-152, 342, -76, -19, -95], ![7, -82, -30, 6, 23]]]
 hmul := by decide  
 g := ![![![![-40, 56, -5, 1, -12], ![19, 0, 0, 0, 0]], ![![-14, 4, -4, -1, -5], ![0, 0, 0, 0, 0]]], ![![![-8, 18, -4, -1, -5], ![0, 0, 0, 0, 0]], ![![-40, 34, -5, 1, -7], ![13, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![59, -56, 5, -1, 12]] ![![19, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![361, 0, 0, 0, 0], ![57, 19, 0, 0, 0]], ![![1121, -1064, 95, -19, 228], ![171, -171, -19, -19, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0]], ![![3, 1, 0, 0, 0]]], ![![![59, -56, 5, -1, 12]], ![![9, -9, -1, -1, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-16, 14, -4, -1, -5]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-16, 14, -4, -1, -5]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![4, 6, 1, 0, 0], ![11, 19, 0, 1, 0], ![7, 7, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-16, 14, -4, -1, -5], ![-6, -2, 2, 0, -2], ![0, 6, -6, 8, 4], ![27, 16, 14, -2, 45], ![6, -26, 8, -6, -14]]]
  hmulB := by decide  
  f := ![![![1801, 1118, -878, 48, 644], ![-552, 8372, -207, 0, 0]], ![![8126, 5051, -3960, 203, 2901], ![-2507, 37835, -897, 0, 0]], ![![2412, 1490, -1171, 61, 861], ![-733, 11200, -267, 0, 0]], ![![7579, 4703, -3690, 191, 2706], ![-2328, 35259, -840, 0, 0]], ![![3031, 1869, -1470, 77, 1082], ![-917, 14063, -336, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-4, -6, 23, 0, 0], ![-11, -19, 0, 23, 0], ![-7, -7, 0, 0, 23]], ![![2, 4, -4, -1, -5], ![0, 0, 2, 0, -2], ![-4, -6, -6, 8, 4], ![-14, -15, 14, -2, 45], ![6, 6, 8, -6, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [12, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22], [0, 1]]
 g := ![![[2, 2], [10, 13], [0, 1], [1]], ![[0, 21], [20, 10], [22, 22], [1]]]
 h' := ![![[22, 22], [18, 18], [0, 17], [11, 22], [0, 1]], ![[0, 1], [0, 5], [6, 6], [12, 1], [22, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [12, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![176135, -62969, 232827, -107179, 254406]
  a := ![79, 95, 33, 35, 155]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-59002, -52364, 232827, -107179, 254406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-11, 18, -4, -1, -5]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-11, 18, -4, -1, -5]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![6, 10, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-11, 18, -4, -1, -5], ![-6, 3, 6, 0, -2], ![0, 10, -1, 16, 4], ![51, 44, 22, 11, 93], ![6, -46, 16, -14, -17]]]
  hmulB := by decide  
  f := ![![![-62770, 15003, 83123, 2369, -18857], ![31303, -298011, -1449, 0, 0]], ![![-171018, 40840, 226470, 6396, -51390], ![85284, -811923, -3864, 0, 0]], ![![-1792, 417, 2387, 69, -537], ![915, -8547, -42, 0, 0]], ![![-7426, 1760, 9850, 279, -2230], ![3728, -35301, -168, 0, 0]], ![![-90729, 21668, 120150, 3399, -27262], ![45249, -430752, -2058, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-1, 0, 23, 0, 0], ![0, -1, 0, 23, 0], ![-6, -10, 0, 0, 23]], ![![1, 3, -4, -1, -5], ![0, 1, 6, 0, -2], ![-1, -2, -1, 16, 4], ![-23, -39, 22, 11, 93], ![4, 6, 16, -14, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [5, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 22], [0, 1]]
 g := ![![[10, 13], [11, 2], [22, 16], [1]], ![[4, 10], [3, 21], [4, 7], [1]]]
 h' := ![![[19, 22], [14, 17], [5, 18], [18, 19], [0, 1]], ![[0, 1], [15, 6], [2, 5], [11, 4], [19, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [5, 4, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36680, -50010, 70319, -37622, 36679]
  a := ![39, 45, 16, 12, 77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11031, -16486, 70319, -37622, 36679]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-6, 1, 0, 0, 0], ![0, -6, 1, 0, 0], ![0, 1, -6, 2, 0], ![6, 7, 2, -4, 12], ![0, -5, 2, -2, -8]]]
  hmulB := by decide  
  f := ![![![-50687, 125207, -796734, 266294, 840], ![-195914, -65504, -3065601, -1610, 0]], ![![-43445, 107321, -682915, 228252, 720], ![-167922, -56143, -2627658, -1380, 0]], ![![-28966, 71539, -455211, 152146, 480], ![-111958, -37420, -1751519, -920, 0]], ![![-21718, 53658, -341460, 114127, 360], ![-83944, -28080, -1313840, -690, 0]], ![![-46281, 114321, -727453, 243138, 767], ![-178884, -59803, -2799027, -1470, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-17, 23, 0, 0, 0], ![-10, 0, 23, 0, 0], ![-10, 0, 0, 23, 0], ![-21, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![4, -6, 1, 0, 0], ![1, 1, -6, 2, 0], ![-15, 7, 2, -4, 12], ![11, -5, 2, -2, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-16, 14, -4, -1, -5]] ![![23, 0, 0, 0, 0], ![-11, 18, -4, -1, -5]]
  ![![23, 0, 0, 0, 0], ![-64, 103, -63, -18, -73]] where
 M := ![![![529, 0, 0, 0, 0], ![-253, 414, -92, -23, -115]], ![![-368, 322, -92, -23, -115], ![11, -100, 50, 11, 28]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![53, -85, 59, 17, 68], ![23, 0, 0, 0, 0]]], ![![![48, -89, 59, 17, 68], ![23, 0, 0, 0, 0]], ![![45, -76, 46, 13, 52], ![16, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-64, 103, -63, -18, -73]] ![![23, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![-138, 23, 0, 0, 0]], ![![-1472, 2369, -1449, -414, -1679], ![276, -506, 299, 92, 368]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![-6, 1, 0, 0, 0]]], ![![![-64, 103, -63, -18, -73]], ![![12, -22, 13, 4, 16]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB934I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB934I0 : PrimesBelowBoundCertificateInterval O 1 23 934 where
  m := 9
  g := ![5, 5, 5, 1, 1, 3, 3, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB934I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N2, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![161051]
    · exact ![169, 169, 13]
    · exact ![289, 289, 17]
    · exact ![361, 361, 19]
    · exact ![529, 529, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
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
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I13N0, I13N1, I13N2, I17N0, I17N1, I17N2, I19N0, I19N1, I19N2, I23N0, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N2, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [], [I13N0, I13N1, I13N2], [I17N0, I17N1, I17N2], [I19N0, I19N1, I19N2], [I23N0, I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
