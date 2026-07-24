
import IdealArithmetic.Examples.NF5_1_337500000_4.RI5_1_337500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-1, -1, 0, 1, -1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-1, -1, 0, 1, -1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-1, -1, 0, 1, -1], ![8, 3, -2, -4, 6], ![-54, -16, 5, 6, -24], ![50, 13, -6, -6, 13], ![-3, 4, 0, -3, -1]]]
  hmulB := by decide  
  f := ![![![1720, 124, -568, -323, 970], ![-1566, -532, 12, -2, 0]], ![![-2, 1, 1, 0, -1], ![4, 1, 0, 0, 0]], ![![-122, -8, 41, 22, -69], ![114, 38, -1, 0, 0]], ![![860, 62, -284, -161, 485], ![-783, -266, 6, -1, 0]], ![![-856, -61, 283, 160, -482], ![782, 265, -6, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-1, -1, 0, 1, -1], ![6, 3, -2, -4, 6], ![-30, -16, 5, 6, -24], ![28, 13, -6, -6, 13], ![0, 4, 0, -3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![3, 0, 0, 0, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![3, 0, 0, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![3, 0, 0, 0, 1], ![-10, -2, 1, 2, 0], ![-3, -13, 0, 3, 12], ![-19, -6, 0, 2, -1], ![-6, -5, -1, 0, 2]]]
  hmulB := by decide  
  f := ![![![-2, 0, 0, 0, -1], ![2, 0, 0, 0, 0]], ![![14, 43, 0, -10, -38], ![2, 1, 6, 0, 1]], ![![-1, 1, 0, -1, -2], ![4, 1, 0, 0, 0]], ![![-12, -36, 0, 9, 32], ![-2, -1, -5, 0, -1]], ![![-1, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![1, 0, 0, 0, 1], ![-6, -2, 1, 2, 0], ![-9, -13, 0, 3, 12], ![-10, -6, 0, 2, -1], ![-4, -5, -1, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![1, -1, 3, 7, 0], ![-2, -1, 0, -1, 6], ![-10, -5, 1, 2, 1]]]
  hmulB := by decide  
  f := ![![![0, 1, -3, -7, 0], ![0, 0, 2, 0, 0]], ![![-2, 0, -3, -7, 0], ![3, 0, 2, 0, 0]], ![![0, 0, 1, 0, 0], ![1, -1, 0, 0, 0]], ![![0, 0, -2, -3, 0], ![0, 1, 1, 0, 0]], ![![-4, 11, -23, -57, 0], ![2, -3, 16, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-4, -1, 3, 7, 0], ![0, -1, 0, -1, 6], ![-4, -5, 1, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-1, -1, 0, 1, -1]] ![![2, 0, 0, 0, 0], ![3, 0, 0, 0, 1]]
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![6, 0, 0, 0, 2]], ![![-2, -2, 0, 2, -2], ![-6, 1, 0, 0, -4]]]
 hmul := by decide  
 g := ![![![![0, 2, -4, -14, 0], ![0, 0, 4, 0, 0]], ![![0, 4, -5, -21, 1], ![-2, -2, 6, 0, 0]]], ![![![0, -2, 0, 8, -1], ![0, 4, -2, 0, 0]], ![![0, -4, 4, 21, -2], ![3, 4, -6, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![3, 0, 0, 0, 1]]
  ![![2, 0, 0, 0, 0], ![1, -1, 0, 1, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![6, 0, 0, 0, 2]], ![![0, 2, 0, 0, 0], ![-10, -2, 1, 2, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, 1, 0, -1, 1], ![2, 0, 0, 0, 0]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-6, -1, 0, 0, 3], ![0, -1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![1, -1, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0], ![-9, -1, 1, 1, -2]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![2, -2, 0, 2, 0], ![-1, -1, -1, -1, 6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![1, -1, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-5, -1, 0, 0, 2], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-9, -1, 1, 1, -2]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![-18, -2, 2, 2, -4], ![10, -2, 0, 2, 4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![-9, -1, 1, 1, -2]], ![![5, -1, 0, 1, 2]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![3, 0, 0, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![3, 0, 0, 0, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![3, 0, 0, 0, 1], ![-10, -2, 1, 2, 0], ![-3, -13, 0, 3, 12], ![-19, -6, 0, 2, -1], ![-6, -5, -1, 0, 2]]]
  hmulB := by decide  
  f := ![![![-4197, -3132, 714, 1820, 2686], ![-3300, -2142, -396, 6, 0]], ![![21, 17, -4, -10, -15], ![21, 12, 2, 0, 0]], ![![675, 506, -115, -294, -435], ![536, 346, 64, -1, 0]], ![![-1400, -1044, 238, 607, 895], ![-1099, -714, -132, 2, 0]], ![![-1, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 0, 0, 0, 1], ![-4, -2, 1, 2, 0], ![-2, -13, 0, 3, 12], ![-7, -6, 0, 2, -1], ![-2, -5, -1, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, -1, 0, 1, -1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![0, -1, 0, 1, -1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, -1, 0, 1, -1], ![8, 4, -2, -4, 6], ![-54, -16, 6, 6, -24], ![50, 13, -6, -5, 13], ![-3, 4, 0, -3, 0]]]
  hmulB := by decide  
  f := ![![![62073, 21092, -14562, -19820, 35878], ![-25596, -20691, 372, -12, 0]], ![![324, 111, -76, -104, 188], ![-132, -108, 2, 0, 0]], ![![-10344, -3514, 2427, 3302, -5978], ![4268, 3448, -62, 2, 0]], ![![20529, 6976, -4816, -6555, 11866], ![-8464, -6843, 123, -4, 0]], ![![20691, 7031, -4854, -6607, 11960], ![-8531, -6897, 124, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![0, -1, 0, 1, -1], ![2, 4, -2, -4, 6], ![-12, -16, 6, 6, -24], ![14, 13, -6, -5, 13], ![0, 4, 0, -3, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![1, -1, 1, 7, 0], ![-2, -1, 0, -3, 6], ![-10, -5, 1, 2, -1]]]
  hmulB := by decide  
  f := ![![![186, -152, 59, 444, 2], ![303, 9, -192, 0, 6]], ![![186, -152, 59, 444, 2], ![304, 9, -192, 0, 6]], ![![184, -150, 58, 437, 2], ![301, 10, -189, 0, 6]], ![![2, 1, -2, 5, 0], ![3, 8, -2, 0, 0]], ![![62, -50, 19, 148, 1], ![101, 5, -64, 0, 2]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![-2, -1, 1, 7, 0], ![-1, -1, 0, -3, 6], ![-1, -5, 1, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![3, 0, 0, 0, 1]] ![![3, 0, 0, 0, 0], ![0, -1, 0, 1, -1]]
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![0, -3, 0, 3, -3]], ![![9, 0, 0, 0, 3], ![-3, 1, 0, 0, -3]]]
 hmul := by decide  
 g := ![![![![0, 4, -6, -21, 0], ![-3, 0, 9, 0, 0]], ![![0, -1, 0, 1, -1], ![0, 0, 0, 0, 0]]], ![![![0, 4, -6, -21, 1], ![-3, 0, 9, 0, 0]], ![![0, -2, 1, 7, -1], ![4, 3, -3, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![-11, -1, 1, 1, -3]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![0, 3, 0, 0, 0], ![0, -1, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![23, -2, 2, 8, -6], ![-42, -18, 0, 0, 0]], ![![0, 3, -2, -5, 6], ![24, 9, 0, 0, 0]]], ![![![4, 2, -1, -2, 3], ![9, 3, 0, 0, 0]], ![![6, 0, 0, 0, 1], ![-1, -1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-11, -1, 1, 1, -3]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![1, 0, 0, 1, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![-33, -3, 3, 3, -9], ![40, 3, -3, -2, 9]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, -1, 0], ![3, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-11, -1, 1, 1, -3], ![0, 0, 0, 0, 0]], ![![12, 1, -1, -2, 3], ![4, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![1, 0, 0, 1, 0]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![3, 0, 0, 3, 0], ![-3, 0, 0, -3, 6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![1, 0, 0, 1, 0]], ![![-1, 0, 0, -1, 2]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![1, -1, 4, 7, 0], ![-2, -1, 0, 0, 6], ![-10, -5, 1, 2, 2]]]
  hmulB := by decide  
  f := ![![![-13, -3, -17, -28, 0], ![25, 5, 20, 0, 0]], ![![-14, -3, -17, -28, 0], ![26, 5, 20, 0, 0]], ![![-1, -1, 0, 0, 0], ![3, 1, 0, 0, 0]], ![![-6, -2, -7, -11, 0], ![12, 3, 8, 0, 0]], ![![48, 2, 65, 112, 5], ![-84, -5, -80, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 5, 0, 0, 0], ![-1, 0, 5, 0, 0], ![-2, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-3, -1, 4, 7, 0], ![0, -1, 0, 0, 6], ![-1, -5, 1, 2, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 1]] where
 M := ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![10, 5, 0, 0, 0], ![4, 4, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1087, -156, 250, 160, -26], ![-470, -650, 50, 0, 0]], ![![-588, -89, 135, 90, -10], ![-250, -350, 25, 0, 0]]], ![![![-588, -89, 135, 90, -10], ![-250, -350, 25, 0, 0]], ![![-270, -42, 62, 42, -4], ![-112, -160, 11, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 1]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-13, -3, 1, 1, -4]] where
 M := ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![10, 5, 0, 0, 5], ![-6, -1, 2, 2, 2]]]
 hmul := by decide  
 g := ![![![![44, -11, -13, -3, -18], ![-60, -25, 0, 0, 0]], ![![15, 0, -3, -1, -2], ![-10, -5, 0, 0, 0]]], ![![![15, 0, -3, -1, -1], ![-10, -5, 0, 0, 0]], ![![4, 5, 2, 0, 8], ![17, 5, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-13, -3, 1, 1, -4]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-16, -3, 1, 2, -6]] where
 M := ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![-65, -15, 5, 5, -20], ![13, -1, -3, -1, -2]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![3, 0, 0, -1, 2], ![5, 0, 0, 0, 0]], ![![9, 1, -1, -1, 2], ![2, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-16, -3, 1, 2, -6]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![-80, -15, 5, 10, -30], ![25, 5, -5, -5, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0]], ![![2, 1, 0, 0, 0]]], ![![![-16, -3, 1, 2, -6]], ![![5, 1, -1, -1, 0]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1738034, 68800, -115596, -174573, 438508]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![1738034, 68800, -115596, -174573, 438508]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![2, 2, 1, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![1738034, 68800, -115596, -174573, 438508], ![-4151530, -164337, 276116, 416990, -1047438], ![9916516, 392554, -659543, -996044, 2501940], ![-7058493, -279406, 469458, 708974, -1780870], ![344627, 13646, -22920, -34615, 86947]]]
  hmulB := by decide  
  f := ![![![-608, -130, 74, 23, -158]], ![![1608, 85, -140, 156, 138]], ![![24, 116, -27, -94, 128]], ![![-215, -1004, 232, 810, -1096]], ![![1589, 340, -194, -61, 415]]]
  g := ![![![281318, 42856, -115596, -24939, 62644], ![-671966, -102367, 276116, 59570, -149634], ![1605086, 244520, -659543, -142292, 357420], ![-1142487, -174046, 469458, 101282, -254410], ![55781, 8498, -22920, -4945, 12421]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [6, 0, 1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 0, 2], [0, 6], [0, 1, 0, 5], [0, 1]]
 g := ![![[0, 6, 0, 1], []], ![[0, 6, 0, 0, 0, 2], [0, 6, 0, 1, 0, 1]], ![[0, 1, 0, 6], []], ![[0, 1, 0, 0, 0, 5], [0, 1, 0, 6, 0, 6]]]
 h' := ![![[0, 6, 0, 2], [0, 0, 0, 1], [0, 1]], ![[0, 6], [0, 6, 0, 1], [0, 6, 0, 2]], ![[0, 1, 0, 5], [0, 0, 0, 6], [0, 6]], ![[0, 1], [0, 1, 0, 6], [0, 1, 0, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6], []]
 b := ![[], [], [0, 3, 0, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [6, 0, 1, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13199422326, 24048699506, 61037592892, 77839866412, 61536534374]
  a := ![40, 29, -14, -10, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15553680494, -14003783754, 61037592892, 11119980916, 8790933482]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-608, -130, 74, 23, -158]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-608, -130, 74, 23, -158]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-608, -130, 74, 23, -158], ![1608, 85, -140, 156, 138], ![-1832, 902, -57, -1016, 936], ![-215, -1004, 232, 810, -1096], ![1589, 340, -194, -61, 415]]]
  hmulB := by decide  
  f := ![![![1738034, 68800, -115596, -174573, 438508]], ![![151796, 6009, -10096, -15247, 38298]], ![![2658098, 105222, -176789, -266987, 670640]], ![![-511775, -20258, 34038, 51404, -129122]], ![![297523, 11778, -19788, -29884, 75065]]]
  g := ![![![-68, -130, 74, 23, -158], ![229, 85, -140, 156, 138], ![-451, 902, -57, -1016, 936], ![159, -1004, 232, 810, -1096], ![178, 340, -194, -61, 415]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![1738034, 68800, -115596, -174573, 438508]] ![![-608, -130, 74, 23, -158]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-7, -5, 1, 1, -2]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-7, -5, 1, 1, -2]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![5, 2, 5, 1, 0], ![6, 9, 2, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-7, -5, 1, 1, -2], ![19, 1, -5, 1, 6], ![-67, -7, -3, -25, 6], ![21, -7, -1, 13, -22], ![40, 16, -6, -8, 6]]]
  hmulB := by decide  
  f := ![![![130, -21, -39, 15, 42], ![-66, -99, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-36, 12, 13, -6, -12], ![33, 33, 0, 0, 0]], ![![44, -3, -12, 4, 14], ![-13, -30, 0, 0, 0]], ![![65, -8, -19, 7, 21], ![-29, -48, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-5, -2, -5, 11, 0], ![-6, -9, -2, 0, 11]], ![![0, 1, 0, 1, -2], ![-2, -5, -2, 1, 6], ![2, -1, 10, -25, 6], ![8, 15, -2, 13, -22], ![4, -2, 2, -8, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 2, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 9, 1], [6, 1, 10], [0, 1]]
 g := ![![[3, 6, 4], [9, 0, 1], []], ![[7, 7, 6, 4], [10, 2, 3, 1], [7, 1]], ![[5, 7], [8, 6, 5, 7], [9, 1]]]
 h' := ![![[5, 9, 1], [4, 4, 9], [0, 0, 1], [0, 1]], ![[6, 1, 10], [2, 9, 2], [0, 8, 1], [5, 9, 1]], ![[0, 1], [3, 9], [7, 3, 9], [6, 1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 1], []]
 b := ![[], [2, 7, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 2, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1284122300178, -959995767444, 41045004936, 333955454497, 551272082283]
  a := ![655, 480, -244, -196, -2389]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-569230187851, -599032310635, -248297857465, 333955454497, 551272082283]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![4, 4, 0, 0, 1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![4, 4, 0, 0, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 5, 0, 1, 0], ![4, 4, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![4, 4, 0, 0, 1], ![-10, -1, 5, 2, 0], ![1, -17, 9, 31, 12], ![-27, -10, 0, -5, 23], ![-46, -25, 3, 8, 3]]]
  hmulB := by decide  
  f := ![![![25387, 87, -14663, -6742, -1217], ![9163, 31625, 352, 0, 0]], ![![9578, 30, -5533, -2542, -459], ![3465, 11935, 132, 0, 0]], ![![6635, 23, -3832, -1762, -318], ![2394, 8265, 92, 0, 0]], ![![13586, 46, -7847, -3607, -651], ![4905, 16925, 188, 0, 0]], ![![12716, 44, -7344, -3376, -609], ![4588, 15840, 176, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, 0, 11, 0, 0], ![-4, -5, 0, 11, 0], ![-4, -4, 0, 0, 11]], ![![0, 0, 0, 0, 1], ![-3, -1, 5, 2, 0], ![-18, -20, 9, 31, 12], ![-9, -7, 0, -5, 23], ![-9, -7, 3, 8, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 3, 1] where
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
 g := ![![[4, 5], [5, 9], [1]], ![[0, 6], [0, 2], [1]]]
 h' := ![![[8, 10], [10, 7], [2, 8], [0, 1]], ![[0, 1], [0, 4], [0, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [9, 3, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2208, -181300, -89324, -28459, 8880]
  a := ![66, 41, -12, 13, -225]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31280, -6775, -89324, -28459, 8880]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-7, -5, 1, 1, -2]] ![![11, 0, 0, 0, 0], ![4, 4, 0, 0, 1]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![44, 44, 0, 0, 11]], ![![-77, -55, 11, 11, -22], ![88, 0, -22, 0, 22]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![4, 4, 0, 0, 1]]], ![![![-7, -5, 1, 1, -2]], ![![8, 0, -2, 0, 2]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![1, 2, 1, 1, 3]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![1, 2, 1, 1, 3]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![5, 5, 2, 1, 0], ![3, 12, 4, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![1, 2, 1, 1, 3], ![-31, -16, 7, 11, 6], ![-75, -79, 4, 39, 66], ![-88, -44, -1, 2, 15], ![-60, -44, -4, 6, 9]]]
  hmulB := by decide  
  f := ![![![679, 344, -158, -246, -144], ![52, 286, 0, 0, 0]], ![![-340, -173, 78, 122, 69], ![-13, -143, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![130, 65, -31, -48, -30], ![20, 55, 0, 0, 0]], ![![-157, -80, 36, 56, 31], ![-2, -66, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-5, -5, -2, 13, 0], ![-3, -12, -4, 0, 13]], ![![-1, -3, -1, 1, 3], ![-8, -11, -3, 11, 6], ![-36, -82, -26, 39, 66], ![-11, -18, -5, 2, 15], ![-9, -14, -4, 6, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [3, 11, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 3], [10, 12, 10], [0, 1]]
 g := ![![[3, 1, 12], [5, 1], [1]], ![[0, 5, 9, 4], [0, 12], [6, 7, 1, 1]], ![[9, 5, 8, 1], [4, 10], [6, 10, 11, 12]]]
 h' := ![![[4, 0, 3], [7, 8, 5], [10, 2, 1], [0, 1]], ![[10, 12, 10], [10, 7, 6], [7, 4, 5], [4, 0, 3]], ![[0, 1], [11, 11, 2], [7, 7, 7], [10, 12, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 4], []]
 b := ![[], [0, 8, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [3, 11, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-129189983, -51717682, 20131546, 21247702, -42666750]
  a := ![-46, -14, -10, -70, 126]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8263711, 27234216, 11407934, 21247702, -42666750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![2, 4, 0, 0, 1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![2, 4, 0, 0, 1]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![2, 1, 1, 0, 0], ![3, 9, 0, 1, 0], ![2, 4, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![2, 4, 0, 0, 1], ![-10, -3, 5, 2, 0], ![1, -17, 7, 31, 12], ![-27, -10, 0, -7, 23], ![-46, -25, 3, 8, 1]]]
  hmulB := by decide  
  f := ![![![-17617, -3722, 8866, 2644, -87], ![-3861, -23634, 416, 0, 0]], ![![-48638, -10280, 24479, 7310, -236], ![-10660, -65247, 1144, 0, 0]], ![![-6112, -1292, 3076, 918, -30], ![-1338, -8199, 144, 0, 0]], ![![-37739, -7978, 18993, 5671, -184], ![-8264, -50625, 888, 0, 0]], ![![-17676, -3736, 8896, 2656, -86], ![-3873, -23712, 416, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -1, 13, 0, 0], ![-3, -9, 0, 13, 0], ![-2, -4, 0, 0, 13]], ![![0, 0, 0, 0, 1], ![-2, -2, 5, 2, 0], ![-10, -27, 7, 31, 12], ![-4, -3, 0, -7, 23], ![-6, -8, 3, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 9, 1] where
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

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [12, 9, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-431981, -510733, -157685, -34391, 66770]
  a := ![-76, -56, 27, 17, 281]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11306, -23893, -157685, -34391, 66770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![1, 2, 1, 1, 3]] ![![13, 0, 0, 0, 0], ![2, 4, 0, 0, 1]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![26, 52, 0, 0, 13]], ![![13, 26, 13, 13, 39], ![-182, -104, 26, 52, 39]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![2, 4, 0, 0, 1]]], ![![![1, 2, 1, 1, 3]], ![![-14, -8, 2, 4, 3]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![103, 15, -8, -7, 29]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![103, 15, -8, -7, 29]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![10, 14, 5, 15, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![103, 15, -8, -7, 29], ![-284, -27, 28, 16, -42], ![416, -118, -13, 80, 96], ![-336, 9, 2, -28, 31], ![-167, -74, 10, 13, -15]]]
  hmulB := by decide  
  f := ![![![-102, -15, 8, 7, -29], ![17, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-60, -8, 5, 5, -17], ![10, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-10, -14, -5, -15, 17]], ![![-11, -23, -9, -26, 29], ![8, 33, 14, 38, -42], ![-32, -86, -29, -80, 96], ![-38, -25, -9, -29, 31], ![-1, 8, 5, 14, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [5, 12, 9, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 1, 13, 2], [7, 4, 1, 4], [7, 11, 3, 11], [0, 1]]
 g := ![![[5, 3, 3, 8], [6, 6, 2], [1], []], ![[12, 5, 10, 1, 12, 9], [8, 16, 15], [9, 3, 4], [15, 8, 4]], ![[0, 0, 1, 11, 16, 16], [2, 4, 9], [13, 9, 13], [3, 2, 16]], ![[4, 13, 16, 4, 13, 3], [5, 4, 16], [15, 14, 2], [4, 10, 2]]]
 h' := ![![[9, 1, 13, 2], [12, 1, 13, 12], [12, 5, 8, 6], [0, 0, 1], [0, 1]], ![[7, 4, 1, 4], [7, 8, 12, 8], [8, 3, 15, 10], [6, 2, 1, 15], [9, 1, 13, 2]], ![[7, 11, 3, 11], [16, 8, 16, 2], [3, 3, 14, 14], [0, 10, 1, 8], [7, 4, 1, 4]], ![[0, 1], [10, 0, 10, 12], [1, 6, 14, 4], [12, 5, 14, 11], [7, 11, 3, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 5, 1], []]
 b := ![[], [], [16, 15, 12, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [5, 12, 9, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23404734655, 22012412826, 17781740974, 18250540137, 9284471481]
  a := ![24, 20, -12, -17, -93]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4084704715, -6351187524, -1684742143, -7118619534, 9284471481]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![1, -1, -3, 7, 0], ![-2, -1, 0, -7, 6], ![-10, -5, 1, 2, -5]]]
  hmulB := by decide  
  f := ![![![-248870, 56492, 14701, -35938, 312], ![-828529, 9265, 86394, -884, 0]], ![![-186490, 42335, 11015, -26929, 234], ![-620856, 6953, 64736, -663, 0]], ![![-186836, 42410, 11036, -26978, 234], ![-622008, 6954, 64855, -663, 0]], ![![-186640, 42367, 11025, -26952, 234], ![-621355, 6951, 64792, -663, 0]], ![![-204950, 46526, 12106, -29596, 257], ![-682312, 7642, 71148, -728, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-12, 17, 0, 0, 0], ![-9, 0, 17, 0, 0], ![-13, 0, 0, 17, 0], ![-14, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![3, -5, 1, 0, 0], ![-3, -1, -3, 7, 0], ![1, -1, 0, -7, 6], ![5, -5, 1, 2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![103, 15, -8, -7, 29]] ![![17, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![289, 0, 0, 0, 0], ![-85, 17, 0, 0, 0]], ![![1751, 255, -136, -119, 493], ![-799, -102, 68, 51, -187]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0]], ![![-5, 1, 0, 0, 0]]], ![![![103, 15, -8, -7, 29]], ![![-47, -6, 4, 3, -11]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [13, 15, 7, 8, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 14, 12, 16, 1], [18, 2, 10, 16, 13], [0, 14, 13, 0, 16], [12, 7, 3, 6, 8], [0, 1]]
 g := ![![[11, 5, 4], [12, 16, 12, 1, 1], [], []], ![[3, 11, 14, 1, 12, 14, 10, 17], [14, 18, 7, 15, 8, 13, 1, 17], [5, 14, 8, 16], [9, 1, 14, 1]], ![[7, 17, 13, 18, 12, 17, 12, 8], [17, 7, 13, 12, 14, 1, 3, 13], [0, 5, 0, 16], [15, 15, 15, 17]], ![[2, 14, 15, 0, 8, 15, 8, 4], [1, 11, 6, 2, 6, 13, 10, 9], [1, 15, 10, 4], [1, 11, 9, 9]], ![[11, 14, 14, 16, 6, 15, 17, 3], [10, 14, 18, 16, 4, 9, 9, 2], [2, 3, 6, 4], [14, 17, 8, 7]]]
 h' := ![![[9, 14, 12, 16, 1], [15, 11, 14, 17], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[18, 2, 10, 16, 13], [0, 17, 9, 9, 13], [15, 7, 17, 5, 13], [2, 9, 0, 18, 4], [9, 14, 12, 16, 1]], ![[0, 14, 13, 0, 16], [17, 7, 0, 0, 9], [16, 2, 14, 1, 18], [15, 13, 10, 2, 15], [18, 2, 10, 16, 13]], ![[12, 7, 3, 6, 8], [6, 9, 9, 5, 10], [4, 3, 2, 4, 15], [6, 13, 2, 8, 17], [0, 14, 13, 0, 16]], ![[0, 1], [2, 13, 6, 7, 6], [12, 7, 5, 9, 10], [0, 3, 6, 10, 2], [12, 7, 3, 6, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 0, 11, 4], [], [], []]
 b := ![[], [0, 14, 8, 0, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [13, 15, 7, 8, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1952271828568361, -1516920899936385, -358045877873805, -78378652056975, 277162829154765]
  a := ![-76, -45, 15, -25, 255]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-102751148872019, -79837942101915, -18844519888095, -4125192213525, 14587517323935]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [19, 4, 17, 20, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9, 14, 19, 21], [0, 3, 22, 2, 17], [8, 19, 9, 11, 10], [15, 14, 1, 14, 21], [0, 1]]
 g := ![![[19, 18, 6, 20, 12], [10, 9, 14, 17, 3], [1], []], ![[3, 10, 6, 8, 21, 2, 7, 22], [4, 1, 1, 21, 21, 11], [17, 17, 12, 9, 21, 11, 13, 7], [13, 4, 21, 4]], ![[2, 0, 7, 16, 13, 1, 20, 20], [5, 2, 13, 16, 21, 7], [6, 12, 14, 10, 14, 14, 9, 11], [20, 18, 21, 13]], ![[19, 4, 13, 16, 5, 18, 13, 10], [3, 17, 17, 11, 12, 7, 14, 19], [4, 8, 8, 18, 16, 4, 18, 11], [3, 3, 0, 8]], ![[9, 9, 8, 11, 11, 7, 5, 5], [8, 17, 20, 12, 20, 2, 15, 10], [5, 18, 6, 22, 4, 19, 3, 19], [14, 8, 18, 4]]]
 h' := ![![[7, 9, 14, 19, 21], [17, 12, 2, 22, 9], [4, 19, 6, 3, 7], [0, 0, 1], [0, 1]], ![[0, 3, 22, 2, 17], [8, 1, 5, 20, 9], [14, 17, 7, 11], [9, 21, 9, 7, 10], [7, 9, 14, 19, 21]], ![[8, 19, 9, 11, 10], [20, 14, 3, 9, 9], [1, 19, 16, 8], [11, 15, 3, 15, 5], [0, 3, 22, 2, 17]], ![[15, 14, 1, 14, 21], [1, 2, 15, 8, 22], [17, 12, 2, 18, 8], [7, 5, 5, 2, 13], [8, 19, 9, 11, 10]], ![[0, 1], [19, 17, 21, 10, 20], [4, 2, 15, 6, 8], [5, 5, 5, 22, 18], [15, 14, 1, 14, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 5, 11, 3], [], [], []]
 b := ![[], [14, 19, 9, 15, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [19, 4, 17, 20, 16, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-602485428283920, -456196418074147, -90602432155893, -1447515743001, 120697766500210]
  a := ![-52, -34, 12, -3, 181]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26195018621040, -19834626872789, -3939236180691, -62935467087, 5247728978270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB1144I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1144I0 : PrimesBelowBoundCertificateInterval O 1 23 1144 where
  m := 9
  g := ![5, 5, 5, 2, 2, 2, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1144I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N2, I3N2, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0]
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
    · exact ![1331, 121]
    · exact ![2197, 169]
    · exact ![83521, 17]
    · exact ![2476099]
    · exact ![6436343]
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N1, I11N1, I13N1, I17N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N2, I3N2, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N1], [I17N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
