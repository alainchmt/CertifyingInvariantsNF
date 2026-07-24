
import IdealArithmetic.Examples.NF5_1_48600000_1.RI5_1_48600000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 2, 1, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 2, 1, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 2, 1, 0, 0], ![0, 3, 3, 1, 0], ![2, 0, 1, 3, 4], ![30, 6, 18, 4, 12], ![-8, 2, -5, -3, -9]]]
  hmulB := by decide  
  f := ![![![-1, 0, -1, -3, -4], ![0, 0, 2, 0, 0]], ![![-2, 0, 0, -1, -2], ![2, -1, 1, 0, 0]], ![![0, -1, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 1, 0, -1, -2], ![-1, 0, 1, 0, 0]], ![![3, -4, -1, -1, 3], ![0, 2, 1, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 2, 1, 0, 0], ![-2, 3, 3, 1, 0], ![-1, 0, 1, 3, 4], ![4, 6, 18, 4, 12], ![0, 2, -5, -3, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![6, -2, 1, 0, 1], ![4, 5, -2, -2, -4], ![-14, 0, -1, 2, 2], ![2, -12, 10, 3, 10], ![6, 7, -5, -3, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, 5, -2, -1, -3], ![2, -1, 0, 0, 0]], ![![1, 2, 0, -1, -2], ![2, 0, 1, 0, 0]], ![![-23, -36, 17, 14, 29], ![0, 12, 0, -1, 0]], ![![4, 1, 0, -1, -1], ![1, 0, 1, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![3, -2, 1, 0, 1], ![2, 5, -2, -2, -4], ![-7, 0, -1, 2, 2], ![1, -12, 10, 3, 10], ![3, 7, -5, -3, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, -3, 1, 1, 2]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, -3, 1, 1, 2]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, -3, 1, 1, 2], ![12, 0, 1, -1, 0], ![-8, 6, -2, -1, -4], ![-28, 0, -2, 5, 4], ![20, -3, 4, -2, 1]]]
  hmulB := by decide  
  f := ![![![-235, -27, -7, 31, 17], ![-40, 38, -12, 0, -2]], ![![6, 2, 0, -1, -1], ![1, -1, 0, 0, 0]], ![![-43, -6, -1, 6, 4], ![-6, 7, -1, 0, 0]], ![![37, 6, 1, -5, -4], ![6, -6, 1, 0, 0]], ![![-118, -12, -4, 15, 8], ![-19, 19, -6, 0, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![1, -3, 1, 1, 2], ![6, 0, 1, -1, 0], ![-5, 6, -2, -1, -4], ![-16, 0, -2, 5, 4], ![11, -3, 4, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![1, 2, 1, 0, 0]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![2, 0, 0, 0, 0], ![6, -4, 3, 1, 3]] where
 M := ![![![4, 0, 0, 0, 0], ![12, -4, 2, 0, 2]], ![![2, 4, 2, 0, 0], ![0, 8, -4, -2, -5]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-6, 6, -5, -2, -5], ![4, 0, 0, 0, 0]]], ![![![-23, -6, -2, -1, 0], ![4, 4, 2, 0, 0]], ![![-21, 6, -8, -3, -7], ![5, 2, 1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![6, -4, 3, 1, 3]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![12, -4, 2, 0, 2]], ![![12, -8, 6, 2, 6], ![-2, -23, 6, 8, 14]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![6, -2, 0, 1, 1], ![0, 0, -2, 0, 0]]], ![![![6, -4, 0, 4, 3], ![0, 0, -6, 0, 0]], ![![-1, -10, 0, 7, 7], ![-3, 0, -6, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![1, -3, 1, 1, 2]]
  ![![2, 0, 0, 0, 0], ![0, -2, 1, 1, 2]] where
 M := ![![![4, 0, 0, 0, 0], ![2, -6, 2, 2, 4]], ![![0, 2, 0, 0, 0], ![12, 0, 1, -1, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, -1, 0, 0, 0], ![2, 0, 0, 0, 0]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, -2, 0, 1, 2], ![-2, 1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, -2, 1, 1, 2]] ![![2, 0, 0, 0, 0], ![1, -3, 1, 1, 2]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, -6, 2, 2, 4]], ![![0, -4, 2, 2, 4], ![-20, 0, 2, 2, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![1, -3, 1, 1, 2]]], ![![![0, -2, 1, 1, 2]], ![![-10, 0, 1, 1, 1]]]]
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
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![0, 0, -1, 1, 0], ![4, 0, 2, 4, 8], ![4, 1, 3, -3, -4]]]
  hmulB := by decide  
  f := ![![![9, -22, -36, 0, 16], ![-6, 72, 24, -6, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, -1, -1, 0, 0], ![1, 2, 0, 0, 0]], ![![0, -1, -1, 0, 0], ![1, 2, 1, 0, 0]], ![![6, -15, -24, 0, 11], ![-3, 48, 16, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![0, 0, -1, 1, 0], ![-4, 0, 2, 4, 8], ![4, 1, 3, -3, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 2, 2, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 2, 5, 8], ![4, 1, 3, -3, -3]]]
  hmulB := by decide  
  f := ![![![0, -1, 0, 0, 0], ![3, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, -2, -1, 0, 0], ![2, 2, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]], ![![0, -2, 0, 0, 3], ![4, 1, 5, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-2, 2, 2, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 2, 5, 8], ![-1, 1, 3, -3, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, -2, 1, 0], ![4, 0, 2, 3, 8], ![4, 1, 3, -3, -5]]]
  hmulB := by decide  
  f := ![![![18, -9, 10, 0, 16], ![27, 9, 18, -6, 0]], ![![10, -5, 4, 0, 8], ![16, 6, 9, -3, 0]], ![![0, 0, -1, 0, 0], ![0, 2, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 1, 0, 0]], ![![12, -6, 6, 0, 11], ![18, 7, 12, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, -2, 1, 0], ![-4, 0, 2, 3, 8], ![4, 1, 3, -3, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![1, -2, 1, 1, 2]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![0, 3, 0, 0, 0], ![0, 1, 2, 0, 0]]]
 hmul := by decide  
 g := ![![![![535, 91, 112, -77, -52], ![96, -135, 9, 0, 0]], ![![-12, 0, -3, 1, 0], ![0, 3, 0, 0, 0]]], ![![![-12, 0, -3, 1, 0], ![0, 3, 0, 0, 0]], ![![-115, -18, -24, 16, 10], ![-19, 29, -2, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![1, -2, 1, 1, 2]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![2, 4, 0, -1, -2]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![3, -6, 3, 3, 6], ![12, 1, 3, -1, 0]]]
 hmul := by decide  
 g := ![![![![139, -64, 0, -20, 8], ![12, 36, 0, 0, 0]], ![![-24, 9, 0, 4, 0], ![0, -6, 0, 0, 0]]], ![![![91, -46, 1, -12, 8], ![9, 24, 0, 0, 0]], ![![178, -81, 1, -26, 10], ![15, 46, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![2, 4, 0, -1, -2]] ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![4, 1, 0, -1, -1]] where
 M := ![![![9, 0, 0, 0, 0], ![3, 3, 0, 0, 0]], ![![6, 12, 0, -3, -6], ![-10, 8, 0, 1, -2]]]
 hmul := by decide  
 g := ![![![![-1, -1, 0, 1, 1], ![3, 0, 0, 0, 0]], ![![-3, 0, 0, 1, 1], ![3, 0, 0, 0, 0]]], ![![![-2, 3, 0, 0, -1], ![3, 0, 0, 0, 0]], ![![-2, 3, 0, 0, -1], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![4, 1, 0, -1, -1]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![12, 3, 0, -3, -3], ![-12, 3, -3, 0, -3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![4, 1, 0, -1, -1]], ![![-4, 1, -1, 0, -1]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 4, -2, -4, -4]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![29, 4, -2, -4, -4]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![29, 4, -2, -4, -4], ![-32, 29, -10, -6, -16], ![-28, -24, 9, 10, 16], ![76, -60, 20, 11, 32], ![-24, 40, -14, -10, -23]]]
  hmulB := by decide  
  f := ![![![1, -4, 2, 0, 4]], ![![4, -3, 2, -2, 0]], ![![-12, 0, -7, 2, 0]], ![![-4, -12, 4, 3, 16]], ![![15, 4, 4, -6, -11]]]
  g := ![![![5, 4, -2, -4, -4], ![-20, 29, -10, -6, -16], ![4, -24, 9, 10, 16], ![44, -60, 20, 11, 32], ![-23, 40, -14, -10, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![29, 4, -2, -4, -4]] ![![29, 4, -2, -4, -4]]
  ![![561, 360, -140, -164, -248]] where
 M := ![![![561, 360, -140, -164, -248]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![561, 360, -140, -164, -248]] ![![29, 4, -2, -4, -4]]
  ![![2157, 15964, -5790, -5128, -9788]] where
 M := ![![![2157, 15964, -5790, -5128, -9788]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![2157, 15964, -5790, -5128, -9788]] ![![29, 4, -2, -4, -4]]
  ![![-440991, 526704, -181592, -120840, -295664]] where
 M := ![![![-440991, 526704, -181592, -120840, -295664]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-440991, 526704, -181592, -120840, -295664]] ![![29, 4, -2, -4, -4]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-26646595, 13292500, -4296890, -1584780, -6635380]]]
 hmul := by decide  
 g := ![![![![-5329319, 2658500, -859378, -316956, -1327076]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [1, 5, 4, 5, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 5, 3, 5], [5, 0, 2, 0, 4], [2, 0, 4, 3, 5], [0, 1, 5, 6, 5], [0, 1]]
 g := ![![[4, 3, 1], []], ![[5, 0, 0, 5, 5, 5, 3], [0, 3, 5, 5, 6]], ![[1, 1, 2, 0, 3, 6, 2, 4], [3, 3, 0, 5, 1, 2, 3, 1]], ![[4, 1, 0, 3, 2, 6, 3, 5], [5, 0, 0, 6, 2, 0, 5, 6]], ![[0, 6, 5, 4, 1, 1, 0, 6], [0, 5, 6, 0, 3, 0, 6, 6]]]
 h' := ![![[3, 5, 3, 5], [0, 0, 0, 1], [0, 1]], ![[5, 0, 2, 0, 4], [6, 6, 6, 5, 4], [3, 5, 3, 5]], ![[2, 0, 4, 3, 5], [3, 3, 4, 3, 6], [5, 0, 2, 0, 4]], ![[0, 1, 5, 6, 5], [3, 3, 0, 5, 6], [2, 0, 4, 3, 5]], ![[0, 1], [0, 2, 4, 0, 5], [0, 1, 5, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], [], [], []]
 b := ![[], [6, 4, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [1, 5, 4, 5, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-924454433420, 262130729833, -1028588432284, -261308999084, -1105986487326]
  a := ![-31, -5, -24, -32, -62]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-132064919060, 37447247119, -146941204612, -37329857012, -157998069618]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![3, -7, 1, 0, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![3, -7, 1, 0, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![3, 10, 4, 1, 0], ![3, 4, 1, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![3, -7, 1, 0, 1], ![4, -3, -12, -2, -4], ![-14, 0, 1, -3, 2], ![-18, -12, 0, -20, -30], ![-14, 2, -20, 12, 9]]]
  hmulB := by decide  
  f := ![![![186, -115, -605, -100, -205], ![55, -550, 0, 0, 0]], ![![-40, 31, 120, 20, 40], ![0, 110, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![16, -7, -55, -9, -19], ![9, -50, 0, 0, 0]], ![![37, -22, -121, -20, -41], ![12, -110, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-3, -10, -4, 11, 0], ![-3, -4, -1, 0, 11]], ![![0, -1, 0, 0, 1], ![2, 3, 0, -2, -4], ![-1, 2, 1, -3, 2], ![12, 28, 10, -20, -30], ![-7, -14, -7, 12, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [5, 3, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 3, 9], [3, 7, 2], [0, 1]]
 g := ![![[4, 8, 4], [0, 5, 1], []], ![[2, 8, 4, 3], [6, 3, 3, 1], [8, 4]], ![[9, 2], [4, 0, 9, 7], [4, 4]]]
 h' := ![![[2, 3, 9], [0, 8, 2], [0, 0, 1], [0, 1]], ![[3, 7, 2], [10, 4, 9], [8, 1, 7], [2, 3, 9]], ![[0, 1], [2, 10], [0, 10, 3], [3, 7, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [9, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [5, 3, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3029843761, -5820822933, 414449943, 697617357, 5826696993]
  a := ![-298, -60, -239, -299, -599]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2054798801, -3282162225, -745701498, 697617357, 5826696993]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![1, 1, 0, 0, 0], ![0, 2, 2, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 2, 5, 8], ![4, 1, 3, -3, -3]]]
  hmulB := by decide  
  f := ![![![144, 63, 40, 0, 160], ![-693, 0, 1100, -220, 0]], ![![14, 6, 4, 0, 16], ![-65, 0, 110, -22, 0]], ![![130, 58, 37, 0, 144], ![-628, -5, 990, -198, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]], ![![118, 51, 32, 0, 131], ![-569, 4, 900, -180, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 11, 0, 0, 0], ![-10, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![-9, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-2, 2, 2, 0, 0], ![0, 0, 0, 1, 0], ![-8, 0, 2, 5, 8], ![0, 1, 3, -3, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-5, 1, 0, 0, 0], ![0, -4, 2, 0, 0], ![0, 0, -6, 1, 0], ![4, 0, 2, -1, 8], ![4, 1, 3, -3, -9]]]
  hmulB := by decide  
  f := ![![![32, 405, -88, -22, 32], ![33, 1122, 198, -44, 0]], ![![32, 393, -82, -22, 32], ![34, 1089, 198, -44, 0]], ![![14, 193, -45, -10, 16], ![13, 534, 88, -22, 0]], ![![19, 203, -44, -11, 16], ![23, 564, 100, -22, 0]], ![![7, 36, -8, -2, 3], ![12, 102, 18, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 11, 0, 0, 0], ![-1, 0, 11, 0, 0], ![-6, 0, 0, 11, 0], ![-1, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -4, 2, 0, 0], ![0, 0, -6, 1, 0], ![0, 0, 2, -1, 8], ![2, 1, 3, -3, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![3, -7, 1, 0, 1]] ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0], ![7, 1, 0, -2, -3]] where
 M := ![![![121, 0, 0, 0, 0], ![11, 11, 0, 0, 0]], ![![33, -77, 11, 0, 11], ![7, -10, -11, -2, -3]]]
 hmul := by decide  
 g := ![![![![4, -1, 0, 2, 3], ![11, 0, 0, 0, 0]], ![![-6, 0, 0, 2, 3], ![11, 0, 0, 0, 0]]], ![![![-4, -8, 1, 2, 4], ![11, 0, 0, 0, 0]], ![![0, -1, -1, 0, 0], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![7, 1, 0, -2, -3]] ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![-55, 11, 0, 0, 0]], ![![77, 11, 0, -22, -33], ![-55, 0, -11, 11, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![-5, 1, 0, 0, 0]]], ![![![7, 1, 0, -2, -3]], ![![-5, 0, -1, 1, 1]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![4, 16, -3, -4, -7]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![4, 16, -3, -4, -7]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![10, 10, 7, 1, 0], ![3, 5, 2, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![4, 16, -3, -4, -7], ![-44, 13, 6, 2, -4], ![18, -24, 3, 12, 18], ![138, -12, 30, 9, 42], ![-50, 25, -3, -13, -34]]]
  hmulB := by decide  
  f := ![![![1945, -540, -270, -96, 162], ![-26, 572, 0, 0, 0]], ![![-488, 128, 69, 26, -37], ![13, -143, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![1122, -312, -155, -55, 94], ![-14, 330, 0, 0, 0]], ![![259, -84, -34, -10, 27], ![6, 77, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-10, -10, -7, 13, 0], ![-3, -5, -2, 0, 13]], ![![5, 7, 3, -4, -7], ![-4, 1, 0, 2, -4], ![-12, -18, -9, 12, 18], ![-6, -24, -9, 9, 42], ![14, 25, 12, -13, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [6, 8, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12, 3], [10, 0, 10], [0, 1]]
 g := ![![[1, 9, 12], [0, 3], [1]], ![[8, 4], [8, 4], [1, 7, 3, 1]], ![[11, 10, 10, 3], [11, 10], [7, 2, 9, 12]]]
 h' := ![![[7, 12, 3], [10, 0, 5], [7, 5, 4], [0, 1]], ![[10, 0, 10], [5, 7], [12, 11, 2], [7, 12, 3]], ![[0, 1], [2, 6, 8], [9, 10, 7], [10, 0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4], []]
 b := ![[], [5, 2, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [6, 8, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1915884, -2725167, -74169, 433699, 2780391]
  a := ![-23, -4, -18, -24, -47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1122619, -1612624, -666988, 433699, 2780391]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![4, -9, 1, 1, 2]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![4, -9, 1, 1, 2]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![8, 10, 1, 0, 0], ![4, 10, 0, 1, 0], ![9, 5, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![4, -9, 1, 1, 2], ![12, -3, -11, -1, 0], ![-8, 6, 7, -7, -4], ![-52, 0, -14, -16, -44], ![-4, -9, -14, 16, 28]]]
  hmulB := by decide  
  f := ![![![16929, -1440, -17182, -1750, -644], ![4654, -19734, 234, 0, 0]], ![![39276, -3338, -39867, -4059, -1494], ![10803, -45786, 546, 0, 0]], ![![40200, -3422, -40801, -4154, -1528], ![11048, -46860, 558, 0, 0]], ![![35420, -3008, -35954, -3661, -1348], ![9746, -41292, 492, 0, 0]], ![![26825, -2278, -27229, -2773, -1021], ![7381, -31272, 372, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-8, -10, 13, 0, 0], ![-4, -10, 0, 13, 0], ![-9, -5, 0, 0, 13]], ![![-2, -3, 1, 1, 2], ![8, 9, -11, -1, 0], ![0, 2, 7, -7, -4], ![40, 40, -14, -16, -44], ![-16, -13, -14, 16, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12], [0, 1]]
 g := ![![[6, 1], [3], [7, 1]], ![[0, 12], [3], [1, 12]]]
 h' := ![![[7, 12], [7, 12], [6, 9], [0, 1]], ![[0, 1], [0, 1], [4, 4], [7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [12, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [1, 6, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![759664, 72936, 478878, -51417, 87964]
  a := ![125, 23, 99, 124, 249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-281336, -357038, 478878, -51417, 87964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![4, 16, -3, -4, -7]] ![![13, 0, 0, 0, 0], ![4, -9, 1, 1, 2]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![52, -117, 13, 13, 26]], ![![52, 208, -39, -52, -91], ![468, -39, -39, -39, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![4, -9, 1, 1, 2]]], ![![![4, 16, -3, -4, -7]], ![![36, -3, -3, -3, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [9, 15, 13, 13, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 9, 12, 3, 16], [5, 4, 4, 13, 13], [3, 9, 14, 4, 1], [9, 11, 4, 14, 4], [0, 1]]
 g := ![![[2, 11, 13, 2, 2], [12, 5, 16, 1], [], []], ![[7, 3, 7, 7, 0, 14, 2, 1], [4, 16, 14, 15], [7, 12, 2, 8], [0, 13, 10, 1]], ![[5, 1, 9, 11, 7, 14, 16, 15], [14, 12, 12, 16], [], [15, 15, 16, 16]], ![[13, 4, 14, 16, 3, 14, 14, 9], [5, 3, 10, 15], [0, 10, 3, 15], [2, 7, 7, 1]], ![[15, 12, 3, 9, 5, 2, 1, 1], [6, 5, 6, 4], [8, 5, 8, 8], [10, 9, 11, 16]]]
 h' := ![![[16, 9, 12, 3, 16], [11, 13, 16, 6, 6], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[5, 4, 4, 13, 13], [0, 1, 2, 5, 13], [6, 10, 4, 13, 7], [1, 1, 10, 1, 5], [16, 9, 12, 3, 16]], ![[3, 9, 14, 4, 1], [9, 15, 12, 5, 3], [13, 3, 11, 12, 4], [9, 3, 2], [5, 4, 4, 13, 13]], ![[9, 11, 4, 14, 4], [5, 0, 2, 12, 3], [13, 0, 13, 3, 7], [8, 12, 5, 11, 7], [3, 9, 14, 4, 1]], ![[0, 1], [10, 5, 2, 6, 9], [9, 4, 6, 6, 15], [8, 1, 16, 5, 5], [9, 11, 4, 14, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 12, 10, 10], [], [], []]
 b := ![[], [4, 1, 14, 16, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [9, 15, 13, 13, 1, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1391554233647, 343644565893, -1130932380958, 25934981958, -749615839851]
  a := ![-30, -3, -22, -28, -59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-81856131391, 20214386229, -66525434174, 1525587174, -44095049403]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-18, 30, -11, -9, -21]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-18, 30, -11, -9, -21]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![9, 4, 15, 14, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-18, 30, -11, -9, -21], ![-120, -9, -10, 16, 12], ![116, -54, 35, 1, 34], ![256, 42, -4, -62, -94], ![-226, 3, -41, 39, 34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![9, -14, 6, 5, 10], ![9, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-9, -4, -15, -14, 19]], ![![9, 6, 16, 15, -21], ![-12, -3, -10, -8, 12], ![-10, -10, -25, -25, 34], ![58, 22, 74, 66, -94], ![-28, -7, -29, -23, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [4, 0, 14, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 3, 0, 12], [8, 5, 12, 6], [15, 10, 7, 1], [0, 1]]
 g := ![![[17, 15, 15, 11], [13, 7, 5, 11], [1], []], ![[0, 13, 16, 15, 17, 13], [10, 10, 14, 13, 10, 2], [15, 14, 5], [1, 18, 11]], ![[9, 18, 18, 15, 18, 6], [3, 7, 7, 10, 3, 16], [4, 18, 1], [0, 6, 17]], ![[18, 12, 5, 14, 12, 6], [10, 17, 17, 2, 16, 6], [7, 9, 7], [6, 7, 1]]]
 h' := ![![[8, 3, 0, 12], [5, 7, 7, 12], [15, 0, 5, 12], [0, 0, 1], [0, 1]], ![[8, 5, 12, 6], [1, 1, 11, 3], [6, 9, 14, 15], [3, 14, 8, 9], [8, 3, 0, 12]], ![[15, 10, 7, 1], [17, 4, 15, 18], [14, 9, 13, 16], [7, 18, 16, 18], [8, 5, 12, 6]], ![[0, 1], [1, 7, 5, 5], [17, 1, 6, 14], [11, 6, 13, 11], [15, 10, 7, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 10, 5], []]
 b := ![[], [], [2, 13, 10, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [4, 0, 14, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![519633284, 237624912, 427917120, 126667872, 220479488]
  a := ![-12, -6, -8, -22, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-77088532, -33910160, -151540800, -155791840, 220479488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![6, 1, 0, 0, 0], ![0, 7, 2, 0, 0], ![0, 0, 5, 1, 0], ![4, 0, 2, 10, 8], ![4, 1, 3, -3, 2]]]
  hmulB := by decide  
  f := ![![![-7579, -752, -21504, -4636, -256], ![23598, -1330, 82004, 608, 0]], ![![-3802, -378, -10782, -2324, -128], ![11838, -665, 41116, 304, 0]], ![![-7593, -758, -21525, -4640, -256], ![23642, -1320, 82080, 608, 0]], ![![-3798, -380, -10748, -2317, -128], ![11826, -658, 40984, 304, 0]], ![![-6785, -679, -19242, -4148, -229], ![21126, -1175, 73372, 544, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 19, 0, 0, 0], ![-17, 0, 19, 0, 0], ![-10, 0, 0, 19, 0], ![-17, 0, 0, 0, 19]], ![![0, 1, 0, 0, 0], ![-4, 7, 2, 0, 0], ![-5, 0, 5, 1, 0], ![-14, 0, 2, 10, 8], ![-3, 1, 3, -3, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![-18, 30, -11, -9, -21]] ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![361, 0, 0, 0, 0], ![114, 19, 0, 0, 0]], ![![-342, 570, -209, -171, -399], ![-228, 171, -76, -38, -114]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0]], ![![6, 1, 0, 0, 0]]], ![![![-18, 30, -11, -9, -21]], ![![-12, 9, -4, -2, -6]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 17, 26, 10, 15]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![29, 17, 26, 10, 15]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![5, 18, 14, 16, 1]] where
  M :=![![![29, 17, 26, 10, 15], ![100, 61, 73, 21, 20], ![32, 60, 39, 38, 34], ![320, 186, 298, 127, 202], ![-18, -28, -55, -53, -91]]]
  hmulB := by decide  
  f := ![![![-23, 7, -2, 0, -3]], ![![-12, -19, 7, 7, 12]], ![![44, 0, -1, -4, -2]], ![![20, 42, -14, -15, -26]], ![![25, 15, -5, -7, -10]]]
  g := ![![![-2, -11, -8, -10, 15], ![0, -13, -9, -13, 20], ![-6, -24, -19, -22, 34], ![-30, -150, -110, -135, 202], ![19, 70, 53, 61, -91]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [4, 4, 21, 20, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 12, 16, 14], [16, 16, 22, 18], [19, 17, 8, 14], [0, 1]]
 g := ![![[8, 13, 4, 13], [12, 11, 16, 6], [3, 1], []], ![[13, 19, 8, 14, 13, 22], [20, 16, 7, 12, 4, 22], [1, 2, 1, 1, 20, 15], [21, 1, 12]], ![[2, 13, 7, 7, 22, 8], [5, 7, 14, 11, 8, 16], [22, 20, 7, 6, 5, 4], [8, 16, 2]], ![[11, 16, 19, 12, 13, 5], [18, 17, 16, 14, 14, 7], [12, 20, 7, 17, 15, 5], [10, 7, 12]]]
 h' := ![![[14, 12, 16, 14], [21, 6, 1, 17], [11, 7, 2, 11], [0, 0, 1], [0, 1]], ![[16, 16, 22, 18], [8, 12, 7, 8], [7, 10, 3, 15], [20, 18, 7, 11], [14, 12, 16, 14]], ![[19, 17, 8, 14], [12, 6, 1, 16], [5, 1, 7, 11], [17, 2, 7, 17], [16, 16, 22, 18]], ![[0, 1], [14, 22, 14, 5], [17, 5, 11, 9], [22, 3, 8, 18], [19, 17, 8, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [21, 13, 4], []]
 b := ![[], [], [2, 4, 12, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [4, 4, 21, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1272408412, 905846930, 955250178, 331220902, 278729230]
  a := ![25, 10, 19, 26, 37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5271206, -178751270, -128128654, -179497686, 278729230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -7, 2, 0, 3]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, -7, 2, 0, 3]] 
 ![![23, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![23, -7, 2, 0, 3], ![12, 19, -7, -7, -12], ![-44, 0, 1, 4, 2], ![-20, -42, 14, 15, 26], ![30, 20, -7, -9, -13]]]
  hmulB := by decide  
  f := ![![![-29, -17, -26, -10, -15]], ![![-22, -13, -19, -7, -10]], ![![-14, -10, -13, -6, -8]], ![![-24, -14, -22, -9, -14]], ![![-3, -1, -1, 1, 2]]]
  g := ![![![4, -7, 2, 0, 3], ![-4, 19, -7, -7, -12], ![-4, 0, 1, 4, 2], ![10, -42, 14, 15, 26], ![-3, 20, -7, -9, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![29, 17, 26, 10, 15]] ![![23, -7, 2, 0, 3]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB434I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB434I0 : PrimesBelowBoundCertificateInterval O 1 23 434 where
  m := 9
  g := ![5, 5, 5, 1, 3, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB434I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
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
    · exact ![16807]
    · exact ![1331, 11, 11]
    · exact ![2197, 169]
    · exact ![1419857]
    · exact ![130321, 19]
    · exact ![279841, 23]
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
      exact NI3N0
      exact NI3N1
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
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I11N1, I11N2, I13N1, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1, I11N2], [I13N1], [], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
