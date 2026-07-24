
import IdealArithmetic.Examples.NF5_1_10125000000_17.RI5_1_10125000000_17
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, -1, 1, 2], ![15, -19, 0, 0, -1]]]
  hmulB := by decide  
  f := ![![![16, -16, 0, 0, -1], ![-6, 0, 0, 0, -2]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, 0, -1], ![-1, 1, 0, 1, 0]], ![![8, -8, 0, 0, 0], ![-3, 0, 0, 0, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![-1, 1, -1, 1, 2], ![8, -19, 0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 1, 1, 0], ![0, 3, 0, 3, 2], ![30, -35, 0, 3, 4], ![30, -23, -19, 0, 0], ![0, -2, -2, -19, 1]]]
  hmulB := by decide  
  f := ![![![219, -429, 69, -377, -323], ![-256, 324, 0, -6, -2]], ![![182, -356, 57, -316, -268], ![-213, 269, 0, -5, -2]], ![![147, -287, 47, -258, -216], ![-173, 217, 0, -4, -2]], ![![36, -72, 11, -60, -54], ![-41, 54, 0, -1, 0]], ![![109, -215, 34, -189, -161], ![-127, 162, 0, -3, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![-1, 1, 1, 1, 0], ![-4, 3, 0, 3, 2], ![29, -35, 0, 3, 4], ![36, -23, -19, 0, 0], ![11, -2, -2, -19, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![16, 2, 0, 2, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![16, 2, 0, 2, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![16, 2, 0, 2, 1], ![15, -1, 0, 2, 3], ![45, -40, -3, 2, 1], ![0, 13, -21, -3, 0], ![15, -38, 17, -21, -4]]]
  hmulB := by decide  
  f := ![![![16, -176, -3, 4, 94], ![90, -92, -2, 0, 0]], ![![0, -1, 0, 0, 1], ![1, -1, 0, 0, 0]], ![![8, -88, -1, 2, 47], ![45, -46, -1, 0, 0]], ![![168, -1123, -9, 36, 602], ![564, -585, -13, 1, 0]], ![![-8, -1, 0, -1, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![7, 2, 0, 2, 1], ![8, -1, 0, 2, 3], ![44, -40, -3, 2, 1], ![4, 13, -21, -3, 0], ![18, -38, 17, -21, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]]
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 1, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 2, 2, 0]], ![![0, 2, 0, 0, 0], ![0, 3, 0, 3, 2]]]
 hmul := by decide  
 g := ![![![![32, -479, 680, 65, -2], ![-206, 0, 0, 68, -4]], ![![16, -252, 360, 35, -1], ![-106, 0, 0, 36, -2]]], ![![![0, 0, 0, -1, -1], ![1, 1, 0, 0, 0]], ![![0, 1, 0, 1, 1], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 1, 1, 0]]
  ![![2, 0, 0, 0, 0], ![0, 2, 1, 1, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 2, 2, 0]], ![![0, 2, 0, 2, 0], ![30, -20, -19, 3, 2]]]
 hmul := by decide  
 g := ![![![![32, -2, 16, -7, 9], ![-29, -11, 0, 0, -4]], ![![16, -2, 8, -4, 4], ![-13, -5, 0, 0, -2]]], ![![![0, 1, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![240, -18, 114, -46, 70], ![-223, -84, 0, 0, -30]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 2, 1, 1, 0]] ![![2, 0, 0, 0, 0], ![16, 2, 0, 2, 1]]
  ![![2, 0, 0, 0, 0], ![15, 1, 0, 1, 1]] where
 M := ![![![4, 0, 0, 0, 0], ![32, 4, 0, 4, 2]], ![![0, 4, 2, 2, 0], ![75, -29, -24, 3, 7]]]
 hmul := by decide  
 g := ![![![![-13, -1, 0, -1, -1], ![2, 0, 0, 0, 0]], ![![-14, 0, 0, 0, -1], ![4, 0, 0, 0, 0]]], ![![![0, 2, 1, 1, 0], ![0, 0, 0, 0, 0]], ![![0, -17, -12, -1, 1], ![5, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![15, 1, 0, 1, 1]] ![![2, 0, 0, 0, 0], ![16, 2, 0, 2, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![32, 4, 0, 4, 2]], ![![30, 2, 0, 2, 2], ![270, 4, -4, 8, 14]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![16, 2, 0, 2, 1]]], ![![![15, 1, 0, 1, 1]], ![![135, 2, -2, 4, 7]]]]
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
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, -1, 1, 2], ![15, -19, 0, 0, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![1, 0, 2, 0, 0]], ![![0, 0, 0, 0, -1], ![-1, 2, -1, 2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, -1, 1, 2], ![5, -19, 0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![0, 3, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, -6, 6, -6, -16], ![-6, -3, 12, 0, 0]]], ![![![0, -6, 6, -6, -16], ![-6, -3, 12, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![15, 0, -1, 1, 1]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![0, 0, 3, 0, 0], ![0, 1, 0, 2, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 9, 0, 4, 0], ![-6, 6, 0, 0, 0]]], ![![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 3, 0, 2, 0], ![-2, 2, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![15, 0, -1, 1, 1]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![15, 2, -1, 2, 1]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![45, 0, -3, 3, 3], ![15, -4, -1, -1, 1]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![0, -2, 0, -1, 0], ![3, 0, 0, 0, 0]], ![![0, -2, 0, -1, 0], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![15, 2, -1, 2, 1]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![45, 6, -3, 6, 3], ![15, -3, 0, 0, 3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]]], ![![![15, 2, -1, 2, 1]], ![![5, -1, 0, 0, 1]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, -1, 1, 2], ![15, -19, 0, 0, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![2, 0, 3, 0, 0]], ![![0, 1, 0, 3, -1], ![1, 3, -9, 3, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, -1, 1, 2], ![3, -19, 0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![0, 5, 0, 0, 0]], ![![0, 5, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, -10, 10, -10, -24], ![-20, -5, 30, 0, 0]]], ![![![0, -10, 10, -10, -24], ![-20, -5, 30, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![0, 0, 1, 0, 0]] ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![15, 2, 1, 1, 1]] where
 M := ![![![25, 0, 0, 0, 0], ![0, 5, 0, 0, 0]], ![![0, 0, 5, 0, 0], ![0, 1, 0, 2, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-15, 23, -1, -13, -1], ![-25, 30, 0, 0, 0]]], ![![![0, -8, 1, 4, 0], ![10, -10, 0, 0, 0]], ![![-15, 3, -1, -3, -1], ![-1, 6, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![15, 2, 1, 1, 1]] ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-30, -1, -2, -1, -2]] where
 M := ![![![25, 0, 0, 0, 0], ![0, 5, 0, 0, 0]], ![![75, 10, 5, 5, 5], ![15, -2, 1, 3, 1]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![15, 2, 1, 1, 1], ![0, 0, 0, 0, 0]], ![![15, 0, 1, 1, 1], ![2, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-30, -1, -2, -1, -2]] ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![0, 5, 0, 0, 0]], ![![-150, -5, -10, -5, -10], ![-30, 5, 0, -5, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]]], ![![![-30, -1, -2, -1, -2]], ![![-6, 1, 0, -1, 0]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![17, -2, -1, 1, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![17, -2, -1, 1, 1]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![1, 0, 1, 1, 0], ![2, 5, 5, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![17, -2, -1, 1, 1], ![15, -2, -3, -1, 1], ![15, -8, -1, -7, -3], ![-30, 33, 1, -4, -6], ![-30, 21, 19, -2, 0]]]
  hmulB := by decide  
  f := ![![![-7, 0, -8, -8, 0], ![28, -28, 0, 0, 0]], ![![-15, 3, 3, 1, -1], ![0, 7, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-1, 0, -1, -1, 0], ![4, -4, 0, 0, 0]], ![![-3, 1, 0, -1, 0], ![4, -3, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-1, 0, -1, 7, 0], ![-2, -5, -5, 0, 7]], ![![2, -1, -1, 1, 1], ![2, -1, -1, -1, 1], ![4, 1, 3, -7, -3], ![-2, 9, 5, -4, -6], ![-4, 3, 3, -2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 2, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 3, 1], [2, 3, 6], [0, 1]]
 g := ![![[4, 3, 1], [1]], ![[2, 0, 1, 4], [6, 1, 1, 1]], ![[0, 1, 1, 6], [6, 6, 3, 6]]]
 h' := ![![[4, 3, 1], [1, 5, 6], [0, 1]], ![[2, 3, 6], [0, 0, 2], [4, 3, 1]], ![[0, 1], [0, 2, 6], [2, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [5, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 2, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3579, -171451, 129862, -181351, -471765]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![160186, 312482, 381434, -181351, -471765]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-2, -2, 1, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-2, -2, 1, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![5, 5, 1, 0, 0], ![5, 1, 0, 1, 0], ![1, 6, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-2, -2, 1, 0, 0], ![0, -1, -2, 2, 0], ![0, 0, -3, -2, 4], ![30, -40, 2, -5, -4], ![-45, 72, -19, 0, 1]]]
  hmulB := by decide  
  f := ![![![3, 3, 16, 8, -20], ![7, 7, 35, 0, 0]], ![![6, 8, 2, 0, -4], ![21, 7, 7, 0, 0]], ![![19, 19, -9, 0, 0], ![64, 0, 0, 0, 0]], ![![3, 3, 15, 9, -20], ![8, 4, 35, 0, 0]], ![![11, 13, -2, -2, -1], ![38, 9, 2, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-5, -5, 7, 0, 0], ![-5, -1, 0, 7, 0], ![-1, -6, 0, 0, 7]], ![![-1, -1, 1, 0, 0], ![0, 1, -2, 2, 0], ![3, -1, -3, -2, 4], ![7, -3, 2, -5, -4], ![7, 23, -19, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6], [0, 1]]
 g := ![![[0, 1], [0, 1]], ![[0, 6], [0, 6]]]
 h' := ![![[0, 6], [0, 6], [0, 1]], ![[0, 1], [0, 1], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59470, -84220, -10573, -78075, -60286]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![80428, 58348, -10573, -78075, -60286]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![17, -2, -1, 1, 1]] ![![7, 0, 0, 0, 0], ![-2, -2, 1, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![49, 0, 0, 0, 0], ![-14, -14, 7, 0, 0]], ![![119, -14, -7, 7, 7], ![-49, 0, 7, -7, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0]], ![![-2, -2, 1, 0, 0]]], ![![![17, -2, -1, 1, 1]], ![![-7, 0, 1, -1, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8630393803796, -7948381778999, -4076726880874, -1954131772585, 139356840097]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![8630393803796, -7948381778999, -4076726880874, -1954131772585, 139356840097]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![6, 10, 3, 1, 0], ![1, 3, 5, 0, 1]] where
  M :=![![![8630393803796, -7948381778999, -4076726880874, -1954131772585, 139356840097], ![2090352601455, -48244811506, -5994250006414, -10107585534333, -4047620385267], ![-60714305779005, 62893304380781, 10059340722827, -22096085547161, -16167550683399], ![-122301806426220, 117240328596374, 45491819967178, 4065090716413, -11988500012828], ![-60165176073330, 50368912548508, 41868504321012, 39497569960764, 9993625580175]]]
  hmulB := by decide  
  f := ![![![577875372513478079573073365129776630312963216, 25288404399163153666828190165889702189471923, -2811079004981837456087970014781365692032808, 27525308909075531022351001390060308735131351, 30656129423419177626840624204687614315777387]], ![![459841941351287664402609363070314214736660805, 20123143372607398229364536615990901356291406, -2236904509912377355522811224170606545659428, 21903150899111856110175061360497577351065735, 24394488394731884417861378575433003154485315]], ![![365917325920978266267920678631495047317279725, 16012908240581339217895420273414125606846127, -1780007526504457880810524744506675994774329, 17429341879287101399129438912156364259746879, 19411813403491827802488744145562151547646155]], ![![825371932382474981507786977902986009130476571, 36119101450927392145735929698566007357329631, -4015027842993169486094828206472736695157707, 39314043277001474199719236610284494196386576, 43785753788953148966916194633709178090103371]], ![![340785285080283600596512535194358755872295856, 14913104991670696654571500641346899763881178, -1657752528766212685214653179785892002294727, 16232254720776139689104087736443494498889351, 18078565555714714641808586356684171478629966]]]
  g := ![![![1837802509019, 1015896856960, 98989476036, -1954131772585, 139356840097], ![6071226017520, 10288224698875, 4051509865720, -10107585534333, -4047620385267], ![8002705289760, 30214255627508, 14289577343755, -22096085547161, -16167550683399], ![-12245804610170, 10232265588248, 8476277080189, 4065090716413, -11988500012828], ![-27922201947099, -34053423981787, -11508393951105, 39497569960764, 9993625580175]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [9, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 8, 1], [0, 2, 10], [0, 1]]
 g := ![![[5, 1, 9], [0, 10, 1], []], ![[8, 1, 3, 5], [0, 7, 0, 4], [4, 1]], ![[0, 8, 0, 6], [7, 0, 3, 2], [6, 1]]]
 h' := ![![[10, 8, 1], [0, 9, 3], [0, 0, 1], [0, 1]], ![[0, 2, 10], [7, 7, 4], [9, 4, 2], [10, 8, 1]], ![[0, 1], [3, 6, 4], [1, 7, 8], [0, 2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [2, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [9, 1, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35472, -103302, 26577, -148809, -123417]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![95613, 159549, 99099, -148809, -123417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 1, 2, 2, 0], ![0, 1, -1, 3, 2], ![15, -19, 0, 0, 1]]]
  hmulB := by decide  
  f := ![![![-251, -822, -1572, -1452, 72], ![1386, -264, 8580, -396, 0]], ![![-66, -207, -393, -363, 18], ![364, -66, 2145, -99, 0]], ![![-191, -615, -1173, -1083, 54], ![1054, -197, 6402, -297, 0]], ![![-63, -206, -394, -364, 18], ![348, -67, 2151, -99, 0]], ![![-205, -672, -1286, -1188, 59], ![1132, -218, 7020, -324, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 11, 0, 0, 0], ![-7, 0, 11, 0, 0], ![-3, 0, 0, 11, 0], ![-9, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-2, 1, 2, 2, 0], ![-2, 1, -1, 3, 2], ![4, -19, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![3, 1, 0, 0, 0], ![0, 3, 1, 0, 0], ![0, 1, 3, 2, 0], ![0, 1, -1, 4, 2], ![15, -19, 0, 0, 2]]]
  hmulB := by decide  
  f := ![![![-11, -40, -160, -66, 18], ![44, -22, 561, -99, 0]], ![![-21, -39, -148, -58, 18], ![78, -22, 517, -99, 0]], ![![-20, -38, -145, -56, 18], ![74, -21, 506, -99, 0]], ![![-1, -2, -2, -1, 0], ![4, 4, 6, 0, 0]], ![![-3, -12, -44, -18, 5], ![12, -2, 153, -27, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 11, 0, 0, 0], ![-2, 0, 11, 0, 0], ![-1, 0, 0, 11, 0], ![-3, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 3, 1, 0, 0], ![-1, 1, 3, 2, 0], ![-1, 1, -1, 4, 2], ![6, -19, 0, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![8630393803796, -7948381778999, -4076726880874, -1954131772585, 139356840097]] ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0], ![74, -2, -1, 6, 5]] where
 M := ![![![94934331841756, -87432199568989, -44843995689614, -21495449498435, 1532925241067], ![19351140209047, -15945008369504, -14147703768162, -14015849079503, -3768906705073]]]
 hmul := by decide  
 g := ![![![![168094265364, -7719670980663, -3962371481706, -2640264167593, -432420155743], ![1257909390848, 0, 0, 0, 0]], ![![125686744405, -1405397355408, -1264080458014, -1406614678141, -453000032283], ![242818730008, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![74, -2, -1, 6, 5]] ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![33, 11, 0, 0, 0]], ![![814, -22, -11, 66, 55], ![297, -22, -11, 22, 22]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![3, 1, 0, 0, 0]]], ![![![74, -2, -1, 6, 5]], ![![27, -2, -1, 2, 2]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![18, -3, 2, 1, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![18, -3, 2, 1, 1]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![9, 11, 5, 1, 0], ![9, 12, 10, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![18, -3, 2, 1, 1], ![15, 2, -4, 5, 1], ![15, -3, -3, -3, 9], ![60, -82, 2, -7, -8], ![-90, 142, -38, -2, 5]]]
  hmulB := by decide  
  f := ![![![55, 45, -62, 53, 5], ![91, -156, 0, 0, 0]], ![![-36, -20, 30, -27, -3], ![-39, 78, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![9, 14, -17, 14, 1], ![29, -42, 0, 0, 0]], ![![9, 12, -14, 12, 1], ![24, -36, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-9, -11, -5, 13, 0], ![-9, -12, -10, 0, 13]], ![![0, -2, -1, 1, 1], ![-3, -5, -3, 5, 1], ![-3, -6, -6, -3, 9], ![15, 7, 9, -7, -8], ![-9, 8, -6, -2, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [6, 4, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 0, 6], [4, 12, 7], [0, 1]]
 g := ![![[11, 12, 12], [3, 9], [1]], ![[10, 12, 1, 5], [4, 1], [3, 10, 11, 8]], ![[5, 7, 1, 8], [7, 4], [11, 11, 11, 5]]]
 h' := ![![[12, 0, 6], [5, 8, 5], [7, 9, 3], [0, 1]], ![[4, 12, 7], [12, 10, 4], [7, 6, 12], [12, 0, 6]], ![[0, 1], [1, 8, 4], [11, 11, 11], [4, 12, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 10], []]
 b := ![[], [0, 0, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [6, 4, 10, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3744429, 6583765, -1283, 4605608, 12317961]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12004350, -14761035, -11246841, 4605608, 12317961]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![1, 3, 1, 0, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![1, 3, 1, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![1, 3, 1, 0, 0], ![5, 3, 0, 1, 0], ![3, 5, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![1, 3, 1, 0, 0], ![0, 2, 3, 2, 0], ![0, 5, 0, 8, 4], ![30, -35, -3, 3, 6], ![30, -23, -19, 0, -1]]]
  hmulB := by decide  
  f := ![![![118, 521, 102, 278, 144], ![-1521, 65, -468, 0, 0]], ![![320, 1413, 278, 740, 384], ![-4160, 182, -1248, 0, 0]], ![![80, 352, 68, 184, 96], ![-1039, 52, -312, 0, 0]], ![![120, 528, 103, 277, 144], ![-1555, 72, -468, 0, 0]], ![![150, 662, 129, 348, 181], ![-1947, 90, -588, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-1, -3, 13, 0, 0], ![-5, -3, 0, 13, 0], ![-3, -5, 0, 0, 13]], ![![0, 0, 1, 0, 0], ![-1, -1, 3, 2, 0], ![-4, -3, 0, 8, 4], ![0, -5, -3, 3, 6], ![4, 3, -19, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [8, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 12], [0, 1]]
 g := ![![[8, 12], [10], [1, 1]], ![[7, 1], [10], [2, 12]]]
 h' := ![![[1, 12], [10, 5], [5, 6], [0, 1]], ![[0, 1], [2, 8], [11, 7], [1, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [5, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [8, 12, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117, -722, 526, 2043, -6254]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![626, 1757, 526, 2043, -6254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![18, -3, 2, 1, 1]] ![![13, 0, 0, 0, 0], ![1, 3, 1, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![13, 39, 13, 0, 0]], ![![234, -39, 26, 13, 13], ![78, 0, -13, 13, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![1, 3, 1, 0, 0]]], ![![![18, -3, 2, 1, 1]], ![![6, 0, -1, 1, 1]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![2, -8, 1, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![2, -8, 1, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![2, 9, 1, 0, 0], ![8, 12, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![2, -8, 1, 0, 0], ![0, 3, -8, 2, 0], ![0, -6, 1, -14, 4], ![30, -46, 8, -7, -16], ![-135, 186, -19, 0, 11]]]
  hmulB := by decide  
  f := ![![![-349, 1574, -159, 436, -128], ![2975, 102, 544, 0, 0]], ![![-300, 1333, -142, 328, -96], ![2550, 68, 408, 0, 0]], ![![-194, 864, -89, 218, -64], ![1650, 51, 272, 0, 0]], ![![-376, 1682, -176, 437, -128], ![3200, 94, 544, 0, 0]], ![![-42, 187, -14, 50, -15], ![358, 23, 64, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -9, 17, 0, 0], ![-8, -12, 0, 17, 0], ![-2, 0, 0, 0, 17]], ![![0, -1, 1, 0, 0], ![0, 3, -8, 2, 0], ![6, 9, 1, -14, 4], ![6, -2, 8, -7, -16], ![-7, 21, -19, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [6, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 16], [0, 1]]
 g := ![![[10, 15], [13], [13], [1]], ![[11, 2], [13], [13], [1]]]
 h' := ![![[8, 16], [3, 10], [9, 8], [11, 8], [0, 1]], ![[0, 1], [15, 7], [5, 9], [7, 9], [8, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [7, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [6, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1194, 11516, -10894, 8606, -2588]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2534, 370, -10894, 8606, -2588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![0, 1, -1, 2, 2], ![15, -19, 0, 0, 0]]]
  hmulB := by decide  
  f := ![![![0, 2429, 2718, 4896, -288], ![17, 306, -44064, 2448, 0]], ![![0, 151, 169, 306, -18], ![1, 34, -2754, 153, 0]], ![![0, 2277, 2548, 4590, -270], ![16, 290, -41310, 2295, 0]], ![![0, -1, -1, -1, 0], ![0, 8, 9, 0, 0]], ![![0, 2286, 2558, 4608, -271], ![16, 290, -41472, 2304, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 17, 0, 0, 0], ![-16, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![-16, 0, 0, 0, 17]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-1, 1, -1, 2, 2], ![2, -19, 0, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3971246942, 173785739, -19318160, 189158085, 210673557]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![3971246942, 173785739, -19318160, 189158085, 210673557]] 
 ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3971246942, 173785739, -19318160, 189158085, 210673557], ![3160103355, 138289284, -15372346, 150521765, 167642613], ![2514639195, 110043127, -12232481, 119777073, 133400917], ![-579544800, -25361460, 2819200, -27604827, -30744692], ![-263544870, -11532988, 1282016, -12553146, -13980983]]]
  hmulB := by decide  
  f := ![![![11026, -10305, -4806, -1721, 509]], ![![6935, -6366, -3332, -1679, 67]], ![![-2189, 2481, -203, -1879, -1041]], ![![-7184, 6998, 2372, -345, -950]], ![![-4004, 3432, 2576, 2230, 493]]]
  g := ![![![86609564, 173785739, -19318160, 189158085, 210673557], ![68919203, 138289284, -15372346, 150521765, 167642613], ![54842171, 110043127, -12232481, 119777073, 133400917], ![-12639386, -25361460, 2819200, -27604827, -30744692], ![-5747692, -11532988, 1282016, -12553146, -13980983]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2

def I17N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI17N3: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 1, -3, 2, 0], ![0, 1, -1, -2, 2], ![15, -19, 0, 0, -4]]]
  hmulB := by decide  
  f := ![![![1021, -3079, 8731, -5916, 42], ![5780, 1003, 49929, -357, 0]], ![![874, -2639, 7488, -5074, 36], ![4948, 867, 42823, -306, 0]], ![![574, -1738, 4937, -3346, 24], ![3250, 579, 28237, -204, 0]], ![![295, -880, 2498, -1693, 12], ![1670, 299, 14289, -102, 0]], ![![124, -363, 1027, -696, 5], ![702, 121, 5874, -42, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-14, 17, 0, 0, 0], ![-8, 0, 17, 0, 0], ![-5, 0, 0, 17, 0], ![-2, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![2, -3, 1, 0, 0], ![0, 1, -3, 2, 0], ![0, 1, -1, -2, 2], ![17, -19, 0, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N3 : Nat.card (O ⧸ I17N3) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N3)

lemma isPrimeI17N3 : Ideal.IsPrime I17N3 := prime_ideal_of_norm_prime hp17.out _ NI17N3
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![2, -8, 1, 0, 0]] ![![17, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0], ![21, 2, -3, 1, 1]] where
 M := ![![![289, 0, 0, 0, 0], ![17, 17, 0, 0, 0]], ![![34, -136, 17, 0, 0], ![2, -5, -7, 2, 0]]]
 hmul := by decide  
 g := ![![![![968, -128, 345, -829, 89], ![1088, -2601, 0, 0, 0]], ![![37, -7, 20, -44, 4], ![68, -136, 0, 0, 0]]], ![![![161, -30, 60, -141, 15], ![187, -442, 0, 0, 0]], ![![-8, -3, 5, -8, 0], ![23, -23, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![21, 2, -3, 1, 1]] ![![3971246942, 173785739, -19318160, 189158085, 210673557]]
  ![![17, 0, 0, 0, 0], ![22, 8, 2, 2, 1]] where
 M := ![![![67511198014, 2954357563, -328408720, 3215687445, 3581450469]], ![![81329385237, 3559055258, -395627393, 3873874123, 4314501497]]]
 hmul := by decide  
 g := ![![![![1648814808, -670735037, -230448354, -21972109, 105108460], ![1794606649, 0, 0, 0, 0]]], ![![![1986294103, -808021038, -277616507, -26469359, 126622052], ![2161926613, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N2 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![22, 8, 2, 2, 1]] ![![17, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![289, 0, 0, 0, 0], ![-51, 17, 0, 0, 0]], ![![374, 136, 34, 34, 17], ![-51, -17, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0]], ![![-3, 1, 0, 0, 0]]], ![![![22, 8, 2, 2, 1]], ![![-3, -1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2, I17N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
    exact isPrimeI17N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1 ⊙ MulI17N2)
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [10, 1, 10, 2, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 12, 8, 1, 7], [7, 15, 14, 6, 1], [3, 7, 12, 4, 1], [3, 3, 4, 8, 10], [0, 1]]
 g := ![![[2, 4, 10, 16, 11], [8, 17, 9, 12, 1], [], []], ![[14, 17, 10, 16, 5, 15, 13, 9], [17, 2, 4, 4, 8, 4, 13, 16], [8, 6, 6, 16], [10, 0, 13, 11]], ![[16, 18, 11, 14, 13, 12, 2, 16], [7, 4, 13, 11, 15, 5], [10, 11, 0, 1], [8, 8, 5, 1]], ![[11, 4, 3, 12, 2, 7, 11, 9], [16, 7, 4, 15, 16, 14, 12, 9], [1, 9, 5, 9], [14, 12, 1, 1]], ![[6, 18, 5, 5, 18, 6, 18, 13], [8, 9, 9, 6, 4, 5, 11, 15], [6, 7, 0, 17], [14, 0, 11, 5]]]
 h' := ![![[18, 12, 8, 1, 7], [15, 12, 3, 8, 7], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[7, 15, 14, 6, 1], [9, 6, 16, 8, 2], [12, 14, 2, 10, 9], [15, 4, 12, 9, 15], [18, 12, 8, 1, 7]], ![[3, 7, 12, 4, 1], [11, 11, 0, 12, 15], [6, 11, 1, 10], [7, 8, 17, 13, 1], [7, 15, 14, 6, 1]], ![[3, 3, 4, 8, 10], [5, 8, 18, 0, 3], [13, 16, 4, 3, 16], [2, 3, 16, 14, 16], [3, 7, 12, 4, 1]], ![[0, 1], [18, 1, 1, 10, 11], [1, 16, 12, 15, 12], [2, 4, 11, 2, 6], [3, 3, 4, 8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 9, 14, 3], [], [], []]
 b := ![[], [11, 7, 3, 16, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [10, 1, 10, 2, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39034854893, 199216877675, -160341921234, 178481406180, -121848930799]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2054466047, 10485098825, -8439048486, 9393758220, -6413101621]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![17, -10, 9, 1, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![17, -10, 9, 1, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![5, 1, 4, 1, 0], ![12, 12, 5, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![17, -10, 9, 1, 1], ![15, 8, -11, 19, 1], ![15, 4, -11, -3, 37], ![270, -355, 9, -22, -22], ![-300, 513, -171, -2, 18]]]
  hmulB := by decide  
  f := ![![![902, 614, -811, 1285, 61], ![161, -1564, 0, 0, 0]], ![![-60, -31, 44, -76, -4], ![0, 92, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![192, 133, -175, 276, 13], ![37, -336, 0, 0, 0]], ![![443, 302, -398, 631, 30], ![79, -768, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-5, -1, -4, 23, 0], ![-12, -12, -5, 0, 23]], ![![0, -1, 0, 1, 1], ![-4, -1, -4, 19, 1], ![-18, -19, -8, -3, 37], ![28, -3, 9, -22, -22], ![-22, 13, -11, -2, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [11, 20, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 4, 18], [18, 18, 5], [0, 1]]
 g := ![![[14, 0, 6], [20, 6, 12], [7, 2, 1], []], ![[3, 8], [4, 10, 10, 4], [0, 4, 14, 13], [10, 2]], ![[20, 11, 5, 7], [9, 5, 19, 21], [1, 12, 4, 11], [0, 2]]]
 h' := ![![[7, 4, 18], [10, 12, 11], [15, 22, 9], [0, 0, 1], [0, 1]], ![[18, 18, 5], [21, 16], [11, 20, 6], [8, 18, 18], [7, 4, 18]], ![[0, 1], [18, 18, 12], [15, 4, 8], [2, 5, 4], [18, 18, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 20], []]
 b := ![[], [0, 17, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [11, 20, 21, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43796, -104939, 56620, -28855, 4347]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5909, -5576, 6535, -28855, 4347]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-6, -8, 1, 0, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-6, -8, 1, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![17, 15, 1, 0, 0], ![22, 0, 0, 1, 0], ![9, 19, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-6, -8, 1, 0, 0], ![0, -5, -8, 2, 0], ![0, -6, -7, -14, 4], ![30, -46, 8, -15, -16], ![-135, 186, -19, 0, 3]]]
  hmulB := by decide  
  f := ![![![-47, -59, 16, -2, 0], ![-184, 23, 0, 0, 0]], ![![12120, 17491, -516, 3404, -960], ![46460, -506, 5520, 0, 0]], ![![7843, 11323, -327, 2212, -624], ![30062, -322, 3588, 0, 0]], ![![-46, -60, 12, -1, 0], ![-180, 12, 0, 0, 0]], ![![9987, 14415, -422, 2812, -793], ![38282, -418, 4560, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-17, -15, 23, 0, 0], ![-22, 0, 0, 23, 0], ![-9, -19, 0, 0, 23]], ![![-1, -1, 1, 0, 0], ![4, 5, -8, 2, 0], ![17, 1, -7, -14, 4], ![16, 6, 8, -15, -16], ![7, 18, -19, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [17, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 22], [0, 1]]
 g := ![![[22, 16], [10, 4], [11, 13], [1]], ![[18, 7], [9, 19], [2, 10], [1]]]
 h' := ![![[17, 22], [14, 19], [20, 2], [6, 17], [0, 1]], ![[0, 1], [15, 4], [8, 21], [19, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [16, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [17, 6, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1636, 5588, -3811, 3845, -3458]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![421, 5585, -3811, 3845, -3458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![17, -10, 9, 1, 1]] ![![23, 0, 0, 0, 0], ![-6, -8, 1, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![-138, -184, 23, 0, 0]], ![![391, -230, 207, 23, 23], ![-207, 0, 23, -161, 23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![-6, -8, 1, 0, 0]]], ![![![17, -10, 9, 1, 1]], ![![-9, 0, 1, -7, 1]]]]
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


lemma PB6264I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB6264I0 : PrimesBelowBoundCertificateInterval O 1 23 6264 where
  m := 9
  g := ![5, 5, 5, 2, 3, 2, 4, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB6264I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2, I17N3]
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
    · exact ![343, 49]
    · exact ![1331, 11, 11]
    · exact ![2197, 169]
    · exact ![289, 17, 17, 17]
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
      exact NI3N0
      exact NI3N0
      exact NI3N0
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
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
      exact NI17N3
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N0, I13N1, I17N0, I17N1, I17N2, I17N3, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N0, I13N1], [I17N0, I17N1, I17N2, I17N3], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
