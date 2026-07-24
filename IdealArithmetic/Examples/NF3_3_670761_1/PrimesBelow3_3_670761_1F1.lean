
import IdealArithmetic.Examples.NF3_3_670761_1.RI3_3_670761_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, 1, 0]] 
 ![![37, 0, 0], ![15, 1, 0], ![33, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, 1, 0], ![-5, 10, 11], ![6, 23, 20]]]
  hmulB := by decide  
  f := ![![![-404, 903, 990], ![-111, -3330, 0]], ![![-165, 361, 396], ![-36, -1332, 0]], ![![-366, 805, 883], ![-85, -2970, 0]]]
  g := ![![![1, 0, 0], ![-15, 37, 0], ![-33, 0, 37]], ![![0, 1, 0], ![-14, 10, 11], ![-27, 23, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-13, 1, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![22, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-13, 1, 0], ![-5, -18, 11], ![6, 23, -8]]]
  hmulB := by decide  
  f := ![![![1257, 4904, -2992], ![-296, 10064, 0]], ![![816, 3173, -1936], ![-184, 6512, 0]], ![![746, 2916, -1779], ![-180, 5984, 0]]]
  g := ![![![1, 0, 0], ![-24, 37, 0], ![-22, 0, 37]], ![![-1, 1, 0], ![5, -18, 11], ![-10, 23, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-2, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-2, 1, 0]] 
 ![![37, 0, 0], ![35, 1, 0], ![5, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-2, 1, 0], ![-5, -7, 11], ![6, 23, 3]]]
  hmulB := by decide  
  f := ![![![361, 504, -792], ![0, 2664, 0]], ![![341, 476, -748], ![1, 2516, 0]], ![![49, 68, -107], ![4, 360, 0]]]
  g := ![![![1, 0, 0], ![-35, 37, 0], ![-5, 0, 37]], ![![-1, 1, 0], ![5, -7, 11], ![-22, 23, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, 1, 0]] ![![37, 0, 0], ![-13, 1, 0]]
  ![![37, 0, 0], ![-35, -7, 1]] where
 M := ![![![1369, 0, 0], ![-481, 37, 0]], ![![555, 37, 0], ![-200, -3, 11]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![22, 8, -1], ![37, 0, 0]]], ![![![15, 1, 0], ![0, 0, 0]], ![![5, 2, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-35, -7, 1]] ![![37, 0, 0], ![-2, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-74, 37, 0]], ![![-1295, -259, 37], ![111, 37, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-2, 1, 0]]], ![![![-35, -7, 1]], ![![3, 1, -2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![19, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![19, 1, 0]] 
 ![![41, 0, 0], ![19, 1, 0], ![35, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![19, 1, 0], ![-5, 14, 11], ![6, 23, 24]]]
  hmulB := by decide  
  f := ![![![759, -2556, -2002], ![328, 7462, 0]], ![![344, -1180, -924], ![165, 3444, 0]], ![![647, -2182, -1709], ![282, 6370, 0]]]
  g := ![![![1, 0, 0], ![-19, 41, 0], ![-35, 0, 41]], ![![0, 1, 0], ![-16, 14, 11], ![-31, 23, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-11, 1, 0]] 
 ![![41, 0, 0], ![30, 1, 0], ![32, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-11, 1, 0], ![-5, -16, 11], ![6, 23, -6]]]
  hmulB := by decide  
  f := ![![![3963, 13330, -9152], ![-738, 34112, 0]], ![![2898, 9741, -6688], ![-532, 24928, 0]], ![![3103, 10403, -7143], ![-539, 26624, 0]]]
  g := ![![![1, 0, 0], ![-30, 41, 0], ![-32, 0, 41]], ![![-1, 1, 0], ![3, -16, 11], ![-12, 23, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-8, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-8, 1, 0]] 
 ![![41, 0, 0], ![33, 1, 0], ![5, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-8, 1, 0], ![-5, -13, 11], ![6, 23, -3]]]
  hmulB := by decide  
  f := ![![![-583, -1562, 1320], ![82, -4920, 0]], ![![-463, -1250, 1056], ![83, -3936, 0]], ![![-67, -191, 161], ![31, -600, 0]]]
  g := ![![![1, 0, 0], ![-33, 41, 0], ![-5, 0, 41]], ![![-1, 1, 0], ![9, -13, 11], ![-18, 23, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![19, 1, 0]] ![![41, 0, 0], ![-11, 1, 0]]
  ![![41, 0, 0], ![-12, 4, 1]] where
 M := ![![![1681, 0, 0], ![-451, 41, 0]], ![![779, 41, 0], ![-214, 3, 11]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![1, -3, -1], ![41, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![-2, -1, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-12, 4, 1]] ![![41, 0, 0], ![-8, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-328, 41, 0]], ![![-492, 164, 41], ![82, -41, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-8, 1, 0]]], ![![![-12, 4, 1]], ![![2, -1, 1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![19, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![19, 1, 0]] 
 ![![43, 0, 0], ![19, 1, 0], ![34, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![19, 1, 0], ![-5, 14, 11], ![6, 23, 24]]]
  hmulB := by decide  
  f := ![![![3643, -11932, -9350], ![1376, 36550, 0]], ![![1609, -5264, -4125], ![603, 16125, 0]], ![![2892, -9434, -7393], ![1062, 28900, 0]]]
  g := ![![![1, 0, 0], ![-19, 43, 0], ![-34, 0, 43]], ![![0, 1, 0], ![-15, 14, 11], ![-29, 23, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-11, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-11, 1, 0]] 
 ![![43, 0, 0], ![32, 1, 0], ![7, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-11, 1, 0], ![-5, -16, 11], ![6, 23, -6]]]
  hmulB := by decide  
  f := ![![![1127, 3748, -2574], ![-172, 10062, 0]], ![![838, 2787, -1914], ![-128, 7482, 0]], ![![185, 610, -419], ![-22, 1638, 0]]]
  g := ![![![1, 0, 0], ![-32, 43, 0], ![-7, 0, 43]], ![![-1, 1, 0], ![10, -16, 11], ![-16, 23, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-8, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-8, 1, 0]] 
 ![![43, 0, 0], ![35, 1, 0], ![37, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-8, 1, 0], ![-5, -13, 11], ![6, 23, -3]]]
  hmulB := by decide  
  f := ![![![2665, 7079, -5984], ![-301, 23392, 0]], ![![2163, 5752, -4862], ![-257, 19006, 0]], ![![2295, 6091, -5149], ![-249, 20128, 0]]]
  g := ![![![1, 0, 0], ![-35, 43, 0], ![-37, 0, 43]], ![![-1, 1, 0], ![1, -13, 11], ![-16, 23, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![19, 1, 0]] ![![43, 0, 0], ![-11, 1, 0]]
  ![![43, 0, 0], ![4, 12, 1]] where
 M := ![![![1849, 0, 0], ![-473, 43, 0]], ![![817, 43, 0], ![-214, 3, 11]]]
 hmul := by decide  
 g := ![![![![39, -12, -1], ![43, 0, 0]], ![![-11, 1, 0], ![0, 0, 0]]], ![![![15, -11, -1], ![43, 0, 0]], ![![-6, -3, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![4, 12, 1]] ![![43, 0, 0], ![-8, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-344, 43, 0]], ![![172, 516, 43], ![-86, -129, 129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-8, 1, 0]]], ![![![4, 12, 1]], ![![-2, -3, 3]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![12, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![12, 1, 0]] 
 ![![47, 0, 0], ![12, 1, 0], ![9, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![12, 1, 0], ![-5, 7, 11], ![6, 23, 17]]]
  hmulB := by decide  
  f := ![![![-139, 196, 308], ![0, -1316, 0]], ![![-35, 49, 77], ![1, -329, 0]], ![![-33, 37, 59], ![25, -252, 0]]]
  g := ![![![1, 0, 0], ![-12, 47, 0], ![-9, 0, 47]], ![![0, 1, 0], ![-4, 7, 11], ![-9, 23, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![14, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![14, 1, 0]] 
 ![![47, 0, 0], ![14, 1, 0], ![18, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![14, 1, 0], ![-5, 9, 11], ![6, 23, 19]]]
  hmulB := by decide  
  f := ![![![6698, -13024, -15873], ![1739, 67821, 0]], ![![1991, -3872, -4719], ![518, 20163, 0]], ![![2564, -4988, -6079], ![670, 25974, 0]]]
  g := ![![![1, 0, 0], ![-14, 47, 0], ![-18, 0, 47]], ![![0, 1, 0], ![-7, 9, 11], ![-14, 23, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![21, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![21, 1, 0]] 
 ![![47, 0, 0], ![21, 1, 0], ![16, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![21, 1, 0], ![-5, 16, 11], ![6, 23, 26]]]
  hmulB := by decide  
  f := ![![![367, -1444, -990], ![188, 4230, 0]], ![![158, -642, -440], ![95, 1880, 0]], ![![116, -492, -337], ![84, 1440, 0]]]
  g := ![![![1, 0, 0], ![-21, 47, 0], ![-16, 0, 47]], ![![0, 1, 0], ![-11, 16, 11], ![-19, 23, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![12, 1, 0]] ![![47, 0, 0], ![14, 1, 0]]
  ![![47, 0, 0], ![2, 19, 1]] where
 M := ![![![2209, 0, 0], ![658, 47, 0]], ![![564, 47, 0], ![163, 21, 11]]]
 hmul := by decide  
 g := ![![![![45, -19, -1], ![47, 0, 0]], ![![12, -18, -1], ![47, 0, 0]]], ![![![10, -18, -1], ![47, 0, 0]], ![![3, -4, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![2, 19, 1]] ![![47, 0, 0], ![21, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![987, 47, 0]], ![![94, 893, 47], ![-47, 329, 235]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![21, 1, 0]]], ![![![2, 19, 1]], ![![-1, 7, 5]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [12, 48, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10, 14], [29, 42, 39], [0, 1]]
 g := ![![[17, 34, 37], [37, 15], [40, 14, 44], [37, 44], [1]], ![[44, 14], [48, 24], [40, 23, 50, 14], [19, 43], [12, 43, 30, 41]], ![[19, 40, 39, 12], [20, 36], [32, 40, 48, 30], [0, 6], [37, 29, 18, 12]]]
 h' := ![![[8, 10, 14], [42, 42, 39], [50, 38, 42], [18, 14, 37], [41, 5, 37], [0, 1]], ![[29, 42, 39], [13, 1], [18, 47, 17], [46, 17, 1], [50, 33, 34], [8, 10, 14]], ![[0, 1], [21, 10, 14], [46, 21, 47], [15, 22, 15], [42, 15, 35], [29, 42, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 37], []]
 b := ![[], [27, 15, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [12, 48, 16, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![276448, 92750, -784135]
  a := ![5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5216, 1750, -14795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [50, 28, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 3, 47], [14, 55, 12], [0, 1]]
 g := ![![[39, 34, 1], [58, 42, 16], [18, 12], [31, 7, 3], [1]], ![[36, 25, 0, 50], [18, 46, 29, 58], [40, 19], [42, 42, 21, 10], [38, 22, 47, 42]], ![[15, 38, 9, 35], [53, 32, 30, 17], [22, 5], [3, 41, 9, 1], [22, 53, 52, 17]]]
 h' := ![![[56, 3, 47], [50, 18, 58], [5, 57, 4], [43, 43, 22], [9, 31, 11], [0, 1]], ![[14, 55, 12], [8, 48, 24], [22, 18, 8], [4, 25, 45], [20, 41, 56], [56, 3, 47]], ![[0, 1], [48, 52, 36], [49, 43, 47], [38, 50, 51], [51, 46, 51], [14, 55, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 1], []]
 b := ![[], [16, 53, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [50, 28, 48, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4903431, -6014755, 9255861]
  a := ![-11, -13, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83109, -101945, 156879]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [1, 25, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 7, 20], [9, 53, 41], [0, 1]]
 g := ![![[5, 52, 34], [4, 16], [53, 36, 20], [39, 47, 16], [1]], ![[36, 28, 11, 22], [47, 1], [22, 16, 58, 39], [3, 39, 17, 46], [34, 20, 18, 9]], ![[3, 43, 58, 41], [57, 25], [0, 41, 16, 15], [46, 17, 54, 25], [15, 56, 2, 52]]]
 h' := ![![[56, 7, 20], [60, 4, 20], [8, 38, 57], [22, 16, 52], [60, 36, 4], [0, 1]], ![[9, 53, 41], [28, 32, 42], [40, 9, 60], [45, 37, 26], [24, 21, 17], [56, 7, 20]], ![[0, 1], [38, 25, 60], [20, 14, 5], [3, 8, 44], [43, 4, 40], [9, 53, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 27], []]
 b := ![[], [8, 37, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [1, 25, 57, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54218835936, 45895253017, -124295555294]
  a := ![261, 262, -587]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![888833376, 752381197, -2037632054]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [54, 59, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 28, 39], [0, 38, 28], [0, 1]]
 g := ![![[63, 5, 16], [32, 42, 64], [61, 4], [20, 19], [15, 1], []], ![[23, 16, 34, 16], [20, 13, 50, 39], [14, 4], [51, 37], [53, 37], [8, 47]], ![[0, 5, 25, 32], [23, 43, 49, 57], [16, 16], [61, 9], [17, 47], [19, 47]]]
 h' := ![![[15, 28, 39], [14, 21, 63], [36, 18, 8], [28, 17, 2], [61, 66, 32], [0, 0, 1], [0, 1]], ![[0, 38, 28], [18, 22, 64], [57, 28, 1], [3, 22, 2], [55, 11, 38], [61, 41, 38], [15, 28, 39]], ![[0, 1], [31, 24, 7], [2, 21, 58], [53, 28, 63], [59, 57, 64], [46, 26, 28], [0, 38, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 47], []]
 b := ![[], [20, 17, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [54, 59, 52, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3813238, 4134168, -7776288]
  a := ![11, 12, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56914, 61704, -116064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [1, 1, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 18, 53], [0, 52, 18], [0, 1]]
 g := ![![[49, 62, 2], [49, 66, 15], [58, 0, 4], [57, 54], [22, 1], []], ![[33, 40, 43, 41], [23, 9, 33, 35], [42, 66, 34, 51], [60, 48], [39, 6], [19, 40]], ![[0, 54, 5, 37], [58, 22, 5, 38], [56, 67, 46, 24], [44, 19], [52, 40], [54, 40]]]
 h' := ![![[22, 18, 53], [22, 54, 12], [13, 14, 21], [1, 49, 2], [49, 48, 57], [0, 0, 1], [0, 1]], ![[0, 52, 18], [45, 41, 7], [4, 25, 59], [21, 5, 3], [62, 45, 41], [39, 23, 52], [22, 18, 53]], ![[0, 1], [13, 47, 52], [15, 32, 62], [35, 17, 66], [24, 49, 44], [17, 48, 18], [0, 52, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 70], []]
 b := ![[], [48, 69, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [1, 1, 49, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![236998, 68373, -684156]
  a := ![5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3338, 963, -9636]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [59, 51, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 63, 3], [62, 9, 70], [0, 1]]
 g := ![![[30, 2, 12], [56, 65], [47, 50], [20, 8, 23], [44, 1], []], ![[16, 16, 53, 71], [71, 50], [72, 9], [68, 49, 22, 23], [25, 8], [44, 9]], ![[8, 26, 30, 37], [63, 27], [18, 48], [12, 21, 57, 37], [46, 27], [50, 9]]]
 h' := ![![[55, 63, 3], [55, 8, 31], [72, 45, 24], [61, 43, 59], [32, 33, 60], [0, 0, 1], [0, 1]], ![[62, 9, 70], [70, 26, 11], [68, 63, 59], [70, 19, 3], [66, 40, 55], [64, 67, 9], [55, 63, 3]], ![[0, 1], [14, 39, 31], [9, 38, 63], [66, 11, 11], [19, 0, 31], [18, 6, 63], [62, 9, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 2], []]
 b := ![[], [61, 49, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [59, 51, 29, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![346020, 11828920, 11496040]
  a := ![-9, 10, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4740, 162040, 157480]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![27, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![27, 1, 0]] 
 ![![79, 0, 0], ![27, 1, 0], ![3, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![27, 1, 0], ![-5, 22, 11], ![6, 23, 32]]]
  hmulB := by decide  
  f := ![![![1479, -7222, -3608], ![474, 25912, 0]], ![![506, -2466, -1232], ![159, 8848, 0]], ![![36, -275, -137], ![77, 984, 0]]]
  g := ![![![1, 0, 0], ![-27, 79, 0], ![-3, 0, 79]], ![![0, 1, 0], ![-8, 22, 11], ![-9, 23, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-20, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-20, 1, 0]] 
 ![![79, 0, 0], ![59, 1, 0], ![69, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-20, 1, 0], ![-5, -25, 11], ![6, 23, -15]]]
  hmulB := by decide  
  f := ![![![25801, 135060, -59400], ![-4740, 426600, 0]], ![![19261, 100845, -44352], ![-3554, 318528, 0]], ![![22531, 117964, -51881], ![-4156, 372600, 0]]]
  g := ![![![1, 0, 0], ![-59, 79, 0], ![-69, 0, 79]], ![![-1, 1, 0], ![9, -25, 11], ![-4, 23, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-7, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-7, 1, 0]] 
 ![![79, 0, 0], ![72, 1, 0], ![35, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-7, 1, 0], ![-5, -12, 11], ![6, 23, -2]]]
  hmulB := by decide  
  f := ![![![12538, 30249, -27720], ![-711, 199080, 0]], ![![11425, 27560, -25256], ![-631, 181384, 0]], ![![5558, 13401, -12281], ![-279, 88200, 0]]]
  g := ![![![1, 0, 0], ![-72, 79, 0], ![-35, 0, 79]], ![![-1, 1, 0], ![6, -12, 11], ![-20, 23, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![27, 1, 0]] ![![79, 0, 0], ![-20, 1, 0]]
  ![![79, 0, 0], ![-28, -7, 1]] where
 M := ![![![6241, 0, 0], ![-1580, 79, 0]], ![![2133, 79, 0], ![-545, 2, 11]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![8, 8, -1], ![79, 0, 0]]], ![![![27, 1, 0], ![0, 0, 0]], ![![-3, 1, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-28, -7, 1]] ![![79, 0, 0], ![-7, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-553, 79, 0]], ![![-2212, -553, 79], ![237, 79, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-7, 1, 0]]], ![![![-28, -7, 1]], ![![3, 1, -1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB183I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB183I1 : PrimesBelowBoundCertificateInterval O 31 79 183 where
  m := 11
  g := ![3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB183I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![43, 43, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
    · exact ![357911]
    · exact ![389017]
    · exact ![79, 79, 79]
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
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I41N2, I43N0, I43N1, I43N2, I47N0, I47N1, I47N2, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N1, I41N2], [I43N0, I43N1, I43N2], [I47N0, I47N1, I47N2], [], [], [], [], [], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
