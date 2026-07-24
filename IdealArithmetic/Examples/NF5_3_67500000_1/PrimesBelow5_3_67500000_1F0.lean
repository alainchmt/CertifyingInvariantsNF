
import IdealArithmetic.Examples.NF5_3_67500000_1.RI5_3_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 0, 1, 2, 2]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![0, 0, 1, 2, 2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![0, 0, 1, 2, 2], ![0, 1, 2, 6, 6], ![0, 2, 7, 16, 18], ![-3, 0, 11, 19, 18], ![2, 2, -2, 2, 3]]]
  hmulB := by decide  
  f := ![![![15, 14, 1, -6, -8]], ![![3, 11, 1, -4, -6]], ![![6, 10, 1, -4, -6]], ![![9, 8, 0, -3, -4]], ![![-4, -6, 0, 2, 3]]]
  g := ![![![-1, 0, 1, 2, 2], ![-3, 1, 2, 6, 6], ![-8, 2, 7, 16, 18], ![-11, 0, 11, 19, 18], ![0, 2, -2, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![693, -413, -77, 100, 233]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![693, -413, -77, 100, 233]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![693, -413, -77, 100, 233], ![-399, 217, 86, -87, -99], ![36, -277, 94, 10, -225], ![552, 309, -529, 265, 417], ![-487, -221, 463, -249, -294]]]
  hmulB := by decide  
  f := ![![![-4149, 13569, 54031, 126995, 130918]], ![![-7959, 25841, 103182, 242562, 250067]], ![![-18705, 60436, 241767, 568416, 586022]], ![![-22599, 72850, 291684, 685813, 707066]], ![![-3022, 9760, 39050, 91811, 94655]]]
  g := ![![![425, -413, -77, 100, 233], ![-258, 217, 86, -87, -99], ![217, -277, 94, 10, -225], ![45, 309, -529, 265, 417], ![-93, -221, 463, -249, -294]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7690, 16348, 2385, -3649, -6411]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![7690, 16348, 2385, -3649, -6411]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![7690, 16348, 2385, -3649, -6411], ![8286, 18361, 4413, 234, -2661], ![8685, 21384, 9910, 12189, 9387], ![60, 4320, 10377, 23383, 23817], ![-5340, -10864, -450, 5260, 7231]]]
  hmulB := by decide  
  f := ![![![-103, 292, -84, -13, 168]], ![![-323, -219, 369, -194, -207]], ![![259, 596, -905, 544, -168]], ![![1288, 1256, -951, 176, 2259]], ![![-1401, -1220, 1194, -385, -1973]]]
  g := ![![![-3697, 16348, 2385, -3649, -6411], ![-7361, 18361, 4413, 234, -2661], ![-17399, 21384, 9910, 12189, 9387], ![-19010, 4320, 10377, 23383, 23817], ![357, -10864, -450, 5260, 7231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![0, 0, 1, 2, 2]] ![![693, -413, -77, 100, 233]]
  ![![166, -101, -38, 42, 21]] where
 M := ![![![166, -101, -38, 42, 21]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![166, -101, -38, 42, 21]] ![![693, -413, -77, 100, 233]]
  ![![166926, -71612, -37535, 30908, 68567]] where
 M := ![![![166926, -71612, -37535, 30908, 68567]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![166926, -71612, -37535, 30908, 68567]] ![![7690, 16348, 2385, -3649, -6411]]
  ![![-867, 548, 70, -113, -286]] where
 M := ![![![-867, 548, 70, -113, -286]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-867, 548, 70, -113, -286]] ![![7690, 16348, 2385, -3649, -6411]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![1908, 3936, 328, -1494, -2188]]]
 hmul := by decide  
 g := ![![![![954, 1968, 164, -747, -1094]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, -15, -13, 8, 32]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![53, -15, -13, 8, 32]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![53, -15, -13, 8, 32], ![-72, -32, 65, -34, -48], ![42, 35, -108, 76, -60], ![240, 187, -181, 53, 342], ![-241, -193, 213, -79, -301]]]
  hmulB := by decide  
  f := ![![![-255, -373, 339, 1066, 1176]], ![![-110, -82, 341, 900, 956]], ![![-168, 63, 986, 2426, 2532]], ![![-104, 291, 1233, 2909, 3002]], ![![-38, -4, 178, 447, 469]]]
  g := ![![![7, -15, -13, 8, 32], ![-8, -32, 65, -34, -48], ![34, 35, -108, 76, -60], ![-34, 187, -181, 53, 342], ![20, -193, 213, -79, -301]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, 146, 588, 1383, 1426]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-46, 146, 588, 1383, 1426]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-46, 146, 588, 1383, 1426], ![-129, 413, 1658, 3899, 4020], ![-363, 1166, 4675, 10993, 11334], ![-447, 1438, 5762, 13548, 13968], ![-20, 66, 262, 616, 635]]]
  hmulB := by decide  
  f := ![![![-172, 114, 10, -21, -52]], ![![31, -23, 0, 3, 10]], ![![-21, 10, 1, -1, -12]], ![![1, 18, -12, 4, 10]], ![![-112, 58, 18, -18, -41]]]
  g := ![![![-966, 146, 588, 1383, 1426], ![-2723, 413, 1658, 3899, 4020], ![-7677, 1166, 4675, 10993, 11334], ![-9461, 1438, 5762, 13548, 13968], ![-430, 66, 262, 616, 635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![53, -15, -13, 8, 32]] ![![53, -15, -13, 8, 32]]
  ![![-2449, -5450, 5108, -2158, -3700]] where
 M := ![![![-2449, -5450, 5108, -2158, -3700]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-2449, -5450, 5108, -2158, -3700]] ![![53, -15, -13, 8, 32]]
  ![![850919, 700469, -1271579, 731842, 252416]] where
 M := ![![![850919, 700469, -1271579, 731842, 252416]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![850919, 700469, -1271579, 731842, 252416]] ![![53, -15, -13, 8, 32]]
  ![![56068445, 8454108, 93100276, -94801836, 244214384]] where
 M := ![![![56068445, 8454108, 93100276, -94801836, 244214384]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![56068445, 8454108, 93100276, -94801836, 244214384]] ![![-46, 146, 588, 1383, 1426]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![27004422, 25570566, -35063400, 17347011, 21733506]]]
 hmul := by decide  
 g := ![![![![9001474, 8523522, -11687800, 5782337, 7244502]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40, 25, 3, -5, -12]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-40, 25, 3, -5, -12]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-40, 25, 3, -5, -12], ![21, -16, -1, 3, 6], ![-9, 11, -4, 1, 0], ![-9, 3, 5, -4, 0], ![9, -5, -3, 3, -1]]]
  hmulB := by decide  
  f := ![![![-8, 21, 91, 215, 222]], ![![-9, 25, 106, 250, 258]], ![![-13, 40, 163, 384, 396]], ![![-17, 53, 215, 506, 522]], ![![-7, 19, 81, 191, 197]]]
  g := ![![![-12, 25, 3, -5, -12], ![8, -16, -1, 3, 6], ![-8, 11, -4, 1, 0], ![-3, 3, 5, -4, 0], ![5, -5, -3, 3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-40, 25, 3, -5, -12]] ![![-40, 25, 3, -5, -12]]
  ![![2035, -1322, -146, 262, 642]] where
 M := ![![![2035, -1322, -146, 262, 642]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![2035, -1322, -146, 262, 642]] ![![-40, 25, 3, -5, -12]]
  ![![-104428, 67997, 7395, -13409, -32994]] where
 M := ![![![-104428, 67997, 7395, -13409, -32994]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-104428, 67997, 7395, -13409, -32994]] ![![-40, 25, 3, -5, -12]]
  ![![5362237, -3492564, -378924, 688180, 1694112]] where
 M := ![![![5362237, -3492564, -378924, 688180, 1694112]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5362237, -3492564, -378924, 688180, 1694112]] ![![-40, 25, 3, -5, -12]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-275369620, 179362765, 19453535, -35338185, -86996340]]]
 hmul := by decide  
 g := ![![![![-55073924, 35872553, 3890707, -7067637, -17399268]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 13, 1, -2, -6]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-19, 13, 1, -2, -6]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![2, 6, 1, 5, 1]] where
  M :=![![![-19, 13, 1, -2, -6], ![12, -6, -1, 2, 6], ![-12, -1, 8, -2, -6], ![0, 7, -7, 7, 0], ![3, -5, 5, -3, 5]]]
  hmulB := by decide  
  f := ![![![5, 11, 1, -4, -6]], ![![6, 12, 1, -4, -6]], ![![6, 13, 2, -4, -6]], ![![0, 1, 1, 1, 0]], ![![7, 15, 2, -4, -7]]]
  g := ![![![-1, 7, 1, 4, -6], ![0, -6, -1, -4, 6], ![0, 5, 2, 4, -6], ![0, 1, -1, 1, 0], ![-1, -5, 0, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 3, 4, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 3, 5, 1], [4, 4, 0, 1], [6, 6, 2, 5], [0, 1]]
 g := ![![[0, 5, 3, 1], []], ![[2, 6, 4, 5, 0, 1], [1, 2, 3, 1, 4, 1]], ![[1, 3, 6, 5, 6, 2], [0, 5, 6, 3, 3, 1]], ![[0, 4, 6, 3, 1, 6], [4, 4, 4, 3, 0, 6]]]
 h' := ![![[0, 3, 5, 1], [0, 0, 0, 1], [0, 1]], ![[4, 4, 0, 1], [2, 1, 3, 1], [0, 3, 5, 1]], ![[6, 6, 2, 5], [1, 6, 0, 3], [4, 4, 0, 1]], ![[0, 1], [0, 0, 4, 2], [6, 6, 2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 0, 5], []]
 b := ![[], [], [2, 2, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 3, 4, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![206893, 1015857, 907169, 5647326, 4437934]
  a := ![-5, -7, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1238425, -3658821, -504395, -2363192, 4437934]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 11, 1, -4, -6]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![5, 11, 1, -4, -6]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![5, 11, 1, -4, -6], ![6, 12, 1, -4, -6], ![6, 13, 2, -4, -6], ![0, 1, 1, 1, 0], ![-3, -7, -1, 3, 5]]]
  hmulB := by decide  
  f := ![![![-19, 13, 1, -2, -6]], ![![-1, 1, 0, 0, 0]], ![![-18, 11, 2, -2, -6]], ![![0, 1, -1, 1, 0]], ![![-5, 3, 1, -1, -1]]]
  g := ![![![0, 11, 1, -4, -6], ![0, 12, 1, -4, -6], ![-1, 13, 2, -4, -6], ![-1, 1, 1, 1, 0], ![0, -7, -1, 3, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-19, 13, 1, -2, -6]] ![![5, 11, 1, -4, -6]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [2, 4, 0, 7, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 9, 3, 3, 6], [3, 2, 2, 8, 4], [6, 10, 8, 10, 4], [5, 0, 9, 1, 8], [0, 1]]
 g := ![![[3, 8, 7, 4, 9], [1], []], ![[1, 3, 7, 6, 5, 1, 4, 7], [1, 6, 2, 4, 6, 7, 1, 6], [9, 9, 5, 3]], ![[10, 1, 7, 10, 3, 4, 3, 5], [8, 6, 0, 8, 1, 1, 4, 1], [0, 8, 5, 5]], ![[7, 9, 0, 1, 10, 4, 9, 4], [6, 9, 4, 5, 1, 4, 10, 5], [5, 0, 10, 5]], ![[7, 3, 3, 0, 5, 7, 5, 8], [4, 6, 10, 9, 1, 0, 9, 7], [3, 5, 0, 9]]]
 h' := ![![[5, 9, 3, 3, 6], [9, 7, 0, 4, 8], [0, 0, 1], [0, 1]], ![[3, 2, 2, 8, 4], [1, 8, 10, 1, 5], [7, 3, 10, 6, 10], [5, 9, 3, 3, 6]], ![[6, 10, 8, 10, 4], [7, 1, 2, 5, 9], [9, 7, 7, 4, 6], [3, 2, 2, 8, 4]], ![[5, 0, 9, 1, 8], [7, 1, 5, 0, 1], [4, 1, 0, 8, 2], [6, 10, 8, 10, 4]], ![[0, 1], [4, 5, 5, 1, 10], [8, 0, 4, 4, 4], [5, 0, 9, 1, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 1, 9, 5], [], [], []]
 b := ![[], [8, 9, 5, 1, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [2, 4, 0, 7, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31615265813032, -38786876639566, 63837279613844, -61602244991122, -6214070803347]
  a := ![6, -59, -1, -60, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2874115073912, -3526079694506, 5803389055804, -5600204090102, -564915527577]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [5, 1, 0, 11, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 3, 2, 6, 3], [2, 8, 3, 9], [8, 5, 0, 6, 8], [0, 9, 8, 5, 2], [0, 1]]
 g := ![![[0, 8, 12, 12, 4], [10, 1], []], ![[10, 5, 3, 0, 10, 4, 3, 3], [4, 5, 5, 10], [5, 9, 8, 5, 4, 7, 3, 1]], ![[11, 6, 1, 4, 2, 8, 10], [5, 4, 10, 4], [2, 4, 11, 11, 1]], ![[9, 2, 3, 6, 3, 9, 4, 5], [5, 0, 9, 12], [9, 11, 0, 9, 11, 11, 6, 5]], ![[0, 11, 4, 5, 5, 0, 4, 5], [12, 11, 7, 1], [6, 6, 10, 10, 11, 11, 10, 8]]]
 h' := ![![[0, 3, 2, 6, 3], [2, 11, 12, 7, 11], [0, 0, 0, 1], [0, 1]], ![[2, 8, 3, 9], [7, 1, 6, 12, 12], [1, 2, 3, 4, 6], [0, 3, 2, 6, 3]], ![[8, 5, 0, 6, 8], [5, 4, 0, 0, 11], [11, 9, 10, 1, 11], [2, 8, 3, 9]], ![[0, 9, 8, 5, 2], [2, 10, 0, 7, 8], [12, 12, 4, 2, 8], [8, 5, 0, 6, 8]], ![[0, 1], [8, 0, 8, 0, 10], [9, 3, 9, 5, 1], [0, 9, 8, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 12, 2, 9], [], [], []]
 b := ![[], [5, 10, 5, 5, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [5, 1, 0, 11, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43260737, -45888089, -15562183, -96273190, -179906688]
  a := ![-1, -5, 1, -6, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3327749, -3529853, -1197091, -7405630, -13838976]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [1, 13, 4, 11, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 3, 12, 10, 10], [5, 1, 12, 6, 14], [6, 6, 2, 2, 15], [12, 6, 8, 16, 12], [0, 1]]
 g := ![![[5, 13, 8], [9, 7, 1, 1], [], []], ![[1, 2, 8, 6, 6, 11, 4, 10], [4, 4, 5, 8], [14, 12, 14, 2], [16, 16, 11, 15]], ![[4, 3, 10, 2, 1, 15, 10, 14], [10, 1, 1, 1], [0, 10, 4, 2], [16, 8, 7, 9]], ![[15, 13, 2, 4, 3, 2, 13, 2], [9, 5, 9, 15], [14, 0, 10, 15], [11, 16, 13, 4]], ![[12, 9, 5, 7, 15, 13, 9, 5], [2, 14, 3, 4], [15, 5, 3, 8], [4, 4, 1, 8]]]
 h' := ![![[12, 3, 12, 10, 10], [8, 12, 8, 12], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[5, 1, 12, 6, 14], [14, 7, 11, 6, 1], [16, 11, 10, 15, 5], [9, 1, 14, 16, 11], [12, 3, 12, 10, 10]], ![[6, 6, 2, 2, 15], [6, 16, 15, 4, 16], [13, 5, 3, 0, 16], [9, 15, 14, 14, 11], [5, 1, 12, 6, 14]], ![[12, 6, 8, 16, 12], [9, 0, 10, 4, 13], [16, 7, 7, 15, 10], [8, 15, 16, 13, 7], [6, 6, 2, 2, 15]], ![[0, 1], [16, 16, 7, 8, 4], [1, 11, 14, 4, 2], [4, 3, 6, 8, 5], [12, 6, 8, 16, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 6, 11, 4], [], [], []]
 b := ![[], [13, 8, 3, 15, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [1, 13, 4, 11, 16, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6268127953, 17818256478, 114604670349, 193955453763, 252172244259]
  a := ![8, 26, -3, 25, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-368713409, 1048132734, 6741451197, 11409144339, 14833661427]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-106, -168, 270, -161, 24]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-106, -168, 270, -161, 24]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![13, 12, 16, 2, 1]] where
  M :=![![![-106, -168, 270, -161, 24], ![-555, -391, 226, 33, -1038], ![3213, 2884, -3571, 1589, 3312], ![-2307, -2568, 4708, -2860, 318], ![966, 1336, -3108, 2110, -1567]]]
  hmulB := by decide  
  f := ![![![-628, -1288, -76, 567, 798]], ![![-693, -1397, -28, 751, 1008]], ![![-771, -1492, 125, 1189, 1482]], ![![-93, -64, 302, 792, 840]], ![![-1504, -2980, 72, 1931, 2495]]]
  g := ![![![-22, -24, -6, -11, 24], ![681, 635, 886, 111, -1038], ![-2097, -1940, -2977, -265, 3312], ![-339, -336, -20, -184, 318], ![1123, 1060, 1156, 276, -1567]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [6, 15, 3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 11, 16, 17], [16, 7, 7, 15], [8, 0, 15, 6], [0, 1]]
 g := ![![[14, 5, 5, 7], [6, 4, 10, 9], [1], []], ![[0, 5, 6, 3, 0, 16], [8, 0, 16, 11, 16, 6], [18, 3, 5], [10, 0, 4]], ![[11, 18, 18, 8, 17, 2], [12, 14, 16, 2, 5, 15], [0, 9, 11], [10, 10, 16]], ![[14, 2, 15, 5, 1, 5], [3, 7, 0, 12, 6, 5], [5, 3, 4], [15, 15, 17]]]
 h' := ![![[11, 11, 16, 17], [2, 17, 4, 8], [13, 4, 16, 16], [0, 0, 1], [0, 1]], ![[16, 7, 7, 15], [13, 2, 9, 12], [3, 11, 2, 4], [4, 16, 1, 9], [11, 11, 16, 17]], ![[8, 0, 15, 6], [11, 11, 11, 16], [17, 0, 16, 1], [6, 14, 16, 12], [16, 7, 7, 15]], ![[0, 1], [1, 8, 14, 2], [0, 4, 4, 17], [12, 8, 1, 17], [8, 0, 15, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 18, 7], []]
 b := ![[], [], [18, 7, 14, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [6, 15, 3, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14901058, -24340740, 66055474, -45985572, 47876036]
  a := ![-10, -8, 5, -6, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33541554, -31518588, -36840058, -7459876, 47876036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-628, -1288, -76, 567, 798]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-628, -1288, -76, 567, 798]] 
 ![![19, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-628, -1288, -76, 567, 798], ![-693, -1397, -28, 751, 1008], ![-771, -1492, 125, 1189, 1482], ![-93, -64, 302, 792, 840], ![426, 888, 88, -302, -457]]]
  hmulB := by decide  
  f := ![![![-106, -168, 270, -161, 24]], ![![-85, -109, 154, -83, -42]], ![![91, 28, 11, -35, 192]], ![![-127, -144, 262, -159, 18]], ![![-44, -80, 78, -33, -61]]]
  g := ![![![-43, -1288, -76, 567, 798], ![-222, -1397, -28, 751, 1008], ![-736, -1492, 125, 1189, 1482], ![-987, -64, 302, 792, 840], ![-85, 888, 88, -302, -457]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-106, -168, 270, -161, 24]] ![![-628, -1288, -76, 567, 798]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1327, -4241, -17037, -40066, -41310]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![1327, -4241, -17037, -40066, -41310]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![20, 3, 1, 0, 0], ![16, 6, 0, 1, 0], ![6, 2, 0, 0, 1]] where
  M :=![![![1327, -4241, -17037, -40066, -41310], ![3732, -11978, -48039, -112962, -116466], ![10512, -33795, -135452, -318498, -328374], ![12948, -41667, -166941, -392531, -404700], ![585, -1903, -7593, -17849, -18401]]]
  hmulB := by decide  
  f := ![![![-505, 289, 51, -64, -198]], ![![402, -52, -177, 108, 210]], ![![-400, 241, 37, -52, -144]], ![![-272, 173, 3, -19, -120]], ![![-69, 87, -21, -1, 1]]]
  g := ![![![53521, 16082, -17037, -40066, -41310], ![150900, 45341, -48039, -112962, -116466], ![425468, 127839, -135452, -318498, -328374], ![524368, 157554, -166941, -392531, -404700], ![23845, 7164, -7593, -17849, -18401]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [21, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[13, 18], [21, 1], [16, 9], [1]], ![[21, 5], [1, 22], [20, 14], [1]]]
 h' := ![![[3, 22], [19, 8], [9, 1], [2, 3], [0, 1]], ![[0, 1], [20, 15], [12, 22], [11, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [11, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [21, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3723, -2408, 932, 2720, -7128]
  a := ![6, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1005, -316, 932, 2720, -7128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![221, -137, -15, 26, 66]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![221, -137, -15, 26, 66]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![4, 10, 1, 0, 0], ![3, 10, 0, 1, 0], ![9, 21, 0, 0, 1]] where
  M :=![![![221, -137, -15, 26, 66], ![-120, 86, 9, -18, -42], ![72, -39, -4, 6, 18], ![42, -27, -3, 5, 12], ![-51, 29, 3, -5, -13]]]
  hmulB := by decide  
  f := ![![![1, 1, -3, -4, -6]], ![![6, 4, -9, -12, -6]], ![![2, 1, -4, -8, -6]], ![![3, 2, -6, -7, -6]], ![![6, 4, -9, -13, -7]]]
  g := ![![![-17, -71, -15, 26, 66], ![12, 46, 9, -18, -42], ![-4, -19, -4, 6, 18], ![-3, -13, -3, 5, 12], ![3, 14, 3, -5, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [5, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 22], [0, 1]]
 g := ![![[13, 13], [12, 2], [1, 16], [1]], ![[19, 10], [20, 21], [19, 7], [1]]]
 h' := ![![[4, 22], [9, 17], [18, 18], [18, 4], [0, 1]], ![[0, 1], [8, 6], [21, 5], [11, 19], [4, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [22, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [5, 19, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-252, 60, 734, 1185, 158]
  a := ![6, 6, 4, 7, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-355, -976, 734, 1185, 158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-102, 71, 3, -11, -32]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-102, 71, 3, -11, -32]] 
 ![![23, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-102, 71, 3, -11, -32], ![63, -36, -3, 5, 30], ![-75, -15, 44, -21, -60], ![27, 61, -75, 40, 12], ![-5, -47, 55, -31, 9]]]
  hmulB := by decide  
  f := ![![![174, 569, 545, 1027, 986]], ![![81, 284, 301, 585, 568]], ![![111, 438, 533, 1074, 1056]], ![![75, 353, 501, 1044, 1038]], ![![61, 212, 222, 430, 417]]]
  g := ![![![-19, 71, 3, -11, -32], ![6, -36, -3, 5, 30], ![9, -15, 44, -21, -60], ![-2, 61, -75, 40, 12], ![-3, -47, 55, -31, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![1327, -4241, -17037, -40066, -41310]] ![![221, -137, -15, 26, 66]]
  ![![-439, 1710, 6342, 14838, 15276]] where
 M := ![![![-439, 1710, 6342, 14838, 15276]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-439, 1710, 6342, 14838, 15276]] ![![-102, 71, 3, -11, -32]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![1104, -713, -69, 161, 368]]]
 hmul := by decide  
 g := ![![![![48, -31, -3, 7, 16]]]]
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


lemma PB402I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB402I0 : PrimesBelowBoundCertificateInterval O 1 23 402 where
  m := 9
  g := ![5, 5, 5, 2, 1, 1, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB402I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
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
    · exact ![2401, 7]
    · exact ![161051]
    · exact ![371293]
    · exact ![1419857]
    · exact ![130321, 19]
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
      exact NI3N0
      exact NI3N0
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
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I19N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [], [], [I19N1], [I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
