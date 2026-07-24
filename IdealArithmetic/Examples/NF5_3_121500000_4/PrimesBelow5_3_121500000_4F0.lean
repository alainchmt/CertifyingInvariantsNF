
import IdealArithmetic.Examples.NF5_3_121500000_4.RI5_3_121500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![86, 32, -21, -8, 18]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![86, 32, -21, -8, 18]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![86, 32, -21, -8, 18], ![-192, -71, 48, 18, -42], ![450, 174, -107, -42, 90], ![-381, -132, 105, 37, -96], ![72, 36, -10, -6, 5]]]
  hmulB := by decide  
  f := ![![![85, 46, -21, -22, 36]], ![![-183, -101, 45, 48, -78]], ![![792, 438, -197, -210, 342]], ![![-1603, -892, 396, 425, -690]], ![![315, 174, -79, -84, 137]]]
  g := ![![![47, 32, -21, -8, 18], ![-105, -71, 48, 18, -42], ![246, 174, -107, -42, 90], ![-209, -132, 105, 37, -96], ![39, 36, -10, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1479, 257, -269, -80, 211]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1479, 257, -269, -80, 211]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1479, 257, -269, -80, 211], ![-2292, -398, 417, 124, -327], ![3552, 617, -646, -192, 507], ![-1608, -280, 292, 87, -228], ![575, 99, -105, -31, 83]]]
  hmulB := by decide  
  f := ![![![-47, -18, 12, 5, -11]], ![![35, 15, -8, -4, 8]], ![![-166, -66, 43, 21, -43]], ![![168, 76, -40, -25, 48]], ![![-48, -19, 13, 7, -13]]]
  g := ![![![640, 257, -269, -80, 211], ![-992, -398, 417, 124, -327], ![1537, 617, -646, -192, 507], ![-696, -280, 292, 87, -228], ![249, 99, -105, -31, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, -82, -21, 2, 27]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-85, -82, -21, 2, 27]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-85, -82, -21, 2, 27], ![-330, -324, -86, 6, 105], ![-1278, -1262, -336, 20, 387], ![-2187, -2203, -608, 18, 648], ![-1461, -1475, -407, 11, 422]]]
  hmulB := by decide  
  f := ![![![52948, 9197, -9631, -2864, 7554]], ![![-14554, -2527, 2647, 787, -2076]], ![![90053, 15638, -16379, -4870, 12846]], ![![-2269, -388, 411, 121, -321]], ![![10320, 1792, -1877, -558, 1472]]]
  g := ![![![8, -82, -21, 2, 27], ![37, -324, -86, 6, 105], ![150, -1262, -336, 20, 387], ![303, -2203, -608, 18, 648], ![205, -1475, -407, 11, 422]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![86, 32, -21, -8, 18]] ![![1479, 257, -269, -80, 211]]
  ![![2472, 431, -450, -134, 353]] where
 M := ![![![2472, 431, -450, -134, 353]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2472, 431, -450, -134, 353]] ![![1479, 257, -269, -80, 211]]
  ![![1488283, 258583, -270734, -80517, 212356]] where
 M := ![![![1488283, 258583, -270734, -80517, 212356]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![1488283, 258583, -270734, -80517, 212356]] ![![-85, -82, -21, 2, 27]]
  ![![170, 61, -13, -6, 14]] where
 M := ![![![170, 61, -13, -6, 14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![170, 61, -13, -6, 14]] ![![-85, -82, -21, 2, 27]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-25298, -24730, -6498, 492, 7984]]]
 hmul := by decide  
 g := ![![![![-12649, -12365, -3249, 246, 3992]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![362, 141, -91, -35, 79]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![362, 141, -91, -35, 79]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![362, 141, -91, -35, 79], ![-843, -326, 211, 81, -183], ![1953, 751, -488, -187, 423], ![-1836, -703, 457, 175, -396], ![239, 92, -60, -23, 52]]]
  hmulB := by decide  
  f := ![![![2, 1, -1, -1, 1]], ![![-3, -2, 1, 1, -3]], ![![33, 21, -4, -7, 3]], ![![-6, 7, 17, 9, -36]], ![![39, 30, 2, -5, -8]]]
  g := ![![![68, 141, -91, -35, 79], ![-159, -326, 211, 81, -183], ![369, 751, -488, -187, 423], ![-348, -703, 457, 175, -396], ![45, 92, -60, -23, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![364, 62, -66, -19, 51]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![364, 62, -66, -19, 51]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![364, 62, -66, -19, 51], ![-555, -91, 100, 27, -75], ![819, 118, -145, -31, 99], ![-270, 2, 40, -13, 0], ![117, 10, -20, -1, 10]]]
  hmulB := by decide  
  f := ![![![330, 128, -80, -31, 69]], ![![-25, -5, 10, 3, -9]], ![![809, 320, -191, -75, 165]], ![![-510, -178, 140, 51, -120]], ![![305, 128, -66, -27, 58]]]
  g := ![![![90, 62, -66, -19, 51], ![-141, -91, 100, 27, -75], ![225, 118, -145, -31, 99], ![-118, 2, 40, -13, 0], ![39, 10, -20, -1, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![362, 141, -91, -35, 79]] ![![362, 141, -91, -35, 79]]
  ![![-82401, -31392, 20482, 7826, -17730]] where
 M := ![![![-82401, -31392, 20482, 7826, -17730]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-82401, -31392, 20482, 7826, -17730]] ![![364, 62, -66, -19, 51]]
  ![![15924, 3038, -2984, -915, 2367]] where
 M := ![![![15924, 3038, -2984, -915, 2367]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![15924, 3038, -2984, -915, 2367]] ![![364, 62, -66, -19, 51]]
  ![![2190339, 380558, -398444, -118498, 312528]] where
 M := ![![![2190339, 380558, -398444, -118498, 312528]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![2190339, 380558, -398444, -118498, 312528]] ![![364, 62, -66, -19, 51]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![328308306, 57042132, -59722674, -17761665, 46844763]]]
 hmul := by decide  
 g := ![![![![109436102, 19014044, -19907558, -5920555, 15614921]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 3, 1, 0, -2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![3, 3, 1, 0, -2]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 3, 1, 0, -2], ![24, 20, 3, -2, -6], ![78, 77, 24, 0, -42], ![240, 209, 37, -17, -60], ![140, 132, 34, -4, -55]]]
  hmulB := by decide  
  f := ![![![-551, -117, 107, 34, -86]], ![![186, 42, -37, -12, 30]], ![![-324, -79, 66, 22, -54]], ![![198, 55, -43, -15, 36]], ![![-159, -35, 31, 10, -25]]]
  g := ![![![1, 3, 1, 0, -2], ![6, 20, 3, -2, -6], ![24, 77, 24, 0, -42], ![60, 209, 37, -17, -60], ![39, 132, 34, -4, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![3, 3, 1, 0, -2]] ![![3, 3, 1, 0, -2]]
  ![![-121, -118, -32, 2, 44]] where
 M := ![![![-121, -118, -32, 2, 44]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-121, -118, -32, 2, 44]] ![![3, 3, 1, 0, -2]]
  ![![949, 1039, 327, 26, -246]] where
 M := ![![![949, 1039, 327, 26, -246]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![949, 1039, 327, 26, -246]] ![![3, 3, 1, 0, -2]]
  ![![25089, 21768, 4512, -1536, -9896]] where
 M := ![![![25089, 21768, 4512, -1536, -9896]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![25089, 21768, 4512, -1536, -9896]] ![![3, 3, 1, 0, -2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-804445, -769245, -194615, 22160, 266150]]]
 hmul := by decide  
 g := ![![![![-160889, -153849, -38923, 4432, 53230]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [6, 3, 2, 1, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 3, 3, 5, 5], [4, 0, 3, 2, 3], [4, 1, 6, 6], [0, 2, 2, 1, 6], [0, 1]]
 g := ![![[6, 0, 1], []], ![[4, 5, 0, 3, 5, 5], [1, 5, 0, 3, 0, 6, 4, 6]], ![[3, 4, 1, 5, 2, 5, 2, 3], [2, 1, 1, 2, 1, 6, 5, 6]], ![[5, 3, 2, 4, 6, 4, 5], [4, 1, 1, 4, 6]], ![[0, 1, 3, 2, 0, 2, 5, 5], [0, 6, 3, 3, 1, 4, 3, 6]]]
 h' := ![![[6, 3, 3, 5, 5], [0, 0, 0, 1], [0, 1]], ![[4, 0, 3, 2, 3], [0, 4, 0, 1], [6, 3, 3, 5, 5]], ![[4, 1, 6, 6], [3, 2, 5, 0, 6], [4, 0, 3, 2, 3]], ![[0, 2, 2, 1, 6], [5, 2, 3, 1, 4], [4, 1, 6, 6]], ![[0, 1], [0, 6, 6, 4, 4], [0, 2, 2, 1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 0, 6, 4], [], [], []]
 b := ![[], [3, 1, 4, 1, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [6, 3, 2, 1, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107237469834117, 151226651298408, 78620844410556, 23164862978334, -93722399921724]
  a := ![17, 4, 8, 14, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15319638547731, 21603807328344, 11231549201508, 3309266139762, -13388914274532]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [3, 4, 10, 1, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 2, 0, 4, 5], [8, 8, 3, 0, 2], [0, 9, 4, 0, 2], [2, 2, 4, 7, 2], [0, 1]]
 g := ![![[5, 3, 2, 6, 3], [1], []], ![[3, 8, 5, 9, 1, 2, 5, 4], [7, 1, 0, 2, 3, 7, 7, 4], [8, 9, 3, 3]], ![[7, 3, 5, 2, 6, 8, 5, 6], [4, 5, 3, 0, 3, 4, 7, 10], [0, 9, 2, 4]], ![[3, 3, 6, 1, 4, 4, 9, 7], [6, 7, 1, 6, 7, 3, 2, 7], [6, 2, 2, 4]], ![[7, 9, 2, 4, 2, 9, 10, 7], [2, 10, 9, 1, 8, 5, 2, 6], [10, 10, 8, 4]]]
 h' := ![![[7, 2, 0, 4, 5], [8, 7, 1, 10, 6], [0, 0, 1], [0, 1]], ![[8, 8, 3, 0, 2], [9, 5, 0, 4, 5], [3, 2, 0, 3, 6], [7, 2, 0, 4, 5]], ![[0, 9, 4, 0, 2], [9, 3, 3, 1, 6], [9, 2, 4, 4, 7], [8, 8, 3, 0, 2]], ![[2, 2, 4, 7, 2], [4, 0, 2, 0, 8], [4, 3, 7, 4, 3], [0, 9, 4, 0, 2]], ![[0, 1], [4, 7, 5, 7, 8], [7, 4, 10, 0, 6], [2, 2, 4, 7, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 9, 2, 9], [], [], []]
 b := ![[], [2, 2, 2, 7, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [3, 4, 10, 1, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7826625075056977475, 7957208801168799491, 2257542971132815960, -22430139915854979, -2413818405821682266]
  a := ![113, -4, 57, 50, -449]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![711511370459725225, 723382618288072681, 205231179193892360, -2039103628714089, -219438036892880206]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5570, 2117, -1385, -523, 1191]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![5570, 2117, -1385, -523, 1191]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![4, 3, 4, 11, 1]] where
  M :=![![![5570, 2117, -1385, -523, 1191], ![-12723, -4820, 3163, 1181, -2703], ![28893, 10883, -7182, -2623, 6063], ![-26082, -9675, 6483, 2225, -5292], ![3363, 1232, -836, -271, 662]]]
  hmulB := by decide  
  f := ![![![-58, -53, -13, 1, 15]], ![![-183, -192, -55, 1, 57]], ![![-687, -695, -194, 1, 183]], ![![-1008, -1077, -321, -13, 252]], ![![-1174, -1239, -364, -11, 299]]]
  g := ![![![62, -112, -473, -1048, 1191], ![-147, 253, 1075, 2378, -2703], ![357, -562, -2418, -5332, 6063], ![-378, 477, 2127, 4649, -5292], ![55, -58, -268, -581, 662]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [9, 0, 6, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 5, 7, 12], [2, 0, 1, 4], [9, 7, 5, 10], [0, 1]]
 g := ![![[5, 10], [6, 5, 1], []], ![[0, 8, 10, 10, 8, 1], [4, 1, 9], [4, 12, 10, 6, 3, 12]], ![[10, 4, 6, 6, 1, 12], [6, 5, 1], [4, 0, 3, 12, 4, 12]], ![[1, 7, 1, 1, 9, 4], [4, 1, 9], [7, 3, 4, 9, 0, 12]]]
 h' := ![![[7, 5, 7, 12], [11, 7, 7], [0, 0, 0, 1], [0, 1]], ![[2, 0, 1, 4], [2, 0, 12, 5], [8, 3, 10, 3], [7, 5, 7, 12]], ![[9, 7, 5, 10], [2, 7, 7, 4], [11, 0, 0, 12], [2, 0, 1, 4]], ![[0, 1], [12, 12, 0, 4], [3, 10, 3, 10], [9, 7, 5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 1, 3], []]
 b := ![[], [], [0, 2, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [9, 0, 6, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47372567016, -47775653477, -14180308033, -40095831, 18838724136]
  a := ![10, 1, 5, 6, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9440574120, -8022448145, -6887323429, -15943543179, 18838724136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58, 53, 13, -1, -15]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![58, 53, 13, -1, -15]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![58, 53, 13, -1, -15], ![183, 192, 55, -1, -57], ![687, 695, 194, -1, -183], ![1008, 1077, 321, 13, -252], ![645, 692, 208, 11, -152]]]
  hmulB := by decide  
  f := ![![![-5570, -2117, 1385, 523, -1191]], ![![-2449, -932, 609, 231, -525]], ![![-2651, -1000, 659, 242, -558]], ![![-136, -70, 34, 30, -51]], ![![-2401, -909, 597, 222, -509]]]
  g := ![![![-23, 53, 13, -1, -15], ![-86, 192, 55, -1, -57], ![-319, 695, 194, -1, -183], ![-518, 1077, 321, 13, -252], ![-338, 692, 208, 11, -152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![5570, 2117, -1385, -523, 1191]] ![![58, 53, 13, -1, -15]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -27, 11, 14, -22]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-45, -27, 11, 14, -22]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![13, 15, 16, 1, 0], ![8, 10, 12, 0, 1]] where
  M :=![![![-45, -27, 11, 14, -22], ![222, 128, -55, -64, 102], ![-1032, -585, 256, 286, -462], ![2232, 1253, -551, -603, 972], ![-428, -238, 108, 116, -191]]]
  hmulB := by decide  
  f := ![![![-79, -15, 13, 4, -10]], ![![108, 10, -23, -6, 18]], ![![-198, -53, 22, 8, -18]], ![![-149, -54, 9, 5, -8]], ![![-116, -40, 8, 4, -7]]]
  g := ![![![-3, -1, 3, 14, -22], ![14, 4, -15, -64, 102], ![-62, -15, 72, 286, -462], ![135, 34, -151, -603, 972], ![-24, -4, 32, 116, -191]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [12, 14, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10, 16], [4, 6, 1], [0, 1]]
 g := ![![[4, 0, 2], [8, 1], [7, 1], []], ![[7, 5, 8, 15], [13, 9], [3, 2], [4, 1]], ![[12, 0, 4, 8], [4, 4], [10, 15], [2, 1]]]
 h' := ![![[3, 10, 16], [7, 13, 6], [1, 9, 1], [0, 0, 1], [0, 1]], ![[4, 6, 1], [16, 14, 6], [6, 14, 14], [12, 9, 6], [3, 10, 16]], ![[0, 1], [11, 7, 5], [12, 11, 2], [9, 8, 10], [4, 6, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 12], []]
 b := ![[], [10, 6, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [12, 14, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14939739952, -15293511488, -5064751720, -278452068, 7951405856]
  a := ![-61, -8, -30, -43, 245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4407712348, -5331222884, -5648611112, -278452068, 7951405856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 15, -13, -4, 10]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![79, 15, -13, -4, 10]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![13, 2, 1, 0, 0], ![4, 5, 0, 1, 0], ![6, 1, 0, 0, 1]] where
  M :=![![![79, 15, -13, -4, 10], ![-108, -10, 23, 6, -18], ![198, 53, -22, -8, 18], ![-42, 25, 23, 5, -12], ![44, 24, 2, 0, 3]]]
  hmulB := by decide  
  f := ![![![45, 27, -11, -14, 22]], ![![-222, -128, 55, 64, -102]], ![![69, 40, -17, -20, 32]], ![![-186, -105, 46, 51, -82]], ![![28, 16, -7, -8, 13]]]
  g := ![![![12, 3, -13, -4, 10], ![-19, -4, 23, 6, -18], ![24, 7, -22, -8, 18], ![-17, -2, 23, 5, -12], ![0, 1, 2, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 12, 1] where
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
 g := ![![[7, 2], [1], [8], [1]], ![[0, 15], [1], [8], [1]]]
 h' := ![![[5, 16], [4, 6], [9, 1], [8, 5], [0, 1]], ![[0, 1], [0, 11], [14, 16], [16, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [15, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [9, 12, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50969, -188251, -205415, -97073, 379164]
  a := ![29, 11, 15, 32, -117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![43102, 19340, -205415, -97073, 379164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-45, -27, 11, 14, -22]] ![![79, 15, -13, -4, 10]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -35, 9, 12, -18]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![1, -35, 9, 12, -18]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![16, 18, 1, 0, 0], ![8, 8, 0, 1, 0], ![8, 11, 0, 0, 1]] where
  M :=![![![1, -35, 9, 12, -18], ![180, 142, -59, -54, 90], ![-918, -545, 250, 224, -378], ![1842, 995, -467, -437, 732], ![-300, -176, 78, 80, -131]]]
  hmulB := by decide  
  f := ![![![169, 179, 53, 2, -42]], ![![498, 556, 175, 16, -102]], ![![676, 755, 238, 22, -138]], ![![296, 361, 125, 21, -36]], ![![350, 414, 139, 20, -53]]]
  g := ![![![-5, -5, 9, 12, -18], ![44, 34, -59, -54, 90], ![-194, -141, 250, 224, -378], ![366, 255, -467, -437, 732], ![-60, -41, 78, 80, -131]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [11, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 18], [0, 1]]
 g := ![![[0, 7], [], [], [1]], ![[0, 12], [], [], [1]]]
 h' := ![![[0, 18], [0, 11], [7], [8], [0, 1]], ![[0, 1], [0, 8], [7], [8], [0, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [0, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [11, 0, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![415175, 233348, -111668, -126076, 207744]
  a := ![-18, -16, -8, -38, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![81501, 50884, -111668, -126076, 207744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![125, -23, -15, 18, -16]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![125, -23, -15, 18, -16]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![125, -23, -15, 18, -16], ![138, 220, -59, -116, 168], ![-1668, -1149, 452, 566, -888], ![4410, 2551, -1111, -1227, 1980], ![-806, -484, 206, 234, -375]]]
  hmulB := by decide  
  f := ![![![-915, -313, 257, 92, -224]], ![![-162, -44, 55, 18, -48]], ![![-336, -103, 104, 36, -88]], ![![-198, -29, 87, 27, -68]], ![![-304, -88, 98, 34, -79]]]
  g := ![![![11, -23, -15, 18, -16], ![-48, 220, -59, -116, 168], ![210, -1149, 452, 566, -888], ![-436, 2551, -1111, -1227, 1980], ![84, -484, 206, 234, -375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -13, 7, 5, -9]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-28, -13, 7, 5, -9]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-28, -13, 7, 5, -9], ![93, 46, -23, -19, 33], ![-339, -175, 84, 77, -129], ![612, 327, -153, -151, 252], ![-117, -64, 28, 29, -46]]]
  hmulB := by decide  
  f := ![![![2096, 367, -379, -113, 297]], ![![1485, 261, -268, -80, 210]], ![![597, 106, -107, -32, 84]], ![![766, 137, -137, -41, 108]], ![![375, 67, -67, -20, 53]]]
  g := ![![![7, -13, 7, 5, -9], ![-25, 46, -23, -19, 33], ![95, -175, 84, 77, -129], ![-178, 327, -153, -151, 252], ![35, -64, 28, 29, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2

def I19N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -21, 9, 10, -16]] i)))

def SI19N3: IdealEqSpanCertificate' Table ![![-37, -21, 9, 10, -16]] 
 ![![19, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-37, -21, 9, 10, -16], ![162, 90, -41, -44, 72], ![-732, -411, 178, 194, -312], ![1500, 829, -379, -403, 660], ![-302, -172, 70, 78, -123]]]
  hmulB := by decide  
  f := ![![![783, 149, -143, -44, 112]], ![![678, 130, -123, -38, 96]], ![![852, 167, -154, -48, 120]], ![![-42, -1, 13, 3, -12]], ![![395, 81, -69, -22, 53]]]
  g := ![![![17, -21, 9, 10, -16], ![-72, 90, -41, -44, 72], ![330, -411, 178, 194, -312], ![-660, 829, -379, -403, 660], ![139, -172, 70, 78, -123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N3 : Nat.card (O ⧸ I19N3) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N3)

lemma isPrimeI19N3 : Ideal.IsPrime I19N3 := prime_ideal_of_norm_prime hp19.out _ NI19N3
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![1, -35, 9, 12, -18]] ![![125, -23, -15, 18, -16]]
  ![![47711, 21260, -10922, -9764, 16622]] where
 M := ![![![47711, 21260, -10922, -9764, 16622]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![47711, 21260, -10922, -9764, 16622]] ![![-28, -13, 7, 5, -9]]
  ![![-3576512, -1987569, 886857, 950023, -1544021]] where
 M := ![![![-3576512, -1987569, 886857, 950023, -1544021]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N2 : IdealMulLeCertificate' Table 
  ![![-3576512, -1987569, 886857, 950023, -1544021]] ![![-37, -21, 9, 10, -16]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![1052494284, 584867994, -260977920, -279554733, 454349603]]]
 hmul := by decide  
 g := ![![![![55394436, 30782526, -13735680, -14713407, 23913137]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2, I19N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
    exact isPrimeI19N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1 ⊙ MulI19N2)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![618, 290, -144, -135, 227]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![618, 290, -144, -135, 227]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![1, 3, 2, 22, 1]] where
  M :=![![![618, 290, -144, -135, 227], ![-2319, -1207, 560, 571, -939], ![9555, 5182, -2349, -2471, 4035], ![-19344, -10698, 4782, 5107, -8304], ![3745, 2058, -928, -985, 1606]]]
  hmulB := by decide  
  f := ![![![-4, 4, 6, 1, -7]], ![![81, 57, 2, -5, -9]], ![![123, 160, 67, 1, -87]], ![![480, 414, 78, -19, -120]], ![![492, 429, 84, -19, -128]]]
  g := ![![![17, -17, -26, -223, 227], ![-60, 70, 106, 923, -939], ![240, -301, -453, -3967, 4035], ![-480, 618, 930, 8165, -8304], ![93, -120, -180, -1579, 1606]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [17, 21, 8, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 16, 5, 3], [19, 3, 5, 15], [18, 3, 13, 5], [0, 1]]
 g := ![![[7, 0, 22, 1], [20, 12], [10, 1], []], ![[13, 7, 18, 4, 1, 8], [20, 11, 1, 2, 6, 13], [17, 18, 6, 16], [7, 5, 9]], ![[4, 15, 17, 15, 11, 14], [17, 21, 8, 12, 0, 5], [8, 13, 10, 22, 20, 15], [5, 8, 18]], ![[5, 14, 3, 21, 16, 15], [15, 6, 13, 14, 12, 5], [22, 19, 12, 20, 14, 5], [4, 12, 2]]]
 h' := ![![[19, 16, 5, 3], [5, 9, 17, 22], [14, 3, 14], [0, 0, 1], [0, 1]], ![[19, 3, 5, 15], [3, 2, 4, 15], [9, 22, 0, 9], [12, 8, 17], [19, 16, 5, 3]], ![[18, 3, 13, 5], [17, 2, 14, 2], [2, 2, 21, 13], [0, 11, 7, 1], [19, 3, 5, 15]], ![[0, 1], [11, 10, 11, 7], [18, 19, 11, 1], [3, 4, 21, 22], [18, 3, 13, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 5, 8], []]
 b := ![[], [], [15, 7, 20, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [17, 21, 8, 13, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-336905735249, -320125066952, -80454699711, 9896291066, 114809231270]
  a := ![-3, 8, -1, 11, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19639781153, -28893598294, -13481441837, -109387252038, 114809231270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -4, -6, -1, 7]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![4, -4, -6, -1, 7]] 
 ![![23, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![4, -4, -6, -1, 7], ![-81, -57, -2, 5, 9], ![-123, -160, -67, -1, 87], ![-480, -414, -78, 19, 120], ![-271, -264, -70, 7, 96]]]
  hmulB := by decide  
  f := ![![![-618, -290, 144, 135, -227]], ![![-141, -61, 32, 28, -48]], ![![-711, -364, 171, 172, -284]], ![![438, 276, -114, -134, 213]], ![![-539, -266, 128, 125, -208]]]
  g := ![![![1, -4, -6, -1, 7], ![11, -57, -2, 5, 9], ![37, -160, -67, -1, 87], ![93, -414, -78, 19, 120], ![62, -264, -70, 7, 96]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![618, 290, -144, -135, 227]] ![![4, -4, -6, -1, 7]]
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


lemma PB539I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB539I0 : PrimesBelowBoundCertificateInterval O 1 23 539 where
  m := 9
  g := ![5, 5, 5, 1, 1, 2, 2, 4, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB539I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2, I19N3]
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
    · exact ![161051]
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![361, 19, 19, 19]
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
      exact NI19N1
      exact NI19N2
      exact NI19N3
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I13N1, I17N1, I19N0, I19N1, I19N2, I19N3, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [], [I13N1], [I17N1], [I19N0, I19N1, I19N2, I19N3], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
