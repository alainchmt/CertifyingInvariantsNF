
import IdealArithmetic.Examples.NF5_1_2025000000_9.RI5_1_2025000000_9
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![2, -3, 1, -1, 6], ![-72, -34, 4, 6, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![1, -2, 0, 0, 3], ![1, 1, 0, -1, 0]], ![![30, 20, 0, 0, -18], ![12, -10, 0, 6, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![1, -3, 1, -1, 6], ![-36, -34, 4, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![55, 9, -6, -2, 3], ![-220, -47, 19, 8, -9], ![664, 81, -75, -24, 39], ![-1318, -309, 97, 50, -48], ![134, -48, -35, -7, 22]]]
  hmulB := by decide  
  f := ![![![54450, -772610, -361470, -1837, 215998], ![-568906, -140894, 0, -140, -2]], ![![54036, -767092, -358884, -1823, 214453], ![-564839, -139887, 0, -139, -2]], ![![-27, 1, 6, 1, -3], ![5, 1, 0, 0, 0]], ![![27225, -386305, -180735, -918, 107999], ![-284453, -70447, 0, -70, -1]], ![![386, -5533, -2588, -13, 1547], ![-4074, -1009, 0, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![27, 9, -6, -2, 3], ![-100, -47, 19, 8, -9], ![341, 81, -75, -24, 39], ![-578, -309, 97, 50, -48], ![112, -48, -35, -7, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![55, 10, -6, -2, 3]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![55, 10, -6, -2, 3]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![55, 10, -6, -2, 3], ![-220, -47, 20, 8, -9], ![664, 82, -75, -22, 39], ![-1316, -312, 98, 49, -42], ![62, -82, -31, -1, 23]]]
  hmulB := by decide  
  f := ![![![-54, -10, 6, 2, -3], ![2, 0, 0, 0, 0]], ![![-27, -1, 5, 1, -3], ![5, 1, 0, 0, 0]], ![![-29, -273, -159, 0, 120], ![-339, -82, 1, 0, 0]], ![![1126, -27152, -16716, -145, 12462], ![-34640, -8348, 98, -1, 0]], ![![-27, -5, 3, 1, -1], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![24, 10, -6, -2, 3], ![-92, -47, 20, 8, -9], ![309, 82, -75, -22, 39], ![-530, -312, 98, 49, -42], ![76, -82, -31, -1, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]]
  ![![2, 0, 0, 0, 0], ![32, 3, -4, -1, 2]] where
 M := ![![![4, 0, 0, 0, 0], ![110, 18, -12, -4, 6]], ![![0, 2, 0, 0, 0], ![-220, -47, 19, 8, -9]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-349, 19062, 7012, -445, -4016], ![5234, 0, 0, 192, -6]]], ![![![-32, -2, 4, 1, -2], ![2, 0, 0, 0, 0]], ![![492, -28705, -10554, 671, 6045], ![-7878, 0, 0, -289, 9]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![32, 3, -4, -1, 2]] ![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]]
  ![![2, 0, 0, 0, 0], ![54, 10, -6, -2, 3]] where
 M := ![![![4, 0, 0, 0, 0], ![110, 18, -12, -4, 6]], ![![64, 6, -8, -2, 4], ![30, 36, -2, -8, 5]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![49, -553, -150, 6, 114], ![14, 0, 0, 0, -12]]], ![![![10, -375, -98, 5, 75], ![10, 0, 0, 0, -8]], ![![-4, -79, -23, -2, 20], ![3, 0, 0, 0, -2]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![54, 10, -6, -2, 3]] ![![2, 0, 0, 0, 0], ![55, 10, -6, -2, 3]]
  ![![2, 0, 0, 0, 0], ![6, 6, -1, -1, 1]] where
 M := ![![![4, 0, 0, 0, 0], ![110, 20, -12, -4, 6]], ![![108, 20, -12, -4, 6], ![-396, -44, 37, 3, -9]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![9, -12, 0, 2, -1], ![3, -1, 0, 0, 0]]], ![![![20, 0, -2, 0, 1], ![-1, -1, 0, 0, 0]], ![![-41, -33, 4, 1, -4], ![34, 7, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![6, 6, -1, -1, 1]] ![![2, 0, 0, 0, 0], ![55, 10, -6, -2, 3]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![110, 20, -12, -4, 6]], ![![12, 12, -2, -2, 2], ![-276, -74, 30, 8, -10]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![55, 10, -6, -2, 3]]], ![![![6, 6, -1, -1, 1]], ![![-138, -37, 15, 4, -5]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![2, -3, 1, 0, 6], ![-72, -34, 4, 6, 2]]]
  hmulB := by decide  
  f := ![![![118, 118, 69, 36, -4], ![81, -159, -72, 0, 6]], ![![59, 59, 34, 18, -2], ![40, -78, -36, 0, 3]], ![![59, 59, 35, 18, -2], ![41, -80, -36, 0, 3]], ![![0, -1, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![39, 39, 23, 12, -1], ![28, -53, -24, 0, 2]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-1, -3, 1, 0, 6], ![-16, -34, 4, 6, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![22, 6, -2, -1, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![22, 6, -2, -1, 1]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![22, 6, -2, -1, 1], ![-74, -11, 9, 3, -5], ![366, 96, -28, -15, 13], ![-446, -24, 62, 17, -36], ![258, 104, -5, -11, 0]]]
  hmulB := by decide  
  f := ![![![1214413, -3009960, -913940, 82730, 634358], ![3678996, 1087008, -11310, 0, -12]], ![![1012326, -2509102, -761859, 68964, 528800], ![3066809, 906129, -9428, 0, -10]], ![![809388, -2006110, -609131, 55139, 422793], ![2452015, 724480, -7538, 0, -8]], ![![-202310, 501390, 152244, -13780, -105671], ![-612839, -181072, 1884, 0, 2]], ![![809594, -2006644, -609292, 55154, 422905], ![2452666, 724672, -7540, 0, -8]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![4, 6, -2, -1, 1], ![-20, -11, 9, 3, -5], ![68, 96, -28, -15, 13], ![-150, -24, 62, 17, -36], ![20, 104, -5, -11, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![23, 6, -2, -1, 1]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![23, 6, -2, -1, 1]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![23, 6, -2, -1, 1], ![-74, -10, 9, 3, -5], ![366, 96, -27, -15, 13], ![-446, -24, 62, 18, -36], ![258, 104, -5, -11, 1]]]
  hmulB := by decide  
  f := ![![![529922, -1437474, -476374, 14591, 322447], ![1608045, 508176, -2646, 3, 0]], ![![529713, -1436939, -476195, 14586, 322326], ![1607445, 507986, -2645, 3, 0]], ![![353266, -958320, -317581, 9728, 214964], ![1072032, 338784, -1764, 2, 0]], ![![-176247, 478070, 158432, -4852, -107239], ![-534799, -169008, 880, -1, 0]], ![![-212, 540, 181, -5, -122], ![-606, -192, 1, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![5, 6, -2, -1, 1], ![-24, -10, 9, 3, -5], ![76, 96, -27, -15, 13], ![-174, -24, 62, 18, -36], ![20, 104, -5, -11, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![22, 6, -2, -1, 1]]
  ![![3, 0, 0, 0, 0], ![23, 5, -2, -1, 1]] where
 M := ![![![9, 0, 0, 0, 0], ![66, 18, -6, -3, 3]], ![![3, 3, 0, 0, 0], ![-52, -5, 7, 2, -4]]]
 hmul := by decide  
 g := ![![![![5069, -12562, -3938, 266, 4252], ![21894, 6930, 0, 0, -18]], ![![48093, -119193, -37369, 2523, 40348], ![207759, 65760, 0, 0, -171]]], ![![![3366, -8352, -2618, 177, 2827], ![14559, 4608, 0, 0, -12]], ![![-32664, 80909, 25369, -1712, -27390], ![-141024, -44638, 0, 0, 116]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![23, 5, -2, -1, 1]] ![![3, 0, 0, 0, 0], ![22, 6, -2, -1, 1]]
  ![![3, 0, 0, 0, 0], ![31, 4, -4, -1, 2]] where
 M := ![![![9, 0, 0, 0, 0], ![66, 18, -6, -3, 3]], ![![69, 15, -6, -3, 3], ![108, 19, -12, -6, 8]]]
 hmul := by decide  
 g := ![![![![-61, 956, 316, -20, -206], ![120, 0, 0, 0, 18]], ![![-340, 5102, 1686, -107, -1099], ![642, 0, 0, 0, 96]]], ![![![-361, 5741, 1894, -121, -1235], ![720, 0, 0, 0, 108]], ![![-590, 9461, 3120, -200, -2034], ![1186, 0, 0, 0, 178]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![31, 4, -4, -1, 2]] ![![3, 0, 0, 0, 0], ![22, 6, -2, -1, 1]]
  ![![3, 0, 0, 0, 0], ![7, 5, -1, -1, 1]] where
 M := ![![![9, 0, 0, 0, 0], ![66, 18, -6, -3, 3]], ![![93, 12, -12, -3, 6], ![-116, -10, 14, 2, -5]]]
 hmul := by decide  
 g := ![![![![-4, -5, 1, 1, -1], ![3, 0, 0, 0, 0]], ![![1, -9, 1, 2, -2], ![9, 0, 0, 0, 0]]], ![![![10, -11, -1, 2, -1], ![9, 0, 0, 0, 0]], ![![-20, 10, 2, -2, 1], ![-8, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![7, 5, -1, -1, 1]] ![![3, 0, 0, 0, 0], ![23, 6, -2, -1, 1]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![69, 18, -6, -3, 3]], ![![21, 15, -3, -3, 3], ![129, 24, -9, -6, 6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![23, 6, -2, -1, 1]]], ![![![7, 5, -1, -1, 1]], ![![43, 8, -3, -2, 2]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 1, -2, 2, 0], ![2, -3, 1, -3, 6], ![-72, -34, 4, 6, -1]]]
  hmulB := by decide  
  f := ![![![61, 78, -318, 325, 54], ![105, -125, -880, -45, 0]], ![![41, 52, -210, 214, 36], ![71, -80, -580, -30, 0]], ![![21, 28, -109, 111, 18], ![37, -39, -300, -15, 0]], ![![24, 25, -106, 108, 18], ![44, -39, -292, -15, 0]], ![![13, 16, -64, 65, 11], ![23, -23, -176, -9, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 5, 0, 0, 0], ![-1, 0, 5, 0, 0], ![-2, 0, 0, 5, 0], ![-1, 0, 0, 0, 5]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-1, 1, -2, 2, 0], ![2, -3, 1, -3, 6], ![3, -34, 4, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![22, 5, -2, -1, 1]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![-10, 5, 0, 0, 0], ![4, -4, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![68309, -72440, -25344, 2408, 27832], ![243440, 76000, -200, 0, 0]], ![![-23916, 25330, 8866, -841, -9735], ![-85135, -26580, 70, 0, 0]]], ![![![-23916, 25330, 8866, -841, -9735], ![-85135, -26580, 70, 0, 0]], ![![7486, -7957, -2781, 265, 3055], ![26731, 8344, -22, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![22, 5, -2, -1, 1]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![-38, -9, 3, 1, -1]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![110, 25, -10, -5, 5], ![-118, -21, 12, 5, -7]]]
 hmul := by decide  
 g := ![![![![341, -1212, -396, 48, 192], ![-540, -300, 0, 0, 0]], ![![-136, 572, 183, -23, -89], ![255, 140, 0, 0, 0]]], ![![![1320, -4940, -1607, 196, 780], ![-2205, -1220, 0, 0, 0]], ![![-1406, 5403, 1752, -215, -851], ![2412, 1332, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![-38, -9, 3, 1, -1]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![70, 11, -7, -2, 3]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![-190, -45, 15, 5, -5], ![150, 14, -18, -3, 7]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-38, -9, 3, 1, -1], ![0, 0, 0, 0, 0]], ![![-26, -6, 2, 1, -1], ![4, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![70, 11, -7, -2, 3]] ![![5, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![-10, 5, 0, 0, 0]], ![![350, 55, -35, -10, 15], ![-360, -55, 35, 10, -15]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![70, 11, -7, -2, 3]], ![![-72, -11, 7, 2, -3]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62131, -12932, 5753, 3015, -3505]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-62131, -12932, 5753, 3015, -3505]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![2, 0, 6, 1, 0], ![6, 2, 2, 0, 1]] where
  M :=![![![-62131, -12932, 5753, 3015, -3505], ![258390, 53747, -23937, -12539, 14585], ![-1075198, -223820, 99548, 52175, -60649], ![2106344, 438072, -195152, -102217, 118908], ![-780806, -162672, 72245, 37887, -44012]]]
  hmulB := by decide  
  f := ![![![-1425, -560, 193, 87, -103]], ![![7590, 2009, -885, -319, 419]], ![![-30806, -6584, 3366, 1063, -1495]], ![![-19514, -4504, 2182, 723, -992]], ![![-9192, -1854, 989, 301, -432]]]
  g := ![![![-6733, -846, -761, 3015, -3505], ![27994, 3511, 3161, -12539, 14585], ![-116522, -14646, -13172, 52175, -60649], ![228190, 28608, 25762, -102217, 118908], ![-84644, -10664, -9579, 37887, -44012]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 5, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 4], [2, 2], [0, 1]]
 g := ![![[6, 5, 1], [1]], ![[2, 5, 2], [1]], ![[6, 4, 4], [1]]]
 h' := ![![[6, 4], [1, 2, 1], [0, 1]], ![[2, 2], [0, 0, 2], [6, 4]], ![[0, 1], [2, 5, 4], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [3, 3, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 5, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2345038716, 1894457271, 224100468, -124444317, -236688627]
  a := ![-11, 15, -9, 3, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![573437016, 338262075, 206306232, -124444317, -236688627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30327, 6314, -2808, -1472, 1710]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![30327, 6314, -2808, -1472, 1710]] 
 ![![7, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![30327, 6314, -2808, -1472, 1710], ![-126064, -26205, 11682, 6116, -7122], ![525016, 109418, -48577, -25484, 29574], ![-1027116, -213210, 95274, 49829, -58104], ![382028, 80056, -35214, -18550, 21401]]]
  hmulB := by decide  
  f := ![![![103689, 17594, -10656, -2900, 4422]], ![![-46312, -6945, 4626, 1160, -1854]], ![![135808, 17870, -13201, -3032, 5106]], ![![-163692, -17478, 15318, 3053, -5616]], ![![64463, 7934, -6186, -1358, 2351]]]
  g := ![![![3111, 6314, -2808, -1472, 1710], ![-12922, -26205, 11682, 6116, -7122], ![53878, 109418, -48577, -25484, 29574], ![-105228, -213210, 95274, 49829, -58104], ![39289, 80056, -35214, -18550, 21401]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17785201, -2713102, 1783249, 452291, -718093]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-17785201, -2713102, 1783249, 452291, -718093]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-17785201, -2713102, 1783249, 452291, -718093], ![52607278, 7056337, -5133183, -1194351, 1995653], ![-146075718, -16795054, 13844598, 2901903, -5170453], ![162734572, 13901118, -14720890, -2520537, 5122656], ![21388370, 6449396, -2610055, -1015897, 1285948]]]
  hmulB := by decide  
  f := ![![![1669333021, 347354750, -154604923, -81007453, 94197149]], ![![-515077656, -107177587, 47703721, 24995085, -29064753]], ![![4842140719, 1007552336, -448453879, -234973784, 273232412]], ![![-7371852283, -1533936984, 682741735, 357732626, -415978491]], ![![4188209281, 871481658, -387890400, -203240584, 236332493]]]
  g := ![![![-2210736, -2713102, 1783249, 452291, -718093], ![6785563, 7056337, -5133183, -1194351, 1995653], ![-19553264, -16795054, 13844598, 2901903, -5170453], ![23006191, 13901118, -14720890, -2520537, 5122656], ![1848242, 6449396, -2610055, -1015897, 1285948]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-62131, -12932, 5753, 3015, -3505]] ![![30327, 6314, -2808, -1472, 1710]]
  ![![-1669333021, -347354750, 154604923, 81007453, -94197149]] where
 M := ![![![-1669333021, -347354750, 154604923, 81007453, -94197149]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-1669333021, -347354750, 154604923, 81007453, -94197149]] ![![-17785201, -2713102, 1783249, 452291, -718093]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [3, 5, 4, 2, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 5, 10, 3, 9], [9, 6, 10, 1, 7], [1, 5, 4, 0, 9], [2, 5, 9, 7, 8], [0, 1]]
 g := ![![[1, 7, 1, 0, 4], [1], []], ![[7, 8, 7, 9, 2, 6, 2, 1], [3, 4, 9, 4, 1, 10, 10, 9], [7, 1, 2, 4]], ![[10, 10, 0, 9, 3, 4, 6, 8], [9, 3, 6, 6, 9, 9, 7, 10], [6, 2, 4, 5]], ![[8, 3, 1, 3, 0, 8, 8, 9], [8, 2, 4, 4, 1, 1, 8, 1], [7, 3, 3, 4]], ![[2, 3, 5, 6, 7, 1, 6, 7], [8, 1, 0, 6, 1, 4, 10, 6], [8, 9, 6, 9]]]
 h' := ![![[8, 5, 10, 3, 9], [8, 6, 7, 9, 9], [0, 0, 1], [0, 1]], ![[9, 6, 10, 1, 7], [10, 10, 10, 0, 7], [10, 9, 3, 9, 10], [8, 5, 10, 3, 9]], ![[1, 5, 4, 0, 9], [10, 6, 2, 10, 3], [8, 6, 5, 6, 5], [9, 6, 10, 1, 7]], ![[2, 5, 9, 7, 8], [2, 3, 10, 1, 10], [2, 10, 3, 9, 4], [1, 5, 4, 0, 9]], ![[0, 1], [6, 8, 4, 2, 4], [2, 8, 10, 9, 3], [2, 5, 9, 7, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 3, 9, 2], [], [], []]
 b := ![[], [3, 4, 2, 8, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [3, 5, 4, 2, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![40311799110216080623, 29429383662259292976, 3350769684094767473, -1735660471113261649, -2773826331262888341]
  a := ![-46, 39, -50, -8, -141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3664709010019643693, 2675398514750844816, 304615425826797043, -157787315555751059, -252166030114808031]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [1, 2, 11, 10, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4, 6, 0, 3], [4, 0, 9, 3, 9], [5, 7, 0, 11, 12], [3, 1, 11, 12, 2], [0, 1]]
 g := ![![[10, 6, 9, 2, 10], [2, 1], []], ![[6, 8, 11, 6, 2, 9], [1, 11, 12, 12], [4, 8, 12, 2, 12, 0, 2, 1]], ![[12, 12, 7, 6, 10, 12, 1, 9], [10, 5, 8, 9], [9, 5, 6, 6, 4, 8, 3, 1]], ![[5, 7, 2, 5, 1, 9, 4, 4], [4, 3, 8, 10], [3, 9, 0, 11, 3, 8, 5, 12]], ![[12, 6, 7, 1, 0, 10, 0, 11], [12, 2, 8, 4], [0, 8, 4, 11, 0, 1, 4, 8]]]
 h' := ![![[3, 4, 6, 0, 3], [11, 8, 2, 8, 7], [0, 0, 0, 1], [0, 1]], ![[4, 0, 9, 3, 9], [8, 7, 8, 4], [10, 1, 0, 4, 5], [3, 4, 6, 0, 3]], ![[5, 7, 0, 11, 12], [12, 6, 2, 9, 1], [3, 3, 5, 7, 3], [4, 0, 9, 3, 9]], ![[3, 1, 11, 12, 2], [8, 6, 5, 11, 10], [5, 3, 8, 1, 7], [5, 7, 0, 11, 12]], ![[0, 1], [2, 12, 9, 7, 8], [1, 6, 0, 0, 11], [3, 1, 11, 12, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 0, 0, 1], [], [], []]
 b := ![[], [6, 1, 6, 5, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [1, 2, 11, 10, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![77093382737072, 56238708236438, 6411129432162, -3306250373959, -5278192796136]
  a := ![-3, 3, -3, -1, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5930260210544, 4326054479726, 493163802474, -254326951843, -406014830472]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![118, 43, -11, -6, 6]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![118, 43, -11, -6, 6]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![16, 0, 13, 1, 0], ![13, 10, 14, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![118, 43, -11, -6, 6], ![-444, -79, 61, 20, -30], ![2200, 577, -179, -78, 90], ![-3096, -363, 399, 120, -174], ![984, 266, -26, -16, 30]]]
  hmulB := by decide  
  f := ![![![2481, -5720, -1800, 80, 720], ![4760, 1360, 0, 0, 0]], ![![-428, 673, 236, -4, -96], ![-578, -170, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![2342, -5381, -1694, 75, 678], ![4479, 1280, 0, 0, 0]], ![![1701, -3958, -1242, 56, 497], ![3292, 940, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-16, 0, -13, 17, 0], ![-13, -10, -14, 0, 17]], ![![8, -1, -1, -6, 6], ![-22, 13, 13, 20, -30], ![134, -19, -25, -78, 90], ![-162, 81, 75, 120, -174], ![50, -2, -14, -16, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [2, 12, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 8, 7], [11, 8, 10], [0, 1]]
 g := ![![[13, 12, 2], [0, 13], [2, 1], []], ![[7, 16, 10, 10], [1, 13], [0, 13], [6, 15]], ![[10, 12, 13, 6], [2, 1], [1, 13], [3, 15]]]
 h' := ![![[8, 8, 7], [16, 12, 6], [13, 8, 9], [0, 0, 1], [0, 1]], ![[11, 8, 10], [16, 14, 13], [1, 9, 9], [1, 9, 8], [8, 8, 7]], ![[0, 1], [5, 8, 15], [14, 0, 16], [13, 8, 8], [11, 8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 16], []]
 b := ![[], [1, 11, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [2, 12, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-90294515698, -73012440880, -8622504008, 4813508100, 9164135696]
  a := ![37, -46, 33, -10, 110]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16849671138, -9685517520, -11735059356, 4813508100, 9164135696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-8, 1, 0, 0, 0], ![0, -8, 1, 0, 0], ![0, 1, -8, 2, 0], ![2, -3, 1, -9, 6], ![-72, -34, 4, 6, -7]]]
  hmulB := by decide  
  f := ![![![127441, -28893, 153726, -39372, 504], ![270453, 13974, 328236, -1428, 0]], ![![84833, -19234, 102325, -26208, 336], ![180031, 9299, 218484, -952, 0]], ![![42380, -9602, 51114, -13092, 168], ![89938, 4659, 109140, -476, 0]], ![![21255, -4817, 25633, -6565, 84], ![45107, 2333, 54732, -238, 0]], ![![22499, -5099, 27128, -6948, 89], ![47747, 2468, 57924, -252, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 17, 0, 0, 0], ![-4, 0, 17, 0, 0], ![-3, 0, 0, 17, 0], ![-3, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![4, -8, 1, 0, 0], ![1, 1, -8, 2, 0], ![2, -3, 1, -9, 6], ![13, -34, 4, 6, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![2, -3, 1, -2, 6], ![-72, -34, 4, 6, 0]]]
  hmulB := by decide  
  f := ![![![4, -3, 0, 0, 0], ![51, 0, 0, 0, 0]], ![![2, -1, 0, 0, 0], ![18, 0, 0, 0, 0]], ![![2, -1, 0, 0, 0], ![18, 1, 0, 0, 0]], ![![0, 0, 0, -1, 0], ![0, 9, 9, 0, 0]], ![![0, -2, 2, -6, -1], ![6, 17, 54, 3, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-16, 17, 0, 0, 0], ![-16, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![2, -3, 1, -2, 6], ![24, -34, 4, 6, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![118, 43, -11, -6, 6]] ![![17, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0], ![30, -7, -3, 0, 1]] where
 M := ![![![289, 0, 0, 0, 0], ![-136, 17, 0, 0, 0]], ![![2006, 731, -187, -102, 102], ![-1388, -423, 149, 68, -78]]]
 hmul := by decide  
 g := ![![![![-13, 7, 3, 0, -1], ![17, 0, 0, 0, 0]], ![![-8, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![28, 64, -2, -6, 3], ![51, 0, 0, 0, 0]], ![![-34, -36, 4, 4, -3], ![-27, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![30, -7, -3, 0, 1]] ![![17, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![289, 0, 0, 0, 0], ![-17, 17, 0, 0, 0]], ![![510, -119, -51, 0, 17], ![-102, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![30, -7, -3, 0, 1]], ![![-6, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-187, -44, 17, 8, -8]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-187, -44, 17, 8, -8]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![1, 9, 2, 1, 0], ![3, 5, 7, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-187, -44, 17, 8, -8], ![592, 78, -68, -22, 40], ![-2924, -770, 216, 126, -92], ![3142, -18, -472, -112, 312], ![-2412, -1088, 32, 120, 30]]]
  hmulB := by decide  
  f := ![![![3707, -11632, -3230, 520, 3152], ![-11894, -3876, 0, 0, 0]], ![![-185, 693, 187, -32, -184], ![703, 228, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![137, -277, -84, 11, 80], ![-290, -96, 0, 0, 0]], ![![576, -1645, -464, 72, 451], ![-1689, -552, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-1, -9, -2, 19, 0], ![-3, -5, -7, 0, 19]], ![![-9, -4, 3, 8, -8], ![26, 4, -16, -22, 40], ![-146, -76, 32, 126, -92], ![122, -30, -128, -112, 312], ![-138, -122, -22, 120, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [12, 9, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 7, 4], [6, 11, 15], [0, 1]]
 g := ![![[1, 7, 16], [4, 3, 7], [13, 1], []], ![[12, 2, 0, 1], [6, 6, 12, 1], [15, 7], [17, 16]], ![[8, 13, 17, 14], [8, 18, 6, 3], [10, 11], [6, 16]]]
 h' := ![![[7, 7, 4], [9, 1, 4], [15, 4, 8], [0, 0, 1], [0, 1]], ![[6, 11, 15], [4, 7, 10], [0, 9, 9], [16, 0, 11], [7, 7, 4]], ![[0, 1], [4, 11, 5], [17, 6, 2], [2, 0, 7], [6, 11, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 9], []]
 b := ![[], [12, 11, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [12, 9, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7981376846, 8559118828, 1450190690, -423292152, -1353297902]
  a := ![-22, 34, -16, 14, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![656029616, 1007117774, 619466332, -423292152, -1353297902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![6, 1, 0, 0, 0], ![0, 6, 1, 0, 0], ![0, 1, 6, 2, 0], ![2, -3, 1, 5, 6], ![-72, -34, 4, 6, 7]]]
  hmulB := by decide  
  f := ![![![5673, 1966, 7531, 2622, 132], ![-17822, 513, -23864, -418, 0]], ![![2836, 982, 3777, 1315, 66], ![-8910, 266, -11970, -209, 0]], ![![2832, 987, 3813, 1327, 66], ![-8898, 267, -12084, -209, 0]], ![![2840, 981, 3762, 1310, 66], ![-8922, 263, -11922, -209, 0]], ![![291, 100, 396, 138, 7], ![-914, 34, -1256, -22, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 19, 0, 0, 0], ![-2, 0, 19, 0, 0], ![-10, 0, 0, 19, 0], ![-1, 0, 0, 0, 19]], ![![0, 1, 0, 0, 0], ![-2, 6, 1, 0, 0], ![-2, 1, 6, 2, 0], ![-2, -3, 1, 5, 6], ![3, -34, 4, 6, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![9, 1, 0, 0, 0], ![0, 9, 1, 0, 0], ![0, 1, 9, 2, 0], ![2, -3, 1, 8, 6], ![-72, -34, 4, 6, 10]]]
  hmulB := by decide  
  f := ![![![-431450, -91146, -598103, -135432, -1512], ![909777, -47899, 1267452, 4788, 0]], ![![-215766, -45579, -299105, -67728, -756], ![454975, -23959, 633840, 2394, 0]], ![![-335520, -70876, -465119, -105320, -1176], ![707494, -37258, 985644, 3724, 0]], ![![-407492, -86077, -564879, -127909, -1428], ![859258, -45253, 1197048, 4522, 0]], ![![-158960, -33583, -220354, -49896, -557], ![335191, -17642, 466956, 1764, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 19, 0, 0, 0], ![-14, 0, 19, 0, 0], ![-18, 0, 0, 19, 0], ![-7, 0, 0, 0, 19]], ![![0, 1, 0, 0, 0], ![-5, 9, 1, 0, 0], ![-9, 1, 9, 2, 0], ![-9, -3, 1, 8, 6], ![0, -34, 4, 6, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![-187, -44, 17, 8, -8]] ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0], ![150, 34, -15, -7, 8]] where
 M := ![![![361, 0, 0, 0, 0], ![114, 19, 0, 0, 0]], ![![-3553, -836, 323, 152, -152], ![-530, -186, 34, 26, -8]]]
 hmul := by decide  
 g := ![![![![-131, -34, 15, 7, -8], ![19, 0, 0, 0, 0]], ![![-144, -33, 15, 7, -8], ![19, 0, 0, 0, 0]]], ![![![-37, -10, 2, 1, 0], ![-19, 0, 0, 0, 0]], ![![-20, -8, 1, 1, 0], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![150, 34, -15, -7, 8]] ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![361, 0, 0, 0, 0], ![171, 19, 0, 0, 0]], ![![2850, 646, -285, -133, 152], ![760, 190, -76, -38, 38]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0]], ![![9, 1, 0, 0, 0]]], ![![![150, 34, -15, -7, 8]], ![![40, 10, -4, -2, 2]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-225, -51, 21, 10, -10]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-225, -51, 21, 10, -10]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![17, 11, 22, 1, 0], ![5, 0, 13, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-225, -51, 21, 10, -10], ![740, 106, -81, -28, 50], ![-3656, -957, 278, 166, -118], ![4044, 15, -591, -145, 414], ![-3288, -1466, 62, 172, 41]]]
  hmulB := by decide  
  f := ![![![3871, -11346, -2724, 796, 3560], ![-14582, -4554, 0, 0, 0]], ![![-135, 526, 120, -38, -160], ![667, 207, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![2689, -8159, -1945, 575, 2550], ![-10470, -3267, 0, 0, 0]], ![![910, -2451, -598, 170, 777], ![-3163, -990, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-17, -11, -22, 23, 0], ![-5, 0, -13, 0, 23]], ![![-15, -7, -3, 10, -10], ![42, 18, -5, -28, 50], ![-256, -121, -80, 166, -118], ![193, 70, -121, -145, 414], ![-279, -146, -185, 172, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [13, 18, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 14], [19, 22, 9], [0, 1]]
 g := ![![[0, 13, 6], [1, 0, 4], [21, 19, 1], []], ![[18, 7], [0, 17, 18, 22], [2, 0, 15, 14], [21, 12]], ![[0, 7, 8, 8], [11, 13, 4, 3], [18, 18], [3, 12]]]
 h' := ![![[0, 0, 14], [10, 14, 12], [3, 19, 21], [0, 0, 1], [0, 1]], ![[19, 22, 9], [0, 9], [20, 10, 15], [3, 18, 22], [0, 0, 14]], ![[0, 1], [0, 0, 11], [19, 17, 10], [0, 5], [19, 22, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 16], []]
 b := ![[], [13, 5, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [13, 18, 4, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4570538613, 924189432, -451128500, -232862636, 284100216]
  a := ![12, -28, 10, -26, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![309074015, 151551236, 42545508, -232862636, 284100216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![10, 1, 0, 0, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![10, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![10, 1, 0, 0, 0], ![0, 10, 1, 0, 0], ![0, 1, 10, 2, 0], ![2, -3, 1, 9, 6], ![-72, -34, 4, 6, 11]]]
  hmulB := by decide  
  f := ![![![-9657, -3205, -32886, -6808, -144], ![22103, -2254, 75808, 552, 0]], ![![-4854, -1613, -16523, -3420, -72], ![11110, -1127, 38088, 276, 0]], ![![-9813, -3257, -33444, -6920, -144], ![22461, -2299, 77096, 552, 0]], ![![-4820, -1606, -16409, -3397, -72], ![11032, -1109, 37824, 276, 0]], ![![-1696, -566, -5720, -1184, -25], ![3882, -376, 13184, 96, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 23, 0, 0, 0], ![-15, 0, 23, 0, 0], ![-12, 0, 0, 23, 0], ![-4, 0, 0, 0, 23]], ![![0, 1, 0, 0, 0], ![-5, 10, 1, 0, 0], ![-8, 1, 10, 2, 0], ![-5, -3, 1, 9, 6], ![4, -34, 4, 6, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-8, 1, 0, 0, 0], ![0, -8, 1, 0, 0], ![0, 1, -8, 2, 0], ![2, -3, 1, -9, 6], ![-72, -34, 4, 6, -7]]]
  hmulB := by decide  
  f := ![![![-3683, 3871, -34172, 8694, -84], ![-10511, -2622, -98532, 322, 0]], ![![-3675, 3842, -33885, 8622, -84], ![-10487, -2599, -97704, 322, 0]], ![![-3665, 3786, -33382, 8496, -84], ![-10457, -2575, -96255, 322, 0]], ![![-1, 7, -44, 11, 0], ![-3, 4, -126, 0, 0]], ![![-3204, 3368, -29715, 7560, -73], ![-9144, -2275, -85680, 280, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-15, 23, 0, 0, 0], ![-5, 0, 23, 0, 0], ![-1, 0, 0, 23, 0], ![-20, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![5, -8, 1, 0, 0], ![1, 1, -8, 2, 0], ![-3, -3, 1, -9, 6], ![24, -34, 4, 6, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-225, -51, 21, 10, -10]] ![![23, 0, 0, 0, 0], ![10, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0], ![176, 13, -14, -3, 4]] where
 M := ![![![529, 0, 0, 0, 0], ![230, 23, 0, 0, 0]], ![![-5175, -1173, 483, 230, -230], ![-1510, -404, 129, 72, -50]]]
 hmul := by decide  
 g := ![![![![-153, -13, 14, 3, -4], ![23, 0, 0, 0, 0]], ![![-166, -12, 14, 3, -4], ![23, 0, 0, 0, 0]]], ![![![-49, -38, 7, 7, -6], ![-23, 0, 0, 0, 0]], ![![-58, -17, 5, 3, -2], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![176, 13, -14, -3, 4]] ![![23, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![-184, 23, 0, 0, 0]], ![![4048, 299, -322, -69, 92], ![-1702, -69, 138, 23, -46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![-8, 1, 0, 0, 0]]], ![![![176, 13, -14, -3, 4]], ![![-74, -3, 6, 1, -2]]]]
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


lemma PB2802I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2802I0 : PrimesBelowBoundCertificateInterval O 1 23 2802 where
  m := 9
  g := ![5, 5, 5, 3, 1, 1, 3, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2802I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0]
    · exact ![I13N0]
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
    · exact ![343, 7, 7]
    · exact ![161051]
    · exact ![371293]
    · exact ![4913, 17, 17]
    · exact ![6859, 19, 19]
    · exact ![12167, 23, 23]
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
      exact NI3N1
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
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
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
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I7N2, I17N1, I17N2, I19N1, I19N2, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [], [], [I17N1, I17N2], [I19N1, I19N2], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
