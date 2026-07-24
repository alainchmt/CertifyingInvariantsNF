
import IdealArithmetic.Examples.NF5_3_1822500000_2.RI5_3_1822500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1538, -974, -121, -62, -277]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1538, -974, -121, -62, -277]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1538, -974, -121, -62, -277], ![2184, 2543, 871, 1211, 4054], ![-10104, -5238, -2296, -3443, -11362], ![24792, 9522, 4749, 7346, 24106], ![-4524, -636, -574, -976, -3151]]]
  hmulB := by decide  
  f := ![![![-509, -2108, 684, 1113, 3381]], ![![-504, -2113, 689, 1119, 3402]], ![![-1080, -4266, 1328, 2207, 6702]], ![![-1944, -8430, 2699, 4446, 13606]], ![![1266, 5328, -1708, -2804, -8549]]]
  g := ![![![769, -974, -121, -62, -277], ![1092, 2543, 871, 1211, 4054], ![-5052, -5238, -2296, -3443, -11362], ![12396, 9522, 4749, 7346, 24106], ![-2262, -636, -574, -976, -3151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 5, -5, -6, -21]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-5, 5, -5, -6, -21]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-5, 5, -5, -6, -21], ![72, 40, 50, 31, 102], ![-216, -102, -43, -32, -202], ![2544, 834, 2208, 1589, 5044], ![-756, -255, -679, -484, -1516]]]
  hmulB := by decide  
  f := ![![![1598, -373, 44, 147, 436]], ![![60, 601, 165, 209, 713]], ![![-2064, -1341, -541, -793, -2628]], ![![5976, 2556, 1214, 1857, 6106]], ![![-593, -410, -162, -236, -783]]]
  g := ![![![8, 5, -5, -6, -21], ![-15, 40, 50, 31, 102], ![-7, -102, -43, -32, -202], ![-1250, 834, 2208, 1589, 5044], ![380, -255, -679, -484, -1516]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3253, -1367, -1956, -1372, -4916]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-3253, -1367, -1956, -1372, -4916]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-3253, -1367, -1956, -1372, -4916], ![19200, 8063, 11545, 8100, 29024], ![-113376, -47616, -68189, -47839, -171400], ![669192, 281088, 402337, 282261, 1011438], ![-185832, -78057, -111723, -78380, -280867]]]
  hmulB := by decide  
  f := ![![![9406, 3316, 1723, 2689, 8810]], ![![-4213, -1016, -647, -1049, -3414]], ![![20027, 5669, 3299, 5265, 17182]], ![![-19669, -3919, -2802, -4625, -15006]], ![![72, -393, -98, -118, -407]]]
  g := ![![![721, -1367, -1956, -1372, -4916], ![-4254, 8063, 11545, 8100, 29024], ![25134, -47616, -68189, -47839, -171400], ![-148247, 281088, 402337, 282261, 1011438], ![41164, -78057, -111723, -78380, -280867]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1538, -974, -121, -62, -277]] ![![-5, 5, -5, -6, -21]]
  ![![2, -1, 0, 0, 0]] where
 M := ![![![2, -1, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, -1, 0, 0, 0]] ![![-5, 5, -5, -6, -21]]
  ![![-82, -30, -60, -43, -144]] where
 M := ![![![-82, -30, -60, -43, -144]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-82, -30, -60, -43, -144]] ![![-3253, -1367, -1956, -1372, -4916]]
  ![![4477858, 1880588, 2693003, 1889341, 6769406]] where
 M := ![![![4477858, 1880588, 2693003, 1889341, 6769406]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![4477858, 1880588, 2693003, 1889341, 6769406]] ![![-3253, -1367, -1956, -1372, -4916]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-277421463922, -116516522824, -166827039976, -117040191172, -419363150660]]]
 hmul := by decide  
 g := ![![![![-138710731961, -58258261412, -83413519988, -58520095586, -209681575330]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 12, 9, 26]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![9, 1, 12, 9, 26]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![9, 1, 12, 9, 26], ![24, -9, 60, 46, 122], ![384, 30, 543, 408, 1168], ![1344, -336, 2950, 2255, 6064], ![-504, 99, -1042, -795, -2153]]]
  hmulB := by decide  
  f := ![![![-381, -77, -58, -95, -308]], ![![184, 37, 24, 40, 130]], ![![-240, -26, -33, -56, -180]], ![![288, 36, 26, 47, 152]], ![![48, 7, 12, 19, 61]]]
  g := ![![![3, 1, 12, 9, 26], ![8, -9, 60, 46, 122], ![128, 30, 543, 408, 1168], ![448, -336, 2950, 2255, 6064], ![-168, 99, -1042, -795, -2153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-227, 62, -4, -18, -52]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-227, 62, -4, -18, -52]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-227, 62, -4, -18, -52], ![-48, -191, -56, -72, -244], ![672, 420, 165, 248, 824], ![-1920, -792, -428, -619, -2016], ![432, 66, 72, 106, 337]]]
  hmulB := by decide  
  f := ![![![-1281, -5322, 1732, 2814, 8548]], ![![-1702, -7107, 2320, 3764, 11436]], ![![-2614, -10720, 3461, 5644, 17136]], ![![-4054, -17812, 5988, 9585, 29176]], ![![1669, 7216, -2404, -3864, -11755]]]
  g := ![![![-85, 62, -4, -18, -52], ![278, -191, -56, -72, -244], ![-606, 420, 165, 248, 824], ![1258, -792, -428, -619, -2016], ![-131, 66, 72, 106, 337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![9, 1, 12, 9, 26]] ![![9, 1, 12, 9, 26]]
  ![![3705, -90, 6142, 4648, 12970]] where
 M := ![![![3705, -90, 6142, 4648, 12970]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3705, -90, 6142, 4648, 12970]] ![![-227, 62, -4, -18, -52]]
  ![![-30411, 1344, -51854, -39286, -109170]] where
 M := ![![![-30411, 1344, -51854, -39286, -109170]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-30411, 1344, -51854, -39286, -109170]] ![![-227, 62, -4, -18, -52]]
  ![![260577, -11574, 444638, 336852, 936026]] where
 M := ![![![260577, -11574, 444638, 336852, 936026]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![260577, -11574, 444638, 336852, 936026]] ![![-227, 62, -4, -18, -52]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-2191299, 105300, -3807678, -2879466, -7997106]]]
 hmul := by decide  
 g := ![![![![-730433, 35100, -1269226, -959822, -2665702]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5855, 1554, 937, 1505, 4906]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5855, 1554, 937, 1505, 4906]] 
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![5855, 1554, 937, 1505, 4906], ![-9384, -2179, -1419, -2309, -7510], ![13992, 2790, 1994, 3291, 10678], ![-19320, -3126, -2561, -4304, -13922], ![-1440, -660, -304, -462, -1521]]]
  hmulB := by decide  
  f := ![![![-53, -306, 133, 187, 562]], ![![-26, -247, 137, 173, 514]], ![![119, -312, 419, 404, 1168]], ![![1029, -756, 2312, 1945, 5480]], ![![-336, 336, -818, -708, -2005]]]
  g := ![![![-541, 1554, 937, 1505, 4906], ![664, -2179, -1419, -2309, -7510], ![-691, 2790, 1994, 3291, 10678], ![481, -3126, -2561, -4304, -13922], ![314, -660, -304, -462, -1521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5855, 1554, 937, 1505, 4906]] ![![5855, 1554, 937, 1505, 4906]]
  ![![-3332447, 384144, -196342, -436836, -1355260]] where
 M := ![![![-3332447, 384144, -196342, -436836, -1355260]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-3332447, 384144, -196342, -436836, -1355260]] ![![5855, 1554, 937, 1505, 4906]]
  ![![-15472255825, -4303445658, -2528373087, -4042210489, -13187465046]] where
 M := ![![![-15472255825, -4303445658, -2528373087, -4042210489, -13187465046]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-15472255825, -4303445658, -2528373087, -4042210489, -13187465046]] ![![5855, 1554, 937, 1505, 4906]]
  ![![11501936279713, -381161457024, 928600181512, 1820317974288, 5747810753968]] where
 M := ![![![11501936279713, -381161457024, 928600181512, 1820317974288, 5747810753968]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![11501936279713, -381161457024, 928600181512, 1820317974288, 5747810753968]] ![![5855, 1554, 937, 1505, 4906]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![40468239021190655, 11811485214704610, 6760642362185225, 10756401972923705, 35121727673884490]]]
 hmul := by decide  
 g := ![![![![8093647804238131, 2362297042940922, 1352128472437045, 2151280394584741, 7024345534776898]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [1, 1, 5, 6, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 0, 1], [4, 2, 1, 2, 4], [0, 3, 3, 6, 3], [3, 1, 3, 5], [0, 1]]
 g := ![![[5, 2, 1], []], ![[4, 3, 6, 2, 5, 6, 2], [6, 6, 5, 2, 1]], ![[2, 4, 0, 5, 4, 3, 3, 1], [3, 6, 2, 5, 5, 6, 0, 1]], ![[4, 5, 2, 5, 5, 5], [6, 0, 2, 5, 1, 3, 6, 6]], ![[5], [1, 4, 4, 6, 6]]]
 h' := ![![[2, 0, 0, 1], [0, 0, 0, 1], [0, 1]], ![[4, 2, 1, 2, 4], [2, 2, 1, 2, 4], [2, 0, 0, 1]], ![[0, 3, 3, 6, 3], [5, 3, 3, 6, 3], [4, 2, 1, 2, 4]], ![[3, 1, 3, 5], [1, 1, 3, 5], [0, 3, 3, 6, 3]], ![[0, 1], [5, 1], [3, 1, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 0, 4], [], [], []]
 b := ![[], [1, 1, 1, 1, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [1, 1, 5, 6, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81740008095405695, -896414340200554, -128652467384931644, -97143353301332674, -273242619722453416]
  a := ![-180, -61, -183, -126, -395]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11677144013629385, -128059191457222, -18378923912133092, -13877621900190382, -39034659960350488]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [2, 1, 7, 1, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 9, 5, 6, 6], [6, 9, 7, 9, 8], [5, 9, 6, 10], [1, 5, 4, 8, 8], [0, 1]]
 g := ![![[7, 5, 0, 7, 4], [1], []], ![[2, 1, 4, 4, 9, 7, 2, 2], [3, 10, 0, 3, 8, 5, 3, 2], [5, 5, 0, 3]], ![[6, 1, 5, 3, 5, 10, 3, 8], [7, 8, 0, 0, 0, 6, 3, 7], [8, 9, 5, 9]], ![[1, 4, 1, 10, 6, 1, 2], [1, 1, 10, 1, 7, 7, 10], [8, 1]], ![[10, 0, 7, 0, 0, 10], [4, 2, 4, 10, 2, 6, 3, 8], [8, 9, 0, 9]]]
 h' := ![![[8, 9, 5, 6, 6], [9, 10, 4, 10, 9], [0, 0, 1], [0, 1]], ![[6, 9, 7, 9, 8], [2, 1, 1, 9, 9], [10, 8, 0, 8, 2], [8, 9, 5, 6, 6]], ![[5, 9, 6, 10], [10, 3, 3, 2, 1], [9, 5, 2, 8, 7], [6, 9, 7, 9, 8]], ![[1, 5, 4, 8, 8], [7, 6, 2, 10, 3], [9, 3, 7, 6, 1], [5, 9, 6, 10]], ![[0, 1], [8, 2, 1, 2], [7, 6, 1, 0, 1], [1, 5, 4, 8, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 5, 7, 8], [], [], []]
 b := ![[], [0, 9, 4, 3, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [2, 1, 7, 1, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![958643984980065626, 81792579732718085, 1339347122922309974, 1005710610245371679, 2885471491197804762]
  a := ![309, 41, 314, 215, 678]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![87149453180005966, 7435689066610735, 121758829356573634, 91428237295033789, 262315590108891342]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [11, 10, 10, 7, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10, 1, 2, 9], [12, 12, 11, 7, 11], [11, 0, 5, 9, 5], [1, 3, 9, 8, 1], [0, 1]]
 g := ![![[3, 1, 6, 4, 3], [4, 1], []], ![[3, 8, 12, 12, 4, 0, 8, 9], [1, 3, 7, 10], [5, 7, 1, 7, 2, 3, 9, 1]], ![[4, 5, 10, 2, 4, 6, 1, 5], [8, 4, 0, 12], [5, 0, 8, 0, 12, 11, 0, 5]], ![[4, 8, 2, 11, 3, 1, 12, 11], [1, 0, 1, 3], [3, 8, 6, 12, 3, 7, 5, 8]], ![[5, 10, 3, 10, 10, 12], [0, 3, 0, 10], [1, 6, 5, 10, 2, 12, 2, 1]]]
 h' := ![![[6, 10, 1, 2, 9], [8, 1, 2, 1, 9], [0, 0, 0, 1], [0, 1]], ![[12, 12, 11, 7, 11], [1, 10, 2, 6, 12], [5, 4, 9, 6, 7], [6, 10, 1, 2, 9]], ![[11, 0, 5, 9, 5], [6, 1, 4, 12, 11], [9, 12, 9, 10, 8], [12, 12, 11, 7, 11]], ![[1, 3, 9, 8, 1], [6, 7, 2, 12, 7], [11, 12, 1, 10, 4], [11, 0, 5, 9, 5]], ![[0, 1], [9, 7, 3, 8], [3, 11, 7, 12, 7], [1, 3, 9, 8, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 12, 4, 11], [], [], []]
 b := ![[], [5, 7, 0, 6, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [11, 10, 10, 7, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41027780040, 1820009620, -69971892406, -53013225525, -147310920627]
  a := ![-5, -4, -5, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3155983080, 140000740, -5382453262, -4077940425, -11331609279]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4003, -1699, -2364, -1655, -5970]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-4003, -1699, -2364, -1655, -5970]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![14, 11, 6, 2, 1]] where
  M :=![![![-4003, -1699, -2364, -1655, -5970], ![24120, 10007, 14796, 10406, 37010], ![-139008, -59226, -81585, -57064, -206352], ![843840, 348624, 521198, 366847, 1301488], ![-235176, -96777, -146170, -102959, -364441]]]
  hmulB := by decide  
  f := ![![![589, 1805, -550, -893, -2704]], ![![600, 3493, -1192, -1936, -5894]], ![![2064, 7182, -2273, -3688, -11188]], ![![2976, 14244, -4718, -7665, -23304]], ![![1822, 7428, -2410, -3913, -11885]]]
  g := ![![![4681, 3763, 1968, 605, -5970], ![-29060, -23359, -12192, -3742, 37010], ![161760, 130038, 68031, 20920, -206352], ![-1022176, -821632, -428690, -131537, 1301488], ![286294, 230122, 120028, 36819, -364441]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [4, 7, 16, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 14, 15], [3, 0, 8, 4], [0, 14, 12, 15], [0, 1]]
 g := ![![[16, 1, 5, 1], [3, 0, 15], [1], []], ![[10, 10, 12, 9, 4, 13], [2, 3, 16], [7, 11, 15], [13, 6, 4]], ![[11, 4, 3, 14, 8, 1], [16], [16, 15, 15], [3, 6, 16]], ![[0, 11, 2, 12, 15, 15], [9, 12, 9], [5, 12, 9], [3, 14, 4]]]
 h' := ![![[4, 2, 14, 15], [4, 1, 1, 16], [13, 10, 1, 7], [0, 0, 1], [0, 1]], ![[3, 0, 8, 4], [7, 16, 3, 11], [10, 14, 3, 13], [15, 3, 3, 7], [4, 2, 14, 15]], ![[0, 14, 12, 15], [3, 5, 13, 8], [13, 13, 13], [14, 6, 13, 7], [3, 0, 8, 4]], ![[0, 1], [6, 12, 0, 16], [5, 14, 0, 14], [5, 8, 0, 3], [0, 14, 12, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 7, 3], []]
 b := ![[], [], [5, 9, 5, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [4, 7, 16, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![138669737474396, 14513918121426, 187361024242097, 140450904458901, 405380159423142]
  a := ![319, 126, 324, 221, 700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-325685440849976, -261451049149008, -132054113664515, -39429965552199, 405380159423142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-589, -1805, 550, 893, 2704]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-589, -1805, 550, 893, 2704]] 
 ![![17, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-589, -1805, 550, 893, 2704], ![-600, -3493, 1192, 1936, 5894], ![-2064, -7182, 2273, 3688, 11188], ![-2976, -14244, 4718, 7665, 23304], ![2208, 8997, -2916, -4735, -14381]]]
  hmulB := by decide  
  f := ![![![4003, 1699, 2364, 1655, 5970]], ![![-6, 11, -36, -28, -70]], ![![11709, 4983, 6885, 4817, 17406]], ![![-46812, -19308, -28990, -20411, -72344]], ![![16895, 6992, 10406, 7322, 26003]]]
  g := ![![![-2581, -1805, 550, 893, 2704], ![-5728, -3493, 1192, 1936, 5894], ![-10751, -7182, 2273, 3688, 11188], ![-22542, -14244, 4718, 7665, 23304], ![13867, 8997, -2916, -4735, -14381]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-4003, -1699, -2364, -1655, -5970]] ![![-589, -1805, 550, 893, 2704]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [6, 14, 13, 7, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 9, 4, 0, 9], [3, 3, 6, 11, 18], [2, 9, 14, 5, 13], [18, 16, 14, 3, 17], [0, 1]]
 g := ![![[18, 10, 4, 14, 4], [18, 11, 17, 10, 1], [], []], ![[13, 11, 10, 3, 11, 9, 17, 5], [13, 18, 4, 12, 6, 4, 16, 11], [0, 1, 1, 1], [6, 5, 12, 5]], ![[5, 4, 9, 12, 11, 4, 0, 15], [1, 13, 10, 11, 7, 14, 15, 14], [13, 13, 17, 4], [17, 1, 7, 1]], ![[11, 4, 10, 2, 15, 16, 12, 12], [14, 11, 15, 14, 13, 1, 12, 13], [12, 11, 9, 1], [11, 2, 15, 17]], ![[8, 13, 4, 0, 11, 10, 15, 17], [18, 6, 18, 2, 6, 18, 1, 7], [15, 9, 14, 4], [17, 15, 9, 4]]]
 h' := ![![[6, 9, 4, 0, 9], [6, 5, 4, 3, 2], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[3, 3, 6, 11, 18], [17, 14, 18, 11, 3], [0, 13, 16, 14, 4], [0, 13, 4, 14, 18], [6, 9, 4, 0, 9]], ![[2, 9, 14, 5, 13], [6, 12, 18, 1, 2], [2, 14, 10, 9, 10], [2, 2, 15, 18, 2], [3, 3, 6, 11, 18]], ![[18, 16, 14, 3, 17], [2, 15, 15, 15, 13], [10, 2, 11, 4, 18], [14, 3, 9, 9, 1], [2, 9, 14, 5, 13]], ![[0, 1], [16, 11, 2, 8, 18], [3, 9, 1, 11, 5], [13, 1, 9, 16, 17], [18, 16, 14, 3, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 17, 7, 3], [], [], []]
 b := ![[], [8, 17, 3, 11, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [6, 14, 13, 7, 9, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2876756823378506046, -250784998084036780, -4006503854624004952, -3007995341698485434, -8635004432270121052]
  a := ![-391, -131, -396, -270, -858]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-151408253862026634, -13199210425475620, -210868623927579208, -158315544299920286, -454473917487901108]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-699077, -159625, -104991, -171118, -556406]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-699077, -159625, -104991, -171118, -556406]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![5, 8, 2, 1, 0], ![9, 14, 0, 0, 1]] where
  M :=![![![-699077, -159625, -104991, -171118, -556406], ![1033248, 201745, 146099, 241605, 783656], ![-1412184, -221136, -185178, -312147, -1009210], ![1746456, 179178, 203963, 354832, 1141274], ![249744, 87507, 45604, 71217, 233303]]]
  hmulB := by decide  
  f := ![![![-307, -355, -147, -22, -68]], ![![48, -223, -397, -159, -76]], ![![-9624, -3084, -10082, -7131, -21322]], ![![-961, 61, -2492, -1788, -4530]], ![![27, -376, 241, 297, 917]]]
  g := ![![![224529, 391261, 10315, -171118, -556406], ![-314247, -552273, -14657, 241605, 783656], ![401367, 713260, 19092, -312147, -1009210], ![-447790, -810318, -21987, 354832, 1141274], ![-95916, -162977, -4210, 71217, 233303]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [7, 10, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 22, 9], [5, 0, 14], [0, 1]]
 g := ![![[1, 17, 12], [14, 12, 4], [17, 21, 1], []], ![[3, 16, 0, 16], [8, 3, 6, 9], [12, 18], [4, 12]], ![[0, 13, 15, 5], [12, 14, 22, 14], [3, 15, 20, 14], [22, 12]]]
 h' := ![![[16, 22, 9], [17, 22, 14], [19, 5, 2], [0, 0, 1], [0, 1]], ![[5, 0, 14], [19, 2, 14], [3, 5, 22], [21, 5], [16, 22, 9]], ![[0, 1], [0, 22, 18], [16, 13, 22], [9, 18, 22], [5, 0, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 18], []]
 b := ![[], [10, 1, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [7, 10, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10337989879, 4145829312, 6683568104, 4729323176, 16506320356]
  a := ![216, 72, 220, 140, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7037630835, -11512053960, -120655576, 4729323176, 16506320356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4213, -1016, -647, -1049, -3414]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-4213, -1016, -647, -1049, -3414]] 
 ![![23, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-4213, -1016, -647, -1049, -3414], ![6408, 1337, 929, 1527, 4958], ![-9048, -1566, -1226, -2049, -6634], ![11688, 1482, 1439, 2468, 7958], ![1344, 510, 256, 396, 1299]]]
  hmulB := by decide  
  f := ![![![15253, 6400, 9175, 6439, 23070]], ![![-3253, -1367, -1956, -1372, -4916]], ![![37706, 15830, 22676, 15911, 57010]], ![![-135829, -57046, -81690, -57311, -205340]], ![![47853, 20094, 28781, 20193, 72349]]]
  g := ![![![2752, -1016, -647, -1049, -3414], ![-3968, 1337, 929, 1527, 4958], ![5263, -1566, -1226, -2049, -6634], ![-6230, 1482, 1439, 2468, 7958], ![-1073, 510, 256, 396, 1299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, -43, -2, 3, 6]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![89, -43, -2, 3, 6]] 
 ![![23, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![89, -43, -2, 3, 6], ![72, 107, 38, 52, 174], ![-432, -246, -99, -146, -484], ![1104, 420, 228, 345, 1132], ![-216, -21, -34, -55, -177]]]
  hmulB := by decide  
  f := ![![![2983, -133, 5088, 3855, 10712]], ![![3484, -155, 5942, 4502, 12510]], ![![7918, -352, 13505, 10232, 28432]], ![![44339, -1961, 75604, 57280, 159172]], ![![-14448, 639, -24636, -18665, -51867]]]
  g := ![![![40, -43, -2, 3, 6], ![-156, 107, 38, 52, 174], ![376, -246, -99, -146, -484], ![-741, 420, 228, 345, 1132], ![75, -21, -34, -55, -177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-699077, -159625, -104991, -171118, -556406]] ![![-4213, -1016, -647, -1049, -3414]]
  ![![124456121, 123895577, 44051422, 62054957, 207209984]] where
 M := ![![![124456121, 123895577, 44051422, 62054957, 207209984]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![124456121, 123895577, 44051422, 62054957, 207209984]] ![![89, -43, -2, 3, 6]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![24718177993, 18780236000, 7201419646, 10396841800, 34553723032]]]
 hmul := by decide  
 g := ![![![![1074703391, 816532000, 313105202, 452036600, 1502335784]]]]
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


lemma PB2088I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2088I0 : PrimesBelowBoundCertificateInterval O 1 23 2088 where
  m := 9
  g := ![5, 5, 5, 1, 1, 1, 2, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2088I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
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
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![2476099]
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
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I17N1, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [], [], [I17N1], [], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
