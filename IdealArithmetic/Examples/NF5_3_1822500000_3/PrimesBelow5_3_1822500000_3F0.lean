
import IdealArithmetic.Examples.NF5_3_1822500000_3.RI5_3_1822500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 81, -17, 13, 67]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-4, 81, -17, 13, 67]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-4, 81, -17, 13, 67], ![-242, -110, 49, -50, -179], ![616, 87, -82, 94, 295], ![-268, -8, 28, -35, -107], ![-146, -72, 32, -32, -109]]]
  hmulB := by decide  
  f := ![![![-285, -575, 357, 857, 894]], ![![-931, -1875, 1158, 2785, 2907]], ![![-6058, -12193, 7516, 18088, 18885]], ![![-5551, -11169, 6879, 16560, 17291]], ![![657, 1323, -817, -1965, -2051]]]
  g := ![![![-2, 81, -17, 13, 67], ![-121, -110, 49, -50, -179], ![308, 87, -82, 94, 295], ![-134, -8, 28, -35, -107], ![-73, -72, 32, -32, -109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 3, -2, 1, 5]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![11, 3, -2, 1, 5]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![11, 3, -2, 1, 5], ![-18, 3, 0, -8, -13], ![36, 19, -16, -32, -31], ![4, 24, -13, -32, -33], ![-14, -3, 3, 2, -1]]]
  hmulB := by decide  
  f := ![![![-20, -27, -3, 10, 14]], ![![-18, -32, -2, 11, 25]], ![![-78, -76, -15, 32, 7]], ![![9, -31, 6, 6, 64]], ![![-2, 22, -3, -5, -39]]]
  g := ![![![5, 3, -2, 1, 5], ![-5, 3, 0, -8, -13], ![34, 19, -16, -32, -31], ![18, 24, -13, -32, -33], ![-8, -3, 3, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-596949, -1201018, 739507, 1780396, 1859071]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-596949, -1201018, 739507, 1780396, 1859071]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-596949, -1201018, 739507, 1780396, 1859071], ![-3875492, -7797208, 4801002, 11558626, 12069397], ![-25160336, -50620767, 31168901, 75040516, 78356527], ![-23030790, -46336274, 28530795, 68689159, 71724505], ![2734352, 5501317, -3387345, -8155184, -8515558]]]
  hmulB := by decide  
  f := ![![![14, -681, 149, -118, -585]], ![![1059, 136, -135, 152, 462]], ![![-2589, -676, 431, -472, -1533]], ![![1129, -304, -50, 91, 122]], ![![640, 297, -134, 138, 490]]]
  g := ![![![-957917, -1201018, 739507, 1780396, 1859071], ![-6218956, -7797208, 4801002, 11558626, 12069397], ![-40374493, -50620767, 31168901, 75040516, 78356527], ![-36957235, -46336274, 28530795, 68689159, 71724505], ![4387782, 5501317, -3387345, -8155184, -8515558]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-4, 81, -17, 13, 67]] ![![11, 3, -2, 1, 5]]
  ![![-3000, 19, 312, -390, -1042]] where
 M := ![![![-3000, 19, 312, -390, -1042]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-3000, 19, 312, -390, -1042]] ![![11, 3, -2, 1, 5]]
  ![![-9082, -9249, 2952, -2740, -11007]] where
 M := ![![![-9082, -9249, 2952, -2740, -11007]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-9082, -9249, 2952, -2740, -11007]] ![![-596949, -1201018, 739507, 1780396, 1859071]]
  ![![-43410, -87375, 53795, 129514, 135235]] where
 M := ![![![-43410, -87375, 53795, 129514, 135235]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-43410, -87375, 53795, 129514, 135235]] ![![-596949, -1201018, 739507, 1780396, 1859071]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-3601995248870, -7246952506726, 4462191263230, 10742924051596, 11217649589420]]]
 hmul := by decide  
 g := ![![![![-1800997624435, -3623476253363, 2231095631615, 5371462025798, 5608824794710]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -14, -2, 2, -19]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![11, -14, -2, 2, -19]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![11, -14, -2, 2, -19], ![80, 24, 11, -4, 119], ![-484, -27, -100, 50, -643], ![526, 6, 136, -75, 743], ![-256, 16, -84, 50, -385]]]
  hmulB := by decide  
  f := ![![![-1119, -1622, -154, 600, 969]], ![![-892, -1296, -115, 492, 785]], ![![-2156, -3153, -228, 1278, 1979]], ![![-1280, -1884, -106, 811, 1223]], ![![-134, -192, -24, 62, 107]]]
  g := ![![![15, -14, -2, 2, -19], ![-50, 24, 11, -4, 119], ![234, -27, -100, 50, -643], ![-270, 6, 136, -75, 743], ![138, 16, -84, 50, -385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1157, -1675, -165, 610, 993]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-1157, -1675, -165, 610, 993]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1157, -1675, -165, 610, 993], ![-2752, -3980, -393, 1450, 2355], ![-6520, -9457, -928, 3442, 5625], ![-1516, -2169, -219, 793, 1259], ![1896, 2730, 272, -996, -1603]]]
  hmulB := by decide  
  f := ![![![33, 25, -11, -2, 17]], ![![-2, 24, -11, -26, -25]], ![![118, 103, -66, -122, -103]], ![![20, 81, -47, -119, -127]], ![![-13, -5, 5, 10, 10]]]
  g := ![![![510, -1675, -165, 610, 993], ![1213, -3980, -393, 1450, 2355], ![2875, -9457, -928, 3442, 5625], ![667, -2169, -219, 793, 1259], ![-835, 2730, 272, -996, -1603]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![11, -14, -2, 2, -19]] ![![11, -14, -2, 2, -19]]
  ![![5885, -728, 1892, -1122, 8212]] where
 M := ![![![5885, -728, 1892, -1122, 8212]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![5885, -728, 1892, -1122, 8212]] ![![-1157, -1675, -165, 610, 993]]
  ![![129575, -201, 38685, -22384, 195431]] where
 M := ![![![129575, -201, 38685, -22384, 195431]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![129575, -201, 38685, -22384, 195431]] ![![-1157, -1675, -165, 610, 993]]
  ![![2879997, -4664, 858766, -496718, 4340396]] where
 M := ![![![2879997, -4664, 858766, -496718, 4340396]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![2879997, -4664, 858766, -496718, 4340396]] ![![-1157, -1675, -165, 610, 993]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![63939783, -119895, 19067553, -11023848, 96389301]]]
 hmul := by decide  
 g := ![![![![21313261, -39965, 6355851, -3674616, 32129767]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2711, -235, -235, 316, 758]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![2711, -235, -235, 316, 758]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2711, -235, -235, 316, 758], ![-2400, 1005, 36, -146, 2], ![-300, -1964, 455, -368, -1762], ![1102, 755, -279, 271, 1026], ![-1616, 632, 34, -106, -37]]]
  hmulB := by decide  
  f := ![![![1507, 3035, -1871, -4502, -4702]], ![![2865, 5764, -3551, -8548, -8924]], ![![13019, 26211, -16144, -38858, -40588]], ![![11961, 24046, -14804, -35649, -37208]], ![![-1388, -2782, 1712, 4126, 4299]]]
  g := ![![![667, -235, -235, 316, 758], ![-1061, 1005, 36, -146, 2], ![1101, -1964, 455, -368, -1762], ![-231, 755, -279, 271, 1026], ![-688, 632, 34, -106, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![2711, -235, -235, 316, 758]] ![![2711, -235, -235, 316, 758]]
  ![![7107325, 305916, -814862, 982754, 2764708]] where
 M := ![![![7107325, 305916, -814862, 982754, 2764708]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![7107325, 305916, -814862, 982754, 2764708]] ![![2711, -235, -235, 316, 758]]
  ![![15393445055, 2726887899, -2210158903, 2474387466, 7729762434]] where
 M := ![![![15393445055, 2726887899, -2210158903, 2474387466, 7729762434]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![15393445055, 2726887899, -2210158903, 2474387466, 7729762434]] ![![2711, -235, -235, 316, 758]]
  ![![26085625151593, 10217187231180, -4952456104684, 5130745665712, 17820705444632]] where
 M := ![![![26085625151593, 10217187231180, -4952456104684, 5130745665712, 17820705444632]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![26085625151593, 10217187231180, -4952456104684, 5130745665712, 17820705444632]] ![![2711, -235, -235, 316, 758]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![24538438987631135, 29001173864930905, -8841244753549255, 8075289356951780, 33124344847392190]]]
 hmul := by decide  
 g := ![![![![4907687797526227, 5800234772986181, -1768248950709851, 1615057871390356, 6624868969478438]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-439, -613, -65, 226, 340]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-439, -613, -65, 226, 340]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![4, 6, 1, 0, 0], ![0, 3, 0, 1, 0], ![6, 4, 0, 0, 1]] where
  M :=![![![-439, -613, -65, 226, 340], ![-908, -1457, -114, 514, 1012], ![-3020, -3462, -527, 1372, 1108], ![222, -797, 153, 159, 1636], ![260, 1000, -30, -290, -1241]]]
  hmulB := by decide  
  f := ![![![879, 1031, -315, 288, 1180]], ![![-4144, -1165, 688, -738, -2444]], ![![-1864, -336, 269, -300, -940]], ![![-2238, -478, 339, -373, -1192]], ![![-1986, 108, 186, -242, -609]]]
  g := ![![![-317, -323, -65, 226, 340], ![-932, -909, -114, 514, 1012], ![-1080, -1264, -527, 1372, 1108], ![-1458, -1248, 153, 159, 1636], ![1118, 1002, -30, -290, -1241]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[6, 4], [6, 1]], ![[2, 3], [5, 6]]]
 h' := ![![[6, 6], [6, 2], [0, 1]], ![[0, 1], [4, 5], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![401272, -974181, 866215, 1296182, 2842430]
  a := ![-55, 82, -115, -139, -330]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2874024, -3061391, 866215, 1296182, 2842430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 14, -8, 71]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![47, 0, 14, -8, 71]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 6, 0, 1, 0], ![6, 6, 0, 0, 1]] where
  M :=![![![47, 0, 14, -8, 71], ![-300, 0, -89, 52, -451], ![1908, -5, 570, -326, 2879], ![-2346, 2, -698, 407, -3531], ![1308, -2, 390, -226, 1971]]]
  hmulB := by decide  
  f := ![![![-55, -48, -2, 14, 19]], ![![-48, -116, -13, 44, 73]], ![![-37, -43, -4, 16, 26]], ![![-55, -116, -12, 43, 70]], ![![-78, -130, -12, 46, 73]]]
  g := ![![![-55, -54, 14, -8, 71], ![349, 342, -89, 52, -451], ![-2230, -2189, 570, -326, 2879], ![2733, 2678, -698, 407, -3531], ![-1526, -1496, 390, -226, 1971]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 0, 1] where
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
 g := ![![[0, 2], [0, 1]], ![[0, 5], [0, 6]]]
 h' := ![![[0, 6], [0, 3], [0, 1]], ![[0, 1], [0, 4], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [4, 0, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60048861, -154773824, 136552662, 206640948, 446029016]
  a := ![-689, 1003, -1441, -1754, -4137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-422759835, -581541944, 136552662, 206640948, 446029016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -5, 5, 10, 10]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-13, -5, 5, 10, 10]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-13, -5, 5, 10, 10], ![-20, -53, 30, 70, 70], ![-140, -300, 187, 460, 490], ![-150, -285, 175, 417, 430], ![20, 30, -20, -50, -53]]]
  hmulB := by decide  
  f := ![![![12861, 18615, 1835, -6780, -11030]], ![![6203, 8978, 885, -3270, -5320]], ![![21398, 30970, 3053, -11280, -18350]], ![![11565, 16740, 1650, -6097, -9920]], ![![-1157, -1675, -165, 610, 993]]]
  g := ![![![-14, -5, 5, 10, 10], ![-81, -53, 30, 70, 70], ![-536, -300, 187, 460, 490], ![-490, -285, 175, 417, 430], ![59, 30, -20, -50, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-439, -613, -65, 226, 340]] ![![47, 0, 14, -8, 71]]
  ![![-46229, 97, -13787, 7968, -69707]] where
 M := ![![![-46229, 97, -13787, 7968, -69707]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-46229, 97, -13787, 7968, -69707]] ![![-13, -5, 5, 10, 10]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-60123, 14, -17864, 10486, -90419]]]
 hmul := by decide  
 g := ![![![![-8589, 2, -2552, 1498, -12917]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 119, 37, -58, 57]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![167, 119, 37, -58, 57]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![6, 2, 4, 1, 0], ![10, 2, 8, 0, 1]] where
  M :=![![![167, 119, 37, -58, 57], ![-344, 284, -133, -10, -981], ![3904, 667, 1092, -838, 4785], ![-4120, 161, -1245, 673, -6461], ![2224, -198, 684, -336, 3669]]]
  hmulB := by decide  
  f := ![![![309, 3, -33, 42, 113]], ![![-368, 70, 25, -30, -61]], ![![184, -217, 36, 30, -55]], ![![170, -59, -1, 33, 41]], ![![326, -138, 2, 52, 47]]]
  g := ![![![-5, 11, -17, -58, 57], ![866, 206, 705, -10, -981], ![-3538, -657, -3076, -838, 4785], ![5132, 1067, 4341, 673, -6461], ![-2950, -624, -2484, -336, 3669]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 6, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10, 1], [0, 0, 10], [0, 1]]
 g := ![![[4, 0, 3], [10, 7, 1], []], ![[10, 9, 3, 1], [6, 1], [5, 1]], ![[0, 10, 5, 6], [1, 0, 6, 10], [7, 1]]]
 h' := ![![[7, 10, 1], [1, 10, 5], [0, 0, 1], [0, 1]], ![[0, 0, 10], [5, 7, 10], [0, 10], [7, 10, 1]], ![[0, 1], [10, 5, 7], [4, 1, 10], [0, 0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [9, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 6, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2457552215, 7684063151, -6595733972, -10295028223, -21331124288]
  a := ![-54, 80, -113, -137, -325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24783987273, 6448760743, 18657579384, -10295028223, -21331124288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19803, 39842, -24532, -59062, -61672]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![19803, 39842, -24532, -59062, -61672]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![19803, 39842, -24532, -59062, -61672], ![128564, 258661, -159266, -383440, -400384], ![834656, 1679268, -1033981, -2489356, -2599360], ![764012, 1537136, -946466, -2278659, -2379352], ![-90708, -182498, 112370, 270536, 282491]]]
  hmulB := by decide  
  f := ![![![-1199, 6, -380, 222, -1880]], ![![397, 3, 114, -66, 584]], ![![-4858, 8, -1453, 840, -7344]], ![![5054, -4, 1494, -863, 7576]], ![![-3733, 8, -1122, 650, -5653]]]
  g := ![![![55643, 39842, -24532, -59062, -61672], ![361243, 258661, -159266, -383440, -400384], ![2345250, 1679268, -1033981, -2489356, -2599360], ![2146750, 1537136, -946466, -2278659, -2379352], ![-254875, -182498, 112370, 270536, 282491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1103, -235, 167, -184, -587]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![-1103, -235, 167, -184, -587]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-1103, -235, 167, -184, -587], ![1980, 36, -217, 266, 727], ![-2376, 455, 156, -238, -443], ![612, -279, -9, 37, -33], ![1284, 34, -140, 172, 489]]]
  hmulB := by decide  
  f := ![![![-5437, -10915, 6677, 16112, 16837]], ![![-6653, -13365, 8192, 19754, 20638]], ![![-23658, -47573, 29246, 70450, 73577]], ![![-20409, -41052, 25260, 60829, 63522]], ![![-2690, -5394, 3288, 7944, 8305]]]
  g := ![![![542, -235, 167, -184, -587], ![-458, 36, -217, 266, 727], ![-123, 455, 156, -238, -443], ![258, -279, -9, 37, -33], ![-320, 34, -140, 172, 489]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![167, 119, 37, -58, 57]] ![![19803, 39842, -24532, -59062, -61672]]
  ![![5437, 10915, -6677, -16112, -16837]] where
 M := ![![![5437, 10915, -6677, -16112, -16837]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![5437, 10915, -6677, -16112, -16837]] ![![-1103, -235, 167, -184, -587]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [8, 8, 6, 9, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 2, 11, 6], [4, 5, 4, 8, 5], [6, 7, 2, 5, 12], [5, 12, 5, 2, 3], [0, 1]]
 g := ![![[3, 3, 9, 11, 10], [4, 1], []], ![[6, 8, 12, 0, 0, 7, 9, 8], [2, 5, 4, 10], [7, 8, 11, 9, 4, 0, 11, 8]], ![[4, 0, 5, 9, 0, 7, 3, 8], [0, 4, 7, 3], [6, 5, 11, 8, 3, 11, 8, 8]], ![[4, 7, 6, 8, 6, 11, 3, 1], [3, 1, 5, 12], [12, 2, 7, 8, 7, 10, 11, 12]], ![[3, 2, 7, 4, 3, 1, 3, 3], [2, 7, 5, 4], [10, 0, 12, 5, 0, 4, 6, 1]]]
 h' := ![![[2, 1, 2, 11, 6], [7, 12, 7, 10, 7], [0, 0, 0, 1], [0, 1]], ![[4, 5, 4, 8, 5], [0, 3, 11, 6, 7], [4, 9, 5, 3, 7], [2, 1, 2, 11, 6]], ![[6, 7, 2, 5, 12], [9, 9, 11, 9, 8], [3, 9, 3, 12, 9], [4, 5, 4, 8, 5]], ![[5, 12, 5, 2, 3], [11, 10, 0, 10, 5], [3, 7, 5, 3, 8], [6, 7, 2, 5, 12]], ![[0, 1], [7, 5, 10, 4, 12], [6, 1, 0, 7, 2], [5, 12, 5, 2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 1, 0, 7], [], [], []]
 b := ![[], [9, 11, 8, 5, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [8, 8, 6, 9, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![154797720869790303916, -991516075391011525290, 802817252189846631023, 1356668473444043254950, 2508385465623207002560]
  a := ![246, -359, 514, 624, 1475]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11907516989983869532, -76270467337770117330, 61755173245372817771, 104359113341849481150, 192952728124862077120]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5051, 4751, -1557, 1458, 5790]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![5051, 4751, -1557, 1458, 5790]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![14, 2, 8, 1, 0], ![16, 5, 9, 0, 1]] where
  M :=![![![5051, 4751, -1557, 1458, 5790], ![-20244, -5113, 3236, -3510, -11454], ![38796, 1740, -4463, 5376, 15150], ![-14774, 963, 1349, -1775, -4398], ![-12740, -3392, 2074, -2238, -7355]]]
  hmulB := by decide  
  f := ![![![-29, -43, 35, 84, 66]], ![![-96, -347, 262, 546, 678]], ![![-1620, -2412, 1421, 3756, 3162]], ![![-832, -1345, 821, 2095, 1878]], ![![-924, -1405, 847, 2208, 1885]]]
  g := ![![![-6353, -1595, -3843, 1458, 5790], ![12480, 3481, 7906, -3510, -11454], ![-16404, -4986, -10813, 5376, 15150], ![4732, 1559, 3243, -1775, -4398], ![8016, 2227, 5069, -2238, -7355]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [5, 16, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 3, 4], [4, 13, 13], [0, 1]]
 g := ![![[3, 5, 9], [9, 9], [6, 1], []], ![[13, 6, 5, 15], [16, 13], [3, 16], [1, 16]], ![[12, 7, 14, 1], [12, 8], [14, 9], [9, 16]]]
 h' := ![![[2, 3, 4], [5, 6, 3], [4, 1, 3], [0, 0, 1], [0, 1]], ![[4, 13, 13], [14, 4, 12], [3, 6, 9], [16, 1, 13], [2, 3, 4]], ![[0, 1], [10, 7, 2], [6, 10, 5], [5, 16, 3], [4, 13, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 9], []]
 b := ![[], [0, 15, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [5, 16, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-569112067, 1330924690, -1184997148, -1758057692, -3910312435]
  a := ![-31, 46, -64, -76, -185]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5094629093, 1435211897, 2827780959, -1758057692, -3910312435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 43, -35, -84, -66]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![29, 43, -35, -84, -66]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![10, 4, 1, 0, 0], ![3, 4, 0, 1, 0], ![1, 13, 0, 0, 1]] where
  M :=![![![29, 43, -35, -84, -66], ![96, 347, -262, -546, -678], ![1620, 2412, -1421, -3756, -3162], ![586, 2273, -1575, -3299, -4350], ![184, -246, 260, 342, 859]]]
  hmulB := by decide  
  f := ![![![-5051, -4751, 1557, -1458, -5790]], ![![20244, 5113, -3236, 3510, 11454]], ![![-490, -1694, 417, -348, -1602]], ![![4741, 308, -566, 673, 1932]], ![![15933, 3830, -2505, 2730, 8851]]]
  g := ![![![41, 81, -35, -84, -66], ![296, 729, -262, -546, -678], ![1780, 3778, -1421, -3756, -3162], ![1799, 4607, -1575, -3299, -4350], ![-253, -813, 260, 342, 859]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [2, 1, 1] where
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
 g := ![![[9, 9], [9], [1], [1]], ![[0, 8], [9], [1], [1]]]
 h' := ![![[16, 16], [3, 3], [2, 3], [15, 16], [0, 1]], ![[0, 1], [0, 14], [16, 14], [16, 1], [16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![282634, -1098312, 926650, 1491558, 2949792]
  a := ![-56, 84, -118, -150, -336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-965196, -2889320, 926650, 1491558, 2949792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![5051, 4751, -1557, 1458, 5790]] ![![29, 43, -35, -84, -66]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -38, -4, 14, 23]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-23, -38, -4, 14, 23]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![1, 8, 15, 1, 0], ![5, 10, 13, 0, 1]] where
  M :=![![![-23, -38, -4, 14, 23], ![-64, -88, -9, 32, 53], ![-148, -213, -22, 74, 119], ![-30, -46, -6, 15, 29], ![40, 62, 6, -22, -37]]]
  hmulB := by decide  
  f := ![![![3, -2, 0, 0, -1]], ![![4, 4, -1, 0, 5]], ![![-20, -1, -2, -6, -25]], ![![-13, 1, -2, -5, -17]], ![![-11, 1, -2, -4, -15]]]
  g := ![![![-8, -20, -27, 14, 23], ![-19, -46, -62, 32, 53], ![-43, -105, -141, 74, 119], ![-10, -24, -32, 15, 29], ![13, 32, 43, -22, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [1, 12, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 11], [7, 7], [0, 1]]
 g := ![![[1, 7, 17], [7, 9, 6], [6, 1], []], ![[11, 7, 5], [4, 5, 4], [5, 11], []], ![[9, 5, 16], [3, 5, 9], [13, 7], []]]
 h' := ![![[18, 11], [12, 0, 6], [13, 3, 5], [0, 0, 1], [0, 1]], ![[7, 7], [18, 1, 4], [15, 18, 16], [1, 16, 7], [18, 11]], ![[0, 1], [2, 18, 9], [13, 17, 17], [11, 3, 11], [7, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17], []]
 b := ![[], [16, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [1, 12, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-984132883, 628893388, -772287006, -705693196, -2922903864]
  a := ![-26, 45, -55, -58, -169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![754530507, 1868604084, 2516361114, -705693196, -2922903864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-75, -151, 93, 224, 234]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-75, -151, 93, 224, 234]] 
 ![![19, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-75, -151, 93, 224, 234], ![-488, -981, 604, 1454, 1518], ![-3164, -6368, 3921, 9440, 9858], ![-2898, -5829, 3589, 8641, 9022], ![344, 692, -426, -1026, -1071]]]
  hmulB := by decide  
  f := ![![![-161, -123, -1, 30, 34]], ![![-4, -15, -2, 6, 10]], ![![-28, -32, -3, 12, 22]], ![![-6, -9, -1, 3, 2]], ![![-124, -94, 0, 22, 25]]]
  g := ![![![-201, -151, 93, 224, 234], ![-1304, -981, 604, 1454, 1518], ![-8468, -6368, 3921, 9440, 9858], ![-7750, -5829, 3589, 8641, 9022], ![920, 692, -426, -1026, -1071]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 1, 3, -4, -11]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-29, 1, 3, -4, -11]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-29, 1, 3, -4, -11], ![36, -6, -1, 2, 7], ![-24, 23, -6, 2, -11], ![12, -7, 7, -5, 15], ![12, -6, -4, 4, -9]]]
  hmulB := by decide  
  f := ![![![265, 533, -327, -788, -823]], ![![174, 350, -215, -518, -541]], ![![614, 1235, -760, -1830, -1911]], ![![592, 1191, -733, -1765, -1843]], ![![-8, -16, 10, 24, 25]]]
  g := ![![![1, 1, 3, -4, -11], ![2, -6, -1, 2, 7], ![-6, 23, -6, 2, -11], ![0, -7, 7, -5, 15], ![4, -6, -4, 4, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-23, -38, -4, 14, 23]] ![![-75, -151, 93, 224, 234]]
  ![![265, 533, -327, -788, -823]] where
 M := ![![![265, 533, -327, -788, -823]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![265, 533, -327, -788, -823]] ![![-29, 1, 3, -4, -11]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [3, 15, 8, 5, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 16, 14, 4], [3, 3, 21, 22, 1], [13, 17, 16, 2, 5], [21, 9, 18, 18, 17], [0, 1]]
 g := ![![[16, 0, 9], [10, 20, 9, 21, 6], [1], []], ![[21, 14, 21, 21, 16, 2, 16], [9, 2, 9, 15, 16, 16, 16], [14, 10, 9, 12, 15, 14, 8], [5, 16]], ![[1, 7, 18, 18, 4, 5, 1, 9], [14, 20, 15, 12, 1, 8, 8, 16], [15, 9, 9, 9, 15, 11, 2, 9], [8, 20, 10, 1]], ![[18, 21, 22, 12, 16, 5, 4, 17], [19, 15, 0, 5, 14, 10, 9, 20], [8, 7, 16, 21, 5, 6, 10, 19], [17, 15, 21, 2]], ![[22, 1, 3, 20, 5, 17, 12, 20], [1, 21, 16, 9, 18, 17, 4, 15], [18, 2, 13, 9, 6, 4, 12, 19], [18, 13, 9, 13]]]
 h' := ![![[21, 16, 14, 4], [16, 6, 5, 3], [20, 8, 15, 18, 12], [0, 0, 1], [0, 1]], ![[3, 3, 21, 22, 1], [6, 9, 21, 22, 2], [15, 0, 4, 20, 2], [12, 20, 12, 3, 5], [21, 16, 14, 4]], ![[13, 17, 16, 2, 5], [17, 6, 11, 1, 20], [9, 7, 16, 2, 4], [8, 22, 17, 20, 20], [3, 3, 21, 22, 1]], ![[21, 9, 18, 18, 17], [2, 15, 5, 19, 10], [1, 2, 13, 3, 2], [3, 4, 5, 1, 17], [13, 17, 16, 2, 5]], ![[0, 1], [17, 10, 4, 1, 14], [6, 6, 21, 3, 3], [19, 0, 11, 22, 4], [21, 9, 18, 18, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 5, 4], [], [], []]
 b := ![[], [2, 12, 20, 20, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [3, 15, 8, 5, 11, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![350609455465909, 6535058958569111, -4884272120174631, -9181308832908704, -14471778228968869]
  a := ![-22, 31, -46, -58, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15243889368083, 284132998198657, -212359657398897, -399187340561248, -629207749085603]
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



lemma PB2088I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2088I0 : PrimesBelowBoundCertificateInterval O 1 23 2088 where
  m := 9
  g := ![5, 5, 5, 3, 3, 1, 2, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2088I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![49, 49, 7]
    · exact ![1331, 11, 11]
    · exact ![371293]
    · exact ![4913, 289]
    · exact ![6859, 19, 19]
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
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
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
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I11N2, I17N1, I19N1, I19N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1, I11N2], [], [I17N1], [I19N1, I19N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
