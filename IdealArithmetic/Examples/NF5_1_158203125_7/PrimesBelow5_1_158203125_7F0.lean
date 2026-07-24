
import IdealArithmetic.Examples.NF5_1_158203125_7.RI5_1_158203125_7
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, -259, 236, -307, 69]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![179, -259, 236, -307, 69]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 1, 1, 0], ![1, 0, 1, 0, 1]] where
  M :=![![![179, -259, 236, -307, 69], ![2070, 737, -754, 1870, -614], ![-10245, -1254, 1491, -5890, 2177], ![10185, -72, -200, 3919, -1675], ![-25125, 669, 28, -8875, 3919]]]
  hmulB := by decide  
  f := ![![![318214693, 161049095, 50541678, 153105259, 56991428]], ![![854871420, 432652142, 135778256, 411311335, 153105259]], ![![3738286350, 1891954227, 593747772, 1798632535, 669517411]], ![![3909575475, 1978643997, 620953429, 1881046284, 700194850]], ![![7509792689, 3800721157, 1192771837, 3613248477, 1344984436]]]
  g := ![![![55, -259, 237, -307, 69], ![1342, 737, -1005, 1870, -614], ![-6211, -1254, 2602, -5890, 2177], ![5930, -72, -1222, 3919, -1675], ![-14522, 669, 2492, -8875, 3919]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![254593, 851089, 238786, 332843, 470517]
  a := ![3, -63, -61, -1, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-107962, 851089, -282287, 332843, 470517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2230627, -82902, 18324, 757277, -339952]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2230627, -82902, 18324, 757277, -339952]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2230627, -82902, 18324, 757277, -339952], ![-10198560, 484613, -184128, -3307900, 1514554], ![27817590, -1497023, 668741, 8766400, -4065177], ![-14748120, 973183, -525158, -4385173, 2087703], ![31315545, -2193369, 1235762, 9125620, -4385173]]]
  hmulB := by decide  
  f := ![![![1404581, 710494, 222892, 675729, 251579]], ![![3773685, 1909377, 599048, 1815125, 675729]], ![![8951383, 4530460, 1421775, 4306567, 1603050]], ![![9706198, 4912792, 1541912, 4670405, 1738431]], ![![24891913, 12598043, 3953758, 11977237, 4458330]]]
  g := ![![![897489, -82902, 18324, 757277, -339952], ![-4110543, 484613, -184128, -3307900, 1514554], ![11223813, -1497023, 668741, 8766400, -4065177], ![-5962746, 973183, -525158, -4385173, 2087703], ![12669668, -2193369, 1235762, 9125620, -4385173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6253, 487, -835, -507, 216]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![6253, 487, -835, -507, 216]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![6253, 487, -835, -507, 216], ![6480, 6150, 1809, -2015, -1014], ![-18450, 2514, 4341, 460, -1508], ![-15330, -4916, 282, 2223, 288], ![4320, -9121, -5057, 2145, 2223]]]
  hmulB := by decide  
  f := ![![![-3579346, -1811511, -568503, -1722159, -641050]], ![![-11405423, -5772312, -1811511, -5487587, -2042684]], ![![-21024510, -10640532, -3339297, -10115690, -3765428]], ![![-22951170, -11615639, -3645309, -11042688, -4110498]], ![![-63447143, -32110714, -10077236, -30526842, -11363213]]]
  g := ![![![2775, 487, -835, -507, 216], ![672, 6150, 1809, -2015, -1014], ![-9728, 2514, 4341, 460, -1508], ![-5351, -4916, 282, 2223, 288], ![5609, -9121, -5057, 2145, 2223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2

def I2N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16978, -1257, 735, 4848, -2352]] i)))

def SI2N3: IdealEqSpanCertificate' Table ![![16978, -1257, 735, 4848, -2352]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![16978, -1257, 735, 4848, -2352], ![-70560, 5431, -3249, -19845, 9696], ![180720, -14289, 8680, 50280, -24693], ![-83790, 7035, -4416, -22712, 11295], ![169425, -14556, 9243, 45435, -22712]]]
  hmulB := by decide  
  f := ![![![-27670216, -14003952, -4394829, -13313199, -4955664]], ![![-88170068, -44623049, -14003952, -42421992, -15791031]], ![![-176365613, -89258991, -28011950, -84856242, -31586625]], ![![-177424875, -89795085, -28180191, -85365893, -31776336]], ![![-490480148, -248232987, -77902404, -235988757, -87843725]]]
  g := ![![![9926, -1257, 735, 4848, -2352], ![-41219, 5431, -3249, -19845, 9696], ![105511, -14289, 8680, 50280, -24693], ![-48852, 7035, -4416, -22712, 11295], ![98725, -14556, 9243, 45435, -22712]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N3 : Nat.card (O ⧸ I2N3) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N3)

lemma isPrimeI2N3 : Ideal.IsPrime I2N3 := prime_ideal_of_norm_prime hp2.out _ NI2N3
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![179, -259, 236, -307, 69]] ![![2230627, -82902, 18324, 757277, -339952]]
  ![![16294105958, -943761295, 455283108, 5037084974, -2356004424]] where
 M := ![![![16294105958, -943761295, 455283108, 5037084974, -2356004424]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![16294105958, -943761295, 455283108, 5037084974, -2356004424]] ![![6253, 487, -835, -507, 216]]
  ![![-24953741926, 2485989928, -1686350921, -6192073879, 3216551154]] where
 M := ![![![-24953741926, 2485989928, -1686350921, -6192073879, 3216551154]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-24953741926, 2485989928, -1686350921, -6192073879, 3216551154]] ![![16978, -1257, 735, 4848, -2352]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![159964631405432, -21416825126270, 16019272980124, 31678448335550, -18557361628860]]]
 hmul := by decide  
 g := ![![![![79982315702716, -10708412563135, 8009636490062, 15839224167775, -9278680814430]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2, I2N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56547, -4144, -11606, -2336, 3832]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![56547, -4144, -11606, -2336, 3832]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![56547, -4144, -11606, -2336, 3832], ![114960, 48351, 3318, -19710, -4672], ![-127560, 49118, 45033, -5210, -17374], ![-175740, -24566, 18320, 17127, -3690], ![-55350, -91058, -33726, 27350, 17127]]]
  hmulB := by decide  
  f := ![![![-83271, -41836, -13178, -39948, -14756]], ![![-147560, -75081, -23498, -71150, -26632]], ![![-325700, -163858, -51583, -156330, -57834]], ![![-353120, -179118, -56144, -170057, -63446]], ![![-951690, -480878, -151046, -457590, -170057]]]
  g := ![![![18849, -4144, -11606, -2336, 3832], ![38320, 48351, 3318, -19710, -4672], ![-42520, 49118, 45033, -5210, -17374], ![-58580, -24566, 18320, 17127, -3690], ![-18450, -91058, -33726, 27350, 17127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127222, -13283, 9176, 30679, -16170]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![127222, -13283, 9176, 30679, -16170]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![127222, -13283, 9176, 30679, -16170], ![-485100, 51441, -35742, -115820, 61358], ![1162920, -124897, 87183, 275345, -146499], ![-452370, 50423, -35662, -104418, 56295], ![844425, -95898, 68254, 192320, -104418]]]
  hmulB := by decide  
  f := ![![![-54426, -16746, 1342, 7712, 863]], ![![-9512, -26973, -11164, 7684, 5429]], ![![36521, -5607, -8885, -737, 3118]], ![![-9919, 12807, 7762, -2774, -3324]], ![![-94774, 11123, 21432, 2813, -7340]]]
  g := ![![![31045, -13283, 9176, 30679, -16170], ![-118711, 51441, -35742, -115820, 61358], ![285253, -124897, 87183, 275345, -146499], ![-111741, 50423, -35662, -104418, 56295], ![209337, -95898, 68254, 192320, -104418]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -6, -2, -6, -2]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![-13, -6, -2, -6, -2]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-13, -6, -2, -6, -2], ![-60, -33, -10, -30, -12], ![-150, -70, -23, -70, -24], ![-150, -78, -24, -73, -28], ![-420, -208, -66, -200, -73]]]
  hmulB := by decide  
  f := ![![![9, 2, 2, 2, -2]], ![![-14, 3, 2, -2, 0]], ![![30, -6, 1, 10, -4]], ![![-7, 0, -2, -3, 2]], ![![46, 0, 2, 8, -5]]]
  g := ![![![3, -6, -2, -6, -2], ![20, -33, -10, -30, -12], ![36, -70, -23, -70, -24], ![45, -78, -24, -73, -28], ![114, -208, -66, -200, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![56547, -4144, -11606, -2336, 3832]] ![![56547, -4144, -11606, -2336, 3832]]
  ![![4400057769, -1296308900, -1364720824, 74848236, 511942020]] where
 M := ![![![4400057769, -1296308900, -1364720824, 74848236, 511942020]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![4400057769, -1296308900, -1364720824, 74848236, 511942020]] ![![56547, -4144, -11606, -2336, 3832]]
  ![![232380364027443, -196399166674604, -132720233147406, 37665448948628, 55119877133484]] where
 M := ![![![232380364027443, -196399166674604, -132720233147406, 37665448948628, 55119877133484]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![232380364027443, -196399166674604, -132720233147406, 37665448948628, 55119877133484]] ![![127222, -13283, 9176, 30679, -16170]]
  ![![1919746566, 6116558461, 2572061038, -1728141617, -1243393000]] where
 M := ![![![1919746566, 6116558461, 2572061038, -1728141617, -1243393000]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![1919746566, 6116558461, 2572061038, -1728141617, -1243393000]] ![![-13, -6, -2, -6, -2]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![3686933832, 11608857, -623144808, -226567845, 187994700]]]
 hmul := by decide  
 g := ![![![![1228977944, 3869619, -207714936, -75522615, 62664900]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13250, 1546, -1130, -2938, 1607]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-13250, 1546, -1130, -2938, 1607]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-13250, 1546, -1130, -2938, 1607], ![48210, -5929, 4222, 10420, -5876], ![-112245, 13637, -10151, -24035, 13358], ![38415, -5325, 3766, 7590, -4592], ![-68880, 8831, -7208, -13545, 7590]]]
  hmulB := by decide  
  f := ![![![-52600, -98351, -37652, 29105, 18870]], ![![113220, -26381, -31810, 88, 11642]], ![![118020, 53905, 5429, -21359, -5733]], ![![-56082, 52157, 34286, -10344, -14347]], ![![-215205, -3544, 35014, 13980, -10344]]]
  g := ![![![-2650, 1546, -1130, -2938, 1607], ![9642, -5929, 4222, 10420, -5876], ![-22449, 13637, -10151, -24035, 13358], ![7683, -5325, 3766, 7590, -4592], ![-13776, 8831, -7208, -13545, 7590]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-13250, 1546, -1130, -2938, 1607]] ![![-13250, 1546, -1130, -2938, 1607]]
  ![![153378580, -15224277, 10322578, 38131135, -19783160]] where
 M := ![![![153378580, -15224277, 10322578, 38131135, -19783160]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![153378580, -15224277, 10322578, 38131135, -19783160]] ![![-13250, 1546, -1130, -2938, 1607]]
  ![![-1097414734955, 90403639364, -56180310482, -299988179760, 148573870316]] where
 M := ![![![-1097414734955, 90403639364, -56180310482, -299988179760, 148573870316]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-1097414734955, 90403639364, -56180310482, -299988179760, 148573870316]] ![![-13250, 1546, -1130, -2938, 1607]]
  ![![3447249529097800, -89244346090024, -8626794617148, 1227160818096920, -539992454237745]] where
 M := ![![![3447249529097800, -89244346090024, -8626794617148, 1227160818096920, -539992454237745]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![3447249529097800, -89244346090024, -8626794617148, 1227160818096920, -539992454237745]] ![![-13250, 1546, -1130, -2938, 1607]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![35325851451344927620, -5562370817980721275, 4329142246184740700, 5777748207881644525, -3784772155976258550]]]
 hmul := by decide  
 g := ![![![![7065170290268985524, -1112474163596144255, 865828449236948140, 1155549641576328905, -756954431195251710]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![424546, 33356, -43212, 215990, -83189]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![424546, 33356, -43212, 215990, -83189]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![4, 6, 1, 2, 1]] where
  M :=![![![424546, 33356, -43212, 215990, -83189], ![-2495670, -44467, 109924, -1047950, 431980], ![7727535, -57961, -154391, 2958685, -1263940], ![-5039865, 214413, -67154, -1671354, 757894], ![11368410, -585145, 247990, 3621585, -1671354]]]
  hmulB := by decide  
  f := ![![![130582, -209789, -121710, 47365, 52798]], ![![1583940, -58637, -297868, -80570, 94730]], ![![628980, 730927, 239231, -230735, -127935]], ![![-1275390, 409379, 411518, -30558, -155773]], ![![823939, -7459, -144023, -47983, 44219]]]
  g := ![![![108186, 76070, 5711, 54624, -83189], ![-603370, -376621, -46008, -273130, 431980], ![1826185, 1075097, 158507, 783795, -1263940], ![-1153063, -618993, -117864, -455306, 757894], ![2579118, 1348997, 274192, 994899, -1671354]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [6, 3, 6, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2, 2], [1, 1, 6, 3], [0, 3, 6, 4], [0, 1]]
 g := ![![[0, 2, 1, 1], []], ![[1, 2, 5, 0, 4], [1, 4, 1]], ![[6, 4, 4, 1, 5, 3], [5, 4, 4, 0, 0, 6]], ![[0, 3, 6, 4, 3, 2], [2, 6, 1, 5, 2, 1]]]
 h' := ![![[0, 2, 2], [0, 0, 0, 1], [0, 1]], ![[1, 1, 6, 3], [1, 1, 4, 3], [0, 2, 2]], ![[0, 3, 6, 4], [6, 6, 4, 1], [1, 1, 6, 3]], ![[0, 1], [2, 0, 6, 2], [0, 3, 6, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 0, 2], []]
 b := ![[], [], [4, 5, 2, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [6, 3, 6, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3719891032, 2113628866, 633405340, 1871021938, 790128746]
  a := ![1, -5, -6, -1, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![79910864, -375306230, -22389058, 41537778, 790128746]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-130582, 209789, 121710, -47365, -52798]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-130582, 209789, 121710, -47365, -52798]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-130582, 209789, 121710, -47365, -52798], ![-1583940, 58637, 297868, 80570, -94730], ![-628980, -730927, -239231, 230735, 127935], ![1275390, -409379, -411518, 30558, 155773], ![2336595, 410920, -203620, -249930, 30558]]]
  hmulB := by decide  
  f := ![![![-424546, -33356, 43212, -215990, 83189]], ![![174576, -7943, 2816, 57140, -26059]], ![![-1164583, 3515, 28229, -453525, 192447]], ![![477383, -49691, 34286, 115342, -60734]], ![![-1684708, 78827, -29254, -548225, 250649]]]
  g := ![![![-91343, 209789, 121710, -47365, -52798], ![-326467, 58637, 297868, 80570, -94730], ![107451, -730927, -239231, 230735, 127935], ![376720, -409379, -411518, 30558, 155773], ![325231, 410920, -203620, -249930, 30558]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![424546, 33356, -43212, 215990, -83189]] ![![-130582, 209789, 121710, -47365, -52798]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [9, 3, 1, 6, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 1, 1, 6, 8], [4, 5, 4, 3, 9], [3, 1, 3, 2, 7], [2, 3, 3, 0, 9], [0, 1]]
 g := ![![[3, 3, 7, 5, 5], [1], []], ![[10, 3, 6, 0, 7, 8, 9, 7], [1, 10, 4, 5, 4, 4, 8, 2], [0, 9, 0, 9]], ![[8, 2, 10, 10, 7, 8, 4, 5], [5, 10, 1, 3, 6, 7, 1, 9], [4, 7, 4, 4]], ![[10, 7, 1, 6, 6, 2, 5, 2], [10, 0, 4, 1, 6, 2, 9, 8], [4, 10, 4, 5]], ![[6, 2, 4, 0, 7, 8, 4, 3], [4, 10, 4, 4, 7, 6, 0, 4], [0, 6, 5, 4]]]
 h' := ![![[6, 1, 1, 6, 8], [2, 8, 10, 5, 4], [0, 0, 1], [0, 1]], ![[4, 5, 4, 3, 9], [1, 6, 2, 3, 7], [3, 8, 8, 6, 6], [6, 1, 1, 6, 8]], ![[3, 1, 3, 2, 7], [4, 4, 5, 4, 5], [2, 9, 7, 7, 10], [4, 5, 4, 3, 9]], ![[2, 3, 3, 0, 9], [7, 4, 5, 9, 4], [6, 3, 4, 4, 3], [3, 1, 3, 2, 7]], ![[0, 1], [7, 0, 0, 1, 2], [4, 2, 2, 5, 3], [2, 3, 3, 0, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 10, 2, 6], [], [], []]
 b := ![[], [7, 5, 3, 4, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [9, 3, 1, 6, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2578647407198577, 1368843417524638, 420463303604146, 1263962853357644, 495299560733560]
  a := ![1, 22, 26, -1, 51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![234422491563507, 124440310684058, 38223936691286, 114905713941604, 45027232793960]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34353364, 3743672, -2626900, -8054674, 4307295]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-34353364, 3743672, -2626900, -8054674, 4307295]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![4, 2, 2, 7, 1]] where
  M :=![![![-34353364, 3743672, -2626900, -8054674, 4307295], ![129218850, -14327017, 10114244, 29938450, -16109348], ![-306249645, 34450299, -24441261, -70230355, 37993124], ![115021275, -13522383, 9734422, 25523536, -14049778], ![-210746670, 25359423, -18389594, -45912835, 25523536]]]
  hmulB := by decide  
  f := ![![![-8821282, -3845135, -318594, 1547987, 388132]], ![![11643960, -11362945, -7371676, 2288350, 3095974]], ![![40617630, 6190239, -3991269, -4093495, 740363]], ![![7908120, 14288655, 5424766, -4244582, -2727715]], ![![6436859, 6461423, 1965336, -2092852, -1085645]]]
  g := ![![![-3967888, -374686, -864730, -2938903, 4307295], ![14896634, 1376283, 3256380, 10977222, -16109348], ![-35247857, -3195073, -7725193, -25860171, 37993124], ![13170799, 1121321, 2910306, 9528614, -14049778], ![-24064678, -1975973, -5341282, -17275199, 25523536]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [4, 5, 12, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4, 4], [0, 1, 7, 1], [9, 7, 2, 12], [0, 1]]
 g := ![![[3, 2, 0, 1], [10, 10, 1], []], ![[12, 10, 3, 10, 12], [0, 0, 10], [5, 0, 12]], ![[1, 7, 5, 6, 3, 4], [0, 3, 4], [10, 1, 3, 6, 5, 1]], ![[3, 0, 6, 6, 1, 12], [11, 12, 10], [8, 2, 9, 7, 9, 12]]]
 h' := ![![[1, 4, 4], [12, 1, 8, 1], [0, 0, 0, 1], [0, 1]], ![[0, 1, 7, 1], [10, 0, 3, 9], [7, 0, 4, 7], [1, 4, 4]], ![[9, 7, 2, 12], [1, 5, 0, 2], [12, 11, 6, 11], [0, 1, 7, 1]], ![[0, 1], [7, 7, 2, 1], [8, 2, 3, 7], [9, 7, 2, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 7, 6], []]
 b := ![[], [], [6, 12, 4, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [4, 5, 12, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2622391704, 1893714997, 524095980, 1457410277, 775934441]
  a := ![-1, -2, -6, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37026620, 26295855, -79059454, -305702370, 775934441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8821282, -3845135, -318594, 1547987, 388132]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-8821282, -3845135, -318594, 1547987, 388132]] 
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-8821282, -3845135, -318594, 1547987, 388132], ![11643960, -11362945, -7371676, 2288350, 3095974], ![40617630, 6190239, -3991269, -4093495, 740363], ![7908120, 14288655, 5424766, -4244582, -2727715], ![-40915725, 9703866, 11576272, -76660, -4244582]]]
  hmulB := by decide  
  f := ![![![-34353364, 3743672, -2626900, -8054674, 4307295]], ![![-21770886, 2353619, -1646812, -5132126, 2736784]], ![![-23557665, 2650023, -1880097, -5402335, 2922548]], ![![920091, -176259, 142594, 104578, -86761]], ![![-37351814, 4254523, -3031138, -8488479, 4613992]]]
  g := ![![![2274717, -3845135, -318594, 1547987, 388132], ![8951266, -11362945, -7371676, 2288350, 3095974], ![-2100589, 6190239, -3991269, -4093495, 740363], ![-9923098, 14288655, 5424766, -4244582, -2727715], ![-9475037, 9703866, 11576272, -76660, -4244582]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-34353364, 3743672, -2626900, -8054674, 4307295]] ![![-8821282, -3845135, -318594, 1547987, 388132]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -10, -4, -12, -3]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-28, -10, -4, -12, -3]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![14, 3, 7, 1, 0], ![10, 14, 13, 0, 1]] where
  M :=![![![-28, -10, -4, -12, -3], ![-90, -61, -16, -50, -24], ![-315, -121, -45, -135, -38], ![-255, -143, -42, -128, -52], ![-780, -371, -122, -365, -128]]]
  hmulB := by decide  
  f := ![![![16, -1, -2, 1, 0]], ![![0, 11, 0, -10, 2]], ![![30, 5, 11, 15, -11]], ![![22, 3, 3, 5, -4]], ![![35, 11, 7, 5, -7]]]
  g := ![![![10, 4, 7, -12, -3], ![50, 25, 38, -50, -24], ![115, 48, 82, -135, -38], ![121, 57, 90, -128, -52], ![330, 148, 241, -365, -128]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [3, 1, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 0, 6], [8, 16, 11], [0, 1]]
 g := ![![[6, 9, 15], [4, 9], [7, 1], []], ![[10, 7, 9, 7], [8, 2], [13, 1], [14, 2]], ![[12, 13, 16, 3], [7, 13], [], [9, 2]]]
 h' := ![![[16, 0, 6], [4, 15, 7], [13, 7, 14], [0, 0, 1], [0, 1]], ![[8, 16, 11], [8, 13, 15], [10, 9, 11], [10, 14, 16], [16, 0, 6]], ![[0, 1], [9, 6, 12], [9, 1, 9], [3, 3], [8, 16, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 14], []]
 b := ![[], [0, 14, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [3, 1, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3257397, -1635326, -509842, -1560210, -582406]
  a := ![0, -6, -2, -10, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1435859, 658764, 1057818, -1560210, -582406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, -1, -2, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![16, -1, -2, 1, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![10, 0, 1, 0, 0], ![2, 16, 0, 1, 0], ![10, 9, 0, 0, 1]] where
  M :=![![![16, -1, -2, 1, 0], ![0, 11, 0, -10, 2], ![30, 5, 11, 15, -11], ![-60, -3, 2, -4, 3], ![45, -22, -4, 20, -4]]]
  hmulB := by decide  
  f := ![![![-28, -10, -4, -12, -3]], ![![-90, -61, -16, -50, -24]], ![![-35, -13, -5, -15, -4]], ![![-103, -67, -18, -56, -26]], ![![-110, -60, -18, -55, -22]]]
  g := ![![![2, -1, -2, 1, 0], ![0, 9, 0, -10, 2], ![0, -8, 11, 15, -11], ![-6, 2, 2, -4, 3], ![5, -18, -4, 20, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16], [0, 1]]
 g := ![![[10, 1], [2], [15], [1]], ![[0, 16], [2], [15], [1]]]
 h' := ![![[7, 16], [7, 16], [3, 6], [16, 7], [0, 1]], ![[0, 1], [0, 1], [11, 11], [14, 10], [7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [13, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1230, 8191, 2190, 1931, 4655]
  a := ![13, -3, -6, 1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4326, -3800, 2190, 1931, 4655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-28, -10, -4, -12, -3]] ![![16, -1, -2, 1, 0]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [16, 6, 12, 7, 17, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 13, 11, 0, 17], [0, 0, 1, 15, 10], [10, 5, 15, 15, 9], [3, 0, 11, 8, 2], [0, 1]]
 g := ![![[9, 8, 5, 17, 5], [3, 6, 16, 2, 1], [], []], ![[2, 16, 6, 1, 14, 7, 5, 6], [15, 16, 8, 5, 4, 8, 11, 11], [17, 12, 11, 16], [17, 1, 8, 4]], ![[16, 2, 3, 3, 13, 1, 17, 13], [13, 9, 8, 0, 15, 12, 2, 12], [17, 14, 7, 1], [11, 13, 6, 5]], ![[14, 8, 3, 2, 14, 4, 7, 1], [11, 1, 10, 13, 11, 4, 0, 16], [9, 18, 1, 1], [9, 13, 14, 5]], ![[0, 13, 1, 5, 16, 7, 1, 18], [13, 5, 15, 11, 5, 15, 12, 18], [11, 7, 6, 16], [16, 8, 2, 4]]]
 h' := ![![[8, 13, 11, 0, 17], [9, 0, 14, 7, 10], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 0, 1, 15, 10], [17, 17, 3, 4, 4], [14, 0, 5, 1, 17], [1, 14, 7, 5, 15], [8, 13, 11, 0, 17]], ![[10, 5, 15, 15, 9], [1, 6, 4, 0, 8], [0, 1, 7, 4, 9], [14, 11, 17, 12, 1], [0, 0, 1, 15, 10]], ![[3, 0, 11, 8, 2], [13, 1, 1, 9, 13], [6, 6, 14, 6, 14], [13, 9, 10, 10, 18], [10, 5, 15, 15, 9]], ![[0, 1], [0, 14, 16, 18, 3], [14, 12, 12, 8, 16], [0, 4, 3, 11, 4], [3, 0, 11, 8, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 10, 18, 7], [], [], []]
 b := ![[], [8, 14, 7, 2, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [16, 6, 12, 7, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28520159, -14437872, -4530360, -13723605, -5109765]
  a := ![-1, -2, 0, -1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1501061, -759888, -238440, -722295, -268935]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-627590816, -317624972, -99679536, -301957944, -112399891]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-627590816, -317624972, -99679536, -301957944, -112399891]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![22, 12, 19, 8, 1]] where
  M :=![![![-627590816, -317624972, -99679536, -301957944, -112399891], ![-3371996730, -1706574315, -535570408, -1622396590, -603915888], ![-7372739955, -3731358493, -1171003907, -3547307165, -1320438646], ![-8048381175, -4073301871, -1278315234, -3872383996, -1441444240], ![-21621663600, -10942767357, -3434144254, -10403009285, -3872383996]]]
  hmulB := by decide  
  f := ![![![-28, 71, -26, 7, -4]], ![![-120, -29, 168, -170, 14]], ![![270, 143, -197, 575, -177]], ![![-960, -133, -10, -368, 189]], ![![-77, 121, -109, 305, -93]]]
  g := ![![![80226382, 44833640, 88518191, 25967008, -112399891], ![431050122, 240887667, 475601368, 139518718, -603915888], ![942474359, 526691533, 1039883929, 305052261, -1320438646], ![1028843135, 574957783, 1135179362, 333007388, -1441444240], ![2763947144, 1544601765, 3049615290, 894611421, -3872383996]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [9, 14, 1, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10, 14, 20], [20, 15, 18, 20], [9, 20, 14, 6], [0, 1]]
 g := ![![[5, 21, 14, 4], [20, 8, 13, 4], [7, 1], []], ![[11, 6, 0, 6, 4, 20], [14, 7, 1, 10, 1, 19], [9, 11, 3, 10, 0, 7], [3, 2, 9]], ![[9, 2, 9, 5, 6, 19], [14, 19, 3, 12, 10, 5], [13, 0, 22, 18, 21, 15], [2, 1, 9]], ![[1, 13, 13, 0, 13, 1], [3, 4, 15, 18, 17, 9], [12, 6, 11, 13, 11, 3], [5, 6, 13]]]
 h' := ![![[1, 10, 14, 20], [4, 6, 8, 2], [6, 8, 2, 2], [0, 0, 1], [0, 1]], ![[20, 15, 18, 20], [21, 6, 21, 22], [20, 13, 22, 3], [20, 6, 16, 6], [1, 10, 14, 20]], ![[9, 20, 14, 6], [4, 7, 21, 20], [8, 17, 6, 12], [14, 11, 20, 8], [20, 15, 18, 20]], ![[0, 1], [22, 4, 19, 2], [10, 8, 16, 6], [13, 6, 9, 9], [9, 20, 14, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 9, 15], []]
 b := ![[], [], [13, 13, 21, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [9, 14, 1, 16, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2134280673, 2533764101, 630891874, 1514532705, 1180031931]
  a := ![3, 3, 10, -4, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1035931383, -505505177, -947378905, -344596641, 1180031931]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, 71, -26, 7, -4]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-28, 71, -26, 7, -4]] 
 ![![23, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-28, 71, -26, 7, -4], ![-120, -29, 168, -170, 14], ![270, 143, -197, 575, -177], ![-960, -133, -10, -368, 189], ![2835, -84, -128, 920, -368]]]
  hmulB := by decide  
  f := ![![![-627590816, -317624972, -99679536, -301957944, -112399891]], ![![-337614454, -170867353, -53622920, -162439226, -60465875]], ![![-811711941, -410809043, -128923285, -390545659, -145375508]], ![![-813801089, -411866365, -129255102, -391550828, -145749669]], ![![-1513090032, -765777903, -240322370, -728005483, -270990509]]]
  g := ![![![-4, 71, -26, 7, -4], ![-15, -29, 168, -170, 14], ![-141, 143, -197, 575, -177], ![106, -133, -10, -368, 189], ![-95, -84, -128, 920, -368]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-627590816, -317624972, -99679536, -301957944, -112399891]] ![![-28, 71, -26, 7, -4]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB784I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB784I0 : PrimesBelowBoundCertificateInterval O 1 23 784 where
  m := 9
  g := ![4, 5, 5, 2, 1, 2, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB784I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2, I2N3]
    · exact ![I3N0, I3N0, I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
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
    · exact ![4, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![161051]
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![2476099]
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
      exact NI2N2
      exact NI2N3
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
      exact NI7N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I2N3, I3N0, I3N1, I3N2, I5N0, I7N1, I13N1, I17N1, I23N1]
  Il := ![[I2N0, I2N1, I2N2, I2N3], [I3N0, I3N0, I3N0, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [I17N1], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
