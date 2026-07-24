
import IdealArithmetic.Examples.NF5_1_48600000_4.RI5_1_48600000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -3, 1, 2, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, -3, 1, 2, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, -3, 1, 2, 1], ![6, -13, 4, 8, 4], ![24, -54, 15, 32, 16], ![96, -216, 58, 127, 64], ![180, -405, 108, 237, 119]]]
  hmulB := by decide  
  f := ![![![1, 6, -5, -1, 1]], ![![3, -7, 5, 1, -1]], ![![-6, 18, -11, -2, 2]], ![![12, -36, 26, 3, -4]], ![![-9, 27, -21, 0, 2]]]
  g := ![![![1, -3, 1, 2, 1], ![3, -13, 4, 8, 4], ![12, -54, 15, 32, 16], ![48, -216, 58, 127, 64], ![90, -405, 108, 237, 119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![943, -2749, 1741, 397, -363]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![943, -2749, 1741, 397, -363]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![943, -2749, 1741, 397, -363], ![-2178, 6388, -4167, -800, 794], ![4764, -14088, 9558, 1391, -1600], ![-9600, 28764, -20697, -1642, 2782], ![5964, -18621, 15737, -1307, -842]]]
  hmulB := by decide  
  f := ![![![1328, -2989, 858, 1791, 896]], ![![2688, -6056, 1641, 3565, 1791]], ![![10746, -24177, 6464, 14178, 7130]], ![![42780, -96204, 25651, 56374, 28356]], ![![80359, -180686, 48172, 105878, 53257]]]
  g := ![![![653, -2749, 1741, 397, -363], ![-1486, 6388, -4167, -800, 794], ![3182, -14088, 9558, 1391, -1600], ![-6191, 28764, -20697, -1642, 2782], ![3403, -18621, 15737, -1307, -842]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -76, 58, 1, -6]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![25, -76, 58, 1, -6]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![25, -76, 58, 1, -6], ![-36, 115, -105, 16, 2], ![12, -66, 141, -91, 32], ![192, -468, 3, 365, -182], ![-552, 1494, -577, -590, 349]]]
  hmulB := by decide  
  f := ![![![662, -1054, -657, 39, 98]], ![![625, -931, -591, 34, 88]], ![![565, -818, -523, 30, 78]], ![![505, -728, -464, 28, 70]], ![![277, -452, -275, 20, 43]]]
  g := ![![![24, -76, 58, 1, -6], ![-32, 115, -105, 16, 2], ![-2, -66, 141, -91, 32], ![237, -468, 3, 365, -182], ![-614, 1494, -577, -590, 349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, -3, 1, 2, 1]] ![![943, -2749, 1741, 397, -363]]
  ![![-52, 157, -116, -6, 14]] where
 M := ![![![-52, 157, -116, -6, 14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-52, 157, -116, -6, 14]] ![![943, -2749, 1741, 397, -363]]
  ![![-802510, 2346794, -1508979, -316046, 300654]] where
 M := ![![![-802510, 2346794, -1508979, -316046, 300654]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-802510, 2346794, -1508979, -316046, 300654]] ![![25, -76, 58, 1, -6]]
  ![![-349296922, 1027551288, -680150485, -118679367, 123669938]] where
 M := ![![![-349296922, 1027551288, -680150485, -118679367, 123669938]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-349296922, 1027551288, -680150485, -118679367, 123669938]] ![![25, -76, 58, 1, -6]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-144938319478, 429909727330, -295766917428, -38298014554, 47146521744]]]
 hmul := by decide  
 g := ![![![![-72469159739, 214954863665, -147883458714, -19149007277, 23573260872]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 11, 28, 13, 4]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-9, 11, 28, 13, 4]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-9, 11, 28, 13, 4], ![24, -69, 44, 56, 26], ![156, -366, 117, 226, 112], ![672, -1524, 420, 901, 452], ![1278, -2871, 760, 1679, 845]]]
  hmulB := by decide  
  f := ![![![81, -239, 164, 21, -26]], ![![-52, 157, -116, -6, 14]], ![![84, -262, 221, -18, -12]], ![![-72, 264, -340, 137, -36]], ![![-150, 365, 0, -287, 143]]]
  g := ![![![-3, 11, 28, 13, 4], ![8, -69, 44, 56, 26], ![52, -366, 117, 226, 112], ![224, -1524, 420, 901, 452], ![426, -2871, 760, 1679, 845]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -123, -66, 5, 10]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![37, -123, -66, 5, 10]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![37, -123, -66, 5, 10], ![60, -113, -68, 4, 10], ![60, -90, -59, 2, 8], ![48, -60, -48, -3, 4], ![-18, 39, 8, -11, -7]]]
  hmulB := by decide  
  f := ![![![27, -81, 58, 5, -8]], ![![2, -5, 0, 4, -2]], ![![38, -120, 105, -12, -4]], ![![26, -54, -36, 79, -36]], ![![-102, 267, -72, -137, 75]]]
  g := ![![![135, -123, -66, 5, 10], ![138, -113, -68, 4, 10], ![118, -90, -59, 2, 8], ![90, -60, -48, -3, 4], ![-30, 39, 8, -11, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-9, 11, 28, 13, 4]] ![![-9, 11, 28, 13, 4]]
  ![![18561, -42402, 12008, 25256, 12642]] where
 M := ![![![18561, -42402, 12008, 25256, 12642]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![18561, -42402, 12008, 25256, 12642]] ![![37, -123, -66, 5, 10]]
  ![![-152151, 405381, -161314, -267617, -129816]] where
 M := ![![![-152151, 405381, -161314, -267617, -129816]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-152151, 405381, -161314, -267617, -129816]] ![![37, -123, -66, 5, 10]]
  ![![-1494495, -1581024, 3800672, 2768968, 1080032]] where
 M := ![![![-1494495, -1581024, 3800672, 2768968, 1080032]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-1494495, -1581024, 3800672, 2768968, 1080032]] ![![37, -123, -66, 5, 10]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![191352453, -103598715, -142363554, -26382483, 3165834]]]
 hmul := by decide  
 g := ![![![![63784151, -34532905, -47454518, -8794161, 1055278]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -38, -12, 2, 2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-19, -38, -12, 2, 2]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-19, -38, -12, 2, 2], ![12, -49, -26, 2, 4], ![24, -48, -27, 2, 4], ![24, -36, -26, 1, 4], ![0, 6, 6, 0, -1]]]
  hmulB := by decide  
  f := ![![![1, -2, 0, 2, 2]], ![![3, -7, 2, 4, 2]], ![![5, -10, 1, 8, 6]], ![![34, -80, 26, 41, 16]], ![![44, -94, 18, 64, 39]]]
  g := ![![![19, -38, -12, 2, 2], ![33, -49, -26, 2, 4], ![35, -48, -27, 2, 4], ![28, -36, -26, 1, 4], ![-4, 6, 6, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-19, -38, -12, 2, 2]] ![![-19, -38, -12, 2, 2]]
  ![![-335, 3100, 1500, -136, -232]] where
 M := ![![![-335, 3100, 1500, -136, -232]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-335, 3100, 1500, -136, -232]] ![![-19, -38, -12, 2, 2]]
  ![![76301, -207666, -114936, 8394, 17418]] where
 M := ![![![76301, -207666, -114936, 8394, 17418]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![76301, -207666, -114936, 8394, 17418]] ![![-19, -38, -12, 2, 2]]
  ![![-6498719, 12595448, 7473240, -484208, -1121648]] where
 M := ![![![-6498719, 12595448, 7473240, -484208, -1121648]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-6498719, 12595448, 7473240, -484208, -1121648]] ![![-19, -38, -12, 2, 2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![442357805, -718239550, -445414980, 26655730, 66462130]]]
 hmul := by decide  
 g := ![![![![88471561, -143647910, -89082996, 5331146, 13292426]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [2, 6, 3, 5, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 3, 6, 5, 2], [4, 2, 3, 0, 5], [5, 6, 1, 2, 4], [1, 2, 4, 0, 3], [0, 1]]
 g := ![![[6, 5, 1], []], ![[0, 3, 4, 2, 6, 2, 2, 2], [6, 4, 3, 0, 5, 3, 2, 1]], ![[3, 5, 6, 3, 1, 3, 4, 5], [1, 5, 1, 0, 6, 2, 2, 6]], ![[2, 2, 5, 0, 1, 2, 3, 2], [6, 2, 3, 3, 2, 1, 3, 1]], ![[1, 5, 2, 5, 0, 5], [6, 2, 5, 3, 4, 4, 2, 6]]]
 h' := ![![[2, 3, 6, 5, 2], [0, 0, 0, 1], [0, 1]], ![[4, 2, 3, 0, 5], [3, 6, 1, 5, 6], [2, 3, 6, 5, 2]], ![[5, 6, 1, 2, 4], [6, 3, 3, 0, 6], [4, 2, 3, 0, 5]], ![[1, 2, 4, 0, 3], [1, 4, 5, 3, 2], [5, 6, 1, 2, 4]], ![[0, 1], [3, 1, 5, 5], [1, 2, 4, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 0, 4, 1], [], [], []]
 b := ![[], [3, 1, 2, 0, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [2, 6, 3, 5, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1030938695752, 2317633434438, -616693100170, -1358859718083, -683542165663]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-147276956536, 331090490634, -88099014310, -194122816869, -97648880809]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [5, 9, 5, 4, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1, 2, 7], [3, 6, 6, 6, 5], [2, 8, 7, 2, 3], [6, 6, 7, 7, 3], [0, 1]]
 g := ![![[0, 7, 5], [1], []], ![[6, 8, 10, 2, 3, 3, 8], [9, 10, 1, 9, 10, 3, 6], [6, 5]], ![[9, 3, 5, 1, 9, 5, 10, 9], [10, 1, 8, 6, 7, 4, 2, 1], [9, 7, 5, 3]], ![[3, 4, 9, 9, 5, 0, 7, 9], [10, 5, 6, 8, 0, 4], [5, 10, 1, 9]], ![[7, 8, 6, 1, 0, 10, 8, 3], [3, 6, 6, 5, 10, 4, 4, 3], [9, 0, 9, 9]]]
 h' := ![![[0, 1, 2, 7], [6, 2, 6, 7], [0, 0, 1], [0, 1]], ![[3, 6, 6, 6, 5], [10, 10, 9, 9, 8], [3, 9, 3, 10, 9], [0, 1, 2, 7]], ![[2, 8, 7, 2, 3], [10, 2, 0, 4, 9], [8, 8, 5, 10, 3], [3, 6, 6, 6, 5]], ![[6, 6, 7, 7, 3], [7, 4, 1, 4, 6], [1, 3, 5, 7], [2, 8, 7, 2, 3]], ![[0, 1], [9, 4, 6, 9, 10], [2, 2, 8, 6, 10], [6, 6, 7, 7, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 8, 5], [], [], []]
 b := ![[], [6, 1, 1, 4, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [5, 9, 5, 4, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-168191595550, 478131514212, -262808729040, -110063612901, 79806190497]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15290145050, 43466501292, -23891702640, -10005782991, 7255108227]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-229, 113, 113, -2, -16]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-229, 113, 113, -2, -16]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![11, 8, 4, 1, 0], ![4, 9, 3, 0, 1]] where
  M :=![![![-229, 113, 113, -2, -16], ![-96, 11, 31, 1, -4], ![-24, -36, -8, 3, 2], ![12, -54, -23, 6, 6], ![30, -21, -5, 8, 5]]]
  hmulB := by decide  
  f := ![![![-13, 37, -21, -8, 6]], ![![36, -103, 59, 21, -16]], ![![-96, 276, -162, -53, 42]], ![![1, -3, 2, 0, 0]], ![![-22, 64, -40, -10, 9]]]
  g := ![![![-11, 21, 13, -2, -16], ![-7, 3, 3, 1, -4], ![-5, -6, -2, 3, 2], ![-6, -12, -5, 6, 6], ![-6, -10, -4, 8, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [9, 2, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 5], [7, 6, 8], [0, 1]]
 g := ![![[0, 7, 3], [3, 10], [1]], ![[5, 9, 9, 5], [7, 10], [8, 10, 12, 8]], ![[7, 2, 1, 7], [], [3, 3, 4, 5]]]
 h' := ![![[0, 6, 5], [2, 5, 9], [4, 11, 7], [0, 1]], ![[7, 6, 8], [12, 2, 1], [6, 11, 6], [0, 6, 5]], ![[0, 1], [3, 6, 3], [4, 4], [7, 6, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4], []]
 b := ![[], [2, 11, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [9, 2, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-204570, 459231, -121043, -270577, -136576]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![255237, 296387, 105461, -270577, -136576]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -37, 21, 8, -6]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, -37, 21, 8, -6]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![6, 9, 1, 0, 0], ![11, 3, 0, 1, 0], ![1, 7, 0, 0, 1]] where
  M :=![![![13, -37, 21, 8, -6], ![-36, 103, -59, -21, 16], ![96, -276, 162, 53, -42], ![-252, 726, -433, -132, 106], ![270, -783, 481, 128, -111]]]
  hmulB := by decide  
  f := ![![![229, -113, -113, 2, 16]], ![![96, -11, -31, -1, 4]], ![![174, -57, -73, 0, 10]], ![![215, -94, -101, 1, 14]], ![![67, -13, -25, -1, 3]]]
  g := ![![![-15, -16, 21, 8, -6], ![41, 45, -59, -21, 16], ![-109, -123, 162, 53, -42], ![284, 329, -433, -132, 106], ![-301, -363, 481, 128, -111]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[9, 12], [3], [9, 1]], ![[0, 1], [3], [5, 12]]]
 h' := ![![[9, 12], [6, 8], [9, 4], [0, 1]], ![[0, 1], [0, 5], [6, 9], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [5, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [12, 4, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1811, -2112, -1503, 4495, 4739]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3335, -2711, -1503, 4495, 4739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-229, 113, 113, -2, -16]] ![![13, -37, 21, 8, -6]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [5, 4, 1, 14, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 2, 2, 16, 13], [0, 4, 0, 8, 15], [11, 10, 1, 16, 11], [8, 0, 14, 11, 12], [0, 1]]
 g := ![![[8, 12, 16, 6, 8], [13, 2, 13, 1], [], []], ![[9, 14, 3, 2, 15, 0, 2, 16], [1, 13, 16, 2], [9, 8, 14, 15], [9, 2, 12, 16]], ![[8, 2, 10, 10, 0, 4, 1, 4], [2, 4, 12, 13], [16, 12, 6, 16], [5, 13, 3, 4]], ![[8, 1, 5, 7, 1, 0, 7, 11], [8, 15, 10, 15], [1, 1, 10, 8], [6, 13, 4, 2]], ![[10, 8, 14, 11, 4, 13, 12, 3], [11, 0, 10, 8], [9, 8, 9, 2], [13, 12, 11, 8]]]
 h' := ![![[11, 2, 2, 16, 13], [3, 6, 16, 14, 5], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 4, 0, 8, 15], [16, 9, 16, 10, 9], [2, 11, 7, 2, 6], [8, 15, 5, 2, 10], [11, 2, 2, 16, 13]], ![[11, 10, 1, 16, 11], [8, 13, 4, 3, 10], [1, 12, 3, 4, 8], [9, 0, 12, 4, 13], [0, 4, 0, 8, 15]], ![[8, 0, 14, 11, 12], [3, 1, 6, 7, 1], [14, 16, 5, 5, 7], [6, 12, 10, 11, 5], [11, 10, 1, 16, 11]], ![[0, 1], [11, 5, 9, 0, 9], [7, 12, 2, 6, 12], [16, 7, 6, 0, 6], [8, 0, 14, 11, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 6, 4], [], [], []]
 b := ![[], [10, 8, 1, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [5, 4, 1, 14, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5827995857835, 13044923030928, -3369902133182, -7767086312516, -3939531179740]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-342823285755, 767348413584, -198229537246, -456887430148, -231737128220]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![473, -1399, 951, 136, -158]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![473, -1399, 951, 136, -158]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![13, 2, 3, 9, 1]] where
  M :=![![![473, -1399, 951, 136, -158], ![-948, 2843, -2053, -155, 272], ![1632, -5028, 4048, -149, -310], ![-1860, 6282, -6727, 1878, -298], ![-1710, 3819, 1311, -4332, 2033]]]
  hmulB := by decide  
  f := ![![![-625, 931, 591, -34, -88]], ![![-528, 695, 457, -25, -68]], ![![-408, 492, 330, -19, -50]], ![![-300, 342, 223, -20, -38]], ![![-685, 944, 605, -39, -93]]]
  g := ![![![133, -57, 75, 82, -158], ![-236, 121, -151, -137, 272], ![298, -232, 262, 139, -310], ![106, 362, -307, 240, -298], ![-1481, -13, -252, -1191, 2033]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [6, 17, 10, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 17, 18, 1], [7, 6, 16, 9], [6, 14, 4, 9], [0, 1]]
 g := ![![[8, 0, 6, 16], [3, 18, 5, 9], [1], []], ![[9, 13, 6, 0, 6, 4], [3, 6, 14, 18, 13, 6], [10, 6, 9], [9, 1, 1]], ![[0, 3, 15, 10, 3, 9], [15, 9, 1, 9, 8, 9], [0, 7, 4], [7, 18, 5]], ![[1, 2, 10, 14, 7, 5], [14, 16, 4, 18, 5, 5], [7, 10, 1], [4, 11, 5]]]
 h' := ![![[9, 17, 18, 1], [1, 10, 9, 4], [13, 2, 9, 3], [0, 0, 1], [0, 1]], ![[7, 6, 16, 9], [12, 18, 10, 17], [4, 18, 17, 14], [8, 14, 6, 3], [9, 17, 18, 1]], ![[6, 14, 4, 9], [16, 15, 2, 1], [11, 8, 3, 18], [7, 9, 6, 17], [7, 6, 16, 9]], ![[0, 1], [1, 14, 17, 16], [7, 10, 9, 3], [12, 15, 6, 18], [6, 14, 4, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 8, 10], []]
 b := ![[], [], [6, 5, 7, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [6, 17, 10, 16, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2119803498, 6104337120, -3620097596, -1130795170, 910269566]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-734384624, 225463052, -334258226, -490695856, 910269566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![625, -931, -591, 34, 88]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![625, -931, -591, 34, 88]] 
 ![![19, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![625, -931, -591, 34, 88], ![528, -695, -457, 25, 68], ![408, -492, -330, 19, 50], ![300, -342, -223, 20, 38], ![-90, 111, 99, 12, -5]]]
  hmulB := by decide  
  f := ![![![-473, 1399, -951, -136, 158]], ![![25, -76, 58, 1, -6]], ![![-534, 1590, -1114, -121, 166]], ![![73, -257, 304, -106, 24]], ![![90, -201, -69, 228, -107]]]
  g := ![![![640, -931, -591, 34, 88], ![496, -695, -457, 25, 68], ![359, -492, -330, 19, 50], ![244, -342, -223, 20, 38], ![-105, 111, 99, 12, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![473, -1399, 951, 136, -158]] ![![625, -931, -591, 34, 88]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 5, 12, -7, 2]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-5, 5, 12, -7, 2]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![9, 14, 6, 8, 1]] where
  M :=![![![-5, 5, 12, -7, 2], ![12, -35, 8, 26, -14], ![-84, 222, -79, -90, 52], ![312, -864, 392, 285, -180], ![-498, 1395, -700, -389, 259]]]
  hmulB := by decide  
  f := ![![![41, -37, -28, 1, 4]], ![![24, -19, -16, 0, 2]], ![![12, -6, -9, -2, 0]], ![![0, 12, -8, -9, -4]], ![![33, -22, -26, -4, 1]]]
  g := ![![![-1, -1, 0, -1, 2], ![6, 7, 4, 6, -14], ![-24, -22, -17, -22, 52], ![84, 72, 64, 75, -180], ![-123, -97, -98, -107, 259]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [13, 12, 3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 11, 14, 6], [21, 11, 15, 19], [18, 0, 17, 21], [0, 1]]
 g := ![![[12, 22, 16, 12], [14, 14, 9, 1], [21, 1], []], ![[0, 0, 6, 4, 1, 1], [6, 4, 22, 15, 14, 13], [4, 6, 7, 4, 21, 9], [5, 4, 13]], ![[9, 19, 19, 2, 8, 19], [16, 11, 2, 5, 0, 5], [13, 7, 10, 15, 6, 20], [2, 9, 16]], ![[8, 9, 10, 10, 20, 20], [8, 2, 18, 20, 19, 22], [3, 9, 5, 20, 9, 22], [15, 16, 4]]]
 h' := ![![[5, 11, 14, 6], [2, 4, 15, 9], [3, 11, 17, 1], [0, 0, 1], [0, 1]], ![[21, 11, 15, 19], [8, 6, 7, 21], [13, 12, 8, 12], [6, 21, 6, 6], [5, 11, 14, 6]], ![[18, 0, 17, 21], [6, 18, 1, 22], [13, 21, 0, 19], [1, 22, 15, 8], [21, 11, 15, 19]], ![[0, 1], [19, 18, 0, 17], [16, 2, 21, 14], [14, 3, 1, 9], [18, 0, 17, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 20, 4], []]
 b := ![[], [], [5, 15, 5, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [13, 12, 3, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2348573839, -5205785248, 1265571750, 3195809572, 1671812564]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-552075619, -1243963528, -381100158, -442551780, 1671812564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 37, 28, -1, -4]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-41, 37, 28, -1, -4]] 
 ![![23, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-41, 37, 28, -1, -4], ![-24, 19, 16, 0, -2], ![-12, 6, 9, 2, 0], ![0, -12, 8, 9, 4], ![18, -33, 4, 17, 9]]]
  hmulB := by decide  
  f := ![![![5, -5, -12, 7, -2]], ![![1, 0, -4, 1, 0]], ![![8, -14, -7, 10, -4]], ![![-9, 33, -28, -6, 6]], ![![26, -65, 20, 23, -13]]]
  g := ![![![-33, 37, 28, -1, -4], ![-19, 19, 16, 0, -2], ![-12, 6, 9, 2, 0], ![-15, -12, 8, 9, 4], ![-16, -33, 4, 17, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-5, 5, 12, -7, 2]] ![![-41, 37, 28, -1, -4]]
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
  g := ![5, 5, 5, 1, 1, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB434I0_primes
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
    · exact ![161051]
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I13N1, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [], [I13N1], [], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
