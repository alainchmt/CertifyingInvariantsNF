
import IdealArithmetic.Examples.NF5_1_48600000_5.RI5_1_48600000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -108, 77, -15, -57]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-35, -108, 77, -15, -57]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-35, -108, 77, -15, -57], ![144, 297, -360, 124, 24], ![-148, -44, 445, -236, 348], ![-184, -1106, 248, 147, -1068], ![358, 1198, -761, 115, 716]]]
  hmulB := by decide  
  f := ![![![57836, -12748, -3401, 2753, 10791]], ![![-13544, 2993, 796, -648, -2532]], ![![3180, -692, -187, 148, 588]], ![![6036, -1322, -354, 285, 1122]], ![![39531, -8718, -2324, 1884, 7379]]]
  g := ![![![11, -108, 77, -15, -57], ![60, 297, -360, 124, 24], ![-248, -44, 445, -236, 348], ![442, -1106, 248, 147, -1068], ![-179, 1198, -761, 115, 716]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21997187, 4850287, 1293363, -1047878, -4105406]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-21997187, 4850287, 1293363, -1047878, -4105406]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-21997187, 4850287, 1293363, -1047878, -4105406], ![10306568, -2272550, -605994, 490970, 1923544], ![-2414514, 532397, 141964, -115024, -450634], ![-4587626, 1011561, 269736, -218545, -856210], ![-8075620, 1780638, 474821, -384696, -1507177]]]
  hmulB := by decide  
  f := ![![![466, 433, -1318, 622, -676]], ![![54, 1886, 379, -696, 2542]], ![![-1613, -6618, 3073, -6, -4968]], ![![4920, 11258, -11971, 3763, 2408]], ![![-2789, -3742, 7551, -3238, 2403]]]
  g := ![![![-9592572, 4850287, 1293363, -1047878, -4105406], ![4494509, -2272550, -605994, 490970, 1923544], ![-1052922, 532397, 141964, -115024, -450634], ![-2000576, 1011561, 269736, -218545, -856210], ![-3521632, 1780638, 474821, -384696, -1507177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 24, -34, 13, -2]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![13, 24, -34, 13, -2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![13, 24, -34, 13, -2], ![-22, 15, 70, -42, 82], ![-40, -223, 55, 28, -208], ![191, 548, -438, 104, 251], ![-157, -321, 394, -137, -22]]]
  hmulB := by decide  
  f := ![![![168747, -37207, -9922, 8038, 31493]], ![![-39531, 8718, 2324, -1884, -7379]], ![![9263, -2040, -545, 440, 1727]], ![![101972, -22481, -5996, 4856, 19029]], ![![115348, -25434, -6782, 5495, 21528]]]
  g := ![![![1, 24, -34, 13, -2], ![-31, 15, 70, -42, 82], ![70, -223, 55, 28, -208], ![-82, 548, -438, 104, 251], ![1, -321, 394, -137, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-35, -108, 77, -15, -57]] ![![-21997187, 4850287, 1293363, -1047878, -4105406]]
  ![![-647, 143, 38, -31, -121]] where
 M := ![![![-647, 143, 38, -31, -121]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-647, 143, 38, -31, -121]] ![![-21997187, 4850287, 1293363, -1047878, -4105406]]
  ![![16733634107, -3689694842, -983883528, 797137975, 3123051309]] where
 M := ![![![16733634107, -3689694842, -983883528, 797137975, 3123051309]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![16733634107, -3689694842, -983883528, 797137975, 3123051309]] ![![13, 24, -34, 13, -2]]
  ![![168747, -37207, -9922, 8038, 31493]] where
 M := ![![![168747, -37207, -9922, 8038, 31493]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![168747, -37207, -9922, 8038, 31493]] ![![13, 24, -34, 13, -2]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![2, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, -169, -80, 88, -269]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![10, -169, -80, 88, -269]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![10, -169, -80, 88, -269], ![362, 1451, -700, 16, 1066], ![-1082, -2818, 2533, -684, -1018], ![1521, 1861, -4170, 1841, -1567], ![-355, 1257, 1464, -1138, 2780]]]
  hmulB := by decide  
  f := ![![![-5692, 1181, 336, -242, -1017]], ![![-1058, 142, 60, -18, -145]], ![![-2154, 365, 117, -70, -345]], ![![-4219, 813, 226, -177, -737]], ![![-4455, 977, 260, -212, -830]]]
  g := ![![![207, -169, -80, 88, -269], ![-851, 1451, -700, 16, 1066], ![869, -2818, 2533, -684, -1018], ![1094, 1861, -4170, 1841, -1567], ![-2120, 1257, 1464, -1138, 2780]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 0, 0, -4]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![1, -1, 0, 0, -4]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1, -1, 0, 0, -4], ![8, 21, -10, 0, 8], ![-8, -21, 29, -10, -8], ![14, 10, -34, 19, -26], ![-2, 21, 6, -8, 35]]]
  hmulB := by decide  
  f := ![![![43915, -9683, -2582, 2092, 8196]], ![![22418, -4943, -1318, 1068, 4184]], ![![16245, -3582, -955, 774, 3032]], ![![17691, -3901, -1040, 843, 3302]], ![![5374, -1185, -316, 256, 1003]]]
  g := ![![![1, -1, 0, 0, -4], ![-8, 21, -10, 0, 8], ![5, -21, 29, -10, -8], ![3, 10, -34, 19, -26], ![-14, 21, 6, -8, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -5, 2, 0, -2]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, -5, 2, 0, -2]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, -5, 2, 0, -2], ![4, 15, -14, 4, 4], ![-8, -11, 23, -10, 8], ![0, -30, -6, 11, -40], ![12, 43, -20, 0, 33]]]
  hmulB := by decide  
  f := ![![![-51, -67, 4, 28, 38]], ![![-78, -105, 2, 40, 56]], ![![-69, -100, -7, 30, 46]], ![![-49, -85, -22, 11, 26]], ![![-2, -5, -2, 0, 1]]]
  g := ![![![5, -5, 2, 0, -2], ![-8, 15, -14, 4, 4], ![-5, -11, 23, -10, 8], ![45, -30, -6, 11, -40], ![-40, 43, -20, 0, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![10, -169, -80, 88, -269]] ![![1, -1, 0, 0, -4]]
  ![![1068, -6648, -5236, 4624, -12455]] where
 M := ![![![1068, -6648, -5236, 4624, -12455]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1068, -6648, -5236, 4624, -12455]] ![![1, -1, 0, 0, -4]]
  ![![79418, -246035, -317310, 239856, -571717]] where
 M := ![![![79418, -246035, -317310, 239856, -571717]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![79418, -246035, -317310, 239856, -571717]] ![![1, -1, 0, 0, -4]]
  ![![5151036, -8190140, -18327046, 12304100, -25993823]] where
 M := ![![![5151036, -8190140, -18327046, 12304100, -25993823]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![5151036, -8190140, -18327046, 12304100, -25993823]] ![![3, -5, 2, 0, -2]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-182616960, -1433867163, 149493834, 285855000, -1539639159]]]
 hmul := by decide  
 g := ![![![![-60872320, -477955721, 49831278, 95285000, -513213053]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![549, -718, -62, 224, 432]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![549, -718, -62, 224, 432]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![549, -718, -62, 224, 432], ![-1312, -1225, -124, 324, 480], ![-804, -1594, -421, 200, 492], ![-36, -1030, -840, -383, -132], ![1072, 880, -74, -380, -475]]]
  hmulB := by decide  
  f := ![![![-2327, -9554, 4434, -8, -7176]], ![![1012, -49, -3148, 1764, -2880]], ![![-5562, -11114, 13999, -4928, -420]], ![![-824, -18694, -2872, 6409, -24396]], ![![3234, 15912, -5398, -1092, 13733]]]
  g := ![![![357, -718, -62, 224, 432], ![316, -1225, -124, 324, 480], ![926, -1594, -421, 200, 492], ![1512, -1030, -840, -383, -132], ![34, 880, -74, -380, -475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![549, -718, -62, 224, 432]] ![![549, -718, -62, 224, 432]]
  ![![1748305, 733636, -139032, -372008, -372744]] where
 M := ![![![1748305, 733636, -139032, -372008, -372744]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![1748305, 733636, -139032, -372008, -372744]] ![![549, -718, -62, 224, 432]]
  ![![-277118539, -1877216562, 199236474, 885633768, 1265167752]] where
 M := ![![![-277118539, -1877216562, 199236474, 885633768, 1265167752]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-277118539, -1877216562, 199236474, 885633768, 1265167752]] ![![549, -718, -62, 224, 432]]
  ![![3474960940833, 2382123300616, -671477131216, -1450406902928, -1640613152976]] where
 M := ![![![3474960940833, 2382123300616, -671477131216, -1450406902928, -1640613152976]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![3474960940833, 2382123300616, -671477131216, -1450406902928, -1640613152976]] ![![549, -718, -62, 224, 432]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-2384247251878075, -4292608916217430, 1111608176413650, 2594842615855280, 3284980521027360]]]
 hmul := by decide  
 g := ![![![![-476849450375615, -858521783243486, 222321635282730, 518968523171056, 656996104205472]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [3, 5, 4, 2, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 5, 3, 4, 4], [5, 1, 5, 6, 2], [3, 4, 1, 6, 2], [2, 3, 5, 5, 6], [0, 1]]
 g := ![![[0, 3, 1], []], ![[3, 6, 5, 1, 0, 1], [3, 4, 6, 2, 1, 2, 6, 1]], ![[3, 3, 2, 6, 4, 5, 0, 1], [0, 0, 3, 6, 6, 2, 5, 1]], ![[6, 5, 2, 3, 6, 2], [3, 4, 5, 0, 2, 3, 5, 1]], ![[6, 3, 4, 6, 4, 4, 2, 3], [4, 4, 5, 2, 3, 6, 5, 6]]]
 h' := ![![[0, 5, 3, 4, 4], [0, 0, 0, 1], [0, 1]], ![[5, 1, 5, 6, 2], [5, 1, 6, 4], [0, 5, 3, 4, 4]], ![[3, 4, 1, 6, 2], [6, 5, 3, 1, 2], [5, 1, 5, 6, 2]], ![[2, 3, 5, 5, 6], [4, 4, 5, 6], [3, 4, 1, 6, 2]], ![[0, 1], [3, 4, 0, 2, 5], [2, 3, 5, 5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 1, 2, 5], [], [], []]
 b := ![[], [0, 1, 0, 1, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [3, 5, 4, 2, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![241829812, -361969251, 775212760, -276255504, -1195529811]
  a := ![5, -7, -8, -8, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![34547116, -51709893, 110744680, -39465072, -170789973]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [9, 1, 6, 10, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 1, 1, 1, 10], [9, 8, 1, 3, 9], [5, 7, 7, 6, 10], [0, 5, 2, 1, 4], [0, 1]]
 g := ![![[10, 9, 4, 3, 1], [1], []], ![[0, 9, 5, 2, 5, 10], [6, 4, 2, 0, 7, 10, 6, 2], [3, 10, 10, 1]], ![[0, 4, 4, 9, 0, 3, 5, 9], [3, 5, 4, 3, 2, 0, 8, 9], [9, 1, 3, 4]], ![[3, 4, 4, 5, 3, 2], [8, 6, 0, 1, 1, 5, 7, 10], [10, 1, 0, 1]], ![[0, 4, 7, 4, 0, 7, 8, 5], [8, 4, 2, 4, 9, 4, 8, 1], [7, 2, 2, 5]]]
 h' := ![![[9, 1, 1, 1, 10], [2, 10, 5, 1, 1], [0, 0, 1], [0, 1]], ![[9, 8, 1, 3, 9], [10, 0, 8, 10], [10, 2, 0, 10, 3], [9, 1, 1, 1, 10]], ![[5, 7, 7, 6, 10], [6, 7, 1, 10, 1], [0, 5, 0, 1, 1], [9, 8, 1, 3, 9]], ![[0, 5, 2, 1, 4], [10, 4, 7, 3], [1, 7, 3, 10, 1], [5, 7, 7, 6, 10]], ![[0, 1], [5, 1, 1, 9, 9], [3, 8, 7, 1, 6], [0, 5, 2, 1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 5, 2, 9], [], [], []]
 b := ![[], [2, 2, 5, 2, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [9, 1, 6, 10, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42391347869937, 66231617024540, -89568108885530, 27903156028440, -20012764100340]
  a := ![-6, -56, 11, -57, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3853758897267, 6021056093140, -8142555353230, 2536650548040, -1819342190940]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -14, 26, -10, 10]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-11, -14, 26, -10, 10]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![4, 7, 6, 1, 0], ![12, 3, 6, 0, 1]] where
  M :=![![![-11, -14, 26, -10, 10], ![0, -55, -28, 32, -80], ![48, 218, -103, 4, 176], ![-180, -436, 412, -115, -124], ![120, 190, -310, 122, -61]]]
  hmulB := by decide  
  f := ![![![-12287, 2710, 722, -586, -2294]], ![![5760, -1267, -340, 272, 1072]], ![![-1344, 302, 77, -68, -256]], ![![-1496, 335, 86, -75, -284]], ![![-10980, 2425, 644, -526, -2053]]]
  g := ![![![-7, 2, 2, -10, 10], ![64, -3, 20, 32, -80], ![-160, -26, -91, 4, 176], ![136, 57, 142, -115, -124], ![28, -37, -52, 122, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [1, 6, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4, 6], [3, 8, 7], [0, 1]]
 g := ![![[12, 6, 3], [3, 3], [1]], ![[11, 0, 4, 7], [4, 3], [5, 7, 9, 8]], ![[1, 1, 5, 7], [], [7, 0, 0, 5]]]
 h' := ![![[1, 4, 6], [11, 4, 9], [12, 7, 4], [0, 1]], ![[3, 8, 7], [12, 4, 5], [9, 1, 9], [1, 4, 6]], ![[0, 1], [10, 5, 12], [7, 5], [3, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 12], []]
 b := ![[], [11, 2, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [1, 6, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23555, 22412, -14296, -12812, -23960]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27871, 14152, 15872, -12812, -23960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12287, -2710, -722, 586, 2294]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![12287, -2710, -722, 586, 2294]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![2, 7, 1, 0, 0], ![12, 11, 0, 1, 0], ![5, 1, 0, 0, 1]] where
  M :=![![![12287, -2710, -722, 586, 2294], ![-5760, 1267, 340, -272, -1072], ![1344, -302, -77, 68, 256], ![2556, -572, -148, 127, 484], ![4512, -994, -266, 214, 841]]]
  hmulB := by decide  
  f := ![![![11, 14, -26, 10, -10]], ![![0, 55, 28, -32, 80]], ![![-2, 15, 19, -16, 28]], ![![24, 93, -32, -9, 68]], ![![-5, -5, 16, -8, 7]]]
  g := ![![![-367, -492, -722, 586, 2294], ![168, 227, 340, -272, -1072], ![-46, -59, -77, 68, 256], ![-84, -109, -148, 127, 484], ![-133, -179, -266, 214, 841]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 12], [0, 1]]
 g := ![![[12, 1], [10], [5, 1]], ![[4, 12], [10], [10, 12]]]
 h' := ![![[5, 12], [3, 12], [1, 7], [0, 1]], ![[0, 1], [11, 1], [10, 6], [5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [1, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [5, 8, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15252, -12352, 11969, 11884, 15422]
  a := ![-8, 27, 13, 26, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19916, -18637, 11969, 11884, 15422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-11, -14, 26, -10, 10]] ![![12287, -2710, -722, 586, 2294]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 44, -4, -16, -18]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![31, 44, -4, -16, -18]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![5, 6, 11, 1, 0], ![8, 13, 15, 0, 1]] where
  M :=![![![31, 44, -4, -16, -18], ![68, 85, 20, -40, -60], ![100, 154, -15, -20, -60], ![46, 130, 64, -15, 30], ![-66, -120, 24, 36, -1]]]
  hmulB := by decide  
  f := ![![![120075, -26476, -7060, 5720, 22410]], ![![-56260, 12405, 3308, -2680, -10500]], ![![13180, -2906, -775, 628, 2460]], ![![25461, -5614, -1497, 1213, 4752]], ![![27706, -6109, -1629, 1320, 5171]]]
  g := ![![![15, 22, 26, -16, -18], ![44, 65, 80, -40, -60], ![40, 62, 65, -20, -60], ![-7, -10, -13, -15, 30], ![-14, -19, -21, 36, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [9, 9, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 7, 15], [16, 9, 2], [0, 1]]
 g := ![![[16, 2, 4], [7, 16], [8, 1], []], ![[0, 10, 9, 15], [12, 2], [5, 13], [4, 4]], ![[16, 10, 13, 2], [9, 4], [10, 15], [0, 4]]]
 h' := ![![[9, 7, 15], [4, 16, 15], [13, 4, 4], [0, 0, 1], [0, 1]], ![[16, 9, 2], [7, 4, 1], [8, 6, 11], [11, 3, 9], [9, 7, 15]], ![[0, 1], [3, 14, 1], [13, 7, 2], [1, 14, 7], [16, 9, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 8], []]
 b := ![[], [13, 0, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [9, 9, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![663563, 124745, -1386815, 617995, -1584685]
  a := ![10, -9, -15, -7, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![603004, 1001040, 916795, 617995, -1584685]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![537, -118, -36, 28, 96]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![537, -118, -36, 28, 96]] 
 ![![17, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![537, -118, -36, 28, 96], ![-248, 77, 12, -16, -24], ![40, -74, 37, -4, -24], ![152, 56, -108, 41, 24], ![176, -58, 48, -20, 73]]]
  hmulB := by decide  
  f := ![![![-2487, -3338, 60, 1268, 1776]], ![![-797, -1105, -24, 380, 552]], ![![-980, -1422, -107, 420, 648]], ![![-319, -650, -264, -3, 120]], ![![-451, -624, -12, 216, 313]]]
  g := ![![![31, -118, -36, 28, 96], ![-23, 77, 12, -16, -24], ![14, -74, 37, -4, -24], ![15, 56, -108, 41, 24], ![-11, -58, 48, -20, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, 62, 16, -12, -42]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-179, 62, 16, -12, -42]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-179, 62, 16, -12, -42], ![108, 23, 16, 8, 12], ![-20, 40, 43, 24, 12], ![-90, -6, 68, 63, 54], ![-98, -26, 0, 8, 5]]]
  hmulB := by decide  
  f := ![![![25, -174, -128, 116, -318]], ![![37, 9, -112, 60, -90]], ![![-74, -228, 163, -32, -120]], ![![134, 38, -404, 215, -318]], ![![-22, -14, 64, -32, 41]]]
  g := ![![![-17, 62, 16, -12, -42], ![-19, 23, 16, 8, 12], ![-50, 40, 43, 24, 12], ![-80, -6, 68, 63, 54], ![0, -26, 0, 8, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![31, 44, -4, -16, -18]] ![![537, -118, -36, 28, 96]]
  ![![-25, 174, 128, -116, 318]] where
 M := ![![![-25, 174, 128, -116, 318]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-25, 174, 128, -116, 318]] ![![-179, 62, 16, -12, -42]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -486, 258, -18, -314]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-137, -486, 258, -18, -314]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![8, 3, 16, 17, 1]] where
  M :=![![![-137, -486, 258, -18, -314], ![664, 1655, -1636, 480, 520], ![-1000, -1306, 2655, -1156, 920], ![-96, -3456, -724, 1259, -4648], ![1228, 5030, -2294, -22, 3773]]]
  hmulB := by decide  
  f := ![![![6425149, -1416718, -377778, 306074, 1199146]], ![![-3010440, 663789, 177004, -143408, -561848]], ![![705256, -155506, -41467, 33596, 131624]], ![![1340000, -295464, -78788, 63833, 250088]], ![![4146988, -914393, -243830, 197549, 773965]]]
  g := ![![![125, 24, 278, 280, -314], ![-184, 5, -524, -440, 520], ![-440, -214, -635, -884, 920], ![1952, 552, 3876, 4225, -4648], ![-1524, -331, -3298, -3377, 3773]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [4, 11, 12, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 6, 10, 5], [4, 13, 2, 9], [10, 18, 7, 5], [0, 1]]
 g := ![![[12, 3, 12, 11], [11, 2, 6, 16], [1], []], ![[8, 12, 3, 0, 5, 4], [1, 9, 16, 14, 1, 4], [11, 3, 16], [14, 10, 6]], ![[4, 11, 15, 0, 16, 1], [5, 13, 5, 16, 16, 4], [14, 7, 4], [3, 18, 5]], ![[10, 8, 11, 13, 15, 6], [4, 9, 16, 5, 13, 5], [1, 8, 4], [1, 18, 6]]]
 h' := ![![[9, 6, 10, 5], [13, 1, 5, 12], [15, 8, 7, 4], [0, 0, 1], [0, 1]], ![[4, 13, 2, 9], [2, 4, 0, 4], [11, 13, 17, 4], [6, 9, 9, 4], [9, 6, 10, 5]], ![[10, 18, 7, 5], [15, 2, 9, 13], [17, 0, 5, 12], [4, 18, 7, 17], [4, 13, 2, 9]], ![[0, 1], [17, 12, 5, 9], [16, 17, 9, 18], [1, 11, 2, 17], [10, 18, 7, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17, 10, 3], []]
 b := ![[], [], [7, 3, 1, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [4, 11, 12, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![663942522, 2433829956, -1371459130, 143290014, 1626328734]
  a := ![-6, -4, 10, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-649825650, -128692434, -1441722046, -1447594656, 1626328734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6425149, 1416718, 377778, -306074, -1199146]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-6425149, 1416718, 377778, -306074, -1199146]] 
 ![![19, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-6425149, 1416718, 377778, -306074, -1199146], ![3010440, -663789, -177004, 143408, 561848], ![-705256, 155506, 41467, -33596, -131624], ![-1340000, 295464, 78788, -63833, -250088], ![-2358804, 520106, 138690, -112366, -440231]]]
  hmulB := by decide  
  f := ![![![137, 486, -258, 18, 314]], ![![66, 271, -104, -12, 204]], ![![168, 478, -357, 76, 216]], ![![106, 540, -152, -53, 476]], ![![-43, -188, 80, 4, -149]]]
  g := ![![![-1285325, 1416718, 377778, -306074, -1199146], ![602226, -663789, -177004, 143408, 561848], ![-141084, 155506, 41467, -33596, -131624], ![-268062, 295464, 78788, -63833, -250088], ![-471869, 520106, 138690, -112366, -440231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-137, -486, 258, -18, -314]] ![![-6425149, 1416718, 377778, -306074, -1199146]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105, 78, -82, -102, -104]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![105, 78, -82, -102, -104]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![4, 15, 15, 1, 0], ![9, 4, 2, 0, 1]] where
  M :=![![![105, 78, -82, -102, -104], ![412, 339, -256, -368, -404], ![772, 720, -433, -624, -700], ![1118, 1126, -476, -873, -970], ![-118, -78, 122, 138, 107]]]
  hmulB := by decide  
  f := ![![![-569181, 125502, 33466, -27114, -106228]], ![![266684, -58803, -15680, 12704, 49772]], ![![-62476, 13776, 3673, -2976, -11660]], ![![29030, -6401, -1707, 1383, 5418]], ![![-190861, 42084, 11222, -9092, -35621]]]
  g := ![![![63, 88, 72, -102, -104], ![240, 325, 264, -368, -404], ![416, 560, 449, -624, -700], ![580, 787, 633, -873, -970], ![-71, -112, -94, 138, 107]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [2, 21, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 7, 18], [0, 15, 5], [0, 1]]
 g := ![![[16, 17, 8], [10, 22, 18], [14, 14, 1], []], ![[19, 2, 12, 8], [21, 9, 6, 13], [4, 8, 8, 2], [4, 2]], ![[0, 8, 18, 19], [19, 9, 1, 17], [16, 20, 9, 15], [17, 2]]]
 h' := ![![[14, 7, 18], [3, 1, 10], [18, 0, 15], [0, 0, 1], [0, 1]], ![[0, 15, 5], [11, 6, 7], [9, 10, 18], [4, 16, 15], [14, 7, 18]], ![[0, 1], [8, 16, 6], [14, 13, 13], [12, 7, 7], [0, 15, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 20], []]
 b := ![[], [12, 8, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [2, 21, 9, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2814747, -2490092, 581996, 2413628, 2944264]
  a := ![-6, 19, 16, 20, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1694245, -2194416, -1804824, 2413628, 2944264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569181, -125502, -33466, 27114, 106228]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![569181, -125502, -33466, 27114, 106228]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![2, 8, 1, 0, 0], ![7, 18, 0, 1, 0], ![0, 10, 0, 0, 1]] where
  M :=![![![569181, -125502, -33466, 27114, 106228], ![-266684, 58803, 15680, -12704, -49772], ![62476, -13776, -3673, 2976, 11660], ![118706, -26174, -6980, 5655, 22154], ![208958, -46074, -12286, 9954, 38999]]]
  hmulB := by decide  
  f := ![![![-105, -78, 82, 102, 104]], ![![-412, -339, 256, 368, 404]], ![![-186, -156, 115, 164, 180]], ![![-403, -338, 246, 357, 390]], ![![-174, -144, 106, 154, 171]]]
  g := ![![![19405, -61222, -33466, 27114, 106228], ![-9092, 28685, 15680, -12704, -49772], ![2130, -6720, -3673, 2976, 11660], ![4047, -12768, -6980, 5655, 22154], ![7124, -22476, -12286, 9954, 38999]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [7, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 22], [0, 1]]
 g := ![![[19, 1], [1, 6], [9, 2], [1]], ![[1, 22], [8, 17], [19, 21], [1]]]
 h' := ![![[5, 22], [16, 22], [6, 11], [16, 5], [0, 1]], ![[0, 1], [11, 1], [15, 12], [18, 18], [5, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [6, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [7, 18, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![318, 702, -905, 396, 132]
  a := ![-2, -3, 3, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28, -22, -905, 396, 132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![105, 78, -82, -102, -104]] ![![569181, -125502, -33466, 27114, 106228]]
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
  g := ![5, 5, 5, 1, 1, 2, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB434I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
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
    · exact ![4913, 17, 17]
    · exact ![130321, 19]
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
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I13N1, I17N1, I17N2, I19N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [], [I13N1], [I17N1, I17N2], [I19N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
