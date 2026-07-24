
import IdealArithmetic.Examples.NF5_1_145800000_1.RI5_1_145800000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7031, 3516, 2244, 1197, 1682]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![7031, 3516, 2244, 1197, 1682]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![7031, 3516, 2244, 1197, 1682], ![20184, 9914, 6395, 3372, 4788], ![57456, 28377, 18074, 9642, 13488], ![16884, 8519, 5387, 2900, 4034], ![-7308, -3612, -2254, -1224, -1669]]]
  hmulB := by decide  
  f := ![![![4978, -1335, 391, -1599, 482]], ![![2892, 1553, -1226, -273, -3198]], ![![-38376, 8535, -1918, 11832, -1092]], ![![-1141, -6281, 4021, -1489, 9728]], ![![37332, -7848, 1582, -11382, 383]]]
  g := ![![![2917, 3516, 2244, 1197, 1682], ![8406, 9914, 6395, 3372, 4788], ![23907, 28377, 18074, 9642, 13488], ![6992, 8519, 5387, 2900, 4034], ![-3042, -3612, -2254, -1224, -1669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 6, 4, 2, 3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![13, 6, 4, 2, 3]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![13, 6, 4, 2, 3], ![36, 18, 11, 6, 8], ![96, 51, 32, 18, 24], ![30, 14, 10, 5, 8], ![-9, -7, -4, -3, -3]]]
  hmulB := by decide  
  f := ![![![-1, 2, -1, 1, -1]], ![![-6, 0, 1, 0, 2]], ![![24, -9, 2, -6, 0]], ![![3, 4, -3, 2, -5]], ![![-20, 6, -1, 5, 1]]]
  g := ![![![5, 6, 4, 2, 3], ![14, 18, 11, 6, 8], ![36, 51, 32, 18, 24], ![11, 14, 10, 5, 8], ![-3, -7, -4, -3, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2407126030, 1191910541, 762397881, 405367469, 570312951]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2407126030, 1191910541, 762397881, 405367469, 570312951]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2407126030, 1191910541, 762397881, 405367469, 570312951], ![6843755412, 3388748289, 2167590961, 1152509580, 1621469876], ![19457638512, 9634628247, 6162727745, 3276726510, 4610038320], ![5798198934, 2871031405, 1836436699, 976434635, 1373749402], ![-2454100275, -1215170269, -777275816, -413278077, -581442414]]]
  hmulB := by decide  
  f := ![![![3968, 739, -815, -764, -2314]], ![![-11900, 4220, -1577, 4115, -2685]], ![![-16352, -7942, 6412, 1769, 16831]], ![![42918, -10207, 2556, -13417, 2198]], ![![14649, 8759, -6769, -1125, -17532]]]
  g := ![![![226408804, 1191910541, 762397881, 405367469, 570312951], ![643708081, 3388748289, 2167590961, 1152509580, 1621469876], ![1830141260, 9634628247, 6162727745, 3276726510, 4610038320], ![545365415, 2871031405, 1836436699, 976434635, 1373749402], ![-230827095, -1215170269, -777275816, -413278077, -581442414]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![7031, 3516, 2244, 1197, 1682]] ![![13, 6, 4, 2, 3]]
  ![![454175, 224902, 143850, 76489, 107607]] where
 M := ![![![454175, 224902, 143850, 76489, 107607]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![454175, 224902, 143850, 76489, 107607]] ![![13, 6, 4, 2, 3]]
  ![![29136554, 14427233, 9228284, 4906686, 6903232]] where
 M := ![![![29136554, 14427233, 9228284, 4906686, 6903232]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![29136554, 14427233, 9228284, 4906686, 6903232]] ![![2407126030, 1191910541, 762397881, 405367469, 570312951]]
  ![![359941143624992948, 178228159996572621, 114002491672854769, 60615201927787552, 85279745744906566]] where
 M := ![![![359941143624992948, 178228159996572621, 114002491672854769, 60615201927787552, 85279745744906566]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![359941143624992948, 178228159996572621, 114002491672854769, 60615201927787552, 85279745744906566]] ![![2407126030, 1191910541, 762397881, 405367469, 570312951]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4446566854790120363909238938, 2201758378743901488359904586, 1408340529595417264163450866, 748815612113855674857553920, 1053511379652959417414236204]]]
 hmul := by decide  
 g := ![![![![2223283427395060181954619469, 1100879189371950744179952293, 704170264797708632081725433, 374407806056927837428776960, 526755689826479708707118102]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-270, 705, -416, 265, -971]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-270, 705, -416, 265, -971]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-270, 705, -416, 265, -971], ![-11652, 1660, -1, 3330, 1060], ![12720, -11505, 6050, -6366, 13320], ![32466, -3406, -758, -8935, -4774], ![-14589, 11356, -5791, 6783, -12530]]]
  hmulB := by decide  
  f := ![![![1558464, 771685, 493602, 262449, 369239]], ![![1476956, 731334, 467791, 248726, 349932]], ![![4199184, 2079259, 1329992, 707154, 994904]], ![![1251330, 619600, 396324, 210725, 296470]], ![![-529625, -262244, -167747, -89189, -125484]]]
  g := ![![![-90, 705, -416, 265, -971], ![-3884, 1660, -1, 3330, 1060], ![4240, -11505, 6050, -6366, 13320], ![10822, -3406, -758, -8935, -4774], ![-4863, 11356, -5791, 6783, -12530]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -7, 3, -8, 4]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![19, -7, 3, -8, 4]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![19, -7, 3, -8, 4], ![48, 8, -11, -6, -32], ![-384, 105, -30, 126, -24], ![-72, -50, 40, -3, 100], ![384, -92, 22, -120, 11]]]
  hmulB := by decide  
  f := ![![![47457, 23499, 15031, 7992, 11244]], ![![44976, 22270, 14245, 7574, 10656]], ![![127872, 63317, 40500, 21534, 30296]], ![![53923, 26701, 17079, 9081, 12776]], ![![-16128, -7986, -5108, -2716, -3821]]]
  g := ![![![9, -7, 3, -8, 4], ![18, 8, -11, -6, -32], ![-170, 105, -30, 126, -24], ![-23, -50, 40, -3, 100], ![168, -92, 22, -120, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-270, 705, -416, 265, -971]] ![![-270, 705, -416, 265, -971]]
  ![![9336129, -6163236, 3017006, -4029712, 6369870]] where
 M := ![![![9336129, -6163236, 3017006, -4029712, 6369870]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![9336129, -6163236, 3017006, -4029712, 6369870]] ![![19, -7, 3, -8, 4]]
  ![![1459190163, -182415601, -15757537, -409862124, -170742706]] where
 M := ![![![1459190163, -182415601, -15757537, -409862124, -170742706]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![1459190163, -182415601, -15757537, -409862124, -170742706]] ![![19, -7, 3, -8, 4]]
  ![![-11035567719, 22873237818, -13293956282, 9154233732, -30812141394]] where
 M := ![![![-11035567719, 22873237818, -13293956282, 9154233732, -30812141394]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-11035567719, 22873237818, -13293956282, 9154233732, -30812141394]] ![![19, -7, 3, -8, 4]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-6497848283109, 1241374788615, -197591392083, 1946000889396, 119458887582]]]
 hmul := by decide  
 g := ![![![![-2165949427703, 413791596205, -65863797361, 648666963132, 39819629194]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 6, -2, 2, -2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-5, 6, -2, 2, -2]] 
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-5, 6, -2, 2, -2], ![-24, -3, 6, 0, 8], ![96, -30, 5, -12, 0], ![12, 18, -10, 5, -12], ![-54, 14, 0, 6, 3]]]
  hmulB := by decide  
  f := ![![![11, 2, -2, -2, -6]], ![![-10, 5, -2, 4, -4]], ![![-17, -8, 7, 2, 18]], ![![50, -10, 2, -15, 0]], ![![20, 10, -8, -2, -21]]]
  g := ![![![-3, 6, -2, 2, -2], ![-8, -3, 6, 0, 8], ![35, -30, 5, -12, 0], ![0, 18, -10, 5, -12], ![-20, 14, 0, 6, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-5, 6, -2, 2, -2]] ![![-5, 6, -2, 2, -2]]
  ![![-179, 20, 16, 12, 28]] where
 M := ![![![-179, 20, 16, 12, 28]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-179, 20, 16, 12, 28]] ![![-5, 6, -2, 2, -2]]
  ![![583, -1006, 438, -322, 458]] where
 M := ![![![583, -1006, 438, -322, 458]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![583, -1006, 438, -322, 458]] ![![-5, 6, -2, 2, -2]]
  ![![34681, -6008, -1792, -2952, -3976]] where
 M := ![![![34681, -6008, -1792, -2952, -3976]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![34681, -6008, -1792, -2952, -3976]] ![![-5, 6, -2, 2, -2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-21965, 171070, -84850, 52250, -93930]]]
 hmul := by decide  
 g := ![![![![-4393, 34214, -16970, 10450, -18786]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-134047746901, -66374971867, -42456322153, -22574055204, -31759519510]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-134047746901, -66374971867, -42456322153, -22574055204, -31759519510]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![1, 3, 0, 3, 1]] where
  M :=![![![-134047746901, -66374971867, -42456322153, -22574055204, -31759519510], ![-381114234120, -188712210034, -120708546581, -64180815858, -90296220816], ![-1083554649792, -536532027273, -343189246708, -182473954590, -256723263432], ![-322889409804, -159881654018, -102267267592, -54375575347, -76501192652], ![136663643022, 67670256834, 43284842818, 23014580202, 32379295715]]]
  hmulB := by decide  
  f := ![![![-2983, -581, 627, 576, 1786]], ![![21432, -5884, 1781, -6954, 2304]], ![![27648, 12909, -10534, -3138, -27816]], ![![-66348, 15668, -3898, 20759, -3244]], ![![-22819, 2161, 680, 6219, 3729]]]
  g := ![![![-14612603913, 4129083809, -6065188879, 10386357618, -31759519510], ![-41545430472, 11739493202, -17244078083, 29529692370, -90296220816], ![-118118769480, 33376823289, -49027035244, 83956547958, -256723263432], ![-35198316736, 9945989134, -14609609656, 25018286087, -76501192652], ![14897763901, -4209661473, 6183548974, -10589043849, 32379295715]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 5, 0, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 0, 2], [5, 5, 3, 6], [5, 4, 4, 6], [0, 1]]
 g := ![![[2, 0, 0, 1], []], ![[2, 3, 0, 6, 1, 2], [1, 0, 1, 6, 0, 1]], ![[0, 1, 1, 6, 3, 3], [1, 0, 6, 2, 2, 6]], ![[4, 4, 4, 1, 6, 3], [5, 4, 2, 6, 5, 6]]]
 h' := ![![[4, 4, 0, 2], [0, 0, 0, 1], [0, 1]], ![[5, 5, 3, 6], [3, 5, 5, 6], [4, 4, 0, 2]], ![[5, 4, 4, 6], [1, 6, 3, 5], [5, 5, 3, 6]], ![[0, 1], [2, 3, 6, 2], [5, 4, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 2], []]
 b := ![[], [], [0, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 5, 0, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![385041014, -172574259, 79446318, -140198433, 151410687]
  a := ![0, -8, -9, -4, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33375761, -89543760, 11349474, -84918642, 151410687]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2983, -581, 627, 576, 1786]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-2983, -581, 627, 576, 1786]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-2983, -581, 627, 576, 1786], ![21432, -5884, 1781, -6954, 2304], ![27648, 12909, -10534, -3138, -27816], ![-66348, 15668, -3898, 20759, -3244], ![-22002, -13644, 10484, 1542, 27137]]]
  hmulB := by decide  
  f := ![![![-134047746901, -66374971867, -42456322153, -22574055204, -31759519510]], ![![-92744246846, -45923164824, -29374455841, -15618418038, -21973608548]], ![![-212242555785, -105093848982, -67222601881, -35742302886, -50285974566]], ![![-141875449187, -70250930479, -44935554051, -23892264481, -33614112886]], ![![-76225013069, -37743514643, -24142395421, -12836527974, -18059757405]]]
  g := ![![![-2216, -581, 627, 576, 1786], ![7301, -5884, 1781, -6954, 2304], ![26886, 12909, -10534, -3138, -27816], ![-24795, 15668, -3898, 20759, -3244], ![-24223, -13644, 10484, 1542, 27137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-134047746901, -66374971867, -42456322153, -22574055204, -31759519510]] ![![-2983, -581, 627, 576, 1786]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [8, 8, 2, 10, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 8, 3, 0, 10], [5, 3, 3, 0, 10], [10, 7, 10, 0, 4], [1, 3, 6, 0, 9], [0, 1]]
 g := ![![[0, 7, 10, 3, 3], [1], []], ![[9, 7, 6, 0, 6, 8, 6, 8], [3, 7, 9, 4, 5, 8, 4, 8], [10, 9, 5, 1]], ![[2, 7, 6, 0, 6, 10, 8, 7], [5, 0, 9, 5, 7, 4, 4, 7], [9, 9, 5, 1]], ![[2, 2, 2, 1, 4, 7, 9, 1], [10, 3, 0, 2, 7, 9, 1, 5], [10, 1, 3, 5]], ![[6, 1, 10, 7, 3, 2, 8, 1], [9, 5, 4, 1, 10, 9, 6, 5], [4, 3, 9, 4]]]
 h' := ![![[0, 8, 3, 0, 10], [3, 3, 9, 1, 5], [0, 0, 1], [0, 1]], ![[5, 3, 3, 0, 10], [9, 3, 6, 10, 5], [8, 2, 9, 3, 6], [0, 8, 3, 0, 10]], ![[10, 7, 10, 0, 4], [5, 8, 0, 4, 2], [8, 7, 8, 5, 2], [5, 3, 3, 0, 10]], ![[1, 3, 6, 0, 9], [4, 0, 1, 1, 6], [9, 8, 10, 7, 9], [10, 7, 10, 0, 4]], ![[0, 1], [9, 8, 6, 6, 4], [2, 5, 5, 7, 5], [1, 3, 6, 0, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 7, 10, 10], [], [], []]
 b := ![[], [6, 9, 10, 4, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [8, 8, 2, 10, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36257296968480775, 14384620229946186, -6099266955822216, 12823403058596009, -11101140821210858]
  a := ![3, -126, -124, -65, -310]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3296117906225525, 1307692748176926, -554478814165656, 1165763914417819, -1009194620110078]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-78439492, -38840034, -24843777, -13209453, -18584427]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-78439492, -38840034, -24843777, -13209453, -18584427]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![12, 0, 4, 1, 0], ![6, 3, 12, 0, 1]] where
  M :=![![![-78439492, -38840034, -24843777, -13209453, -18584427], ![-223013124, -110426995, -70633914, -37556100, -52837812], ![-634053744, -313957530, -200820907, -106776612, -150224400], ![-188942238, -93556482, -59842800, -31818457, -44765502], ![79970211, 39597984, 25328595, 13467231, 18947096]]]
  hmulB := by decide  
  f := ![![![-58, -132, 87, -27, 201]], ![![2412, -427, 42, -684, -108]], ![![-1296, 2178, -1219, 900, -2736]], ![![-966, 618, -292, 395, -606]], ![![-537, 1689, -987, 585, -2260]]]
  g := ![![![14736962, 1301019, 19308243, -13209453, -18584427], ![41898996, 3698957, 54895710, -37556100, -52837812], ![119124000, 10516590, 156075257, -106776612, -150224400], ![35497866, 3133848, 46509004, -31818457, -44765502], ![-15024549, -1326408, -19685037, 13467231, 18947096]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 1, 3], [0, 11, 10], [0, 1]]
 g := ![![[4, 10, 12], [12, 1], [1]], ![[1, 11, 8, 4], [0, 4], [4, 8, 0, 1]], ![[0, 9, 0, 10], [1, 1], [11, 4, 12, 12]]]
 h' := ![![[12, 1, 3], [6, 3, 8], [3, 0, 12], [0, 1]], ![[0, 11, 10], [4, 8, 6], [11, 1, 2], [12, 1, 3]], ![[0, 1], [0, 2, 12], [7, 12, 12], [0, 11, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 12], []]
 b := ![[], [10, 3, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 0, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1080138, 785647, -479183, 454718, -978270]
  a := ![1, -9, -9, -5, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-51318, 286189, 726245, 454718, -978270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58, -132, 87, -27, 201]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-58, -132, 87, -27, 201]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![9, 2, 1, 0, 0], ![10, 10, 0, 1, 0], ![11, 7, 0, 0, 1]] where
  M :=![![![-58, -132, 87, -27, 201], ![2412, -427, 42, -684, -108], ![-1296, 2178, -1219, 900, -2736], ![-6678, 906, 36, 1859, 654], ![1683, -2106, 1149, -981, 2570]]]
  hmulB := by decide  
  f := ![![![-78439492, -38840034, -24843777, -13209453, -18584427]], ![![-223013124, -110426995, -70633914, -37556100, -52837812]], ![![-137387340, -68028602, -43514056, -23136453, -32550759]], ![![-246420646, -122017444, -78047670, -41497999, -58383684]], ![![-180304313, -89279335, -57106950, -30363804, -42718945]]]
  g := ![![![-214, -111, 87, -27, 201], ![774, 545, 42, -684, -108], ![2367, 1136, -1219, 900, -2736], ![-2522, -1718, 36, 1859, 654], ![-2086, -968, 1149, -981, 2570]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [10, 8, 1] where
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
 g := ![![[6, 4], [4], [5, 1]], ![[0, 9], [4], [10, 12]]]
 h' := ![![[5, 12], [3, 2], [2, 2], [0, 1]], ![[0, 1], [0, 11], [12, 11], [5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [10, 8, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33183, -14393, 6990, -12793, 11446]
  a := ![-1, -7, -14, 5, -38]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2131, 1495, 6990, -12793, 11446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-78439492, -38840034, -24843777, -13209453, -18584427]] ![![-58, -132, 87, -27, 201]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 8, -4, 6, -6]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-11, 8, -4, 6, -6]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![10, 8, 13, 1, 0], ![9, 1, 8, 0, 1]] where
  M :=![![![-11, 8, -4, 6, -6], ![-72, 1, 8, 12, 24], ![288, -108, 37, -96, 48], ![132, 26, -30, -17, -76], ![-282, 90, -28, 90, -35]]]
  hmulB := by decide  
  f := ![![![-175, -88, -56, -30, -42]], ![![-504, -247, -160, -84, -120]], ![![-1440, -708, -451, -240, -336]], ![![-1466, -722, -461, -245, -344]], ![![-789, -389, -248, -132, -185]]]
  g := ![![![-1, -2, -2, 6, -6], ![-24, -7, -20, 12, 24], ![48, 36, 53, -96, 48], ![58, 14, 47, -17, -76], ![-51, -35, -54, 90, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [8, 1, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 6, 7], [1, 10, 10], [0, 1]]
 g := ![![[3, 3, 2], [7, 1], [11, 1], []], ![[12, 12, 3, 5], [3, 16], [13, 15], [11, 15]], ![[16, 14, 4, 3], [11, 9], [1, 2], [8, 15]]]
 h' := ![![[10, 6, 7], [4, 14, 6], [14, 15, 1], [0, 0, 1], [0, 1]], ![[1, 10, 10], [12, 1, 5], [6, 11, 13], [12, 6, 10], [10, 6, 7]], ![[0, 1], [14, 2, 6], [0, 8, 3], [5, 11, 6], [1, 10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 4], []]
 b := ![[], [9, 0, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [8, 1, 6, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![297224, 1499276, -957208, 388590, -2198188]
  a := ![0, -4, 8, -18, 20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![952648, 34632, 680978, 388590, -2198188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, 88, 56, 30, 42]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![175, 88, 56, 30, 42]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![2, 7, 1, 0, 0], ![9, 4, 0, 1, 0], ![6, 15, 0, 0, 1]] where
  M :=![![![175, 88, 56, 30, 42], ![504, 247, 160, 84, 120], ![1440, 708, 451, 240, 336], ![420, 214, 134, 73, 100], ![-186, -90, -56, -30, -41]]]
  hmulB := by decide  
  f := ![![![11, -8, 4, -6, 6]], ![![72, -1, -8, -12, -24]], ![![14, 5, -5, 0, -12]], ![![15, -6, 2, -5, 2]], ![![84, -9, -4, -18, -17]]]
  g := ![![![-27, -62, 56, 30, 42], ![-76, -177, 160, 84, 120], ![-214, -497, 451, 240, 336], ![-65, -148, 134, 73, 100], ![26, 61, -56, -30, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [4, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 16], [0, 1]]
 g := ![![[8, 13], [13], [4], [1]], ![[0, 4], [13], [4], [1]]]
 h' := ![![[2, 16], [16, 9], [0, 9], [13, 2], [0, 1]], ![[0, 1], [0, 8], [1, 8], [0, 15], [2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [14, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [4, 15, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23177, -11491, 5640, -9159, 9437]
  a := ![13, -8, -13, 2, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2218, -9170, 5640, -9159, 9437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-11, 8, -4, 6, -6]] ![![175, 88, 56, 30, 42]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79495968304, 39363158141, 25178389926, 13387366953, 18834734747]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![79495968304, 39363158141, 25178389926, 13387366953, 18834734747]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![9, 18, 1, 0, 0], ![11, 5, 0, 1, 0], ![15, 14, 0, 0, 1]] where
  M :=![![![79495968304, 39363158141, 25178389926, 13387366953, 18834734747], ![226016816964, 111914300794, 71585259841, 38061931074, 53549467812], ![642593613744, 318186124125, 203525699680, 108214752174, 152247724296], ![191487040110, 94816564948, 60648803512, 32247009847, 45368434210], ![-81047305047, -40131316764, -25669737629, -13648616859, -19202288180]]]
  hmulB := by decide  
  f := ![![![4570, -911, 172, -1287, 265]], ![![3180, 3004, -1933, -558, -5148]], ![![1926, 3060, -1892, -123, -4869]], ![![3164, -201, -101, -902, -389]], ![![9159, 833, -1143, -2430, -3497]]]
  g := ![![![-30362715722, -39182683250, 25178389926, 13387366953, 18834734747], ![-86324935821, -111401188478, 71585259841, 38061931074, 53549467812], ![-245432411670, -316727282691, 203525699680, 108214752174, 152247724296], ![-73136621735, -94381843497, 60648803512, 32247009847, 45368434210], ![30955233777, 39947319967, -25669737629, -13648616859, -19202288180]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [1, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 18], [0, 1]]
 g := ![![[5, 1], [5, 1], [6], [1]], ![[0, 18], [0, 18], [6], [1]]]
 h' := ![![[14, 18], [14, 18], [14, 18], [18, 14], [0, 1]], ![[0, 1], [0, 1], [0, 1], [5, 5], [14, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [7, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [1, 5, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-690, 145, 108, 251, 265]
  a := ![-1, -4, -2, -4, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-442, -356, 108, 251, 265]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-374, -130, -101, -43, -73]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-374, -130, -101, -43, -73]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![8, 5, 1, 0, 0], ![6, 4, 0, 1, 0], ![9, 5, 0, 0, 1]] where
  M :=![![![-374, -130, -101, -43, -73], ![-876, -501, -246, -168, -172], ![-2064, -1266, -841, -444, -672], ![-906, -252, -274, -85, -210], ![105, 146, 135, 57, 126]]]
  hmulB := by decide  
  f := ![![![244, 188, -139, -7, -355]], ![![-4260, 885, -174, 1296, -28]], ![![-1036, 133, 9, 292, 116]], ![![-162, 132, -68, 77, -148]], ![![-1035, 503, -222, 396, -437]]]
  g := ![![![71, 48, -101, -43, -73], ![192, 119, -246, -168, -172], ![704, 425, -841, -444, -672], ![194, 132, -274, -85, -210], ![-129, -73, 135, 57, 126]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18], [0, 1]]
 g := ![![[1, 5], [17, 16], [7], [1]], ![[18, 14], [3, 3], [7], [1]]]
 h' := ![![[11, 18], [16, 9], [8, 15], [11, 11], [0, 1]], ![[0, 1], [1, 10], [2, 4], [18, 8], [11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [14, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [8, 8, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3653, -1119, 803, -1101, 1222]
  a := ![3, 3, 7, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-377, -360, 803, -1101, 1222]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![594497, -166279, 50969, -192890, 67796]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![594497, -166279, 50969, -192890, 67796]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![594497, -166279, 50969, -192890, 67796], ![813552, 351126, -291373, -100962, -771560], ![-9258720, 2153151, -521396, 2881122, -403848], ![-1214472, -1297270, 917424, -67067, 2306528], ![9030876, -1988282, 438740, -2778696, 226785]]]
  hmulB := by decide  
  f := ![![![126333122795459, 62555004953571, 40012904983433, 21274888642330, 29931717398724]], ![![118640918458767, 58746139394499, 37576588723480, 19979497639116, 28109227134220]], ![![73694422274643, 36490469391030, 23340893116831, 12410368656780, 17460192327852]], ![![42612588992396, 21100014442132, 13496487989230, 7176091792193, 10096069369024]], ![![53063138658141, 26274700000777, 16806442192429, 8935996680714, 12572085890541]]]
  g := ![![![163009, -166279, 50969, -192890, 67796], ![198351, 351126, -291373, -100962, -771560], ![-2520087, 2153151, -521396, 2881122, -403848], ![-263062, -1297270, 917424, -67067, 2306528], ![2453295, -1988282, 438740, -2778696, 226785]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![79495968304, 39363158141, 25178389926, 13387366953, 18834734747]] ![![-374, -130, -101, -43, -73]]
  ![![-126333122795459, -62555004953571, -40012904983433, -21274888642330, -29931717398724]] where
 M := ![![![-126333122795459, -62555004953571, -40012904983433, -21274888642330, -29931717398724]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-126333122795459, -62555004953571, -40012904983433, -21274888642330, -29931717398724]] ![![594497, -166279, 50969, -192890, 67796]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![286, 85, -84, 15, -113]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![286, 85, -84, 15, -113]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![5, 8, 4, 19, 1]] where
  M :=![![![286, 85, -84, 15, -113], ![-1356, 388, -13, 174, 60], ![720, -1401, 622, -438, 696], ![2070, -184, -184, -161, -322], ![-807, 834, -319, 273, -350]]]
  hmulB := by decide  
  f := ![![![5576, 2761, 1766, 939, 1321]], ![![15852, 7850, 5021, 2670, 3756]], ![![45072, 22317, 14276, 7590, 10680]], ![![13434, 6650, 4254, 2261, 3182]], ![![25415, 12583, 8049, 4279, 6021]]]
  g := ![![![37, 43, 16, 94, -113], ![-72, -4, -11, -42, 60], ![-120, -303, -94, -594, 696], ![160, 104, 48, 259, -322], ![41, 158, 47, 301, -350]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [16, 11, 1, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 12, 10, 19], [21, 20, 10, 1], [8, 13, 3, 3], [0, 1]]
 g := ![![[20, 15, 8, 18], [21, 20, 10, 13], [8, 1], []], ![[16, 18, 5, 4, 9, 5], [18, 14, 18, 21, 4, 22], [4, 5, 0, 5, 7, 21], [4, 2, 16]], ![[11, 6, 17, 14, 5, 16], [7, 20, 20, 14, 3, 2], [6, 19, 11, 1, 17, 2], [18, 5, 1]], ![[12, 17, 17, 15, 7, 9], [0, 16, 12, 9], [8, 6, 3, 13, 8, 2], [16, 21, 9]]]
 h' := ![![[2, 12, 10, 19], [9, 9, 3, 8], [10, 11, 4, 17], [0, 0, 1], [0, 1]], ![[21, 20, 10, 1], [14, 11, 11, 4], [6, 1, 11, 11], [9, 18, 17, 9], [2, 12, 10, 19]], ![[8, 13, 3, 3], [0, 13, 2, 4], [6, 11, 1, 18], [15, 10, 18, 18], [21, 20, 10, 1]], ![[0, 1], [1, 13, 7, 7], [16, 0, 7], [15, 18, 10, 19], [8, 13, 3, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17, 21, 14], []]
 b := ![[], [], [9, 2, 1, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [16, 11, 1, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1565166251, -263147248, 28207767, -455486081, -74719435]
  a := ![1, 6, 10, -2, 27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![84294062, 14548184, 14221109, 41921008, -74719435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5576, 2761, 1766, 939, 1321]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![5576, 2761, 1766, 939, 1321]] 
 ![![23, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![5576, 2761, 1766, 939, 1321], ![15852, 7850, 5021, 2670, 3756], ![45072, 22317, 14276, 7590, 10680], ![13434, 6650, 4254, 2261, 3182], ![-5685, -2814, -1801, -957, -1348]]]
  hmulB := by decide  
  f := ![![![286, 85, -84, 15, -113]], ![![140, 76, -59, 18, -76]], ![![280, 13, -46, -6, -68]], ![![90, -8, -8, -7, -14]], ![![139, 88, -65, 21, -84]]]
  g := ![![![-4018, 2761, 1766, 939, 1321], ![-11424, 7850, 5021, 2670, 3756], ![-32480, 22317, 14276, 7590, 10680], ![-9678, 6650, 4254, 2261, 3182], ![4097, -2814, -1801, -957, -1348]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![286, 85, -84, 15, -113]] ![![5576, 2761, 1766, 939, 1321]]
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


lemma PB752I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB752I0 : PrimesBelowBoundCertificateInterval O 1 23 752 where
  m := 9
  g := ![5, 5, 5, 2, 1, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB752I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![2401, 7]
    · exact ![161051]
    · exact ![2197, 169]
    · exact ![4913, 289]
    · exact ![361, 361, 19]
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
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I13N1, I17N1, I19N0, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [I17N1], [I19N0, I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
