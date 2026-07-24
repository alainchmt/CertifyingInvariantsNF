
import IdealArithmetic.Examples.NF5_1_16200000_1.RI5_1_16200000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-124, 50, -62, 50, -159]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-124, 50, -62, 50, -159]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-124, 50, -62, 50, -159], ![-318, -377, 123, -56, 405], ![810, -208, 222, -284, 681], ![840, 1358, -706, 279, -1908], ![-448, 272, -267, 214, -710]]]
  hmulB := by decide  
  f := ![![![4081, 558, -635, 322, -2070]], ![![-2070, 1631, -1055, 630, -1311]], ![![-2622, -6224, 4628, -2638, 8565]], ![![9600, 5138, -4246, 2343, -9588]], ![![1799, 4338, -3224, 1838, -5960]]]
  g := ![![![-62, 50, -62, 50, -159], ![-159, -377, 123, -56, 405], ![405, -208, 222, -284, 681], ![420, 1358, -706, 279, -1908], ![-224, 272, -267, 214, -710]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3143, 5079, -3834, 2175, -7329]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![3143, 5079, -3834, 2175, -7329]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3143, 5079, -3834, 2175, -7329], ![-14658, -8587, 7017, -3885, 15555], ![31110, 3999, -4657, 2349, -15465], ![-8136, 17031, -11787, 6878, -18252], ![-21750, -2865, 3306, -1671, 10898]]]
  hmulB := by decide  
  f := ![![![334, -2859, 1701, -1128, 4830]], ![![4997, 1121, 462, -873, 954]], ![![-2755, 6636, -4381, 3126, -12306]], ![![-16969, -12336, 3291, -145, 10623]], ![![29, -7731, 4407, -2826, 12575]]]
  g := ![![![3526, 5079, -3834, 2175, -7329], ![-12379, -8587, 7017, -3885, 15555], ![22442, 3999, -4657, 2349, -15465], ![-1003, 17031, -11787, 6878, -18252], ![-15709, -2865, 3306, -1671, 10898]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, -2, -1, -1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![1, -2, -2, -1, -1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, -2, -2, -1, -1], ![-2, 7, -16, 3, -29], ![-58, -10, -47, 11, -73], ![-72, -58, -46, -3, -36], ![8, -8, -1, -5, 7]]]
  hmulB := by decide  
  f := ![![![72, 54, -43, 24, -91]], ![![-55, 3, 1, 0, 15]], ![![157, -18, 4, -4, -31]], ![![60, 134, -100, 57, -186]], ![![-49, 58, -39, 23, -55]]]
  g := ![![![3, -2, -2, -1, -1], ![18, 7, -16, 3, -29], ![36, -10, -47, 11, -73], ![34, -58, -46, -3, -36], ![5, -8, -1, -5, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-124, 50, -62, 50, -159]] ![![3143, 5079, -3834, 2175, -7329]]
  ![![-2, 1, -4, 1, -6]] where
 M := ![![![-2, 1, -4, 1, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-2, 1, -4, 1, -6]] ![![3143, 5079, -3834, 2175, -7329]]
  ![![-23020, -520, 1690, -727, 8433]] where
 M := ![![![-23020, -520, 1690, -727, 8433]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-23020, -520, 1690, -727, 8433]] ![![1, -2, -2, -1, -1]]
  ![![-192, 202, -61, 66, -67]] where
 M := ![![![-192, 202, -61, 66, -67]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-192, 202, -61, 66, -67]] ![![1, -2, -2, -1, -1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-2346, -884, -2950, 264, -4058]]]
 hmul := by decide  
 g := ![![![![-1173, -442, -1475, 132, -2029]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-319, -197, 42, 10, 143]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-319, -197, 42, 10, 143]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-319, -197, 42, 10, 143], ![286, -490, 342, -252, 955], ![1910, 1437, -397, 34, -1273], ![-1416, 1519, -1175, 917, -3252], ![-1358, -725, 114, 84, 424]]]
  hmulB := by decide  
  f := ![![![675, 625, -488, 274, -999]], ![![-666, -244, 214, -116, 527]], ![![1054, -167, 61, -46, -149]], ![![184, 915, -667, 383, -1188]], ![![-513, 322, -202, 122, -223]]]
  g := ![![![-154, -197, 42, 10, 143], ![-223, -490, 342, -252, 955], ![1061, 1437, -397, 34, -1273], ![612, 1519, -1175, 917, -3252], ![-594, -725, 114, 84, 424]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39105, -86713, 64625, -36810, 120200]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-39105, -86713, 64625, -36810, 120200]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-39105, -86713, 64625, -36810, 120200], ![240400, 162990, -131023, 72900, -282440], ![-564880, -118483, 117570, -61666, 337400], ![217200, -258019, 173207, -102115, 244728], ![394664, 83943, -82979, 43566, -237165]]]
  hmulB := by decide  
  f := ![![![20445, 22009, -8033, 2780, -24408]], ![![-9457, 13123, -9556, 7210, -26576]], ![![-23250, -34021, 14228, -6440, 42328]], ![![66736, -11815, 21379, -21425, 56200]], ![![30744, 29123, -9815, 2732, -30245]]]
  g := ![![![-27214, -86713, 64625, -36810, 120200], ![113152, 162990, -131023, 72900, -282440], ![-227179, -118483, 117570, -61666, 337400], ![42935, -258019, 173207, -102115, 244728], ![158893, 83943, -82979, 43566, -237165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-319, -197, 42, 10, 143]] ![![-319, -197, 42, 10, 143]]
  ![![-82715, 131242, -92894, 69064, -259106]] where
 M := ![![![-82715, 131242, -92894, 69064, -259106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-82715, 131242, -92894, 69064, -259106]] ![![-39105, -86713, 64625, -36810, 120200]]
  ![![11, 3, 1, -2, 2]] where
 M := ![![![11, 3, 1, -2, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![11, 3, 1, -2, 2]] ![![-39105, -86713, 64625, -36810, 120200]]
  ![![81093, 100568, -76996, 43486, -151506]] where
 M := ![![![81093, 100568, -76996, 43486, -151506]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![81093, 100568, -76996, 43486, -151506]] ![![-39105, -86713, 64625, -36810, 120200]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![14150101131, -5455604313, 3115390317, -1946674080, 1938664578]]]
 hmul := by decide  
 g := ![![![![4716700377, -1818534771, 1038463439, -648891360, 646221526]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6363, 3222, -1954, 1194, -1820]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-6363, 3222, -1954, 1194, -1820]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-6363, 3222, -1954, 1194, -1820], ![-3640, -14855, 10896, -6238, 19556], ![39112, 31366, -24805, 13870, -51932], ![-50112, -7998, 8622, -4429, 26832], ![-27192, -21930, 17334, -9694, 36257]]]
  hmulB := by decide  
  f := ![![![-1759, -1342, 394, -38, 1228]], ![![-916, -1539, 700, -326, 2028]], ![![684, 826, -265, 126, -884]], ![![-2112, 1374, -1182, 1043, -3312]], ![![-1883, -1292, 332, 12, 1069]]]
  g := ![![![-1923, 3222, -1954, 1194, -1820], ![-1472, -14855, 10896, -6238, 19556], ![12960, 31366, -24805, 13870, -51932], ![-15888, -7998, 8622, -4429, 26832], ![-9013, -21930, 17334, -9694, 36257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-6363, 3222, -1954, 1194, -1820]] ![![-6363, 3222, -1954, 1194, -1820]]
  ![![-58009447, -99290572, 74755972, -42443384, 142114888]] where
 M := ![![![-58009447, -99290572, 74755972, -42443384, 142114888]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-58009447, -99290572, 74755972, -42443384, 142114888]] ![![-6363, 3222, -1954, 1194, -1820]]
  ![![1916922194717, 855733517970, -725368886790, 397296663522, -1704557755668]] where
 M := ![![![1916922194717, 855733517970, -725368886790, 397296663522, -1704557755668]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![1916922194717, 855733517970, -725368886790, 397296663522, -1704557755668]] ![![-6363, 3222, -1954, 1194, -1820]]
  ![![-17241869740815759, 4915854265828968, -2550130623712376, 1654228916324592, -226103159817712]] where
 M := ![![![-17241869740815759, 4915854265828968, -2550130623712376, 1654228916324592, -226103159817712]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-17241869740815759, 4915854265828968, -2550130623712376, 1654228916324592, -226103159817712]] ![![-6363, 3222, -1954, 1194, -1820]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-84672923654539948715, -216837797145121743410, 160853241219482327510, -91756938970794491590, 296136480518777758580]]]
 hmul := by decide  
 g := ![![![![-16934584730907989743, -43367559429024348682, 32170648243896465502, -18351387794158898318, 59227296103755551716]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![761, 296, 964, -82, 1320]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![761, 296, 964, -82, 1320]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![3, 4, 3, 4, 1]] where
  M :=![![![761, 296, 964, -82, 1320], ![2640, 979, 3354, -302, 4632], ![9264, 3476, 11553, -1046, 15912], ![14592, 5624, 18176, -1593, 24912], ![1640, 656, 2088, -170, 2845]]]
  hmulB := by decide  
  f := ![![![-385, -264, 212, -118, 456]], ![![912, 197, -194, 102, -552]], ![![-1104, 556, -337, 206, -312]], ![![-768, -1384, 1040, -591, 1968]], ![![-445, -608, 463, -262, 901]]]
  g := ![![![-457, -712, -428, -766, 1320], ![-1608, -2507, -1506, -2690, 4632], ![-5496, -8596, -5169, -9242, 15912], ![-8592, -13432, -8080, -14463, 24912], ![-985, -1532, -921, -1650, 2845]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [1, 1, 1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [6, 6, 6, 6], [0, 0, 0, 1], [0, 1]]
 g := ![![[0, 0, 6, 1], []], ![[1], [0, 6, 1]], ![[0, 0, 0, 6], [6, 5, 3, 4, 5, 6]], ![[0, 6, 1, 1, 1, 1], [1, 0, 0, 0, 6, 1]]]
 h' := ![![[0, 0, 1], [0, 0, 0, 1], [0, 1]], ![[6, 6, 6, 6], [0, 1], [0, 0, 1]], ![[0, 0, 0, 1], [0, 0, 1], [6, 6, 6, 6]], ![[0, 1], [6, 6, 6, 6], [0, 0, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 3, 2], []]
 b := ![[], [], [6, 5, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [1, 1, 1, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2773586441, 997034322, 3494351171, -328529134, 4848968923]
  a := ![0, 36, -63, 23, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1681902904, -2628405910, -1578936514, -2817772118, 4848968923]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![385, 264, -212, 118, -456]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![385, 264, -212, 118, -456]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![385, 264, -212, 118, -456], ![-912, -197, 194, -102, 552], ![1104, -556, 337, -206, 312], ![768, 1384, -1040, 591, -1968], ![-776, 384, -232, 142, -211]]]
  hmulB := by decide  
  f := ![![![-761, -296, -964, 82, -1320]], ![![-812, -309, -1030, 90, -1416]], ![![-1867, -708, -2339, 208, -3216]], ![![-2302, -888, -2872, 251, -3936]], ![![-343, -136, -436, 36, -595]]]
  g := ![![![87, 264, -212, 118, -456], ![-206, -197, 194, -102, 552], ![249, -556, 337, -206, 312], ![174, 1384, -1040, 591, -1968], ![-175, 384, -232, 142, -211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![761, 296, 964, -82, 1320]] ![![385, 264, -212, 118, -456]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [10, 9, 5, 2, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 5, 2, 8, 4], [10, 8, 0, 10, 10], [3, 0, 10, 8], [4, 8, 10, 7, 8], [0, 1]]
 g := ![![[6, 3, 0, 8, 1], [1], []], ![[0, 7, 4, 5, 10, 0, 2, 5], [0, 0, 5, 6, 5, 7, 1, 9], [4, 7, 3, 5]], ![[7, 5, 5, 8, 9, 1, 2, 2], [6, 2, 1, 6, 5, 2, 8, 10], [8, 2, 3, 1]], ![[10, 7, 7, 0, 5, 8, 8], [2, 3, 9, 9, 10, 1, 10], [4, 9]], ![[2, 9, 3, 6, 4, 8, 7, 6], [0, 4, 3, 10, 9, 4, 6, 7], [7, 4, 0, 9]]]
 h' := ![![[6, 5, 2, 8, 4], [1, 2, 6, 9, 1], [0, 0, 1], [0, 1]], ![[10, 8, 0, 10, 10], [8, 0, 1, 7, 9], [7, 9, 2, 7, 7], [6, 5, 2, 8, 4]], ![[3, 0, 10, 8], [2, 10, 9, 7, 8], [9, 2, 9, 5, 10], [10, 8, 0, 10, 10]], ![[4, 8, 10, 7, 8], [3, 2, 2, 9, 1], [2, 6, 3, 6, 9], [3, 0, 10, 8]], ![[0, 1], [4, 8, 4, 1, 3], [1, 5, 7, 4, 7], [4, 8, 10, 7, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 1, 9, 6], [], [], []]
 b := ![[], [10, 4, 9, 5, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [10, 9, 5, 2, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-991029913255226603, -374333775527188521, -1249207271876815911, 110906881493885851, -1719195605802174192]
  a := ![3, 431, -805, 243, -1672]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-90093628477747873, -34030343229744411, -113564297443346901, 10082443772171441, -156290509618379472]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4065, -1484, -5097, 474, -7055]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-4065, -1484, -5097, 474, -7055]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![1, 6, 3, 8, 1]] where
  M :=![![![-4065, -1484, -5097, 474, -7055], ![-14110, -5425, -17435, 1546, -23899], ![-47798, -18468, -60116, 5198, -82391], ![-75336, -28242, -95514, 8507, -131652], ![-8874, -3116, -11165, 1080, -15556]]]
  hmulB := by decide  
  f := ![![![-1661, 948, -587, 356, -607]], ![![-1214, -4133, 3043, -1740, 5509]], ![![11018, 8500, -6746, 3768, -14215]], ![![-13608, -1878, 2130, -1081, 6924]], ![![-7109, -1486, 1476, -774, 4240]]]
  g := ![![![230, 3142, 1236, 4378, -7055], ![753, 10613, 4174, 14826, -23899], ![2661, 36606, 14389, 51102, -82391], ![4332, 58590, 23034, 81671, -131652], ![514, 6940, 2731, 9656, -15556]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [4, 0, 10, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12, 10, 7], [9, 9, 11, 12], [9, 4, 5, 7], [0, 1]]
 g := ![![[9, 0, 12, 1], [2, 8, 1], []], ![[5, 0, 0, 0, 0, 7], [4, 9, 10], [3, 2, 12, 8, 2, 5]], ![[10, 8, 12, 4, 4, 4], [5, 1, 10], [1, 2, 0, 4, 12, 12]], ![[12, 4, 4, 11, 1, 7], [10], [10, 12, 5, 9, 8, 5]]]
 h' := ![![[3, 12, 10, 7], [5, 7, 2, 1], [0, 0, 0, 1], [0, 1]], ![[9, 9, 11, 12], [1, 6, 12, 1], [2, 4, 6, 6], [3, 12, 10, 7]], ![[9, 4, 5, 7], [2, 0, 7, 10], [10, 8, 1, 6], [9, 9, 11, 12]], ![[0, 1], [12, 0, 5, 1], [0, 1, 6], [9, 4, 5, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 10, 9], []]
 b := ![[], [], [8, 0, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [4, 0, 10, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3916741874, 1430979456, 4999263768, -456008856, 6922237458]
  a := ![1, 34, -62, 20, -129]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-231191968, -3084803484, -1212880662, -4294916040, 6922237458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1661, -948, 587, -356, 607]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![1661, -948, 587, -356, 607]] 
 ![![13, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1661, -948, 587, -356, 607], ![1214, 4133, -3043, 1740, -5509], ![-11018, -8500, 6746, -3768, 14215], ![13608, 1878, -2130, 1081, -6924], ![7662, 5944, -4715, 2634, -9926]]]
  hmulB := by decide  
  f := ![![![4065, 1484, 5097, -474, 7055]], ![![4525, 1673, 5654, -520, 7808]], ![![6491, 2448, 8153, -728, 11222]], ![![8922, 3314, 11268, -1019, 15554]], ![![1308, 468, 1643, -156, 2282]]]
  g := ![![![704, -948, 587, -356, 607], ![-1788, 4133, -3043, 1740, -5509], ![2386, -8500, 6746, -3768, 14215], ![1166, 1878, -2130, 1081, -6924], ![-1675, 5944, -4715, 2634, -9926]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-4065, -1484, -5097, 474, -7055]] ![![1661, -948, 587, -356, 607]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -35, 17, -12, 52]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-3, -35, 17, -12, 52]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![8, 14, 16, 1, 0], ![8, 14, 5, 0, 1]] where
  M :=![![![-3, -35, 17, -12, 52], ![104, 46, -11, -10, -28], ![-56, 191, -148, 84, -380], ![-432, -229, -7, 27, 72], ![-28, -151, 75, -48, 223]]]
  hmulB := by decide  
  f := ![![![5, -63, 45, -26, 76]], ![![152, 156, -121, 68, -244]], ![![-488, -201, 172, -94, 412]], ![![-312, -97, 87, -47, 224]], ![![4, 48, -35, 20, -61]]]
  g := ![![![-19, -35, -3, -12, 52], ![24, 34, 17, -10, -28], ![136, 255, 24, 84, -380], ![-72, -95, -47, 27, 72], ![-84, -153, -16, -48, 223]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [14, 5, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 5, 13], [2, 11, 4], [0, 1]]
 g := ![![[7, 16, 4], [12, 9], [6, 1], []], ![[15, 11, 8, 4], [8, 15], [4, 2], [5, 16]], ![[10, 15, 16, 16], [8, 16], [13, 8], [14, 16]]]
 h' := ![![[4, 5, 13], [3, 15, 2], [1, 7, 14], [0, 0, 1], [0, 1]], ![[2, 11, 4], [6, 14, 13], [4, 16, 7], [14, 12, 11], [4, 5, 13]], ![[0, 1], [6, 5, 2], [13, 11, 13], [12, 5, 5], [2, 11, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 4], []]
 b := ![[], [0, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [14, 5, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![910827985, 275578408, 1202407756, -127534747, 1715724939]
  a := ![1, -178, 320, -109, 665]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-693805503, -1291710840, -313862411, -127534747, 1715724939]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 63, -45, 26, -76]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-5, 63, -45, 26, -76]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![11, 2, 1, 0, 0], ![6, 4, 0, 1, 0], ![5, 13, 0, 0, 1]] where
  M :=![![![-5, 63, -45, 26, -76], ![-152, -156, 121, -68, 244], ![488, 201, -172, 94, -412], ![-336, 113, -61, 39, -24], ![-340, -141, 121, -66, 289]]]
  hmulB := by decide  
  f := ![![![3, 35, -17, 12, -52]], ![![-104, -46, 11, 10, 28]], ![![-7, 6, -1, 4, -8]], ![![2, 15, -3, 5, -16]], ![![-77, -16, -1, 14, -7]]]
  g := ![![![42, 61, -45, 26, -76], ![-135, -194, 121, -68, 244], ![228, 325, -172, 94, -412], ![13, 23, -61, 39, -24], ![-160, -228, 121, -66, 289]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[3, 8], [4], [2], [1]], ![[0, 9], [4], [2], [1]]]
 h' := ![![[6, 16], [4, 5], [8, 2], [2, 6], [0, 1]], ![[0, 1], [0, 12], [3, 15], [4, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [15, 11, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44933, 14960, 20172, -2916, 26720]
  a := ![-1, 70, -111, 53, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17239, -21240, 20172, -2916, 26720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-3, -35, 17, -12, 52]] ![![-5, 63, -45, 26, -76]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 199, -146, 84, -271]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![85, 199, -146, 84, -271]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![6, 8, 4, 1, 0], ![4, 11, 9, 0, 1]] where
  M :=![![![85, 199, -146, 84, -271], ![-542, -378, 310, -170, 661], ![1322, 297, -265, 148, -775], ![-504, 587, -355, 225, -492], ![-910, -205, 204, -106, 568]]]
  hmulB := by decide  
  f := ![![![63, 165, -80, 44, -233]], ![![-466, -92, -50, 86, -109]], ![![-218, -1009, 527, -312, 1519]], ![![-130, -171, 69, -29, 206]], ![![-342, -460, 187, -80, 558]]]
  g := ![![![35, 132, 103, 84, -271], ![-114, -331, -261, -170, 661], ![186, 402, 322, 148, -775], ![6, 221, 167, 225, -492], ![-134, -295, -236, -106, 568]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [13, 15, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 17, 2], [15, 1, 17], [0, 1]]
 g := ![![[18, 2, 16], [9, 3, 5], [9, 1], []], ![[16, 9, 18, 18], [3, 12, 8, 8], [6, 1], [9, 4]], ![[1, 2, 12, 17], [14, 13, 18, 16], [11, 4], [13, 4]]]
 h' := ![![[13, 17, 2], [16, 6, 4], [16, 4, 9], [0, 0, 1], [0, 1]], ![[15, 1, 17], [17, 1, 16], [4, 7, 17], [14, 8, 1], [13, 17, 2]], ![[0, 1], [7, 12, 18], [10, 8, 12], [18, 11, 17], [15, 1, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 16], []]
 b := ![[], [8, 15, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [13, 15, 10, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1421939, 145330, -496190, 570858, -1841712]
  a := ![0, -42, 54, -42, 112]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![132619, 833542, 726094, 570858, -1841712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -96, 69, -40, 123]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-19, -96, 69, -40, 123]] 
 ![![19, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-19, -96, 69, -40, 123], ![246, 207, -167, 92, -345], ![-690, -220, 184, -104, 483], ![360, -234, 126, -85, 132], ![474, 152, -139, 74, -352]]]
  hmulB := by decide  
  f := ![![![-1, 1080, -615, 394, -1755]], ![![-185, 199, -154, 120, -426]], ![![71, 412, -219, 132, -630]], ![![663, 546, -165, 29, -519]], ![![31, 532, -296, 186, -847]]]
  g := ![![![-49, -96, 69, -40, 123], ![149, 207, -167, 92, -345], ![-215, -220, 184, -104, 483], ![-27, -234, 126, -85, 132], ![161, 152, -139, 74, -352]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 11, 84, -4, 119]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![33, 11, 84, -4, 119]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![33, 11, 84, -4, 119], ![238, 26, 324, -50, 499], ![998, 413, 973, -100, 1295], ![1176, 675, 1437, -47, 1788], ![6, 7, 178, 2, 250]]]
  hmulB := by decide  
  f := ![![![-2653, -6063, 4514, -2572, 8377]], ![![44, -1310, 940, -542, 1601]], ![![-2368, -1089, 919, -504, 2145]], ![![-574, -4131, 3005, -1725, 5290]], ![![1180, -319, 162, -106, -6]]]
  g := ![![![-21, 11, 84, -4, 119], ![-56, 26, 324, -50, 499], ![-264, 413, 973, -100, 1295], ![-466, 675, 1437, -47, 1788], ![-48, 7, 178, 2, 250]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![85, 199, -146, 84, -271]] ![![-19, -96, 69, -40, 123]]
  ![![49865, 4305, -5979, 2898, -22238]] where
 M := ![![![49865, 4305, -5979, 2898, -22238]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![49865, 4305, -5979, 2898, -22238]] ![![33, 11, 84, -4, 119]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-22287, -8398, -28025, 2508, -38551]]]
 hmul := by decide  
 g := ![![![![-1173, -442, -1475, 132, -2029]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![497, 41, -58, 28, -219]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![497, 41, -58, 28, -219]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![18, 10, 1, 13, 1]] where
  M :=![![![497, 41, -58, 28, -219], ![-438, 462, -308, 182, -423], ![-846, -1597, 1195, -680, 2253], ![2472, 1197, -1005, 551, -2316], ![582, 1113, -834, 474, -1570]]]
  hmulB := by decide  
  f := ![![![-17, -1, -4, 4, -9]], ![![-18, -40, 16, -10, 51]], ![![102, 17, 3, -20, 15]], ![![24, 135, -87, 43, -228]], ![![-6, 59, -46, 23, -115]]]
  g := ![![![193, 97, 7, 125, -219], ![312, 204, 5, 247, -423], ![-1800, -1049, -46, -1303, 2253], ![1920, 1059, 57, 1333, -2316], ![1254, 731, 32, 908, -1570]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [13, 6, 22, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 6, 14, 4], [22, 4, 19, 19], [16, 12, 13], [0, 1]]
 g := ![![[3, 2, 14, 16], [14, 11, 14, 4], [22, 1], []], ![[7, 11, 18, 18, 4, 4], [10, 6, 18, 18, 19, 3], [18, 10, 0, 6, 19, 2], [3, 4, 16]], ![[14, 17, 22, 6, 1, 20], [21, 4, 20, 19, 1, 11], [13, 17, 10, 9, 19, 5], [7, 16, 16]], ![[18, 0, 16, 18, 9], [16, 8, 22, 3, 13], [14, 8, 11, 8, 3], [8]]]
 h' := ![![[7, 6, 14, 4], [2, 11, 21, 4], [13, 16, 16, 2], [0, 0, 1], [0, 1]], ![[22, 4, 19, 19], [7, 17, 18, 22], [6, 22, 0, 15], [10, 14, 3, 14], [7, 6, 14, 4]], ![[16, 12, 13], [20, 20, 14, 8], [11, 13, 16, 7], [2, 18, 3, 4], [22, 4, 19, 19]], ![[0, 1], [12, 21, 16, 12], [10, 18, 14, 22], [14, 14, 16, 5], [16, 12, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 6, 3], []]
 b := ![[], [], [7, 16, 13, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [13, 6, 22, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6744361031, 2630920398, 7852818671, -703661112, 10702636707]
  a := ![13, 62, -101, 45, -211]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8082743465, -4538932464, -123905132, -6079910361, 10702636707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -1, -4, 4, -9]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-17, -1, -4, 4, -9]] 
 ![![23, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-17, -1, -4, 4, -9], ![-18, -40, 16, -10, 51], ![102, 17, 3, -20, 15], ![24, 135, -87, 43, -228], ![-66, 3, -18, 18, -44]]]
  hmulB := by decide  
  f := ![![![497, 41, -58, 28, -219]], ![![89, 29, -26, 14, -66]], ![![417, -32, -1, -4, -102]], ![![410, 77, -79, 41, -234]], ![![263, 68, -64, 34, -173]]]
  g := ![![![5, -1, -4, 4, -9], ![-25, -40, 16, -10, 51], ![3, 17, 3, -20, 15], ![134, 135, -87, 43, -228], ![23, 3, -18, 18, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![497, 41, -58, 28, -219]] ![![-17, -1, -4, 4, -9]]
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


lemma PB251I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB251I0 : PrimesBelowBoundCertificateInterval O 1 23 251 where
  m := 9
  g := ![5, 5, 5, 2, 1, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB251I0_primes
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
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![6859, 19, 19]
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I13N1, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [], [I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
