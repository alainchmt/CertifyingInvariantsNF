
import IdealArithmetic.Examples.NF5_1_729000000_1.RI5_1_729000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20411, -10633, -1744, 12976, 9396]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![20411, -10633, -1744, 12976, 9396]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![22, 28, 1, 0, 0], ![22, 25, 0, 1, 0], ![26, 18, 0, 0, 1]] where
  M :=![![![20411, -10633, -1744, 12976, 9396], ![112752, -58737, -9634, 71680, 51904], ![311424, -162233, -26609, 197982, 143360], ![803784, -418722, -68678, 510991, 370012], ![1209372, -630009, -103332, 768836, 556719]]]
  hmulB := by decide  
  f := ![![![-185, 11, 34, -4, -4]], ![![-48, -115, 14, 36, -16]], ![![-190, -99, 33, 30, -16]], ![![-166, -109, 48, 31, -20]], ![![-206, -41, 22, 16, -9]]]
  g := ![![![-16241, -15701, -1744, 12976, 9396], ![-89716, -86733, -9634, 71680, 51904], ![-247798, -239559, -26609, 197982, 143360], ![-639566, -618301, -68678, 510991, 370012], ![-962290, -930295, -103332, 768836, 556719]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [16, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 28], [0, 1]]
 g := ![![[2, 20], [16], [22, 20], [26, 1]], ![[0, 9], [16], [20, 9], [23, 28]]]
 h' := ![![[26, 28], [21, 7], [25, 4], [19, 22], [0, 1]], ![[0, 1], [0, 22], [13, 25], [11, 7], [26, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [28, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [16, 3, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9082, -3734, -2044, 6519, 4598]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7204, -6629, -2044, 6519, 4598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-311237, 444682, -307646, -118078, 121494]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-311237, 444682, -307646, -118078, 121494]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![25, 6, 1, 0, 0], ![24, 6, 0, 1, 0], ![10, 6, 0, 0, 1]] where
  M :=![![![-311237, 444682, -307646, -118078, 121494], ![1457928, -2191473, 1611496, 356660, -472312], ![-2833872, 4489088, -3492757, -277752, 713320], ![3550956, -6268590, 5387732, -817807, -319348], ![-3103944, 6044256, -5596866, 1737964, -224991]]]
  hmulB := by decide  
  f := ![![![-5779777, 3011770, 493010, -3676574, -2661986]], ![![-31943832, 16641931, 2728744, -20309868, -14706296]], ![![-14634317, 7624588, 1249549, -9305862, -6738178]], ![![-19245660, 10026756, 1643604, -12237303, -8860868]], ![![-20418170, 10637142, 1744186, -12981648, -9399971]]]
  g := ![![![310305, 78278, -307646, -118078, 121494], ![-1471248, -385053, 1611496, 356660, -472312], ![2897169, 787318, -3492757, -277752, 713320], ![-3735224, -1095588, 5387732, -817807, -319348], ![3357120, 1053366, -5596866, 1737964, -224991]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [5, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28], [0, 1]]
 g := ![![[10, 6], [16], [15, 1], [8, 1]], ![[0, 23], [16], [23, 28], [16, 28]]]
 h' := ![![[8, 28], [6, 21], [12, 4], [18, 1], [0, 1]], ![[0, 1], [0, 8], [15, 25], [26, 28], [8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [16, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [5, 21, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-62293, 203317, -190550, 11788, 138094]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![104745, 15425, -190550, 11788, 138094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19211, -5875, -6476, 370, 1650]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![19211, -5875, -6476, 370, 1650]] 
 ![![29, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![19211, -5875, -6476, 370, 1650], ![19800, -4675, -5890, 248, 1480], ![8880, -937, -1963, 30, 496], ![-6924, 3098, 2970, -103, -680], ![-7500, 2699, 2884, 16, -595]]]
  hmulB := by decide  
  f := ![![![-13169, 27225, -26230, 10238, -2366]], ![![-9607, 18082, -16340, 4246, -138]], ![![4840, -2785, -1705, 9318, -5576]], ![![-36316, 55472, -41530, -7283, 10976]], ![![32488, -40761, 23226, 22572, -17731]]]
  g := ![![![4956, -5875, -6476, 370, 1650], ![4213, -4675, -5890, 248, 1480], ![1103, -937, -1963, 30, 496], ![-2562, 3098, 2970, -103, -680], ![-2421, 2699, 2884, 16, -595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![20411, -10633, -1744, 12976, 9396]] ![![-311237, 444682, -307646, -118078, 121494]]
  ![![13169, -27225, 26230, -10238, 2366]] where
 M := ![![![13169, -27225, 26230, -10238, 2366]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![13169, -27225, 26230, -10238, 2366]] ![![19211, -5875, -6476, 370, 1650]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8093, -8517, 3214, 8588, -5878]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![8093, -8517, 3214, 8588, -5878]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![12, 26, 1, 1, 0], ![25, 14, 12, 0, 1]] where
  M :=![![![8093, -8517, 3214, 8588, -5878], ![-70536, 93141, -57722, -40596, 34352], ![206112, -293661, 202441, 79686, -81192], ![-451884, 683948, -506870, -102029, 142196], ![564912, -875143, 665266, 91098, -159801]]]
  hmulB := by decide  
  f := ![![![-85405, 46457, 40220, -3820, -10706]], ![![-128472, 64941, 57730, -5208, -15280]], ![![-91680, 43461, 39589, -3390, -10416]], ![![-143712, 73703, 65173, -5939, -17268]], ![![-161707, 83194, 73484, -6706, -19471]]]
  g := ![![![1677, -4823, 2102, 8588, -5878], ![-14264, 21539, -13850, -40596, 34352], ![41280, -39639, 35389, 79686, -81192], ![-89756, 43418, -68103, -102029, 142196], ![111831, -32467, 80380, 91098, -159801]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [4, 16, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 15, 21], [7, 15, 10], [0, 1]]
 g := ![![[19, 26, 19], [3, 26, 19], [20, 5, 18], [1]], ![[30, 7, 20, 29], [29, 18, 20, 29], [11, 10, 19, 6], [30, 4, 30, 23]], ![[10, 26, 13, 5], [24, 11, 13, 5], [4, 23, 8, 7], [9, 27, 11, 8]]]
 h' := ![![[17, 15, 21], [19, 17, 22], [13, 17, 22], [27, 15, 24], [0, 1]], ![[7, 15, 10], [23, 4, 5], [17, 4, 5], [19, 16, 24], [17, 15, 21]], ![[0, 1], [22, 10, 4], [16, 10, 4], [28, 0, 14], [7, 15, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 24], []]
 b := ![[], [18, 13, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [4, 16, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1827752, 942763, 168112, -1167881, -846296]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1075620, 1392123, 370695, -1167881, -846296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3181, -5536, 4712, -522, -404]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![3181, -5536, 4712, -522, -404]] 
 ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![3181, -5536, 4712, -522, -404], ![-4848, 11293, -11644, 6192, -2088], ![-12528, 9430, 925, -19996, 12384], ![76728, -99556, 60016, 47365, -38948], ![-120684, 164044, -106124, -60982, 54601]]]
  hmulB := by decide  
  f := ![![![-32742920549, 17057056696, 2797652184, -20815714706, -15072793292]], ![![-11115745879, 5790622965, 949762276, -7066632758, -5116994364]], ![![-19284061761, 10045815378, 1647687397, -12259490638, -8877176252]], ![![-63774486303, 33222602332, 5449081144, -40543466801, -29357785840]], ![![-91099960557, 47457501228, 7783850660, -57915138804, -41936725595]]]
  g := ![![![1245, -5536, 4712, -522, -404], ![-3227, 11293, -11644, 6192, -2088], ![745, 9430, 925, -19996, 12384], ![14561, -99556, 60016, 47365, -38948], ![-26327, 164044, -106124, -60982, 54601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-599, 72152, 40610, -7764, -12014]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-599, 72152, 40610, -7764, -12014]] 
 ![![31, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-599, 72152, 40610, -7764, -12014], ![-144168, 156637, 111776, -14892, -31056], ![-186336, 139720, 109417, -12448, -29784], ![-106620, 34586, 36712, -2273, -9368], ![-49188, -1310, 7882, 842, -1637]]]
  hmulB := by decide  
  f := ![![![-4478107041857, 2332819565836, 382622739318, -2846874897728, -2061440477498]], ![![-4264898539824, 2221750991437, 364405572928, -2711331480220, -1963292614544]], ![![-5382043627946, 2803715177440, 459857760613, -3421536099888, -2477556360892]], ![![-6121968334089, 3189170642350, 523079120734, -3891929739977, -2818171430002]], ![![-10292519971056, 5361772674438, 879423414626, -6543281897034, -4738032629741]]]
  g := ![![![-79297, 72152, 40610, -7764, -12014], ![-191780, 156637, 111776, -14892, -31056], ![-179098, 139720, 109417, -12448, -29784], ![-52423, 34586, 36712, -2273, -9368], ![-5614, -1310, 7882, 842, -1637]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![8093, -8517, 3214, 8588, -5878]] ![![3181, -5536, 4712, -522, -404]]
  ![![1395089873, -1929914869, 1279493394, 643993862, -601114002]] where
 M := ![![![1395089873, -1929914869, 1279493394, 643993862, -601114002]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![1395089873, -1929914869, 1279493394, 643993862, -601114002]] ![![-599, 72152, 40610, -7764, -12014]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-114403100383, 193897244575, -160913865536, 11744648654, 17484312604]]]
 hmul := by decide  
 g := ![![![![-3690422593, 6254749825, -5190769856, 378859634, 564010084]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2843, -5014, 4306, -646, -260]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![2843, -5014, 4306, -646, -260]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![6, 8, 1, 0, 0], ![26, 32, 0, 1, 0], ![18, 31, 0, 0, 1]] where
  M :=![![![2843, -5014, 4306, -646, -260], ![-3120, 8717, -9776, 6532, -2584], ![-15504, 14296, -2983, -20112, 13064], ![79944, -105566, 65424, 46007, -38932], ![-122988, 169198, -111322, -58474, 53831]]]
  hmulB := by decide  
  f := ![![![3743, -5058, -3494, 438, 940]], ![![11280, -9215, -7232, 532, 1752]], ![![3330, -3004, -2299, 180, 560]], ![![12406, -11506, -8740, 707, 2140]], ![![11154, -10087, -7742, 562, 1855]]]
  g := ![![![-41, -290, 4306, -646, -260], ![-1832, -1135, -9776, 6532, -2584], ![7842, 7480, -2983, -20112, 13064], ![-21838, -24170, 65424, 46007, -38932], ![29630, 34113, -111322, -58474, 53831]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [6, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36], [0, 1]]
 g := ![![[17, 9], [4], [6, 27], [7], [1]], ![[24, 28], [4], [27, 10], [7], [1]]]
 h' := ![![[9, 36], [14, 3], [1, 2], [31, 29], [31, 9], [0, 1]], ![[0, 1], [4, 34], [19, 35], [33, 8], [1, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [6, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [6, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50405, -27355, -1147, 31959, 23227]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32209, -47592, -1147, 31959, 23227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![190695167, -197684834, -142562808, 18644468, 39513850]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![190695167, -197684834, -142562808, 18644468, 39513850]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![1, 33, 1, 0, 0], ![4, 22, 0, 1, 0], ![8, 25, 0, 0, 1]] where
  M :=![![![190695167, -197684834, -142562808, 18644468, 39513850], ![474166200, -349231055, -274603204, 30985184, 74577872], ![447467232, -279411614, -231060495, 23708284, 61970368], ![134739108, -34309844, -41877560, 1328385, 10127632], ![17033412, 30938312, 14079872, -4321966, -4975367]]]
  hmulB := by decide  
  f := ![![![-3581431117, 8136325718, -8283947712, 4110755008, -1297059742]], ![![-15564716904, 10623788349, 2862902452, -26944373360, 16443020032]], ![![-11312404561, 6351066229, 4233676621, -22065367116, 13173887962]], ![![-18170259952, 19203675754, -7343993376, -19134102495, 13124504240]], ![![715876012, -8418150295, 12326839508, -13124989586, 6321744353]]]
  g := ![![![-1552181, 84023332, -142562808, 18644468, 39513850], ![762316, 166663617, -274603204, 30985184, 74577872], ![2376531, 142560629, -231060495, 23708284, 61970368], ![2440056, 28790118, -41877560, 1328385, 10127632], ![1622820, -5790001, 14079872, -4321966, -4975367]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [18, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 36], [0, 1]]
 g := ![![[3, 12], [25], [32, 7], [30], [1]], ![[21, 25], [25], [24, 30], [30], [1]]]
 h' := ![![[20, 36], [28, 7], [16, 32], [6, 28], [19, 20], [0, 1]], ![[0, 1], [20, 30], [27, 5], [11, 9], [12, 17], [20, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [33, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [18, 17, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6208, 26334, -27966, 7098, 13314]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3058, 12438, -27966, 7098, 13314]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![188063, -303652, 240814, 8026, -42210]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![188063, -303652, 240814, 8026, -42210]] 
 ![![37, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![188063, -303652, 240814, 8026, -42210], ![-506520, 909239, -792196, 143948, 32104], ![192624, -681982, 829499, -663780, 287896], ![1980636, -2190766, 953688, 1909109, -1343612], ![-3681264, 4587458, -2582702, -2614244, 2037005]]]
  hmulB := by decide  
  f := ![![![-783085, -314928, -47282, 44698, 24902]], ![![-605693, -274265, -53806, 37862, 24350]], ![![-76829, -70642, -26983, 8622, 9022]], ![![-478044, -214894, -41648, 29613, 18900]], ![![-743220, -309258, -50798, 43372, 25261]]]
  g := ![![![246401, -303652, 240814, 8026, -42210], ![-743891, 909239, -792196, 143948, 32104], ![578083, -681982, 829499, -663780, 287896], ![1710698, -2190766, 953688, 1909109, -1343612], ![-3632280, 4587458, -2582702, -2614244, 2037005]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![2843, -5014, 4306, -646, -260]] ![![190695167, -197684834, -142562808, 18644468, 39513850]]
  ![![783085, 314928, 47282, -44698, -24902]] where
 M := ![![![783085, 314928, 47282, -44698, -24902]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![783085, 314928, 47282, -44698, -24902]] ![![188063, -303652, 240814, 8026, -42210]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [33, 10, 28, 4, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 1, 18, 40, 8], [24, 39, 4, 5, 20], [24, 14, 26, 6, 8], [1, 27, 34, 31, 5], [0, 1]]
 g := ![![[40, 9, 6, 17, 10], [26, 30, 13, 31], [19, 16], [1], []], ![[5, 33, 33, 16, 28, 4, 10, 23], [39, 1, 27, 1], [38, 17, 2, 21], [18, 20, 32, 12, 38, 7, 2, 23], [15, 33, 25, 23]], ![[17, 14, 1, 12, 3, 36, 6, 25], [36, 38, 0, 2], [5, 32], [12, 5, 20, 32, 6, 19, 21, 21], [14, 20, 36, 31]], ![[8, 35, 1, 8, 21, 40, 10, 8], [32, 22, 38, 1], [6, 30, 40, 8], [34, 2, 4, 2, 30, 22, 28, 10], [0, 32, 14, 23]], ![[32, 23, 23, 19, 10, 22, 19, 10], [39, 27, 13, 36], [0, 24, 6, 25], [23, 29, 32, 2, 36, 32, 40, 23], [28, 12, 23, 25]]]
 h' := ![![[33, 1, 18, 40, 8], [1, 16, 19, 11, 25], [11, 24, 26, 13, 21], [8, 31, 13, 37], [0, 0, 1], [0, 1]], ![[24, 39, 4, 5, 20], [24, 20, 14, 17, 7], [9, 36, 19, 34, 1], [19, 16, 1, 17, 29], [20, 16, 24, 27, 34], [33, 1, 18, 40, 8]], ![[24, 14, 26, 6, 8], [3, 16, 34, 30, 27], [17, 19, 30, 0, 24], [31, 36, 28, 14], [32, 6, 15, 29, 9], [24, 39, 4, 5, 20]], ![[1, 27, 34, 31, 5], [33, 33, 14, 10, 40], [8, 29, 17, 19, 1], [40, 14, 36, 38, 7], [2, 26, 6, 0, 27], [24, 14, 26, 6, 8]], ![[0, 1], [21, 38, 1, 14, 24], [18, 15, 31, 16, 35], [10, 26, 4, 17, 5], [20, 34, 36, 26, 12], [1, 27, 34, 31, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 15, 32, 24], [], [], []]
 b := ![[], [8, 12, 25, 11, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [33, 10, 28, 4, 0, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3127414513857, -5846576161944, 5255806184668, -1306330047844, 4791151924]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![76278402777, -142599418584, 128190394748, -31861708484, 116857364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [17, 33, 37, 11, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 7, 0, 39, 40], [13, 41, 17, 30, 4], [38, 28, 34, 32, 21], [39, 9, 35, 28, 21], [0, 1]]
 g := ![![[16, 19, 36, 32, 38], [37, 15, 15, 37, 25], [17, 36, 37, 14], [1], []], ![[16, 42, 7, 41, 11, 39, 25, 36], [37, 24, 23, 13, 31, 7, 36, 23], [28, 40, 25, 4], [40, 24, 15, 34, 9, 0, 4, 25], [42, 18, 20, 9]], ![[15, 3, 30, 19, 14, 26, 23, 31], [30, 14, 8, 23, 21, 29, 20, 40], [22, 13, 19, 23], [14, 21, 31, 38, 14, 35, 30, 11], [7, 17, 37, 16]], ![[20, 11, 33, 35, 12, 33, 22, 4], [31, 28, 30, 2, 9, 32, 6, 35], [22, 12, 11, 41], [21, 16, 6, 36, 8, 33, 15, 21], [21, 10, 30, 11]], ![[8, 39, 31, 27, 30, 42, 3, 25], [22, 37, 17, 40, 5, 16, 27, 4], [11, 27, 24, 24], [21, 24, 33, 6, 32, 19, 20, 6], [10, 30, 34, 11]]]
 h' := ![![[29, 7, 0, 39, 40], [16, 29, 31, 42, 9], [0, 35, 30, 10, 38], [26, 10, 6, 32, 33], [0, 0, 1], [0, 1]], ![[13, 41, 17, 30, 4], [34, 24, 7, 13, 26], [22, 41, 18, 27, 35], [38, 29, 2, 16, 41], [41, 4, 12, 20, 7], [29, 7, 0, 39, 40]], ![[38, 28, 34, 32, 21], [7, 7, 1, 2, 13], [28, 26, 41, 42, 28], [12, 28, 11, 11, 25], [7, 30, 29, 18, 11], [13, 41, 17, 30, 4]], ![[39, 9, 35, 28, 21], [6, 14, 9, 25, 32], [17, 0, 37, 4, 39], [41, 4, 11, 36, 16], [12, 18, 31, 21, 42], [38, 28, 34, 32, 21]], ![[0, 1], [40, 12, 38, 4, 6], [2, 27, 3, 3, 32], [24, 15, 13, 34, 14], [18, 34, 13, 27, 26], [39, 9, 35, 28, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 9, 16, 35], [], [], []]
 b := ![[], [25, 19, 30, 30, 26], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [17, 33, 37, 11, 10, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4926964871501, 2000039306344, 1072487827770, -3218346795115, -2887425695626]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-114580578407, 46512542008, 24941577390, -74845274305, -67149434782]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18055057, -8958632, -8018196, 714909, 2120112]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![18055057, -8958632, -8018196, 714909, 2120112]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![12, 32, 1, 0, 0], ![39, 40, 0, 1, 0], ![1, 9, 0, 0, 1]] where
  M :=![![![18055057, -8958632, -8018196, 714909, 2120112], ![25441344, -11854553, -10866634, 924504, 2859636], ![17157816, -7516139, -7059785, 571910, 1849008], ![-1626624, 1378658, 1043284, -126005, -285998], ![-4999758, 2746864, 2369758, -226651, -631319]]]
  hmulB := by decide  
  f := ![![![870995, -1464206, 1206232, -67663, -143834]], ![![-1726008, 3524075, -3368422, 1261792, -270652]], ![![-987324, 2029853, -1948803, 747114, -167304]], ![![-405681, 1357760, -1623580, 1255686, -536220]], ![![-870473, 1385963, -1083956, -72524, 212805]]]
  g := ![![![1793018, 4254176, -8018196, 714909, 2120112], ![2487780, 5811933, -10866634, 924504, 2859636], ![1653654, 3805947, -7059785, 571910, 1849008], ![-190337, -518984, 1043284, -126005, -285998], ![-509918, -1241223, 2369758, -226651, -631319]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [8, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 46], [0, 1]]
 g := ![![[23, 6], [5, 34], [28, 7], [0, 16], [1]], ![[0, 41], [0, 13], [9, 40], [17, 31], [1]]]
 h' := ![![[4, 46], [7, 10], [11, 9], [0, 30], [39, 4], [0, 1]], ![[0, 1], [0, 37], [0, 38], [26, 17], [8, 43], [4, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [35, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [8, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3112, 4870, -3782, -773, 1402]
  a := ![-1, -1, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1511, 3068, -3782, -773, 1402]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11915047, -6206848, -1018896, 7573275, 5484070]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![11915047, -6206848, -1018896, 7573275, 5484070]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![30, 37, 1, 0, 0], ![18, 33, 0, 1, 0], ![37, 24, 0, 0, 1]] where
  M :=![![![11915047, -6206848, -1018896, 7573275, 5484070], ![65808840, -34282069, -5623966, 41834768, 30293100], ![181758600, -94684845, -15530637, 115548434, 83669536], ![469112796, -244378998, -40082224, 298230123, 215950318], ![705825834, -367692058, -60307578, 448716357, 324918341]]]
  hmulB := by decide  
  f := ![![![-1077571, 1673986, -1276300, -165349, 300672]], ![![3608064, -5991961, 4881358, -147224, -661396]], ![![2068146, -3483996, 2875611, -173872, -335020]], ![![2044662, -3538717, 2991090, -342689, -247058]], ![![1220041, -1970708, 1563506, 50630, -273125]]]
  g := ![![![-6313779, -7447733, -1018896, 7573275, 5484070], ![-34879632, -41144193, -5623966, 41834768, 30293100], ![-96339722, -113642946, -15530637, 115548434, 83669536], ![-248653712, -293313583, -40082224, 298230123, 215950318], ![-374123827, -441318971, -60307578, 448716357, 324918341]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [5, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 46], [0, 1]]
 g := ![![[31, 3], [46, 17], [20, 21], [28, 8], [1]], ![[36, 44], [43, 30], [8, 26], [10, 39], [1]]]
 h' := ![![[33, 46], [5, 12], [41, 39], [1, 16], [42, 33], [0, 1]], ![[0, 1], [25, 35], [12, 8], [12, 31], [3, 14], [33, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [9, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [5, 14, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182, 3053, -3758, 1467, 2431]
  a := ![3, 3, 0, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-73, 752, -3758, 1467, 2431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-597214555, 220717007, 222767782, -15499391, -57561688]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-597214555, 220717007, 222767782, -15499391, -57561688]] 
 ![![47, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-597214555, 220717007, 222767782, -15499391, -57561688], ![-690740256, 227733013, 242186044, -14957940, -61997564], ![-371985384, 101751556, 118695825, -5804212, -29915880], ![165874848, -81778158, -73369014, 6511275, 19390358], ![217548510, -89932117, -86499468, 6673073, 22552117]]]
  hmulB := by decide  
  f := ![![![-111727841, 159082439, -109575432, -43383019, 44104390]], ![![4129131, -6722772, 5374940, 75217, -876998]], ![![-67319605, 99276119, -71402111, -19937387, 23518126]], ![![-11910395, 7662221, 2924926, -21464796, 12999596]], ![![-42206347, 72614182, -61062774, 6289926, 5486105]]]
  g := ![![![-102670893, 220717007, 222767782, -15499391, -57561688], ![-112493749, 227733013, 242186044, -14957940, -61997564], ![-55837829, 101751556, 118695825, -5804212, -29915880], ![33165881, -81778158, -73369014, 6511275, 19390358], ![39564419, -89932117, -86499468, 6673073, 22552117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![18055057, -8958632, -8018196, 714909, 2120112]] ![![11915047, -6206848, -1018896, 7573275, 5484070]]
  ![![-3626200829, 1827214, 545401940, -38744974, -177809012]] where
 M := ![![![-3626200829, 1827214, 545401940, -38744974, -177809012]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-3626200829, 1827214, 545401940, -38744974, -177809012]] ![![-597214555, 220717007, 222767782, -15499391, -57561688]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![1916367331782308279, -725293347291448085, -724398191324348110, 51572132953128973, 187539530379686360]]]
 hmul := by decide  
 g := ![![![![40773773016644857, -15431773346626555, -15412727474986130, 1097279424534659, 3990202774035880]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![900498205, -243323486, -285655648, 13727966, 71922192]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![900498205, -243323486, -285655648, 13727966, 71922192]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![13, 0, 1, 0, 0], ![0, 7, 0, 1, 0], ![14, 27, 0, 0, 1]] where
  M :=![![![900498205, -243323486, -285655648, 13727966, 71922192], ![863066304, -148845623, -226414136, 4066240, 54911864], ![329471184, 20377072, -43088135, -6766680, 8132480], ![-382738272, 166119016, 156615780, -12591335, -40989292], ![-389765436, 134505610, 140028884, -9087154, -35981027]]]
  hmulB := by decide  
  f := ![![![138713, -135426, 69448, 44434, 35672]], ![![428064, -95363, -217032, 424272, 177736]], ![![54145, -41666, 13937, 20218, 24760]], ![![148560, -81921, -12364, 112977, 40436]], ![![311618, -78771, -137892, 270606, 163237]]]
  g := ![![![68058697, -43043744, -285655648, 13727966, 71922192], ![57314792, -31319427, -226414136, 4066240, 54911864], ![14637023, -2864776, -43088135, -6766680, 8132480], ![-34809308, 25678665, 156615780, -12591335, -40989292], ![-32196350, 22067989, 140028884, -9087154, -35981027]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [6, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 52], [0, 1]]
 g := ![![[38, 9], [29], [11, 37], [13], [37, 1]], ![[0, 44], [29], [2, 16], [13], [21, 52]]]
 h' := ![![[37, 52], [48, 3], [40, 33], [22, 39], [43, 38], [0, 1]], ![[0, 1], [0, 50], [42, 20], [34, 14], [18, 15], [37, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [31, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [6, 16, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-151, 6933, -8379, 3159, 4779]
  a := ![1, 5, -3, -2, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![790, -2721, -8379, 3159, 4779]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1260364862909, 656572919049, 107689309764, -801253980009, -580193175494]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-1260364862909, 656572919049, 107689309764, -801253980009, -580193175494]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![39, 22, 1, 0, 0], ![43, 13, 0, 1, 0], ![31, 25, 0, 0, 1]] where
  M :=![![![-1260364862909, 656572919049, 107689309764, -801253980009, -580193175494], ![-6962318105928, 3626941417271, 594881096140, -4426166784424, -3205015920036], ![-19230095520216, 10017702270880, 1643076361623, -12225182584004, -8852333568848], ![-49632842360124, 25855671756728, 4240777169118, -31553174521557, -22847857207990], ![-74677460331114, 38902384190247, 6380663563894, -47474833731211, -34376833345963]]]
  hmulB := by decide  
  f := ![![![21392747, -4074265, -5828178, 142261, 1425052]], ![![17100624, 173519, -2732844, -255940, 569044]], ![![22904625, -2854353, -5393471, -10173, 1275172]], ![![21331597, -3173110, -5312096, 46000, 1273150]], ![![20382151, -2241317, -4631790, -41240, 1085099]]]
  g := ![![![886408710132, 437896966636, 107689309764, -801253980009, -580193175494], ![4896565743320, 2418964594351, 594881096140, -4426166784424, -3205015920036], ![13524436190999, 6681240285442, 1643076361623, -12225182584004, -8852333568848], ![34906545772055, 17244269302191, 4240777169118, -31553174521557, -22847857207990], ![52520308393282, 25945687885649, 6380663563894, -47474833731211, -34376833345963]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [44, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 52], [0, 1]]
 g := ![![[22, 47], [44], [35, 6], [49], [39, 1]], ![[0, 6], [44], [4, 47], [49], [25, 52]]]
 h' := ![![[39, 52], [34, 10], [50, 37], [46, 18], [33, 46], [0, 1]], ![[0, 1], [0, 43], [9, 16], [6, 35], [25, 7], [39, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [47, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [44, 14, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46, 251, -188, -15, 37]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![128, 69, -188, -15, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58631, -92695, 71978, 6075, -14920]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![58631, -92695, 71978, 6075, -14920]] 
 ![![53, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![58631, -92695, 71978, 6075, -14920], ![-179040, 306879, -257220, 24596, 24300], ![145800, -327184, 330883, -160020, 49192], ![384672, -345674, 59830, 515353, -332190], ![-834150, 965293, -468652, -726773, 527799]]]
  hmulB := by decide  
  f := ![![![-15483041, 8066771, 1322512, -9844763, -7128506]], ![![-4243197, 2210650, 362484, -2697847, -1953502]], ![![-15851187, 8258289, 1354083, -10078357, -7297694]], ![![-20854388, 10864492, 1781626, -13258805, -9600698]], ![![-31626595, 16476488, 2701902, -20107588, -14559897]]]
  g := ![![![-25992, -92695, 71978, 6075, -14920], ![96469, 306879, -257220, 24596, 24300], ![-134033, -327184, 330883, -160020, 49192], ![17894, -345674, 59830, 515353, -332190], ![116042, 965293, -468652, -726773, 527799]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![900498205, -243323486, -285655648, 13727966, 71922192]] ![![-1260364862909, 656572919049, 107689309764, -801253980009, -580193175494]]
  ![![-15483041, 8066771, 1322512, -9844763, -7128506]] where
 M := ![![![-15483041, 8066771, 1322512, -9844763, -7128506]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-15483041, 8066771, 1322512, -9844763, -7128506]] ![![58631, -92695, 71978, 6075, -14920]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [42, 32, 29, 39, 57, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 16, 47, 38, 12], [22, 58, 32, 20, 16], [4, 21, 10, 8, 26], [9, 22, 29, 52, 5], [0, 1]]
 g := ![![[5, 23, 50, 34, 51], [12, 38, 7, 37, 26], [13, 57], [24, 2, 1], []], ![[20, 46, 6, 20, 22, 17, 13, 19], [32, 45, 56, 0, 53, 35, 49, 35], [7, 3, 32, 53], [11, 52, 24, 47, 42, 19, 56, 22], [31, 52, 55, 12, 50, 36, 48, 17]], ![[42, 35, 53, 1, 14, 36, 27, 26], [16, 12, 11, 52, 43, 20, 13, 49], [8, 53, 30, 57], [42, 48, 7, 37, 1, 5, 8, 57], [51, 52, 39, 4, 0, 48, 11, 25]], ![[36, 42, 56, 39, 34, 52, 28, 53], [50, 29, 19, 3, 9, 58, 3, 26], [49, 34, 25, 46], [51, 22, 19, 31, 3, 6, 24, 48], [7, 24, 12, 58, 18, 51, 46, 53]], ![[32, 55, 30, 26, 35, 41, 51, 28], [13, 5, 7, 27, 16, 55, 20, 45], [16, 50, 43, 19], [28, 57, 58, 20, 20, 23, 22, 12], [39, 26, 40, 4, 1, 22, 20, 7]]]
 h' := ![![[26, 16, 47, 38, 12], [27, 8, 6, 48, 46], [10, 46, 5, 8, 47], [54, 33, 24, 36], [0, 0, 0, 1], [0, 1]], ![[22, 58, 32, 20, 16], [29, 17, 32, 15, 53], [20, 37, 2, 56, 23], [14, 37, 52, 23, 42], [49, 8, 22, 30, 46], [26, 16, 47, 38, 12]], ![[4, 21, 10, 8, 26], [4, 40, 20, 12, 3], [16, 26, 4, 34, 46], [23, 34, 34, 11, 23], [10, 42, 36, 19, 9], [22, 58, 32, 20, 16]], ![[9, 22, 29, 52, 5], [10, 9, 29, 47, 26], [12, 17, 48, 34, 58], [8, 15, 27, 12, 39], [6, 12, 49, 40, 16], [4, 21, 10, 8, 26]], ![[0, 1], [13, 44, 31, 55, 49], [52, 51, 0, 45, 3], [55, 58, 40, 36, 14], [35, 56, 11, 28, 47], [9, 22, 29, 52, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 56, 20, 20], [], [], []]
 b := ![[], [13, 19, 22, 43, 18], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [42, 32, 29, 39, 57, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1207381534776076, 628977554400930, 103153863238594, -767562713574862, -555805356521214]
  a := ![7, -21, -1, -23, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20464093809764, 10660636515270, 1748370563366, -13009537518218, -9420429771546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [54, 50, 60, 11, 44, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 7, 1, 9, 50], [37, 23, 5, 54, 5], [39, 12, 28, 2, 34], [22, 18, 27, 57, 33], [0, 1]]
 g := ![![[32, 27, 54, 55, 19], [28, 30, 53, 41], [50, 11, 33, 27, 5], [34, 17, 1], []], ![[35, 47, 45, 41, 29, 17, 55, 55], [41, 7, 14, 36], [55, 48, 60, 45, 50, 3, 24, 35], [22, 47, 42, 55, 25, 28, 49, 21], [10, 6, 16, 18, 45, 45, 38, 11]], ![[32, 21, 3, 21, 60, 50, 21, 39], [31, 58, 39, 15], [9, 53, 9, 15, 59, 42, 48, 27], [21, 12, 58, 32, 11, 20, 43, 60], [15, 37, 60, 41, 27, 34, 14, 3]], ![[49, 41, 18, 28, 24, 30, 20, 42], [30, 36, 11, 57], [28, 22, 19, 40, 5, 48, 40, 3], [36, 57, 28, 57, 55, 30, 10, 48], [49, 59, 25, 36, 37, 42, 17, 20]], ![[50, 6, 49, 5, 55, 55, 1, 37], [49, 17, 32, 19], [19, 54, 54, 26, 27, 56, 50, 43], [53, 59, 34, 58, 58, 36, 0, 18], [32, 16, 50, 22, 19, 35, 0, 8]]]
 h' := ![![[41, 7, 1, 9, 50], [25, 42, 36, 21, 43], [45, 53, 37, 47, 23], [55, 5, 45, 20, 26], [0, 0, 0, 1], [0, 1]], ![[37, 23, 5, 54, 5], [48, 52, 53, 36, 19], [35, 18, 34, 1, 6], [32, 22, 27, 41, 18], [0, 12, 34, 9, 29], [41, 7, 1, 9, 50]], ![[39, 12, 28, 2, 34], [19, 59, 9, 11, 52], [31, 44, 59, 58, 36], [15, 6, 36, 59, 15], [6, 30, 3, 7, 16], [37, 23, 5, 54, 5]], ![[22, 18, 27, 57, 33], [41, 33, 0, 38, 45], [40, 0, 57, 19, 39], [22, 55, 54, 16, 37], [4, 15, 0, 38, 35], [39, 12, 28, 2, 34]], ![[0, 1], [41, 58, 24, 16, 24], [53, 7, 57, 58, 18], [47, 34, 21, 47, 26], [14, 4, 24, 6, 42], [22, 18, 27, 57, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 56, 53, 2], [], [], []]
 b := ![[], [53, 13, 48, 17, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [54, 50, 60, 11, 44, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6550206502304, 3404177964784, 569666946400, -4168194102704, -3020795445410]
  a := ![1, -6, 1, -5, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-107380434464, 55806196144, 9338802400, -68331050864, -49521236810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB1681I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1681I1 : PrimesBelowBoundCertificateInterval O 23 61 1681 where
  m := 9
  g := ![3, 3, 3, 1, 1, 3, 3, 1, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1681I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![841, 841, 29]
    · exact ![29791, 31, 31]
    · exact ![1369, 1369, 37]
    · exact ![115856201]
    · exact ![147008443]
    · exact ![2209, 2209, 47]
    · exact ![2809, 2809, 53]
    · exact ![714924299]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N0, I29N1, I29N2, I31N1, I31N2, I37N0, I37N1, I37N2, I47N2, I53N2]
  Il := ![[I29N0, I29N1, I29N2], [I31N1, I31N2], [I37N0, I37N1, I37N2], [], [], [I47N2], [I53N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
