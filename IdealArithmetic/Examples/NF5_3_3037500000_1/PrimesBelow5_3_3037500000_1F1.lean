
import IdealArithmetic.Examples.NF5_3_3037500000_1.RI5_3_3037500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2150032, -1790360, -391323, 69353, 60860]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-2150032, -1790360, -391323, 69353, 60860]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![5, 9, 1, 0, 0], ![7, 12, 0, 1, 0], ![13, 6, 0, 0, 1]] where
  M :=![![![-2150032, -1790360, -391323, 69353, 60860], ![3416653, 1483939, -155633, -391925, 77846], ![3889605, 9099588, 4055552, 1087503, -861696], ![-9425956, -9411590, -2608084, -19331, 467194], ![20570966, 19979828, 5372066, -73670, -947803]]]
  hmulB := by decide  
  f := ![![![-2120198, -1622254, -444321, -78257, 95998]], ![![5201633, 4130681, 1143947, 231755, -252512]], ![![777838, 612065, 169052, 33175, -37124]], ![![1773064, 1438376, 400787, 87012, -89496]], ![![-359306, -304944, -86029, -21165, 19663]]]
  g := ![![![-50692, 18419, -391323, 69353, 60860], ![204355, 245540, -155633, -391925, 77846], ![-441332, -1216560, 4055552, 1087503, -861696], ![-80129, 396206, -2608084, -19331, 467194], ![225785, -751652, 5372066, -73670, -947803]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [26, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 28], [0, 1]]
 g := ![![[25, 22], [24], [11, 4], [17, 1]], ![[22, 7], [24], [21, 25], [5, 28]]]
 h' := ![![[17, 28], [1, 14], [4, 16], [22, 2], [0, 1]], ![[0, 1], [7, 15], [15, 13], [27, 27], [17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [20, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [26, 12, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![207011, 339144, 115732, 212364, 40344]
  a := ![-5, -2, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-82161, -120444, 115732, 212364, 40344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![566218373, 399274011, 106520035, 11939264, -21806220]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![566218373, 399274011, 106520035, 11939264, -21806220]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![27, 23, 1, 0, 0], ![27, 28, 0, 1, 0], ![14, 8, 0, 0, 1]] where
  M :=![![![566218373, 399274011, 106520035, 11939264, -21806220], ![-1187402836, -836912902, -223239413, -24933346, 45684748], ![2487727794, 1751974017, 467193388, 51857364, -95551440], ![-273543888, -191419516, -50934238, -5379485, 10368654], ![1379974897, 968448293, 257944936, 27870473, -52620749]]]
  hmulB := by decide  
  f := ![![![-32938881, -12530863, 2514477, 4145862, -978164]], ![![-49653158, -102670406, -44065317, -11090360, 9269888]], ![![-52848929, -74113124, -26814986, -4526060, 5356772]], ![![-87625109, -117543281, -41410697, -6399445, 8197058]], ![![-11367163, -21387111, -8878494, -2100705, 1850629]]]
  g := ![![![-80237780, -76225394, 106520035, 11939264, -21806220], ![168057765, 159663769, -223239413, -24933346, 45684748], ![-351342150, -333829951, 467193388, 51857364, -95551440], ![37991913, 36129114, -50934238, -5379485, 10368654], ![-193115540, -183575603, 257944936, 27870473, -52620749]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 28], [0, 1]]
 g := ![![[10, 7], [24], [13, 4], [28, 1]], ![[3, 22], [24], [9, 25], [27, 28]]]
 h' := ![![[28, 28], [28, 6], [19, 13], [3, 27], [0, 1]], ![[0, 1], [22, 23], [6, 16], [5, 2], [28, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [8, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [3, 1, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-512379, -566525, -182055, -55194, 53316]
  a := ![6, -62, -1, -57, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![177480, 163436, -182055, -55194, 53316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, 23, 2, -3, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![38, 23, 2, -3, 0]] 
 ![![29, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![38, 23, 2, -3, 0], ![-3, 44, 26, 9, -6], ![-321, -399, -133, -21, 24], ![218, 174, 36, -17, -8], ![-517, -451, -102, -25, 3]]]
  hmulB := by decide  
  f := ![![![41482, 29291, 7818, 885, -1602]], ![![34183, 24136, 6442, 729, -1320]], ![![34939, 24677, 6587, 747, -1350]], ![![36470, 25748, 6872, 777, -1408]], ![![35049, 24761, 6610, 751, -1355]]]
  g := ![![![-18, 23, 2, -3, 0], ![-61, 44, 26, 9, -6], ![439, -399, -133, -21, 24], ![-152, 174, 36, -17, -8], ![477, -451, -102, -25, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-2150032, -1790360, -391323, 69353, 60860]] ![![566218373, 399274011, 106520035, 11939264, -21806220]]
  ![![-41482, -29291, -7818, -885, 1602]] where
 M := ![![![-41482, -29291, -7818, -885, 1602]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-41482, -29291, -7818, -885, 1602]] ![![38, 23, 2, -3, 0]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![150420, 106142, 28321, 3187, -5800]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![150420, 106142, 28321, 3187, -5800]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![10, 19, 18, 1, 0], ![29, 4, 20, 0, 1]] where
  M :=![![![150420, 106142, 28321, 3187, -5800], ![-315813, -222817, -59445, -6687, 12174], ![662883, 467598, 124742, 14037, -25548], ![-73944, -52122, -13908, -1573, 2850], ![370792, 261530, 69790, 7876, -14297]]]
  hmulB := by decide  
  f := ![![![1978, 1912, 557, 179, -134]], ![![-7191, -6937, -2019, -633, 492]], ![![26427, 25620, 7472, 2505, -1758]], ![![11185, 10869, 3173, 1096, -734]], ![![19330, 18758, 5473, 1857, -1279]]]
  g := ![![![9250, 2219, 2805, 3187, -5800], ![-19419, -4660, -5889, -6687, 12174], ![40755, 9777, 12356, 14037, -25548], ![-4544, -1085, -1374, -1573, 2850], ![22795, 5454, 6902, 7876, -14297]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [23, 3, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 11, 29], [27, 19, 2], [0, 1]]
 g := ![![[10, 8, 20], [29, 20, 28], [26, 25, 10], [1]], ![[28, 25, 6, 3], [9, 21, 0, 27], [11, 13, 7, 26], [8, 11, 20, 23]], ![[7, 4, 2, 10], [30, 26, 25, 18], [21, 22, 21, 5], [11, 3, 30, 8]]]
 h' := ![![[18, 11, 29], [15, 30, 12], [22, 0, 11], [8, 28, 14], [0, 1]], ![[27, 19, 2], [15, 12, 13], [23, 3, 23], [6, 30, 24], [18, 11, 29]], ![[0, 1], [18, 20, 6], [3, 28, 28], [24, 4, 24], [27, 19, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 1], []]
 b := ![[], [28, 25, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [23, 3, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86697428, -135413253, -45662165, -79583343, -14402149]
  a := ![-1, -3, 1, -5, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36348333, 46267060, 54028419, -79583343, -14402149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![255907, 247237, 72013, 23014, -17388]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![255907, 247237, 72013, 23014, -17388]] 
 ![![31, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![255907, 247237, 72013, 23014, -17388], ![-933326, -901706, -262641, -83936, 63416], ![3403944, 3288615, 957878, 306114, -231288], ![-1602458, -1548176, -450940, -144123, 108878], ![5297331, 5117819, 1490668, 476339, -359951]]]
  hmulB := by decide  
  f := ![![![-357, -1211, -791, -384, 196]], ![![82, -448, -411, -242, 108]], ![![-1818, -2139, -796, -180, 168]], ![![591, 209, -97, -121, 34]], ![![-1688, -1746, -643, -159, 139]]]
  g := ![![![-189619, 247237, 72013, 23014, -17388], ![691566, -901706, -262641, -83936, 63416], ![-2522208, 3288615, 957878, 306114, -231288], ![1187383, -1548176, -450940, -144123, 108878], ![-3925097, 5117819, 1490668, 476339, -359951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142, 87, 8, -11, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![142, 87, 8, -11, 0]] 
 ![![31, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![142, 87, 8, -11, 0], ![-11, 166, 98, 37, -22], ![-1173, -1455, -487, -57, 96], ![876, 742, 166, -19, -24], ![-1765, -1403, -286, 103, 53]]]
  hmulB := by decide  
  f := ![![![12774, 10409, 2904, 639, -650]], ![![9169, 7431, 2070, 448, -462]], ![![14067, 11695, 3281, 765, -742]], ![![10750, 8609, 2390, 498, -530]], ![![14057, 11931, 3366, 829, -769]]]
  g := ![![![-62, 87, 8, -11, 0], ![-234, 166, 98, 37, -22], ![1523, -1455, -487, -57, 96], ![-673, 742, 166, -19, -24], ![1177, -1403, -286, 103, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![150420, 106142, 28321, 3187, -5800]] ![![255907, 247237, 72013, 23014, -17388]]
  ![![-12774, -10409, -2904, -639, 650]] where
 M := ![![![-12774, -10409, -2904, -639, 650]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-12774, -10409, -2904, -639, 650]] ![![142, 87, 8, -11, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4778323, 5085458, 1501718, 74874, -277158]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![4778323, 5085458, 1501718, 74874, -277158]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![20, 28, 4, 19, 1]] where
  M :=![![![4778323, 5085458, 1501718, 74874, -277158], ![-15168816, -12612005, -2749840, 493284, 426906], ![23973114, 10307238, -1151921, -2771670, 559662], ![12252698, 17094444, 6166494, 1031079, -1230620], ![-29855464, -39169732, -13607064, -1998400, 2680109]]]
  hmulB := by decide  
  f := ![![![249847, 241258, 70262, 22410, -16974]], ![![-911160, -880313, -256424, -82212, 61794]], ![![3316458, 3201294, 932131, 294858, -226218]], ![![-1568942, -1519572, -443066, -146413, 105092]], ![![-862838, -836444, -243978, -81627, 57473]]]
  g := ![![![278959, 347186, 70550, 144348, -277158], ![-640728, -663929, -120472, -205890, 426906], ![345402, -144954, -91637, -362304, 559662], ![996354, 1393292, 299702, 659807, -1230620], ![-2255612, -3086832, -657500, -1430283, 2680109]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [8, 3, 31, 33, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 10, 36, 15], [21, 23, 8, 3], [8, 3, 30, 19], [0, 1]]
 g := ![![[17, 32, 24, 12], [26, 16, 21], [10, 1, 1, 16], [1], []], ![[4, 5, 9, 33, 14, 17], [7, 30, 28], [3, 18, 6, 32, 31, 2], [6, 16, 26], [25, 19, 3]], ![[28, 35, 14, 3, 13, 9], [31, 4, 12], [10, 29, 9, 5, 4, 1], [9, 35, 7], [0, 10, 9]], ![[30, 33, 28, 21, 7, 19], [3, 0, 4], [8, 1, 31, 5, 36, 15], [14, 36, 1], [11, 31, 28]]]
 h' := ![![[12, 10, 36, 15], [13, 0, 7, 30], [31, 26, 23, 13], [29, 34, 6, 4], [0, 0, 1], [0, 1]], ![[21, 23, 8, 3], [27, 0, 9, 23], [3, 25, 29, 19], [17, 26, 26, 11], [18, 13, 34, 27], [12, 10, 36, 15]], ![[8, 3, 30, 19], [2, 9, 33, 22], [19, 23, 18, 7], [11, 1, 18, 5], [34, 35, 23, 9], [21, 23, 8, 3]], ![[0, 1], [20, 28, 25, 36], [28, 0, 4, 35], [20, 13, 24, 17], [13, 26, 16, 1], [8, 3, 30, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [28, 13, 16], []]
 b := ![[], [], [7, 26, 23, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [8, 3, 31, 33, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![189632675013631, 296182132599714, 99875063198673, 174050964510705, 31495217193318]
  a := ![8, 19, -3, 26, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11899234293317, -15829295913870, -705562312827, -11469139517901, 31495217193318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-249847, -241258, -70262, -22410, 16974]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-249847, -241258, -70262, -22410, 16974]] 
 ![![37, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-249847, -241258, -70262, -22410, 16974], ![911160, 880313, 256424, 82212, -61794], ![-3316458, -3201294, -932131, -294858, 226218], ![1568942, 1519572, 443066, 146413, -105092], ![-5134600, -4941868, -1437176, -435952, 356127]]]
  hmulB := by decide  
  f := ![![![-4778323, -5085458, -1501718, -74874, 277158]], ![![409968, 340865, 74320, -13332, -11538]], ![![-647922, -278574, 31133, 74910, -15126]], ![![-331154, -462012, -166662, -27867, 33260]], ![![-1646829, -1552810, -403394, 15562, 69889]]]
  g := ![![![-15469, -241258, -70262, -22410, 16974], ![56358, 880313, 256424, 82212, -61794], ![-205800, -3201294, -932131, -294858, 226218], ![96370, 1519572, 443066, 146413, -105092], ![-321649, -4941868, -1437176, -435952, 356127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![4778323, 5085458, 1501718, 74874, -277158]] ![![-249847, -241258, -70262, -22410, 16974]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5320059, 4605713, 1068613, -135258, -173116]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![5320059, 4605713, 1068613, -135258, -173116]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![16, 25, 33, 38, 1]] where
  M :=![![![5320059, 4605713, 1068613, -135258, -173116], ![-9656638, -5150266, -106277, 909824, -97400], ![-4447176, -17670069, -8787290, -2747238, 1917048], ![21943386, 22681424, 6512224, 204673, -1186554], ![-48383209, -48607457, -13557444, -160905, 2436309]]]
  hmulB := by decide  
  f := ![![![-766259, -704369, -202785, -59432, 48012]], ![![2581228, 2418334, 699399, 212230, -166876]], ![![-8965950, -8503779, -2466424, -764532, 591336]], ![![4002544, 3849220, 1119994, 355275, -269962]], ![![-2557477, -2389572, -690637, -208567, 164603]]]
  g := ![![![197315, 217893, 165401, 157150, -173116], ![-197518, -66226, 75803, 112464, -97400], ![-856584, -1599909, -1757314, -1843782, 1917048], ![998250, 1276714, 1113866, 1104725, -1186554], ![-2130833, -2671102, -2291601, -2261967, 2436309]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [40, 4, 39, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18, 34, 21], [30, 24, 9, 20], [19, 39, 39], [0, 1]]
 g := ![![[8, 18, 35, 5], [2, 19, 2], [26, 24, 21], [16, 1], []], ![[20, 20, 3, 31, 17, 21], [37, 18, 8], [26, 9, 40], [17, 12, 29, 15, 7, 36], [40, 38, 31]], ![[26, 3, 1, 39, 10, 37], [35, 9, 8], [40, 37, 39], [33, 0, 8, 21, 4, 32], [39, 36, 31]], ![[34, 26, 1, 31, 32], [18, 19, 9], [3, 4, 23], [32, 31, 30, 26, 5], [4]]]
 h' := ![![[8, 18, 34, 21], [27, 20, 38, 28], [36, 36, 4, 24], [16, 19, 28, 12], [0, 0, 1], [0, 1]], ![[30, 24, 9, 20], [27, 0, 16, 1], [21, 7, 39, 7], [35, 12, 10, 32], [22, 2, 7, 20], [8, 18, 34, 21]], ![[19, 39, 39], [33, 34, 29, 7], [30, 13, 12, 7], [21, 13, 36, 30], [37, 8, 15, 31], [30, 24, 9, 20]], ![[0, 1], [38, 28, 40, 5], [26, 26, 27, 3], [8, 38, 8, 8], [37, 31, 18, 31], [19, 39, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 9, 13], []]
 b := ![[], [], [32, 16, 29, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [40, 4, 39, 25, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![173088824552694, 270348598278959, 91164219362985, 158874751896049, 28749849414715]
  a := ![-10, 1, 5, -7, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6997774782506, -10936527733876, -20916605154210, -22771207947881, 28749849414715]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![766259, 704369, 202785, 59432, -48012]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![766259, 704369, 202785, 59432, -48012]] 
 ![![41, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![766259, 704369, 202785, 59432, -48012], ![-2581228, -2418334, -699399, -212230, 166876], ![8965950, 8503779, 2466424, 764532, -591336], ![-4002544, -3849220, -1119994, -355275, 269962], ![13347435, 12806551, 3724312, 1176979, -896899]]]
  hmulB := by decide  
  f := ![![![-5320059, -4605713, -1068613, 135258, 173116]], ![![-672775, -660725, -179854, 902, 31932]], ![![-4173531, -3276060, -645779, 175872, 92580]], ![![-5725506, -5046584, -1201384, 126967, 197834]], ![![-1544830, -1173476, -216669, 73203, 29247]]]
  g := ![![![-298177, 704369, 202785, 59432, -48012], ![1034441, -2418334, -699399, -212230, 166876], ![-3661359, 8503779, 2466424, 764532, -591336], ![1669356, -3849220, -1119994, -355275, 269962], ![-5547439, 12806551, 3724312, 1176979, -896899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![5320059, 4605713, 1068613, -135258, -173116]] ![![766259, 704369, 202785, 59432, -48012]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27098208, 19120733, 5102216, 574609, -1044982]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![27098208, 19120733, 5102216, 574609, -1044982]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![31, 13, 2, 0, 1]] where
  M :=![![![27098208, 19120733, 5102216, 574609, -1044982], ![-56899401, -40148722, -10713372, -1206537, 2194200], ![119474463, 84302283, 22495415, 2533431, -4607274], ![-13361406, -9427962, -2515784, -283327, 515256], ![66896707, 47202989, 12595758, 1418527, -2579729]]]
  hmulB := by decide  
  f := ![![![-104, -137, -44, -61, -8]], ![![-501, -868, -300, -573, -114]], ![![-6843, -10407, -3487, -5907, -1032]], ![![-10194, -16038, -5416, -9517, -1740]], ![![-1728, -2684, -904, -1565, -281]]]
  g := ![![![1383550, 760593, 167260, 13363, -1044982], ![-2905107, -1597054, -351204, -28059, 2194200], ![6099999, 3353415, 737441, 58917, -4607274], ![-682194, -375030, -82472, -6589, 515256], ![3415542, 1877662, 412912, 32989, -2579729]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [27, 22, 5, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28, 36, 27], [22, 35, 6, 2], [9, 22, 1, 14], [0, 1]]
 g := ![![[38, 18, 30, 16], [23, 29, 37, 6], [21, 19, 15], [37, 1], []], ![[23, 30, 36, 2, 36, 3], [6, 28, 16, 28, 5, 34], [28, 42, 38], [39, 14, 37, 25, 40, 32], [26, 21, 41]], ![[23, 28, 11, 7, 36, 26], [9, 34, 10, 30, 39, 5], [8, 30, 10], [13, 9, 37, 2], [27, 0, 4]], ![[28, 20, 42, 24, 35, 6], [27, 7, 24, 41, 35, 38], [36, 2, 23], [37, 26, 8, 7, 29, 15], [32, 13, 24]]]
 h' := ![![[6, 28, 36, 27], [24, 37, 5, 4], [6, 21, 4, 36], [33, 19, 8, 31], [0, 0, 1], [0, 1]], ![[22, 35, 6, 2], [33, 11, 2, 14], [22, 34, 32, 33], [2, 16, 15, 9], [22, 14, 33, 16], [6, 28, 36, 27]], ![[9, 22, 1, 14], [23, 8, 24, 20], [39, 31, 19, 29], [13, 11, 40, 28], [13, 0, 42], [22, 35, 6, 2]], ![[0, 1], [16, 30, 12, 5], [32, 0, 31, 31], [31, 40, 23, 18], [34, 29, 10, 27], [9, 22, 1, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [39, 31, 8], []]
 b := ![[], [], [3, 18, 37, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [27, 22, 5, 6, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6515862666735, 10188679962764, 3436529863256, 5996986638220, 1086936431952]
  a := ![6, -10, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-632073644739, -91662643084, 29364116264, 139464805540, 1086936431952]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-104, -137, -44, -61, -8]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-104, -137, -44, -61, -8]] 
 ![![43, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-104, -137, -44, -61, -8], ![-501, -868, -300, -573, -114], ![-6843, -10407, -3487, -5907, -1032], ![-10194, -16038, -5416, -9517, -1740], ![-50881, -79067, -26634, -46141, -8289]]]
  hmulB := by decide  
  f := ![![![27098208, 19120733, 5102216, 574609, -1044982]], ![![-693051, -489023, -130492, -14696, 26726]], ![![29246493, 20636583, 5506709, 620163, -1127826]], ![![8511942, 6006100, 1602680, 180493, -328244]], ![![19831273, 13993122, 3733954, 420516, -764749]]]
  g := ![![![69, -137, -44, -61, -8], ![565, -868, -300, -573, -114], ![6108, -10407, -3487, -5907, -1032], ![9698, -16038, -5416, -9517, -1740], ![47283, -79067, -26634, -46141, -8289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![27098208, 19120733, 5102216, 574609, -1044982]] ![![-104, -137, -44, -61, -8]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![650345074, 458889376, 122451009, 13790365, -25079120]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![650345074, 458889376, 122451009, 13790365, -25079120]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![5, 25, 1, 0, 0], ![34, 46, 0, 1, 0], ![12, 19, 0, 0, 1]] where
  M :=![![![650345074, 458889376, 122451009, 13790365, -25079120], ![-1365561235, -963552379, -257116349, -28956301, 52659850], ![2867335449, 2023217868, 539879722, 60800955, -110572452], ![-320666700, -226265326, -60377116, -6799637, 12365802], ![1605488274, 1132847064, 302291298, 34043878, -61912105]]]
  hmulB := by decide  
  f := ![![![32, 498, 197, 677, 194]], ![![11347, 15949, 5253, 7873, 1160]], ![![7564, 11063, 3678, 5863, 948]], ![![14120, 20572, 6830, 10845, 1746]], ![![18121, 27925, 9391, 16079, 2851]]]
  g := ![![![-2762403, -58728497, 122451009, 13790365, -25079120], ![5800352, 123315086, -257116349, -28956301, 52659850], ![-12179281, -258930692, 539879722, 60800955, -110572452], ![1362062, 28957354, -60377116, -6799637, 12365802], ![-6819464, -144981357, 302291298, 34043878, -61912105]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [28, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 46], [0, 1]]
 g := ![![[26, 42], [2, 8], [3, 8], [25, 12], [1]], ![[0, 5], [6, 39], [7, 39], [31, 35], [1]]]
 h' := ![![[24, 46], [38, 18], [10, 14], [5, 14], [19, 24], [0, 1]], ![[0, 1], [0, 29], [17, 33], [12, 33], [31, 23], [24, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [43, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [28, 23, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1037, 11884, 4715, 21773, 6422]
  a := ![6, 13, 4, 20, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17914, -26161, 4715, 21773, 6422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2953, 2067, 571, 84, -120]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![2953, 2067, 571, 84, -120]] 
 ![![47, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![2953, 2067, 571, 84, -120], ![-6516, -4814, -1377, -210, 288], ![15630, 12105, 3460, 456, -708], ![-3156, -2580, -674, -17, 126], ![11373, 8697, 2264, 117, -437]]]
  hmulB := by decide  
  f := ![![![42953, 67011, 22591, 39318, 7104]], ![![15547, 24277, 8186, 14262, 2580]], ![![133239, 208008, 70135, 122160, 22092]], ![![184400, 287958, 97098, 169177, 30606]], ![![734139, 1146579, 386632, 673743, 121909]]]
  g := ![![![-829, 2067, 571, 84, -120], ![1993, -4814, -1377, -210, 288], ![-4971, 12105, 3460, 456, -708], ![944, -2580, -674, -17, 126], ![-3204, 8697, 2264, 117, -437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10508, -10152, -2957, -945, 714]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-10508, -10152, -2957, -945, 714]] 
 ![![47, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-10508, -10152, -2957, -945, 714], ![38325, 37027, 10785, 3447, -2604], ![-139773, -135036, -39332, -12567, 9498], ![65808, 63582, 18520, 5923, -4470], ![-217500, -210114, -61198, -19536, 14785]]]
  hmulB := by decide  
  f := ![![![-11350, -7866, -2093, -249, 432]], ![![-5537, -3833, -1018, -120, 210]], ![![-9045, -6300, -1685, -204, 348]], ![![-9022, -6234, -1656, -197, 342]], ![![-10352, -7218, -1926, -228, 397]]]
  g := ![![![7409, -10152, -2957, -945, 714], ![-27023, 37027, 10785, 3447, -2604], ![98547, -135036, -39332, -12567, 9498], ![-46408, 63582, 18520, 5923, -4470], ![153316, -210114, -61198, -19536, 14785]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84702, 59391, 15814, 1697, -3224]] i)))

def SI47N3: IdealEqSpanCertificate' Table ![![84702, 59391, 15814, 1697, -3224]] 
 ![![47, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![84702, 59391, 15814, 1697, -3224], ![-175623, -122552, -32578, -3363, 6618], ![360627, 249465, 66115, 6327, -13344], ![-33454, -21258, -5460, -93, 1024], ![182803, 121197, 31634, 1807, -6177]]]
  hmulB := by decide  
  f := ![![![-12242, 40713, 26850, 10931, -6182]], ![![-16639, 23113, 18088, 8188, -4270]], ![![21721, 66504, 31609, 9320, -6824]], ![![-20594, 31500, 24040, 10733, -5656]], ![![12289, 26601, 11586, 2991, -2447]]]
  g := ![![![-58755, 59391, 15814, 1697, -3224], ![121067, -122552, -32578, -3363, 6618], ![-245797, 249465, 66115, 6327, -13344], ![20390, -21258, -5460, -93, 1024], ![-117840, 121197, 31634, 1807, -6177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N3 : Nat.card (O ⧸ I47N3) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N3)

lemma isPrimeI47N3 : Ideal.IsPrime I47N3 := prime_ideal_of_norm_prime hp47.out _ NI47N3
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![650345074, 458889376, 122451009, 13790365, -25079120]] ![![2953, 2067, 571, 84, -120]]
  ![![515507876476, 363747027499, 97063023952, 10931184115, -19879421534]] where
 M := ![![![515507876476, 363747027499, 97063023952, 10931184115, -19879421534]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![515507876476, 363747027499, 97063023952, 10931184115, -19879421534]] ![![-10508, -10152, -2957, -945, 714]]
  ![![-8436068609, -5952566345, -1588395349, -178884182, 325318324]] where
 M := ![![![-8436068609, -5952566345, -1588395349, -178884182, 325318324]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N2 : IdealMulLeCertificate' Table 
  ![![-8436068609, -5952566345, -1588395349, -178884182, 325318324]] ![![84702, 59391, 15814, 1697, -3224]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-176509016628606, -124546360928180, -33234213599315, -3742818743967, 6806679971546]]]
 hmul := by decide  
 g := ![![![![-3755510992098, -2649922572940, -707110927645, -79634441361, 144822978118]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2, I47N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
    exact isPrimeI47N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1 ⊙ MulI47N2)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-627, -1054, -424, -96, 88]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-627, -1054, -424, -96, 88]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![11, 25, 26, 1, 0], ![38, 43, 38, 0, 1]] where
  M :=![![![-627, -1054, -424, -96, 88], ![4744, 5053, 1506, 88, -280], ![-15312, -12858, -2875, 444, 456], ![1882, -512, -842, -489, 212], ![-2698, 2406, 2152, 1030, -517]]]
  hmulB := by decide  
  f := ![![![-23671, -22866, -6660, -2128, 1608]], ![![86312, 83381, 24286, 7760, -5864]], ![![-314760, -304086, -88571, -28308, 21384]], ![![-115815, -111889, -32590, -10417, 7868]], ![![-181864, -175699, -51176, -16358, 12355]]]
  g := ![![![-55, -46, -24, -96, 88], ![272, 281, 186, 88, -280], ![-708, -822, -599, 444, 456], ![-15, 49, 72, -489, 212], ![106, -21, -94, 1030, -517]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [35, 29, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 47, 14], [29, 5, 39], [0, 1]]
 g := ![![[1, 30, 47], [4, 7], [21, 31, 11], [26, 36], [1]], ![[27, 14, 27, 41], [22, 28], [48, 40, 20, 14], [32, 38], [25, 2, 42, 41]], ![[14, 41, 52, 45], [7, 7], [21, 48, 34, 3], [20, 6], [14, 36, 6, 12]]]
 h' := ![![[18, 47, 14], [15, 5, 10], [7, 11, 31], [50, 16, 8], [18, 24, 47], [0, 1]], ![[29, 5, 39], [31, 16, 14], [18, 13, 44], [35, 15, 52], [28, 51, 41], [18, 47, 14]], ![[0, 1], [14, 32, 29], [43, 29, 31], [5, 22, 46], [49, 31, 18], [29, 5, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 4], []]
 b := ![[], [42, 37, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [35, 29, 6, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86331788, 136979760, 46365535, 82144791, 15144348]
  a := ![2, -5, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26278229, -48449943, -50280835, 82144791, 15144348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 28, 8, 2, -2]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![31, 28, 8, 2, -2]] 
 ![![53, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![31, 28, 8, 2, -2], ![-108, -103, -30, -12, 6], ![318, 276, 77, -6, -30], ![-222, -252, -78, -73, 0], ![218, 22, -16, -238, -87]]]
  hmulB := by decide  
  f := ![![![771, 832, 260, 26, -50]], ![![225, 253, 82, 10, -16]], ![![252, 224, 57, -2, -10]], ![![63, 84, 30, 5, -6]], ![![-20, -54, -24, -6, 5]]]
  g := ![![![-11, 28, 8, 2, -2], ![41, -103, -30, -12, 6], ![-106, 276, 77, -6, -30], ![105, -252, -78, -73, 0], ![16, 22, -16, -238, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1263, -1222, -356, -114, 86]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-1263, -1222, -356, -114, 86]] 
 ![![53, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-1263, -1222, -356, -114, 86], ![4616, 4463, 1300, 416, -314], ![-16854, -16290, -4745, -1518, 1146], ![7944, 7676, 2236, 715, -540], ![-26260, -25376, -7392, -2364, 1785]]]
  hmulB := by decide  
  f := ![![![-59, -110, -36, -2, 6]], ![![-35, -71, -24, -2, 4]], ![![-21, -24, -5, 0, 0]], ![![-48, -84, -28, -5, 4]], ![![-27, -62, -20, -14, -1]]]
  g := ![![![905, -1222, -356, -114, 86], ![-3305, 4463, 1300, 416, -314], ![12063, -16290, -4745, -1518, 1146], ![-5684, 7676, 2236, 715, -540], ![18791, -25376, -7392, -2364, 1785]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-627, -1054, -424, -96, 88]] ![![31, 28, 8, 2, -2]]
  ![![59, 110, 36, 2, -6]] where
 M := ![![![59, 110, 36, 2, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![59, 110, 36, 2, -6]] ![![-1263, -1222, -356, -114, 86]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [11, 3, 32, 46, 39, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 46, 55, 50, 9], [5, 8, 17, 24, 35], [24, 34, 11, 24, 9], [45, 29, 35, 20, 6], [0, 1]]
 g := ![![[21, 14, 18, 32, 51], [56, 14, 22, 12, 16], [49, 19, 4, 5], [0, 20, 1], []], ![[31, 21, 16, 11, 39, 7, 21, 12], [18, 7, 19, 7, 29, 23, 0, 19], [29, 43, 56, 27], [57, 47, 23, 32, 36, 6, 32, 5], [5, 45, 11, 16, 4, 14, 3, 21]], ![[8, 46, 47, 31, 23, 57, 38, 26], [22, 2, 25, 19, 37, 11, 9, 28], [13, 46, 15, 36], [5, 25, 33, 7, 43, 23, 8, 4], [22, 14, 25, 58, 54, 17, 48, 41]], ![[40, 44, 1, 57, 23, 23, 15, 22], [58, 11, 43, 56, 13, 46, 12, 1], [55, 55, 58, 49], [27, 14, 31, 17, 28, 51, 37, 26], [47, 25, 26, 57, 5, 50, 57, 21]], ![[14, 5, 52, 53, 52, 23, 17, 40], [19, 54, 34, 10, 30, 31, 49, 34], [33, 3, 24, 7], [50, 14, 49, 46, 11, 9, 41, 43], [11, 24, 57, 7, 32, 18, 49, 39]]]
 h' := ![![[5, 46, 55, 50, 9], [33, 37, 21, 38, 46], [51, 57, 3, 50, 4], [0, 16, 47, 6, 51], [0, 0, 0, 1], [0, 1]], ![[5, 8, 17, 24, 35], [50, 1, 16, 19, 32], [47, 1, 20, 5, 15], [37, 2, 30, 27, 26], [11, 49, 49, 54, 42], [5, 46, 55, 50, 9]], ![[24, 34, 11, 24, 9], [39, 12, 25, 37, 17], [56, 3, 35, 40, 44], [9, 37, 15, 44, 53], [1, 26, 34, 30, 52], [5, 8, 17, 24, 35]], ![[45, 29, 35, 20, 6], [11, 0, 56, 22, 3], [0, 33, 9, 31, 20], [30, 36, 37, 10, 7], [32, 44, 16, 44, 55], [24, 34, 11, 24, 9]], ![[0, 1], [44, 9, 0, 2, 20], [11, 24, 51, 51, 35], [16, 27, 48, 31, 40], [26, 58, 19, 48, 28], [45, 29, 35, 20, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 21, 2, 21], [], [], []]
 b := ![[], [31, 49, 34, 31, 37], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [11, 3, 32, 46, 39, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1708466240789104215, 2668411282657364863, 899810686689361638, 1568091006086270027, 283752861686222285]
  a := ![10, -1, 0, 5, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28957054928628885, 45227309875548557, 15251028587955282, 26577813662479153, 4809370537054615]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2788, -2687, -780, -247, 188]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-2788, -2687, -780, -247, 188]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![21, 53, 54, 1, 0], ![4, 19, 35, 0, 1]] where
  M :=![![![-2788, -2687, -780, -247, 188], ![10093, 9724, 2824, 901, -682], ![-36609, -35313, -10273, -3297, 2484], ![17174, 16606, 4844, 1561, -1172], ![-56947, -55057, -16054, -5159, 3881]]]
  hmulB := by decide  
  f := ![![![260, 181, 48, 5, -10]], ![![-545, -386, -104, -17, 20]], ![![1083, 723, 191, -21, -54]], ![![571, 363, 94, -33, -34]], ![![473, 304, 79, -23, -27]]]
  g := ![![![27, 112, 98, -247, 188], ![-100, -411, -360, 901, -682], ![372, 1512, 1325, -3297, 2484], ![-179, -719, -630, 1561, -1172], ![588, 2371, 2077, -5159, 3881]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [59, 30, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 51, 25], [38, 9, 36], [0, 1]]
 g := ![![[29, 38, 25], [57, 16], [42, 11, 47], [5, 27, 5], [1]], ![[29, 47, 18, 34], [19, 22], [19, 50, 46, 49], [28, 35, 45, 14], [55, 52, 48, 9]], ![[39, 19, 16, 36], [50, 12], [16, 39, 35, 1], [36, 26, 42, 14], [12, 31, 29, 52]]]
 h' := ![![[58, 51, 25], [33, 20, 5], [23, 21, 4], [10, 30, 48], [2, 31, 35], [0, 1]], ![[38, 9, 36], [24, 38, 57], [13, 17, 12], [7, 45, 23], [22, 14, 53], [58, 51, 25]], ![[0, 1], [40, 3, 60], [60, 23, 45], [9, 47, 51], [57, 16, 34], [38, 9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 23], []]
 b := ![[], [5, 49, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [59, 30, 26, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2378877476, 3718576173, 1254156726, 2187653557, 396314347]
  a := ![6, 1, -3, 6, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-740116469, -1963230081, -2143444877, 2187653557, 396314347]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![260, 181, 48, 5, -10]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![260, 181, 48, 5, -10]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![47, 42, 1, 0, 0], ![37, 60, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![260, 181, 48, 5, -10], ![-545, -386, -104, -17, 20], ![1083, 723, 191, -21, -54], ![-226, -242, -76, -83, -8], ![263, -151, -82, -365, -97]]]
  hmulB := by decide  
  f := ![![![-2788, -2687, -780, -247, 188]], ![![10093, 9724, 2824, 901, -682]], ![![4201, 4046, 1175, 376, -284]], ![![8518, 8207, 2384, 762, -576]], ![![-2259, -2180, -634, -202, 153]]]
  g := ![![![-31, -35, 48, 5, -10], ![72, 82, -104, -17, 20], ![-91, -99, 191, -21, -54], ![109, 130, -76, -83, -8], ![335, 413, -82, -365, -97]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [1, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 60], [0, 1]]
 g := ![![[22, 1], [3], [46, 13], [23, 25], [39, 1]], ![[0, 60], [3], [4, 48], [22, 36], [17, 60]]]
 h' := ![![[39, 60], [39, 60], [15, 53], [38, 14], [22, 56], [0, 1]], ![[0, 1], [0, 1], [8, 8], [35, 47], [10, 5], [39, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [18, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [1, 22, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27375, 42626, 14272, 25366, 4702]
  a := ![3, 5, 0, 9, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28169, -34078, 14272, 25366, 4702]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-2788, -2687, -780, -247, 188]] ![![260, 181, 48, 5, -10]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB2695I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB2695I1 : PrimesBelowBoundCertificateInterval O 23 61 2695 where
  m := 9
  g := ![3, 3, 2, 2, 2, 4, 3, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB2695I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2, I47N3]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
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
    · exact ![1874161, 37]
    · exact ![2825761, 41]
    · exact ![3418801, 43]
    · exact ![2209, 47, 47, 47]
    · exact ![148877, 53, 53]
    · exact ![714924299]
    · exact ![226981, 3721]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
      exact NI47N3
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
      exact NI61N1
  β := ![I29N0, I29N1, I29N2, I31N1, I31N2, I37N1, I41N1, I43N1, I47N0, I47N1, I47N2, I47N3, I53N1, I53N2]
  Il := ![[I29N0, I29N1, I29N2], [I31N1, I31N2], [I37N1], [I41N1], [I43N1], [I47N0, I47N1, I47N2, I47N3], [I53N1, I53N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
