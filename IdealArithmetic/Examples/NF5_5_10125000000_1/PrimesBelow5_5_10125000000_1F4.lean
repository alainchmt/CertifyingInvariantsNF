
import IdealArithmetic.Examples.NF5_5_10125000000_1.RI5_5_10125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, -299, -324, -47, 44]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![401, -299, -324, -47, 44]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![34, 24, 1, 0, 0], ![126, 3, 0, 1, 0], ![155, 9, 0, 0, 1]] where
  M :=![![![401, -299, -324, -47, 44], ![-1414, 1054, 1256, 235, -188], ![3762, -2805, -3569, -765, 564], ![-8518, 6345, 8612, 2054, -1436], ![11348, -8468, -11684, -2874, 1955]]]
  hmulB := by decide  
  f := ![![![4149, 2903, 648, -91, -68]], ![![1858, 5728, 3268, 95, -364]], ![![1212, 1487, 619, -7, -68]], ![![3322, 2451, 604, -69, -64]], ![![4213, 3159, 800, -86, -85]]]
  g := ![![![67, 46, -324, -47, 44], ![-284, -179, 1256, 235, -188], ![854, 510, -3569, -765, 564], ![-2150, -1233, 8612, 2054, -1436], ![2979, 1675, -11684, -2874, 1955]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [131, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 156], [0, 1]]
 g := ![![[80, 86], [101], [104, 75], [85, 154], [26, 30], [108], [1]], ![[137, 71], [101], [46, 82], [125, 3], [97, 127], [108], [1]]]
 h' := ![![[39, 156], [83, 20], [35, 27], [12, 46], [48, 25], [30, 117], [26, 39], [0, 1]], ![[0, 1], [78, 137], [146, 130], [79, 111], [81, 132], [40, 40], [134, 118], [39, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [152, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [131, 118, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-787760, 1675264, 1910347, 1484064, 882148]
  a := ![-25, -17, 5, -1, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2480666, -360284, 1910347, 1484064, 882148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 35, 30, 1, -3]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-47, 35, 30, 1, -3]] 
 ![![157, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![74, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![-47, 35, 30, 1, -3], ![92, -69, -52, 2, 4], ![-104, 78, 35, -16, 2], ![-92, 68, 160, 61, -34], ![234, -174, -294, -90, 55]]]
  hmulB := by decide  
  f := ![![![-309, -485, -232, -3, 25]], ![![-117, -178, -84, -1, 9]], ![![-142, -232, -113, -2, 12]], ![![-275, -427, -204, -4, 21]], ![![-96, -174, -90, -6, 7]]]
  g := ![![![-27, 35, 30, 1, -3], ![47, -69, -52, 2, 4], ![-32, 78, 35, -16, 2], ![-143, 68, 160, 61, -34], ![264, -174, -294, -90, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -17, 0, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-43, -17, 0, 1, 0]] 
 ![![157, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![153, 0, 0, 0, 1]] where
  M :=![![![-43, -17, 0, 1, 0], ![2, -60, -36, -1, 4], ![-62, 41, 39, 3, -4], ![62, -19, -24, 0, 4], ![-24, 58, 44, 8, -1]]]
  hmulB := by decide  
  f := ![![![353, -259, -268, -3, 24]], ![![173, -127, -132, -2, 12]], ![![311, -228, -233, 0, 20]], ![![118, -87, -100, -10, 12]], ![![305, -223, -216, 11, 15]]]
  g := ![![![8, -17, 0, 1, 0], ![58, -60, -36, -1, 4], ![-52, 41, 39, 3, -4], ![27, -19, -24, 0, 4], ![-69, 58, 44, 8, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2

def I157N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![469, -345, -370, -29, 42]] i)))

def SI157N3: IdealEqSpanCertificate' Table ![![469, -345, -370, -29, 42]] 
 ![![157, 0, 0, 0, 0], ![131, 1, 0, 0, 0], ![146, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![138, 0, 0, 0, 1]] where
  M :=![![![469, -345, -370, -29, 42], ![-1318, 972, 1048, 87, -116], ![2486, -1817, -1959, -141, 232], ![-2962, 2233, 2440, 272, -224], ![2084, -1374, -1444, 100, 311]]]
  hmulB := by decide  
  f := ![![![-11567, 7665, 11402, 2947, -1962]], ![![-9239, 6081, 9074, 2348, -1562]], ![![-12200, 8203, 12121, 3125, -2084]], ![![2081, -1712, -2318, -577, 394]], ![![-15862, 10986, 16016, 4108, -2749]]]
  g := ![![![603, -345, -370, -29, 42], ![-1707, 972, 1048, 87, -116], ![3174, -1817, -1959, -141, 232], ![-4001, 2233, 2440, 272, -224], ![2212, -1374, -1444, 100, 311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N3 : Nat.card (O ⧸ I157N3) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N3)

lemma isPrimeI157N3 : Ideal.IsPrime I157N3 := prime_ideal_of_norm_prime hp157.out _ NI157N3
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![401, -299, -324, -47, 44]] ![![-47, 35, 30, 1, -3]]
  ![![1961, -1458, -4218, -1840, 971]] where
 M := ![![![1961, -1458, -4218, -1840, 971]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![1961, -1458, -4218, -1840, 971]] ![![-43, -17, 0, 1, 0]]
  ![![36893, -27517, -25130, -1467, 2709]] where
 M := ![![![36893, -27517, -25130, -1467, 2709]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N2 : IdealMulLeCertificate' Table 
  ![![36893, -27517, -25130, -1467, 2709]] ![![469, -345, -370, -29, 42]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![1087853, -811376, -749832, -48670, 82425]]]
 hmul := by decide  
 g := ![![![![6929, -5168, -4776, -310, 525]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2, I157N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
    exact isPrimeI157N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1 ⊙ MulI157N2)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3259, 2100, 2444, 206, -277]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-3259, 2100, 2444, 206, -277]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![36, 16, 131, 1, 0], ![15, 102, 58, 0, 1]] where
  M :=![![![-3259, 2100, 2444, 206, -277], ![8722, -6748, -7292, -581, 824], ![-17302, 12663, 13959, 1117, -1574], ![20366, -14789, -16288, -1262, 1822], ![-16226, 12116, 13142, 966, -1455]]]
  hmulB := by decide  
  f := ![![![101, -126, -150, -82, -31]], ![![766, -1074, -1328, -807, -328]], ![![3730, -5037, -6163, -3637, -1450]], ![![3204, -4330, -5299, -3129, -1248]], ![![2127, -2900, -3558, -2116, -848]]]
  g := ![![![-40, 166, -52, 206, -277], ![106, -500, 129, -581, 824], ![-208, 953, -252, 1117, -1574], ![236, -1107, 266, -1262, 1822], ![-179, 890, -178, 966, -1455]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [124, 126, 145, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 56, 158], [65, 106, 5], [0, 1]]
 g := ![![[120, 83, 46], [80, 135, 93], [43, 144], [33, 34], [117, 146], [35, 18, 1], []], ![[70, 161, 36, 47], [68, 160, 139, 144], [71, 143], [153, 54], [77, 93], [126, 15, 71, 55], [53, 25]], ![[122, 28, 16, 86], [108, 128, 63, 130], [49, 39], [94, 85], [84, 62], [97, 114, 152, 32], [43, 25]]]
 h' := ![![[116, 56, 158], [23, 159, 32], [128, 120, 16], [9, 50, 12], [134, 29, 94], [61, 41, 31], [0, 0, 1], [0, 1]], ![[65, 106, 5], [123, 97, 152], [149, 116, 118], [71, 129, 44], [61, 71, 39], [127, 55, 147], [38, 117, 106], [116, 56, 158]], ![[0, 1], [36, 70, 142], [159, 90, 29], [81, 147, 107], [162, 63, 30], [31, 67, 148], [34, 46, 56], [65, 106, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 78], []]
 b := ![[], [105, 87, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [124, 126, 145, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![194740232034, -275230586897, -335541808068, -205222480579, -86760139601]
  a := ![-37, -48, -6, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![54503997711, 72747627863, 193746572053, -205222480579, -86760139601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, 126, 150, 82, 31]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-101, 126, 150, 82, 31]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![56, 33, 1, 0, 0], ![108, 97, 0, 1, 0], ![29, 40, 0, 0, 1]] where
  M :=![![![-101, 126, 150, 82, 31], ![-766, 1074, 1328, 807, 328], ![-3730, 5037, 6163, 3637, 1450], ![-17730, 24223, 29736, 17716, 7110], ![-50714, 69116, 84794, 50418, 20203]]]
  hmulB := by decide  
  f := ![![![3259, -2100, -2444, -206, 277]], ![![-8722, 6748, 7292, 581, -824]], ![![-540, 567, 551, 40, -62]], ![![-3156, 2715, 2820, 217, -318]], ![![-1461, 1208, 1274, 100, -144]]]
  g := ![![![-112, -86, 150, 82, 31], ![-1054, -823, 1328, 807, 328], ![-4808, -3737, 6163, 3637, 1450], ![-23328, -18159, 29736, 17716, 7110], ![-66443, -51704, 84794, 50418, 20203]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [91, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 162], [0, 1]]
 g := ![![[31, 43], [128, 146], [100], [24], [133], [156, 55], [1]], ![[0, 120], [0, 17], [100], [24], [133], [14, 108], [1]]]
 h' := ![![[113, 162], [88, 80], [83, 31], [50, 153], [21, 137], [148, 40], [72, 113], [0, 1]], ![[0, 1], [0, 83], [0, 132], [61, 10], [17, 26], [104, 123], [127, 50], [113, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [45, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [91, 50, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103321, 207198, 238391, 180244, 103738]
  a := ![-8, -7, 1, -1, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-220417, -179711, 238391, 180244, 103738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-3259, 2100, 2444, 206, -277]] ![![-101, 126, 150, 82, 31]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1731, 849, 26, -49, -1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![1731, 849, 26, -49, -1]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![106, 153, 141, 49, 1]] where
  M :=![![![1731, 849, 26, -49, -1], ![-68, 2577, 1756, 82, -196], ![3056, -1998, -2303, -188, 262], ![-4084, 1888, 2552, 239, -278], ![1846, -2878, -2482, -114, 301]]]
  hmulB := by decide  
  f := ![![![-197, 147, 136, 9, -15]], ![![468, -349, -324, -22, 36]], ![![-796, 594, 555, 40, -62]], ![![736, -548, -524, -43, 62]], ![![-156, 117, 107, 7, -11]]]
  g := ![![![11, 6, 1, 0, -1], ![124, 195, 176, 58, -196], ![-148, -252, -235, -78, 262], ![152, 266, 250, 83, -278], ![-180, -293, -269, -89, 301]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [20, 12, 155, 59, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 77, 54, 123], [47, 8, 12, 161], [121, 81, 101, 50], [0, 1]]
 g := ![![[3, 76, 11, 116], [64, 114, 33, 58], [165, 90, 24, 162], [25, 100, 85], [2, 79, 29], [108, 1], []], ![[49, 111, 106, 95, 163, 60], [65, 68, 53, 64, 131, 125], [18, 2, 25, 144, 39, 78], [88, 80, 21], [87, 157, 54], [30, 155, 165, 165, 80, 125], [73, 95, 99]], ![[60, 134, 125, 149, 146, 43], [123, 120, 127, 158, 149, 119], [86, 48, 77, 64, 142, 106], [115, 69, 108], [92, 60, 25], [160, 47, 151, 90, 6, 74], [24, 70, 36]], ![[149, 11, 11, 101, 25, 98], [77, 51, 90, 92, 146, 61], [25, 10, 62, 82, 97, 137], [132, 23, 3], [75, 106, 72], [163, 75, 40, 126, 147, 19], [124, 41, 162]]]
 h' := ![![[107, 77, 54, 123], [56, 55, 143, 139], [40, 124, 24, 152], [49, 13, 148, 117], [81, 5, 90, 98], [11, 20, 115, 153], [0, 0, 1], [0, 1]], ![[47, 8, 12, 161], [40, 152, 132, 153], [16, 63, 10, 56], [4, 44, 0, 122], [125, 111, 113, 45], [23, 97, 72, 87], [136, 8, 44, 56], [107, 77, 54, 123]], ![[121, 81, 101, 50], [122, 43, 99, 74], [31, 21, 58, 141], [134, 75, 25, 47], [51, 72, 124, 129], [87, 77, 70, 5], [59, 66, 87, 123], [47, 8, 12, 161]], ![[0, 1], [142, 84, 127, 135], [95, 126, 75, 152], [19, 35, 161, 48], [34, 146, 7, 62], [96, 140, 77, 89], [137, 93, 35, 155], [121, 81, 101, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [73, 92, 78], []]
 b := ![[], [], [72, 166, 29, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [20, 12, 155, 59, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29851637510601522, 40896429003955338, 50137071604321486, 29934991208178950, 12087973160910366]
  a := ![52, 39, -8, -1, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7851358039323954, -10829721345001980, -9905791281940360, -3367519123810952, 12087973160910366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197, 147, 136, 9, -15]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-197, 147, 136, 9, -15]] 
 ![![167, 0, 0, 0, 0], ![138, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![134, 0, 0, 0, 1]] where
  M :=![![![-197, 147, 136, 9, -15], ![468, -349, -324, -22, 36], ![-796, 594, 555, 40, -62], ![736, -548, -524, -43, 62], ![-602, 452, 446, 48, -51]]]
  hmulB := by decide  
  f := ![![![1731, 849, 26, -49, -1]], ![![1430, 717, 32, -40, -2]], ![![1003, 471, 1, -29, 1]], ![![556, 296, 24, -15, -2]], ![![1400, 664, 6, -40, 1]]]
  g := ![![![-191, 147, 136, 9, -15], ![454, -349, -324, -22, 36], ![-775, 594, 555, 40, -62], ![720, -548, -524, -43, 62], ![-606, 452, 446, 48, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![1731, 849, 26, -49, -1]] ![![-197, 147, 136, 9, -15]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -83, -66, -29, -10]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-7, -83, -66, -29, -10]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![21, 43, 45, 1, 0], ![9, 22, 101, 0, 1]] where
  M :=![![![-7, -83, -66, -29, -10], ![242, -446, -508, -293, -116], ![1326, -1815, -2219, -1317, -528], ![6482, -8787, -10804, -6430, -2576], ![18392, -25016, -30716, -18282, -7333]]]
  hmulB := by decide  
  f := ![![![-195, 139, 186, 19, -22]], ![![698, -508, -640, -65, 76]], ![![-1554, 1131, 1397, 147, -168]], ![![-241, 175, 215, 23, -26]], ![![-841, 612, 755, 80, -91]]]
  g := ![![![4, 8, 13, -29, -10], ![43, 85, 141, -293, -116], ![195, 384, 638, -1317, -528], ![952, 1875, 3114, -6430, -2576], ![2707, 5332, 8859, -18282, -7333]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [144, 66, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 169, 67], [161, 3, 106], [0, 1]]
 g := ![![[112, 74, 150], [66, 51], [161, 7, 159], [52, 73, 116], [35, 148], [113, 122, 1], []], ![[74, 166, 13, 21], [13, 38], [158, 127, 128, 172], [142, 172, 103, 83], [168, 158], [75, 28, 100, 84], [96, 164]], ![[28, 66, 41, 10], [129, 29], [42, 110, 71, 31], [145, 4, 105, 106], [16, 116], [144, 46, 156, 139], [57, 164]]]
 h' := ![![[134, 169, 67], [15, 147, 91], [171, 109, 140], [124, 116, 32], [77, 110, 17], [163, 59, 54], [0, 0, 1], [0, 1]], ![[161, 3, 106], [74, 107, 88], [40, 61, 111], [150, 134, 83], [118, 148, 155], [69, 146, 136], [153, 116, 3], [134, 169, 67]], ![[0, 1], [23, 92, 167], [112, 3, 95], [11, 96, 58], [69, 88, 1], [132, 141, 156], [67, 57, 169], [161, 3, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 117], []]
 b := ![[], [58, 34, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [144, 66, 51, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124767452134, -177158233728, -215799594618, -132449009574, -56356596873]
  a := ![-35, -20, 10, 2, -69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19730670665, 39063550920, 66106486245, -132449009574, -56356596873]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195, 139, 186, 19, -22]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-195, 139, 186, 19, -22]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![77, 129, 1, 0, 0], ![101, 157, 0, 1, 0], ![118, 119, 0, 0, 1]] where
  M :=![![![-195, 139, 186, 19, -22], ![698, -508, -640, -65, 76], ![-1554, 1131, 1397, 147, -168], ![2318, -1695, -2056, -240, 256], ![-2140, 1570, 1924, 252, -249]]]
  hmulB := by decide  
  f := ![![![-7, -83, -66, -29, -10]], ![![242, -446, -508, -293, -116]], ![![185, -380, -421, -239, -94]], ![![253, -504, -562, -320, -126]], ![![268, -508, -572, -327, -129]]]
  g := ![![![-80, -140, 186, 19, -22], ![275, 481, -640, -65, 76], ![-602, -1053, 1397, 147, -168], ![894, 1565, -2056, -240, 256], ![-846, -1483, 1924, 252, -249]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [38, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 172], [0, 1]]
 g := ![![[152, 41], [51], [20, 16], [26, 126], [33], [159, 164], [1]], ![[0, 132], [51], [159, 157], [61, 47], [33], [70, 9], [1]]]
 h' := ![![[106, 172], [91, 53], [105, 33], [50, 4], [126, 105], [13, 129], [135, 106], [0, 1]], ![[0, 1], [0, 120], [143, 140], [128, 169], [11, 68], [20, 44], [126, 67], [106, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [153, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [38, 67, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![101126, -12934, -48150, 41410, 79776]
  a := ![8, -2, -6, -10, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-56574, -56626, -48150, 41410, 79776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-7, -83, -66, -29, -10]] ![![-195, 139, 186, 19, -22]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6201, 6336, 2304, -76, -251]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![6201, 6336, 2304, -76, -251]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![177, 42, 1, 0, 0], ![84, 136, 0, 1, 0], ![67, 118, 0, 0, 1]] where
  M :=![![![6201, 6336, 2304, -76, -251], ![7378, 7562, 2784, -85, -304], ![786, 673, 175, -19, -18], ![-3438, -3225, -1060, 56, 114], ![-4394, -4742, -1830, 40, 201]]]
  hmulB := by decide  
  f := ![![![129, -174, -218, -128, -49]], ![![1214, -1684, -2052, -1239, -512]], ![![445, -611, -751, -449, -181]], ![![1134, -1569, -1916, -1154, -474]], ![![1291, -1776, -2172, -1302, -530]]]
  g := ![![![-2114, -282, 2304, -76, -251], ![-2558, -346, 2784, -85, -304], ![-153, -11, 175, -19, -18], ![960, 113, -1060, 56, 114], ![1691, 240, -1830, 40, 201]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [67, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 178], [0, 1]]
 g := ![![[125, 171], [11, 31], [47], [142], [113, 138], [18, 12], [1]], ![[0, 8], [115, 148], [47], [142], [166, 41], [116, 167], [1]]]
 h' := ![![[38, 178], [158, 156], [174, 63], [97, 88], [126, 121], [47, 73], [112, 38], [0, 1]], ![[0, 1], [0, 23], [62, 116], [40, 91], [70, 58], [136, 106], [124, 141], [38, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [46, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [67, 141, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1381131, 2996025, 3401582, 2655389, 1606379]
  a := ![40, 24, -6, 1, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5218666, -3857855, 3401582, 2655389, 1606379]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-194095, 264671, 324748, 193179, 77438]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-194095, 264671, 324748, 193179, 77438]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![105, 36, 1, 0, 0], ![158, 28, 0, 1, 0], ![144, 15, 0, 0, 1]] where
  M :=![![![-194095, 264671, 324748, 193179, 77438], ![-1936782, 2641026, 3240504, 1927639, 772716], ![-8694710, 11856243, 14547455, 8653667, 3468920], ![-42411742, 57833321, 70960724, 42211542, 16920976], ![-120654792, 164526768, 201872184, 120085242, 48137527]]]
  hmulB := by decide  
  f := ![![![-35789, 25379, 28736, 2405, -3266]], ![![102790, -76388, -84692, -6987, 9620]], ![![-1453, 354, 747, 82, -86]], ![![-14148, 9455, 11008, 938, -1252]], ![![-21294, 14838, 16932, 1425, -1925]]]
  g := ![![![-424391, -100541, 324748, 193179, 77438], ![-4234792, -1003250, 3240504, 1927639, 772716], ![-19011069, -4503847, 14547455, 8653667, 3468920], ![-92733698, -21969221, 70960724, 42211542, 16920976], ![-263812884, -62499003, 201872184, 120085242, 48137527]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [144, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 178], [0, 1]]
 g := ![![[98, 46], [141, 171], [65], [70], [84, 101], [106, 125], [1]], ![[0, 133], [88, 8], [65], [70], [149, 78], [151, 54], [1]]]
 h' := ![![[29, 178], [102, 15], [12, 23], [171, 94], [76, 138], [130, 82], [35, 29], [0, 1]], ![[0, 1], [0, 164], [142, 156], [33, 85], [140, 41], [2, 97], [160, 150], [29, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [94, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [144, 150, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13086, 41822, 45190, 39962, 28522]
  a := ![4, 1, -2, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-84800, -17496, 45190, 39962, 28522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 32, 32, 6, -1]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-39, 32, 32, 6, -1]] 
 ![![179, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![112, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![-39, 32, 32, 6, -1], ![42, -4, 12, 39, 24], ![-342, 375, 431, 201, 66], ![-810, 1191, 1488, 938, 390], ![-2810, 3764, 4598, 2694, 1069]]]
  hmulB := by decide  
  f := ![![![-1951, 1814, 2294, 534, -379]], ![![-203, 204, 250, 57, -41]], ![![-591, 507, 665, 159, -111]], ![![-578, 655, 760, 164, -122]], ![![-1563, 1286, 1724, 420, -290]]]
  g := ![![![-14, 32, 32, 6, -1], ![-34, -4, 12, 39, 24], ![-282, 375, 431, 201, 66], ![-1165, 1191, 1488, 938, 390], ![-3439, 3764, 4598, 2694, 1069]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![6201, 6336, 2304, -76, -251]] ![![-194095, 264671, 324748, 193179, 77438]]
  ![![-503, -1685, -1196, -483, -159]] where
 M := ![![![-503, -1685, -1196, -483, -159]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-503, -1685, -1196, -483, -159]] ![![-39, 32, 32, 6, -1]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![1195899, -1631585, -2001578, -1190529, -477214]]]
 hmul := by decide  
 g := ![![![![6681, -9115, -11182, -6651, -2666]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0, 0, 0]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![0, 0, 0, 0, 181]] where
  M :=![![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![0, 0, 0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 5 2 7 [10, 174, 111, 135, 82, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 102, 52, 70, 68], [121, 40, 10, 63, 156], [152, 42, 89, 175, 158], [5, 177, 30, 54, 161], [0, 1]]
 g := ![![[36, 36, 64, 107, 144], [70, 88, 162, 43], [164, 139, 175, 51, 80], [136, 38, 148, 102], [161, 129, 159, 16, 27], [1], []], ![[107, 163, 157, 126, 42, 21, 92, 68], [153, 81, 54, 132], [73, 94, 41, 37, 169, 86, 66, 85], [92, 106, 78, 126], [30, 73, 41, 58, 54, 47, 65, 74], [31, 8, 87, 48, 41, 151, 11, 163], [123, 26, 135, 99]], ![[155, 179, 158, 92, 110, 34, 76, 170], [76, 146, 103, 33], [68, 117, 131, 141, 115, 133, 142, 29], [95, 119, 36, 46], [60, 75, 154, 29, 147, 131, 130, 79], [62, 148, 40, 142, 143, 12, 171, 152], [152, 56, 81, 82]], ![[108, 68, 139, 17, 33, 150, 84, 91], [122, 162, 101, 11], [167, 81, 81, 22, 40, 82, 41, 140], [103, 118, 165, 46], [83, 173, 61, 155, 126, 87, 70, 32], [78, 31, 88, 51, 132, 70, 90, 31], [94, 162, 157, 167]], ![[86, 73, 89, 89, 61, 54, 77, 165], [92, 55, 83, 67], [150, 126, 149, 124, 41, 39, 116, 114], [87, 22, 179, 49], [9, 142, 65, 76, 173, 129, 90, 178], [139, 71, 61, 60, 151, 122, 93, 80], [48, 67, 154, 38]]]
 h' := ![![[2, 102, 52, 70, 68], [145, 49, 39, 39, 169], [170, 87, 108, 52, 119], [87, 169, 49, 132, 108], [19, 118, 126, 110, 144], [171, 7, 70, 46, 99], [0, 0, 1], [0, 1]], ![[121, 40, 10, 63, 156], [163, 137, 58, 129, 1], [173, 53, 119, 79, 133], [19, 122, 127, 140, 77], [45, 10, 80, 180, 44], [156, 53, 18, 162, 174], [41, 104, 135, 40, 47], [2, 102, 52, 70, 68]], ![[152, 42, 89, 175, 158], [20, 28, 90, 42, 89], [150, 78, 159, 81, 157], [77, 141, 132, 65, 173], [22, 155, 52, 104, 74], [150, 82, 154, 21, 65], [89, 48, 124, 98, 152], [121, 40, 10, 63, 156]], ![[5, 177, 30, 54, 161], [176, 71, 172, 36, 56], [126, 152, 47, 90, 83], [13, 153, 136, 44, 174], [89, 158, 148, 48, 107], [66, 44, 27, 111, 95], [82, 41, 31, 111, 20], [152, 42, 89, 175, 158]], ![[0, 1], [124, 77, 3, 116, 47], [35, 173, 110, 60, 51], [44, 139, 99, 162, 11], [178, 102, 137, 101, 174], [44, 176, 93, 22, 110], [88, 169, 71, 113, 143], [5, 177, 30, 54, 161]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 3, 175, 180], [], [], []]
 b := ![[], [123, 68, 153, 25, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 5
  hpos := by decide
  P := [10, 174, 111, 135, 82, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1193908600792524713607, 1629180243471552065783, 1998727665165908853662, 1189625702419144007636, 477406823084788673860]
  a := ![49, 29, -10, -4, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6596180114875827147, 9000995820284818043, 11042694282684579302, 6572517692923447556, 2637606757374523060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 194264244901 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-587, -601, -220, 7, 24]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-587, -601, -220, 7, 24]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![130, 187, 1, 0, 0], ![138, 143, 0, 1, 0], ![164, 8, 0, 0, 1]] where
  M :=![![![-587, -601, -220, 7, 24], ![-706, -712, -256, 9, 28], ![-58, -75, -33, 1, 4], ![294, 331, 132, 0, -12], ![428, 448, 172, 6, -13]]]
  hmulB := by decide  
  f := ![![![-237, 179, 144, 9, -16]], ![![498, -378, -300, -25, 36]], ![![322, -245, -193, -18, 24]], ![![206, -157, -124, -13, 16]], ![![-188, 142, 116, 8, -13]]]
  g := ![![![121, 206, -220, 7, 24], ![140, 239, -256, 9, 28], ![18, 31, -33, 1, 4], ![-78, -127, 132, 0, -12], ![-108, -170, 172, 6, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [60, 189, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 190], [0, 1]]
 g := ![![[70, 156], [20, 107], [167, 3], [2, 34], [114, 6], [150, 4], [1]], ![[0, 35], [43, 84], [173, 188], [70, 157], [126, 185], [158, 187], [1]]]
 h' := ![![[2, 190], [137, 27], [103, 38], [71, 24], [36, 15], [168, 31], [131, 2], [0, 1]], ![[0, 1], [0, 164], [179, 153], [119, 167], [66, 176], [39, 160], [135, 189], [2, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [157, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [60, 189, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-492920, 1151045, 1292892, 1039447, 652503]
  a := ![22, 13, -6, -1, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2193838, -2065344, 1292892, 1039447, 652503]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27073, 19625, 21728, 1783, -2464]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-27073, 19625, 21728, 1783, -2464]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![134, 121, 1, 0, 0], ![21, 3, 0, 1, 0], ![15, 29, 0, 0, 1]] where
  M :=![![![-27073, 19625, 21728, 1783, -2464], ![77486, -57176, -62876, -5143, 7132], ![-150866, 110719, 122045, 10021, -13852], ![179058, -131317, -144904, -11988, 16476], ![-146696, 107878, 119028, 9928, -13563]]]
  hmulB := by decide  
  f := ![![![3977, -4327, -4908, -2271, -744]], ![![17778, -26834, -33872, -21681, -9084]], ![![14606, -20767, -25791, -15844, -6480]], ![![3203, -4308, -5264, -3096, -1232]], ![![10203, -14205, -17536, -10604, -4295]]]
  g := ![![![-15388, -13316, 21728, 1783, -2464], ![44523, 38531, -62876, -5143, 7132], ![-86427, -74791, 122045, 10021, -13852], ![102622, 88797, -144904, -11988, 16476], ![-84301, -72937, 119028, 9928, -13563]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [157, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 190], [0, 1]]
 g := ![![[188, 24], [161, 50], [175, 67], [146, 23], [64, 68], [119, 90], [1]], ![[32, 167], [27, 141], [26, 124], [92, 168], [4, 123], [107, 101], [1]]]
 h' := ![![[89, 190], [126, 62], [29, 94], [189, 110], [75, 65], [35, 100], [34, 89], [0, 1]], ![[0, 1], [105, 129], [182, 97], [47, 81], [130, 126], [149, 91], [124, 102], [89, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [8, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [157, 102, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-258389, 541189, 617327, 473876, 282172]
  a := ![16, 10, -3, 1, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-508713, -438534, 617327, 473876, 282172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -12, -14, -8, -3]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![7, -12, -14, -8, -3]] 
 ![![191, 0, 0, 0, 0], ![150, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![114, 0, 0, 1, 0], ![119, 0, 0, 0, 1]] where
  M :=![![![7, -12, -14, -8, -3], ![74, -106, -128, -77, -32], ![366, -491, -605, -355, -138], ![1678, -2313, -2832, -1700, -694], ![4954, -6716, -8250, -4886, -1941]]]
  hmulB := by decide  
  f := ![![![50299, -36954, -40984, -3372, 4651]], ![![38736, -28460, -31564, -2597, 3582]], ![![37045, -27215, -30181, -2483, 3425]], ![![28240, -20749, -23016, -1894, 2612]], ![![32797, -24094, -26718, -2198, 3032]]]
  g := ![![![26, -12, -14, -8, -3], ![240, -106, -128, -77, -32], ![1113, -491, -605, -355, -138], ![5274, -2313, -2832, -1700, -694], ![15257, -6716, -8250, -4886, -1941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-587, -601, -220, 7, 24]] ![![-27073, 19625, 21728, 1783, -2464]]
  ![![245987, 154574, 26584, -5942, -2704]] where
 M := ![![![245987, 154574, 26584, -5942, -2704]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![245987, 154574, 26584, -5942, -2704]] ![![7, -12, -14, -8, -3]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-476163, -485522, -176866, 5730, 19291]]]
 hmul := by decide  
 g := ![![![![-2493, -2542, -926, 30, 101]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15095, 11081, 12206, 997, -1383]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-15095, 11081, 12206, 997, -1383]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![91, 103, 1, 0, 0], ![84, 7, 0, 1, 0], ![38, 5, 0, 0, 1]] where
  M :=![![![-15095, 11081, 12206, 997, -1383], ![43484, -31915, -35152, -2862, 3988], ![-84424, 61992, 68283, 5596, -7718], ![99624, -73028, -80388, -6405, 9198], ![-81946, 60436, 66610, 5796, -7273]]]
  hmulB := by decide  
  f := ![![![-26337, 11557, 13296, 1029, -1463]], ![![45948, -43911, -37464, -2234, 4116]], ![![11653, -17654, -13417, -687, 1473]], ![![-9388, 3155, 4160, 349, -458]], ![![-4280, 1381, 1862, 158, -205]]]
  g := ![![![-5995, -6457, 12206, 997, -1383], ![17260, 18595, -35152, -2862, 3988], ![-33549, -36123, 68283, 5596, -7718], ![39396, 42517, -80388, -6405, 9198], ![-32922, -35257, 66610, 5796, -7273]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [178, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [146, 192], [0, 1]]
 g := ![![[177, 16], [165], [151], [48], [121], [165], [146, 1]], ![[4, 177], [165], [151], [48], [121], [165], [99, 192]]]
 h' := ![![[146, 192], [92, 4], [133, 101], [143, 94], [141, 137], [16, 182], [67, 101], [0, 1]], ![[0, 1], [97, 189], [18, 92], [164, 99], [71, 56], [147, 11], [145, 92], [146, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [1, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [178, 47, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13692430, 30552158, 34571698, 27377676, 16724563]
  a := ![-105, -72, 16, 0, -217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31580182, -19718131, 34571698, 27377676, 16724563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 28, 40, 10, -7]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-39, 28, 40, 10, -7]] 
 ![![193, 0, 0, 0, 0], ![92, 1, 0, 0, 0], ![161, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![160, 0, 0, 0, 1]] where
  M :=![![![-39, 28, 40, 10, -7], ![230, -174, -244, -63, 40], ![-778, 573, 811, 199, -146], ![2274, -1727, -2424, -644, 378], ![-2958, 2112, 3018, 678, -619]]]
  hmulB := by decide  
  f := ![![![23243, -17146, -19278, -1610, 2193]], ![![10722, -7912, -8896, -743, 1012]], ![![20093, -14819, -16659, -1391, 1895]], ![![8179, -6037, -6794, -568, 773]], ![![19970, -14728, -16554, -1382, 1883]]]
  g := ![![![-45, 28, 40, 10, -7], ![279, -174, -244, -63, 40], ![-910, 573, 811, 199, -146], ![2794, -1727, -2424, -644, 378], ![-3290, 2112, 3018, 678, -619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-505, 371, 406, 33, -46]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-505, 371, 406, 33, -46]] 
 ![![193, 0, 0, 0, 0], ![139, 1, 0, 0, 0], ![113, 0, 1, 0, 0], ![183, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-505, 371, 406, 33, -46], ![1446, -1062, -1164, -95, 132], ![-2798, 2055, 2255, 185, -256], ![3302, -2425, -2668, -222, 304], ![-2712, 1992, 2196, 186, -251]]]
  hmulB := by decide  
  f := ![![![1247, 1393, 538, -11, -58]], ![![907, 1011, 390, -8, -42]], ![![729, 818, 317, -6, -34]], ![![1179, 1318, 510, -9, -54]], ![![92, 118, 52, 4, -3]]]
  g := ![![![-535, 371, 406, 33, -46], ![1533, -1062, -1164, -95, 132], ![-2969, 2055, 2255, 185, -256], ![3511, -2425, -2668, -222, 304], ![-2890, 1992, 2196, 186, -251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2

def I193N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -33, -40, -23, -9]] i)))

def SI193N3: IdealEqSpanCertificate' Table ![![25, -33, -40, -23, -9]] 
 ![![193, 0, 0, 0, 0], ![143, 1, 0, 0, 0], ![126, 0, 1, 0, 0], ![87, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![25, -33, -40, -23, -9], ![224, -309, -380, -228, -92], ![1040, -1412, -1731, -1026, -410], ![5012, -6842, -8396, -4999, -2006], ![14306, -19500, -23926, -14228, -5701]]]
  hmulB := by decide  
  f := ![![![4375, -3969, -3958, -299, 447]], ![![3169, -2892, -2878, -217, 325]], ![![2990, -2690, -2691, -204, 304]], ![![1817, -1673, -1658, -124, 187]], ![![1559, -1389, -1396, -107, 158]]]
  g := ![![![64, -33, -40, -23, -9], ![611, -309, -380, -228, -92], ![2778, -1412, -1731, -1026, -410], ![13485, -6842, -8396, -4999, -2006], ![38417, -19500, -23926, -14228, -5701]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N3 : Nat.card (O ⧸ I193N3) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N3)

lemma isPrimeI193N3 : Ideal.IsPrime I193N3 := prime_ideal_of_norm_prime hp193.out _ NI193N3
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-15095, 11081, 12206, 997, -1383]] ![![-39, 28, 40, 10, -7]]
  ![![-841, 569, 880, 199, -228]] where
 M := ![![![-841, 569, 880, 199, -228]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-841, 569, 880, 199, -228]] ![![-505, 371, 406, 33, -46]]
  ![![60673, -44640, -50982, -5594, 6238]] where
 M := ![![![60673, -44640, -50982, -5594, 6238]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N2 : IdealMulLeCertificate' Table 
  ![![60673, -44640, -50982, -5594, 6238]] ![![25, -33, -40, -23, -9]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-300115, 411283, 502958, 300115, 122169]]]
 hmul := by decide  
 g := ![![![![-1555, 2131, 2606, 1555, 633]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2, I193N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
    exact isPrimeI193N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1 ⊙ MulI193N2)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-270775, 202362, 181154, 11154, -19788]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-270775, 202362, 181154, 11154, -19788]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![169, 51, 95, 21, 1]] where
  M :=![![![-270775, 202362, 181154, 11154, -19788], ![615948, -461111, -409104, -24818, 44616], ![-1002032, 750354, 660579, 39566, -71944], ![810752, -608182, -523540, -30263, 56824], ![-604252, 453682, 388108, 22350, -42135]]]
  hmulB := by decide  
  f := ![![![44805, -61098, -74966, -44594, -17876]], ![![447092, -609663, -748048, -444982, -178376]], ![![2007112, -2736930, -3358177, -1997638, -800776]], ![![9790456, -13350418, -16380788, -9744239, -3906088]], ![![2307113, -3146017, -3860121, -2296223, -920467]]]
  g := ![![![15601, 6150, 10462, 2166, -19788], ![-35148, -13891, -23592, -4882, 44616], ![56632, 22434, 38047, 7870, -71944], ![-44632, -17798, -30060, -6211, 56824], ![33079, 13211, 22289, 4605, -42135]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [65, 84, 37, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [187, 139, 160, 19], [137, 93, 129, 138], [56, 161, 105, 40], [0, 1]]
 g := ![![[182, 76, 133, 127], [10, 51, 116], [6, 42, 41, 172], [151, 6, 37], [24, 164, 164], [159, 183, 1], []], ![[91, 131, 49, 29, 119, 25], [176, 44, 116], [113, 68, 47, 11, 82, 28], [74, 127, 60], [158, 23, 62], [64, 76, 40], [18, 53, 20, 174, 30, 161]], ![[103, 65, 160, 105, 39, 109], [106, 92, 168], [9, 142, 108, 108, 88, 155], [23, 176, 116], [27, 71, 172], [1, 166, 142], [6, 28, 37, 60, 152, 92]], ![[52, 173, 51, 103, 140, 133], [163, 41, 142], [64, 192, 168, 196, 17, 39], [109, 52, 16], [195, 61, 47], [174, 62, 41], [1, 38, 137, 28, 30, 172]]]
 h' := ![![[187, 139, 160, 19], [154, 36, 29, 179], [4, 56, 77, 71], [170, 33, 119, 127], [23, 195, 63, 148], [106, 162, 153, 178], [0, 0, 0, 1], [0, 1]], ![[137, 93, 129, 138], [164, 66, 174, 41], [104, 34, 181, 71], [56, 121, 120, 74], [170, 80, 22, 116], [183, 110, 80, 125], [194, 101, 156, 146], [187, 139, 160, 19]], ![[56, 161, 105, 40], [95, 111, 91, 41], [22, 5, 13, 94], [115, 11, 130, 34], [172, 83, 176, 126], [96, 104, 36, 70], [113, 134, 33, 158], [137, 93, 129, 138]], ![[0, 1], [37, 181, 100, 133], [83, 102, 123, 158], [90, 32, 25, 159], [87, 36, 133, 4], [101, 18, 125, 21], [24, 159, 8, 89], [56, 161, 105, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [101, 50, 15], []]
 b := ![[], [], [70, 165, 7, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [65, 84, 37, 14, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9552791661687641, 13081446995207208, 16038509688285194, 9572657023859776, 3862852045989700]
  a := ![-38, -25, 7, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3362308565654553, -933624402793236, -1781382917161098, -363183938791492, 3862852045989700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44805, 61098, 74966, 44594, 17876]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-44805, 61098, 74966, 44594, 17876]] 
 ![![197, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![101, 0, 0, 0, 1]] where
  M :=![![![-44805, 61098, 74966, 44594, 17876], ![-447092, 609663, 748048, 444982, 178376], ![-2007112, 2736930, 3358177, 1997638, 800776], ![-9790456, 13350418, 16380788, 9744239, 3906088], ![-27852308, 37979846, 46600772, 27720834, 11112211]]]
  hmulB := by decide  
  f := ![![![270775, -202362, -181154, -11154, 19788]], ![![152191, -113735, -101834, -6272, 11124]], ![![87556, -65442, -58527, -3598, 6392]], ![![-2741, 2060, 1738, 97, -188]], ![![141891, -106052, -94846, -5832, 10359]]]
  g := ![![![-67497, 61098, 74966, 44594, 17876], ![-673517, 609663, 748048, 444982, 178376], ![-3023588, 2736930, 3358177, 1997638, 800776], ![-14748701, 13350418, 16380788, 9744239, 3906088], ![-41957743, 37979846, 46600772, 27720834, 11112211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-270775, 202362, 181154, 11154, -19788]] ![![-44805, 61098, 74966, 44594, 17876]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![-197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)


lemma PB3864I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB3864I4 : PrimesBelowBoundCertificateInterval O 151 197 3864 where
  m := 9
  g := ![4, 2, 2, 2, 3, 1, 3, 4, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB3864I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2, I157N3]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1, I193N2, I193N3]
    · exact ![I197N0, I197N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![24649, 157, 157, 157]
    · exact ![4330747, 26569]
    · exact ![777796321, 167]
    · exact ![5177717, 29929]
    · exact ![32041, 32041, 179]
    · exact ![194264244901]
    · exact ![36481, 36481, 191]
    · exact ![37249, 193, 193, 193]
    · exact ![1506138481, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
      exact NI157N3
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
      exact NI193N3
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I157N2, I157N3, I167N1, I179N2, I191N2, I193N1, I193N2, I193N3, I197N1]
  Il := ![[I157N1, I157N2, I157N3], [], [I167N1], [], [I179N2], [], [I191N2], [I193N1, I193N2, I193N3], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
