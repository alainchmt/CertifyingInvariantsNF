
import IdealArithmetic.Examples.NF5_1_40500000_1.RI5_1_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![267, -217, -427, 1216, 1402]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![267, -217, -427, 1216, 1402]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![147, 34, 153, 75, 1]] where
  M :=![![![267, -217, -427, 1216, 1402], ![6638, -652, -2463, 2182, 5522], ![20930, -3495, -1676, -7040, 890], ![-4460, 877, 3083, -4701, -8660], ![4202, -722, -580, -1528, 1087]]]
  hmulB := by decide  
  f := ![![![-2923825, -838053, 392989, -1180870, -1701162]], ![![-7465226, -2139750, 1003395, -3015044, -4343474]], ![![-19060510, -5463295, 2561908, -7698130, -11089930]], ![![-1133992, -325035, 152419, -457995, -659788]], ![![-23505399, -6737329, 3159342, -9493325, -13676089]]]
  g := ![![![-1311, -305, -1369, -662, 1402], ![-5128, -1200, -5397, -2624, 5522], ![-700, -215, -878, -470, 890], ![8080, 1881, 8459, 4107, -8660], ![-991, -240, -1063, -529, 1087]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [70, 149, 76, 154, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 146, 7, 109], [54, 122, 61, 4], [103, 45, 89, 44], [0, 1]]
 g := ![![[65, 47, 12, 9], [57, 132, 106], [24, 87, 95, 82], [147, 84, 59, 105], [52, 85, 42, 9], [1], []], ![[89, 26, 30, 44, 48, 36], [36, 37, 35], [87, 76, 86, 15, 66, 47], [36, 56, 138, 155, 119, 4], [108, 103, 39, 67, 83, 86], [79, 73, 48], [151, 117, 106]], ![[74, 31, 59, 62, 117, 57], [27, 33, 56], [156, 83, 55, 34, 91, 39], [127, 155, 82, 118, 66, 121], [123, 150, 110, 48, 47, 93], [113, 13, 58], [65, 65, 16]], ![[75, 61, 46, 79, 97, 3], [15, 119, 156], [149, 127, 138, 108, 14, 48], [78, 108, 24, 55, 60, 108], [4, 132, 42, 74, 154, 3], [37, 64, 9], [22, 138, 52]]]
 h' := ![![[3, 146, 7, 109], [103, 88, 81, 154], [47, 71, 51, 109], [72, 62, 5, 32], [128, 151, 47, 24], [87, 8, 81, 3], [0, 0, 1], [0, 1]], ![[54, 122, 61, 4], [109, 68, 97, 66], [66, 125, 55, 105], [110, 5, 10, 105], [145, 139, 44, 22], [2, 60, 138, 63], [115, 17, 101, 131], [3, 146, 7, 109]], ![[103, 45, 89, 44], [76, 82, 85, 140], [32, 34, 70, 128], [36, 118, 23, 150], [150, 45, 137, 73], [111, 55, 23, 45], [93, 40, 75, 23], [54, 122, 61, 4]], ![[0, 1], [124, 76, 51, 111], [111, 84, 138, 129], [9, 129, 119, 27], [138, 136, 86, 38], [35, 34, 72, 46], [120, 100, 137, 3], [103, 45, 89, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 57, 56], []]
 b := ![[], [], [75, 33, 45, 143], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [70, 149, 76, 154, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13739844, 8228207, 1973463, 7729734, -14793436]
  a := ![-11, -7, 13, -19, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13763664, 3256083, 14429103, 7116162, -14793436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2923825, -838053, 392989, -1180870, -1701162]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-2923825, -838053, 392989, -1180870, -1701162]] 
 ![![157, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-2923825, -838053, 392989, -1180870, -1701162], ![-7465226, -2139750, 1003395, -3015044, -4343474], ![-19060510, -5463295, 2561908, -7698130, -11089930], ![-1133992, -325035, 152419, -457995, -659788], ![-5420254, -1553602, 728532, -2189124, -3153653]]]
  hmulB := by decide  
  f := ![![![267, -217, -427, 1216, 1402]], ![![95, -47, -100, 254, 312]], ![![368, -213, -386, 1024, 1238]], ![![-8, -11, -13, 63, 52]], ![![122, -82, -156, 424, 507]]]
  g := ![![![498464, -838053, 392989, -1180870, -1701162], ![1272698, -2139750, 1003395, -3015044, -4343474], ![3249503, -5463295, 2561908, -7698130, -11089930], ![193327, -325035, 152419, -457995, -659788], ![924064, -1553602, 728532, -2189124, -3153653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![267, -217, -427, 1216, 1402]] ![![-2923825, -838053, 392989, -1180870, -1701162]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3469, 743, -663, 1234, 3162]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![3469, 743, -663, 1234, 3162]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![96, 34, 55, 24, 1]] where
  M :=![![![3469, 743, -663, 1234, 3162], ![11954, 1388, 203, 3396, 386], ![7950, 16365, -8414, 12990, 26010], ![4424, -2807, 239, -1013, 2396], ![-394, 7406, -2776, 5036, 6105]]]
  hmulB := by decide  
  f := ![![![967, -179, -441, 620, 1146]], ![![4678, -618, -893, -258, 1522]], ![![4050, -45, 1678, -6660, -6630]], ![![-5660, 887, 1777, -1517, -4100]], ![![2084, -119, 384, -2168, -1857]]]
  g := ![![![-1841, -655, -1071, -458, 3162], ![-154, -72, -129, -36, 386], ![-15270, -5325, -8828, -3750, 26010], ![-1384, -517, -807, -359, 2396], ![-3598, -1228, -2077, -868, 6105]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [18, 147, 77, 102, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [153, 10, 33, 40], [116, 103, 112, 49], [118, 49, 18, 74], [0, 1]]
 g := ![![[73, 124, 92, 46], [21, 135, 115, 36], [0, 9, 96], [25, 85, 21], [108, 107, 104], [61, 1], []], ![[151, 46, 0, 21, 93, 91], [44, 132, 78, 82, 105, 55], [37, 103, 57], [0, 38, 6], [13, 34, 150], [20, 83, 162, 62, 108, 62], [145, 158, 133]], ![[4, 58, 88, 13, 18, 64], [85, 157, 47, 20, 35, 22], [34, 116, 91], [32, 12, 83], [100, 107, 46], [95, 66, 108, 30, 103, 9], [132, 142, 119]], ![[7, 39, 120, 154, 97, 134], [162, 26, 80, 76, 50, 53], [145, 69, 143], [1, 127, 4], [149, 144, 131], [154, 22, 68, 71, 19, 15], [155, 105, 97]]]
 h' := ![![[153, 10, 33, 40], [111, 140, 34, 32], [21, 10, 24, 157], [99, 126, 86, 111], [68, 38, 118, 64], [43, 143, 46, 58], [0, 0, 1], [0, 1]], ![[116, 103, 112, 49], [93, 138, 136, 111], [51, 126, 135, 151], [126, 109, 100, 63], [17, 124, 25, 13], [96, 125, 133, 65], [98, 91, 145, 134], [153, 10, 33, 40]], ![[118, 49, 18, 74], [10, 52, 85, 71], [79, 101, 83, 63], [56, 86, 42, 108], [119, 95, 113, 88], [146, 2, 60, 131], [159, 143, 153, 47], [116, 103, 112, 49]], ![[0, 1], [101, 159, 71, 112], [53, 89, 84, 118], [113, 5, 98, 44], [72, 69, 70, 161], [132, 56, 87, 72], [50, 92, 27, 145], [118, 49, 18, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [72, 106, 159], []]
 b := ![[], [], [142, 26, 111, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [18, 147, 77, 102, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-877869811, 2903581004, -101165252, 871637636, -910389487]
  a := ![-49, -56, 48, -106, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![530794607, 207710574, 306565991, 139392548, -910389487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-967, 179, 441, -620, -1146]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-967, 179, 441, -620, -1146]] 
 ![![163, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![139, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-967, 179, 441, -620, -1146], ![-4678, 618, 893, 258, -1522], ![-4050, 45, -1678, 6660, 6630], ![5660, -887, -1777, 1517, 4100], ![-898, 14, -352, 1424, 1405]]]
  hmulB := by decide  
  f := ![![![-3469, -743, 663, -1234, -3162]], ![![-2989, -633, 556, -1058, -2660]], ![![-3007, -734, 617, -1132, -2856]], ![![-1751, -352, 328, -607, -1586]], ![![-934, -246, 196, -364, -891]]]
  g := ![![![85, 179, 441, -620, -1146], ![-1027, 618, 893, 258, -1522], ![-3731, 45, -1678, 6660, 6630], ![435, -887, -1777, 1517, 4100], ![-804, 14, -352, 1424, 1405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![3469, 743, -663, 1234, 3162]] ![![-967, 179, 441, -620, -1146]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6884473, -1973341, 925353, -2780526, -4005606]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-6884473, -1973341, 925353, -2780526, -4005606]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![128, 11, 1, 0, 0], ![93, 68, 0, 1, 0], ![157, 43, 0, 0, 1]] where
  M :=![![![-6884473, -1973341, 925353, -2780526, -4005606], ![-17577870, -5038234, 2362631, -7099260, -10227390], ![-44880690, -12863975, 6032156, -18126250, -26111910], ![-2669888, -765499, 358971, -1078471, -1553732], ![-12762966, -3658002, 1715300, -5154524, -7425313]]]
  hmulB := by decide  
  f := ![![![256185, -20123, 19731, -194368, -139198]], ![![-806330, 160472, 423783, -664190, -1137350]], ![![114860, -971, 49119, -192902, -192992]], ![![-186697, 53840, 181580, -372949, -533950]], ![![27131, 23237, 128984, -353814, -426193]]]
  g := ![![![4563709, 2090806, 925353, -2780526, -4005606], ![11652316, 5338325, 2362631, -7099260, -10227390], ![29750386, 13629817, 6032156, -18126250, -26111910], ![1770153, 810972, 358971, -1078471, -1553732], ![8460021, 3875867, 1715300, -5154524, -7425313]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [79, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 166], [0, 1]]
 g := ![![[26, 100], [41, 150], [17, 147], [62], [88], [134, 162], [1]], ![[36, 67], [56, 17], [15, 20], [62], [88], [50, 5], [1]]]
 h' := ![![[117, 166], [101, 10], [160, 22], [131, 67], [112, 79], [102, 103], [88, 117], [0, 1]], ![[0, 1], [102, 157], [62, 145], [121, 100], [3, 88], [129, 64], [83, 50], [117, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [9, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [79, 50, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-62, -174, 346, -489, -1098]
  a := ![-4, -4, 5, -9, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1039, 458, 346, -489, -1098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-733, -213, 99, -298, -426]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-733, -213, 99, -298, -426]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![96, 104, 1, 0, 0], ![37, 14, 0, 1, 0], ![84, 107, 0, 0, 1]] where
  M :=![![![-733, -213, 99, -298, -426], ![-1874, -536, 255, -756, -1106], ![-4830, -1355, 626, -1930, -2730], ![-268, -95, 43, -121, -172], ![-1388, -374, 174, -544, -771]]]
  hmulB := by decide  
  f := ![![![-179, 13, -23, 160, 126]], ![![698, -134, -341, 502, 902]], ![![354, -79, -230, 404, 642]], ![![19, -8, -32, 73, 98]], ![![362, -80, -231, 402, 643]]]
  g := ![![![219, 235, 99, -298, -426], ![566, 610, 255, -756, -1106], ![1412, 1513, 626, -1930, -2730], ![87, 93, 43, -121, -172], ![400, 429, 174, -544, -771]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [137, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 166], [0, 1]]
 g := ![![[81, 128], [74, 28], [110, 130], [57], [141], [143, 114], [1]], ![[0, 39], [145, 139], [46, 37], [57], [141], [110, 53], [1]]]
 h' := ![![[92, 166], [49, 63], [127, 144], [94, 56], [87, 70], [115, 108], [30, 92], [0, 1]], ![[0, 1], [0, 104], [15, 23], [69, 111], [14, 97], [31, 59], [144, 75], [92, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [126, 157]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [137, 75, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7028, 8271, 1376, 6612, -5125]
  a := ![36, 27, -39, 62, 143]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![364, 1922, 1376, 6612, -5125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15434702, 4424033, -2074566, 6233744, 8980335]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![15434702, 4424033, -2074566, 6233744, 8980335]] 
 ![![167, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![107, 0, 0, 1, 0], ![102, 0, 0, 0, 1]] where
  M :=![![![15434702, 4424033, -2074566, 6233744, 8980335], ![39408493, 11295616, -5296864, 15916242, 22928947], ![100619325, 28840415, -13524163, 40637980, 58543095], ![5986278, 1715841, -804611, 2417729, 3482982], ![28613206, 8201374, -3845878, 11556258, 16647951]]]
  hmulB := by decide  
  f := ![![![-6808, 531, -610, 5292, 3979]], ![![-1985, 138, -258, 1754, 1421]], ![![-4745, 330, -657, 4280, 3520]], ![![-4338, 348, -337, 3235, 2369]], ![![-3996, 304, -408, 3234, 2495]]]
  g := ![![![-9087146, 4424033, -2074566, 6233744, 8980335], ![-23201661, 11295616, -5296864, 15916242, 22928947], ![-59239400, 28840415, -13524163, 40637980, 58543095], ![-3524408, 1715841, -804611, 2417729, 3482982], ![-16845960, 8201374, -3845878, 11556258, 16647951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-6884473, -1973341, 925353, -2780526, -4005606]] ![![-733, -213, 99, -298, -426]]
  ![![10579866849, 3032496824, -1422031866, 4272980770, 6155659652]] where
 M := ![![![10579866849, 3032496824, -1422031866, 4272980770, 6155659652]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![10579866849, 3032496824, -1422031866, 4272980770, 6155659652]] ![![15434702, 4424033, -2074566, 6233744, 8980335]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![341431743856148152, 97864233182180629, -45891567921089238, 137896932898670930, 198654396257742665]]]
 hmul := by decide  
 g := ![![![![2044501460216456, 586013372348387, -274799807910714, 825730137117790, 1189547282980495]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3807115, -1091236, 511700, -1537616, -2215026]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-3807115, -1091236, 511700, -1537616, -2215026]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![143, 158, 162, 84, 1]] where
  M :=![![![-3807115, -1091236, 511700, -1537616, -2215026], ![-9720310, -2786231, 1306586, -3925900, -5655850], ![-24819350, -7113280, 3335619, -10023540, -14439650], ![-1476448, -423364, 198476, -596423, -859012], ![-7058006, -2022692, 948542, -2850344, -4106295]]]
  hmulB := by decide  
  f := ![![![1389, -132, -8, -752, -382]], ![![-2650, 597, 1742, -3100, -4870]], ![![-20810, 2960, 5027, -1620, -10190]], ![![-2056, -28, -1108, 4053, 4196]], ![![-21783, 3198, 5760, -3004, -12281]]]
  g := ![![![1808911, 2016664, 2077144, 1066616, -2215026], ![4618880, 5149353, 5303782, 2723500, -5655850], ![11792200, 13146540, 13540803, 6953220, -14439650], ![701516, 782084, 805540, 413645, -859012], ![3353423, 3738566, 3850684, 1977332, -4106295]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [95, 28, 9, 157, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [164, 71, 62, 41], [25, 146, 145, 168], [0, 128, 139, 137], [0, 1]]
 g := ![![[113, 79, 111, 140], [78, 52, 126], [116, 37, 20, 133], [151, 119, 12, 152], [86, 53, 113], [16, 1], []], ![[71, 110, 60, 150, 133, 109], [25, 86, 163], [53, 152, 167, 40, 111, 140], [140, 99, 161, 164, 1, 164], [63, 127, 85], [144, 34, 170, 92, 14, 150], [19, 148, 124]], ![[51, 84, 73, 7, 155, 123], [124, 123, 6], [43, 146, 167, 133, 103, 68], [96, 107, 42, 3, 95, 153], [104, 89, 100], [91, 98, 37, 8, 14, 75], [118, 161, 25]], ![[0, 20, 76, 73, 152, 57], [38, 49, 172], [54, 161, 74, 10, 81, 83], [82, 5, 0, 100, 134, 64], [96, 142, 55], [80, 11, 66, 18, 100, 47], [30, 2, 85]]]
 h' := ![![[164, 71, 62, 41], [138, 5, 1, 60], [52, 7, 162, 105], [14, 12, 88, 47], [119, 123, 113, 49], [37, 149, 1, 74], [0, 0, 1], [0, 1]], ![[25, 146, 145, 168], [88, 22, 38, 110], [120, 63, 31, 110], [163, 108, 165, 87], [151, 90, 27, 171], [9, 14, 82, 137], [6, 46, 113, 106], [164, 71, 62, 41]], ![[0, 128, 139, 137], [69, 49, 137, 150], [36, 43, 158, 51], [18, 64, 87, 114], [155, 73, 138, 2], [1, 11, 158, 10], [141, 119, 34, 136], [25, 146, 145, 168]], ![[0, 1], [163, 97, 170, 26], [60, 60, 168, 80], [168, 162, 6, 98], [20, 60, 68, 124], [12, 172, 105, 125], [91, 8, 25, 104], [0, 128, 139, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [156, 135, 33], []]
 b := ![[], [], [120, 111, 9, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [95, 28, 9, 157, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70047437, 136455006, -15750060, 107399532, -121059348]
  a := ![-21, -9, 26, -28, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![99661499, 111351630, 113270892, 59401068, -121059348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1389, -132, -8, -752, -382]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![1389, -132, -8, -752, -382]] 
 ![![173, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![163, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![86, 0, 0, 0, 1]] where
  M :=![![![1389, -132, -8, -752, -382], ![-2650, 597, 1742, -3100, -4870], ![-20810, 2960, 5027, -1620, -10190], ![-2056, -28, -1108, 4053, 4196], ![-4462, 636, 1086, -368, -2211]]]
  hmulB := by decide  
  f := ![![![-3807115, -1091236, 511700, -1537616, -2215026]], ![![-562335, -161183, 75582, -227116, -327176]], ![![-3730515, -1069276, 501403, -1506676, -2170456]], ![![-2165166, -620604, 291012, -874467, -1259720]], ![![-1933352, -554156, 259854, -780840, -1124847]]]
  g := ![![![649, -132, -8, -752, -382], ![2441, 597, 1742, -3100, -4870], ![733, 2960, 5027, -1620, -10190], ![-3346, -28, -1108, 4053, 4196], ![174, 636, 1086, -368, -2211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-3807115, -1091236, 511700, -1537616, -2215026]] ![![1389, -132, -8, -752, -382]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38, 63, -22, 10, 9]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-38, 63, -22, 10, 9]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![155, 111, 109, 1, 0], ![102, 3, 135, 0, 1]] where
  M :=![![![-38, 63, -22, 10, 9], ![47, -138, 42, -172, 53], ![-185, 85, 431, 10, -1535], ![-482, 267, -169, 213, 442], ![334, -206, 234, -78, -703]]]
  hmulB := by decide  
  f := ![![![-48672, -13951, 6542, -19658, -28319]], ![![-124273, -35620, 16704, -50192, -72307]], ![![-317305, -90945, 42649, -128150, -184615]], ![![-312534, -89579, 42008, -126225, -181841]], ![![-269630, -77281, 36241, -108896, -156877]]]
  g := ![![![-14, -6, -13, 10, 9], ![119, 105, 65, -172, 53], ![865, 20, 1154, 10, -1535], ![-439, -138, -464, 213, 442], ![470, 59, 579, -78, -703]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [116, 121, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 18, 120], [5, 160, 59], [0, 1]]
 g := ![![[167, 16, 110], [74, 4, 155], [143, 155], [148, 156], [43, 132, 139], [30, 144, 1], []], ![[94, 47, 174, 122], [66, 11, 160, 6], [113, 13], [113, 144], [29, 178, 170, 91], [1, 101, 130, 2], [88, 80]], ![[147, 118, 8, 177], [78, 139, 9, 52], [110, 138], [34, 20], [84, 153, 60, 3], [155, 107, 154, 142], [149, 80]]]
 h' := ![![[139, 18, 120], [8, 139, 162], [41, 71, 100], [55, 35, 100], [24, 46, 131], [100, 72, 26], [0, 0, 1], [0, 1]], ![[5, 160, 59], [90, 61, 177], [76, 127, 176], [98, 16, 152], [26, 106, 167], [26, 91, 91], [163, 112, 160], [139, 18, 120]], ![[0, 1], [9, 158, 19], [56, 160, 82], [69, 128, 106], [95, 27, 60], [121, 16, 62], [104, 67, 18], [5, 160, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 22], []]
 b := ![[], [146, 158, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [116, 121, 35, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![940968, -676484, 253046, -230942, -417392]
  a := ![12, -4, -14, -2, 48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![443078, 146426, 456836, -230942, -417392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48672, -13951, 6542, -19658, -28319]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-48672, -13951, 6542, -19658, -28319]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![46, 163, 1, 0, 0], ![2, 69, 0, 1, 0], ![157, 17, 0, 0, 1]] where
  M :=![![![-48672, -13951, 6542, -19658, -28319], ![-124273, -35620, 16704, -50192, -72307], ![-317305, -90945, 42649, -128150, -184615], ![-18878, -5411, 2537, -7623, -10982], ![-90232, -25862, 12128, -36442, -52499]]]
  hmulB := by decide  
  f := ![![![-38, 63, -22, 10, 9]], ![![47, -138, 42, -172, 53]], ![![32, -109, 35, -154, 42]], ![![15, -51, 15, -65, 23]], ![![-27, 41, -14, -8, 9]]]
  g := ![![![23105, 4232, 6542, -19658, -28319], ![58994, 10805, 16704, -50192, -72307], ![150624, 27587, 42649, -128150, -184615], ![8960, 1641, 2537, -7623, -10982], ![42833, 7845, 12128, -36442, -52499]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [172, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 178], [0, 1]]
 g := ![![[40, 51], [100, 121], [161], [3], [0, 121], [138, 177], [1]], ![[0, 128], [149, 58], [161], [3], [49, 58], [115, 2], [1]]]
 h' := ![![[101, 178], [163, 87], [136, 168], [21, 124], [0, 160], [71, 11], [7, 101], [0, 1]], ![[0, 1], [0, 92], [99, 11], [15, 55], [50, 19], [108, 168], [5, 78], [101, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [176, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [172, 78, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7341, 4656, -936, 4008, 3826]
  a := ![24, 19, -20, 44, 83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3119, -1030, -936, 4008, 3826]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-38, 63, -22, 10, 9]] ![![-48672, -13951, 6542, -19658, -28319]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 0, -7, -2, 31]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-10, 0, -7, -2, 31]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![118, 161, 1, 0, 0], ![55, 99, 0, 1, 0], ![170, 142, 0, 0, 1]] where
  M :=![![![-10, 0, -7, -2, 31], ![89, -47, 37, -14, -109], ![-355, 260, -114, 110, 215], ![42, -58, -4, -31, 78], ![-136, 124, -30, 58, -3]]]
  hmulB := by decide  
  f := ![![![120, 16, -31, 64, 101]], ![![431, 29, -75, 84, 209]], ![![466, 37, -87, 116, 252]], ![![271, 21, -50, 65, 144]], ![![452, 38, -88, 126, 259]]]
  g := ![![![-24, -17, -7, -2, 31], ![83, 60, 37, -14, -109], ![-163, -126, -114, 110, 215], ![-61, -41, -4, -31, 78], ![4, -2, -30, 58, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [171, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 180], [0, 1]]
 g := ![![[25, 39], [70], [25, 138], [65], [139, 55], [107, 55], [1]], ![[1, 142], [70], [135, 43], [65], [133, 126], [101, 126], [1]]]
 h' := ![![[69, 180], [31, 138], [69, 147], [32, 92], [123, 80], [165, 69], [10, 69], [0, 1]], ![[0, 1], [141, 43], [76, 34], [45, 89], [32, 101], [39, 112], [65, 112], [69, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [136, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [171, 112, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![370, -302, -159, -386, 214]
  a := ![0, -3, -1, -4, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22, 183, -159, -386, 214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 2, -2, -5]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-6, 1, 2, -2, -5]] 
 ![![181, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-6, 1, 2, -2, -5], ![-19, 2, 2, 4, -1], ![5, -5, -11, 30, 35], ![26, -3, -7, 3, 14], ![2, -2, -2, 6, 7]]]
  hmulB := by decide  
  f := ![![![-172, -71, 26, -82, -99]], ![![-13, -5, 2, -6, -8]], ![![-65, -25, 9, -30, -35]], ![![-18, -8, 3, -9, -11]], ![![-56, -22, 8, -26, -31]]]
  g := ![![![1, 1, 2, -2, -5], ![-1, 2, 2, 4, -1], ![-10, -5, -11, 30, 35], ![-2, -3, -7, 3, 14], ![-2, -2, -2, 6, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4492, 1293, -606, 1818, 2619]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![4492, 1293, -606, 1818, 2619]] 
 ![![181, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![148, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![4492, 1293, -606, 1818, 2619], ![11493, 3280, -1542, 4632, 6687], ![29325, 8415, -3929, 11850, 16995], ![1722, 513, -243, 709, 1038], ![8358, 2382, -1110, 3366, 4813]]]
  hmulB := by decide  
  f := ![![![2674, 237, 2442, -7902, -8703]], ![![123, 70, 408, -1140, -1359]], ![![1387, 291, 2107, -6306, -7239]], ![![568, 12, 327, -1175, -1227]], ![![64, 42, 240, -666, -797]]]
  g := ![![![-194, 1293, -606, 1818, 2619], ![-495, 3280, -1542, 4632, 6687], ![-1273, 8415, -3929, 11850, 16995], ![-73, 513, -243, 709, 1038], ![-364, 2382, -1110, 3366, 4813]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2

def I181N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![560, -48, 23, -372, -239]] i)))

def SI181N3: IdealEqSpanCertificate' Table ![![560, -48, 23, -372, -239]] 
 ![![181, 0, 0, 0, 0], ![166, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![560, -48, 23, -372, -239], ![-1461, 303, 829, -1364, -2259], ![-9505, 1320, 2136, -320, -4135], ![-574, -66, -600, 1895, 2114], ![-2040, 284, 462, -78, -899]]]
  hmulB := by decide  
  f := ![![![2506, 112, -321, 598, 1935]], ![![2337, 111, -293, 562, 1769]], ![![1907, 144, -281, 496, 1590]], ![![470, 2, -52, 99, 342]], ![![136, 40, -35, 56, 156]]]
  g := ![![![110, -48, 23, -372, -239], ![-535, 303, 829, -1364, -2259], ![-2572, 1320, 2136, -320, -4135], ![48, -66, -600, 1895, 2114], ![-553, 284, 462, -78, -899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N3 : Nat.card (O ⧸ I181N3) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N3)

lemma isPrimeI181N3 : Ideal.IsPrime I181N3 := prime_ideal_of_norm_prime hp181.out _ NI181N3
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-10, 0, -7, -2, 31]] ![![-6, 1, 2, -2, -5]]
  ![![35, -31, 9, -10, -6]] where
 M := ![![![35, -31, 9, -10, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![35, -31, 9, -10, -6]] ![![4492, 1293, -606, 1818, 2619]]
  ![![-2506, -112, 321, -598, -1935]] where
 M := ![![![-2506, -112, 321, -598, -1935]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N2 : IdealMulLeCertificate' Table 
  ![![-2506, -112, 321, -598, -1935]] ![![560, -48, 23, -372, -239]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2, I181N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
    exact isPrimeI181N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1 ⊙ MulI181N2)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6166, -1104, -2629, 3472, 6713]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![6166, -1104, -2629, 3472, 6713]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![8, 147, 1, 0, 0], ![188, 56, 0, 1, 0], ![20, 127, 0, 0, 1]] where
  M :=![![![6166, -1104, -2629, 3472, 6713], ![27083, -3507, -4807, -2448, 7637], ![18015, 600, 11474, -40140, -42495], ![-34318, 5278, 10256, -7843, -23182], ![4044, 100, 2418, -8590, -9025]]]
  hmulB := by decide  
  f := ![![![-32533620, -9325080, 4372817, -13139630, -18928951]], ![![-83066113, -23809165, 11164859, -33548622, -48330187]], ![![-66403536, -19033185, 8925253, -26818964, -38635432]], ![![-56443146, -16178246, 7586480, -22796175, -32840182]], ![![-58954871, -16898181, 7924083, -23810608, -34301590]]]
  g := ![![![-3978, -3464, -2629, 3472, 6713], ![1953, -679, -4807, -2448, 7637], ![43573, 31197, 11474, -40140, -42495], ![9538, 9848, 10256, -7843, -23182], ![9320, 6659, 2418, -8590, -9025]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [56, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 190], [0, 1]]
 g := ![![[74, 149], [124, 30], [186, 79], [63, 34], [49, 10], [99, 117], [1]], ![[121, 42], [145, 161], [184, 112], [125, 157], [56, 181], [9, 74], [1]]]
 h' := ![![[58, 190], [123, 63], [89, 139], [101, 156], [121, 15], [186, 34], [135, 58], [0, 1]], ![[0, 1], [148, 128], [129, 52], [172, 35], [36, 176], [57, 157], [61, 133], [58, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [78, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [56, 133, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![567, 6433, -2520, 6322, 6349]
  a := ![23, 9, -23, 28, 89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6779, -4102, -2520, 6322, 6349]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1122, -129, -130, -284, 89]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![1122, -129, -130, -284, 89]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![117, 179, 1, 0, 0], ![64, 36, 0, 1, 0], ![186, 68, 0, 0, 1]] where
  M :=![![![1122, -129, -130, -284, 89], ![-301, 188, 812, -1974, -2539], ![-11565, 1785, 3571, -2880, -8175], ![-2878, 247, -181, 2059, 1418], ![-2454, 370, 774, -634, -1775]]]
  hmulB := by decide  
  f := ![![![7556968, 2166045, -1015726, 3052096, 4396853]], ![![19294751, 5530434, -2593390, 7792734, 11226209]], ![![22969580, 6583746, -3087321, 9276918, 13364327]], ![![6184230, 1772579, -831217, 2497677, 3598154]], ![![14301824, 4099316, -1922296, 5776198, 8321193]]]
  g := ![![![94, 143, -130, -284, 89], ![2635, 516, 812, -1974, -2539], ![6678, 116, 3571, -2880, -8175], ![-1975, -722, -181, 2059, 1418], ![1454, 28, 774, -634, -1775]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [158, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [165, 190], [0, 1]]
 g := ![![[5, 81], [45, 156], [56, 172], [139, 32], [33, 125], [190, 103], [1]], ![[0, 110], [0, 35], [168, 19], [71, 159], [30, 66], [186, 88], [1]]]
 h' := ![![[165, 190], [148, 182], [129, 27], [3, 118], [134, 154], [158, 121], [33, 165], [0, 1]], ![[0, 1], [0, 9], [0, 164], [182, 73], [141, 37], [68, 70], [136, 26], [165, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [147, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [158, 26, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7, 608, 391, 950, -1380]
  a := ![14, 7, -17, 20, 55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![786, -51, 391, 950, -1380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1420, -182, -243, -152, 371]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![1420, -182, -243, -152, 371]] 
 ![![191, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![111, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![1420, -182, -243, -152, 371], ![809, 53, 645, -2144, -2329], ![-11275, 1890, 4156, -4640, -10165], ![-4382, 460, 242, 1803, 502], ![-2402, 404, 892, -1006, -2187]]]
  hmulB := by decide  
  f := ![![![69554, 19850, -9237, 28030, 40027]], ![![21315, 6089, -2835, 8594, 12281]], ![![42809, 12200, -5681, 17240, 24632]], ![![13978, 3992, -1856, 5635, 8040]], ![![24350, 6942, -3233, 9808, 14016]]]
  g := ![![![106, -182, -243, -152, 371], ![833, 53, 645, -2144, -2329], ![1354, 1890, 4156, -4640, -10165], ![-828, 460, 242, 1803, 502], ![295, 404, 892, -1006, -2187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![6166, -1104, -2629, 3472, 6713]] ![![1122, -129, -130, -284, 89]]
  ![![11188823, -2354337, -6518757, 10892478, 17851626]] where
 M := ![![![11188823, -2354337, -6518757, 10892478, 17851626]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![11188823, -2354337, -6518757, 10892478, 17851626]] ![![1420, -182, -243, -152, 371]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-3127989046, -2258999593, -12769755378, 35274431990, 42323987005]]]
 hmul := by decide  
 g := ![![![![-16376906, -11827223, -66857358, 184682890, 221591555]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12459, 3601, -1749, 5054, 7568]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![12459, 3601, -1749, 5054, 7568]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![171, 140, 118, 1, 0], ![69, 92, 155, 0, 1]] where
  M :=![![![12459, 3601, -1749, 5054, 7568], ![32812, 8768, -3993, 12808, 17728], ![78800, 25655, -11928, 33950, 49280], ![5168, 927, -695, 1709, 3512], ![22140, 7702, -3362, 9876, 13447]]]
  hmulB := by decide  
  f := ![![![6895, -959, -1557, 252, 3024]], ![![9576, -638, 1309, -8766, -7056]], ![![-38700, 7355, 18604, -27320, -48960]], ![![-10735, 3200, 10962, -22813, -32392]], ![![-24093, 5268, 15029, -26060, -41657]]]
  g := ![![![-7119, -7255, -9177, 5054, 7568], ![-17516, -17696, -22089, 12808, 17728], ![-47290, -47985, -60396, 33950, 49280], ![-2743, -2909, -3869, 1709, 3512], ![-13443, -13534, -16855, 9876, 13447]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [120, 45, 179, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 32, 149], [148, 160, 44], [0, 1]]
 g := ![![[133, 67, 23], [54, 49], [162, 157], [177, 162], [117, 36], [133, 3], [1]], ![[74, 177, 29, 41], [23, 165], [25, 27], [7, 98], [174, 109], [95, 97], [40, 74, 161, 122]], ![[150, 112, 129, 171], [172, 84], [187, 83], [9, 126], [61, 129], [108, 144], [135, 14, 14, 71]]]
 h' := ![![[59, 32, 149], [57, 188, 122], [174, 10, 7], [182, 40, 100], [112, 132, 82], [177, 16, 6], [73, 148, 14], [0, 1]], ![[148, 160, 44], [162, 60, 54], [151, 89, 101], [16, 103, 151], [85, 167, 171], [182, 121, 63], [52, 28, 167], [59, 32, 149]], ![[0, 1], [76, 138, 17], [114, 94, 85], [121, 50, 135], [64, 87, 133], [67, 56, 124], [176, 17, 12], [148, 160, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 192], []]
 b := ![[], [171, 45, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [120, 45, 179, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![138634, 48562, 39576, -1301, -97244]
  a := ![10, 8, -10, 19, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36637, 47550, 79098, -1301, -97244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9358, -2683, 1258, -3780, -5445]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-9358, -2683, 1258, -3780, -5445]] 
 ![![193, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![-9358, -2683, 1258, -3780, -5445], ![-23895, -6848, 3212, -9650, -13905], ![-61015, -17485, 8197, -24640, -35485], ![-3626, -1043, 489, -1467, -2114], ![-17354, -4970, 2330, -7006, -10089]]]
  hmulB := by decide  
  f := ![![![3724, -559, -1062, 720, 2345]], ![![507, -74, -134, 70, 285]], ![![-1, 6, 31, -80, -100]], ![![1038, -157, -303, 219, 676]], ![![1300, -194, -364, 234, 797]]]
  g := ![![![3320, -2683, 1258, -3780, -5445], ![8477, -6848, 3212, -9650, -13905], ![21638, -17485, 8197, -24640, -35485], ![1289, -1043, 489, -1467, -2114], ![6152, -4970, 2330, -7006, -10089]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![125632, -26838, -75209, 127594, 206975]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![125632, -26838, -75209, 127594, 206975]] 
 ![![193, 0, 0, 0, 0], ![147, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![171, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![125632, -26838, -75209, 127594, 206975], ![876113, -122819, -202645, 44642, 399827], ![1288765, -92470, 143082, -1092870, -842345], ![-909334, 152540, 335702, -375569, -821506], ![281408, -20616, 29118, -233054, -177041]]]
  hmulB := by decide  
  f := ![![![-245582858, -70390162, 33008127, -99184936, -142885603]], ![![-190298999, -54544461, 25577584, -76857152, -110720240]], ![![-17202267, -4930608, 2312131, -6947584, -10008752]], ![![-218082488, -62507858, 29311867, -88078197, -126885239]], ![![-16355824, -4688002, 2198357, -6605730, -9516240]]]
  g := ![![![-101026, -26838, -75209, 127594, 206975], ![43094, -122819, -202645, 44642, 399827], ![1088222, -92470, 143082, -1092870, -842345], ![246509, 152540, 335702, -375569, -821506], ![232683, -20616, 29118, -233054, -177041]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![12459, 3601, -1749, 5054, 7568]] ![![-9358, -2683, 1258, -3780, -5445]]
  ![![-245582858, -70390162, 33008127, -99184936, -142885603]] where
 M := ![![![-245582858, -70390162, 33008127, -99184936, -142885603]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-245582858, -70390162, 33008127, -99184936, -142885603]] ![![125632, -26838, -75209, 127594, 206975]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18040, 2737, 5638, -4472, -12929]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-18040, 2737, 5638, -4472, -12929]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![101, 24, 142, 17, 1]] where
  M :=![![![-18040, 2737, 5638, -4472, -12929], ![-47731, 5678, 3224, 17106, 3011], ![43245, -14505, -42629, 89580, 127815], ![80126, -10871, -17155, 1255, 31814], ![8890, -3306, -9218, 19082, 28181]]]
  hmulB := by decide  
  f := ![![![134511342, 38554849, -18079562, 54326236, 78262405]], ![![343439687, 98439768, -46161454, 138707898, 199822673]], ![![876883815, 251340315, -117861253, 354154500, 510195165]], ![![52169606, 14953321, -7012075, 21070181, 30353714]], ![![748639306, 214581722, -100624011, 302359303, 435578976]]]
  g := ![![![6537, 1589, 9348, 1093, -12929], ![-1786, -338, -2154, -173, 3011], ![-65310, -15645, -92347, -10575, 127815], ![-15904, -3931, -23019, -2739, 31814], ![-14403, -3450, -20360, -2335, 28181]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [128, 110, 127, 26, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 183, 187, 117], [0, 79, 142, 141], [136, 131, 65, 136], [0, 1]]
 g := ![![[109, 109, 133, 59], [103, 64, 61], [89, 126, 2, 64], [92, 184, 196], [182, 125, 136], [155, 171, 1], []], ![[88, 190, 172, 192, 110, 141], [83, 181, 49], [87, 31, 57, 105, 95, 130], [156, 141, 40], [184, 183, 28], [88, 25, 116], [60, 61, 173, 33, 194, 3]], ![[159, 158, 109, 56, 102, 95], [78, 122, 105], [178, 115, 143, 171, 104, 8], [145, 181, 4], [23, 38, 133], [146, 16, 93], [126, 104, 101, 119, 29, 108]], ![[145, 34, 176, 184, 72, 16], [19, 65, 175], [112, 142, 159, 36, 143, 109], [142, 104, 29], [188, 163, 42], [160, 16, 4], [165, 15, 46, 88, 21, 160]]]
 h' := ![![[35, 183, 187, 117], [186, 103, 9, 16], [34, 193, 34, 88], [86, 156, 19, 189], [47, 100, 121, 183], [57, 68, 186, 147], [0, 0, 0, 1], [0, 1]], ![[0, 79, 142, 141], [196, 73, 188, 104], [24, 186, 118, 7], [97, 172, 2, 90], [103, 13, 141, 146], [58, 8, 55, 182], [129, 137, 152, 126], [35, 183, 187, 117]], ![[136, 131, 65, 136], [156, 113, 138, 148], [68, 73, 54, 41], [9, 31, 111, 15], [144, 86, 22, 2], [112, 153, 93, 112], [26, 14, 15, 68], [0, 79, 142, 141]], ![[0, 1], [194, 105, 59, 126], [159, 139, 188, 61], [149, 35, 65, 100], [195, 195, 110, 63], [182, 165, 60, 150], [119, 46, 30, 2], [136, 131, 65, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [177, 168, 129], []]
 b := ![[], [], [96, 81, 195, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [128, 110, 127, 26, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-738146556, 313744802, -351486944, 66668728, 1217259940]
  a := ![-23, -7, 22, -30, -99]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-627824368, -146703014, -879199992, -104704316, 1217259940]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![134511342, 38554849, -18079562, 54326236, 78262405]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![134511342, 38554849, -18079562, 54326236, 78262405]] 
 ![![197, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![134511342, 38554849, -18079562, 54326236, 78262405], ![343439687, 98439768, -46161454, 138707898, 199822673], ![876883815, 251340315, -117861253, 354154500, 510195165], ![52169606, 14953321, -7012075, 21070181, 30353714], ![249360220, 71473866, -33516308, 100711226, 145084647]]]
  hmulB := by decide  
  f := ![![![-18040, 2737, 5638, -4472, -12929]], ![![-6103, 918, 1848, -1366, -4185]], ![![-3535, 496, 957, -476, -2042]], ![![-12322, 1876, 3891, -3149, -8961]], ![![-11310, 1706, 3502, -2718, -7995]]]
  g := ![![![-95673208, 38554849, -18079562, 54326236, 78262405], ![-244276625, 98439768, -46161454, 138707898, 199822673], ![-623696756, 251340315, -117861253, 354154500, 510195165], ![-37106414, 14953321, -7012075, 21070181, 30353714], ![-177361194, 71473866, -33516308, 100711226, 145084647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-18040, 2737, 5638, -4472, -12929]] ![![134511342, 38554849, -18079562, 54326236, 78262405]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB397I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB397I4 : PrimesBelowBoundCertificateInterval O 151 197 397 where
  m := 9
  g := ![2, 2, 3, 2, 2, 4, 3, 3, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB397I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2, I181N3]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![607573201, 157]
    · exact ![705911761, 163]
    · exact ![27889, 27889, 167]
    · exact ![895745041, 173]
    · exact ![5735339, 32041]
    · exact ![32761, 181, 181, 181]
    · exact ![36481, 36481, 191]
    · exact ![7189057, 193, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
      exact NI181N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I163N1, I167N2, I173N1, I181N1, I181N2, I181N3, I191N2, I193N1, I193N2, I197N1]
  Il := ![[I157N1], [I163N1], [I167N2], [I173N1], [], [I181N1, I181N2, I181N3], [I191N2], [I193N1, I193N2], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
