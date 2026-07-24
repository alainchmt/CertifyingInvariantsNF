
import IdealArithmetic.Examples.NF5_1_48600000_4.RI5_1_48600000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10685, -23985, 6486, 14117, 7094]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![10685, -23985, 6486, 14117, 7094]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![234, 106, 1, 0, 0], ![125, 49, 0, 1, 0], ![61, 111, 0, 0, 1]] where
  M :=![![![10685, -23985, 6486, 14117, 7094], ![42564, -95725, 25602, 56144, 28234], ![169404, -380946, 101589, 223240, 112288], ![673728, -1514916, 403734, 887605, 446480], ![1254738, -2821263, 751750, 1652927, 831461]]]
  hmulB := by decide  
  f := ![![![13513, -38649, 22138, 7947, -6060]], ![![-36360, 104413, -61002, -20282, 15894]], ![![-2322, 6806, -4367, -934, 880]], ![![-1307, 3848, -2526, -470, 474]], ![![-11509, 33051, -19298, -6434, 5037]]]
  g := ![![![-14414, -8524, 6486, 14117, 7094], ![-57154, -33831, 25602, 56144, 28234], ![-227070, -134444, 101589, 223240, 112288], ![-902669, -534485, 403734, 887605, 446480], ![-1680894, -995301, 751750, 1652927, 831461]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [58, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [242, 256], [0, 1]]
 g := ![![[49, 226], [197], [146], [215], [122], [168], [225], [1]], ![[0, 31], [197], [146], [215], [122], [168], [225], [1]]]
 h' := ![![[242, 256], [161, 45], [153, 35], [59, 143], [129, 27], [254, 76], [80, 164], [199, 242], [0, 1]], ![[0, 1], [0, 212], [142, 222], [227, 114], [238, 230], [142, 181], [190, 93], [167, 15], [242, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [149, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [58, 15, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1780, -3153, -143, 3036, 2572]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1950, -1643, -143, 3036, 2572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155, 468, -331, -37, 50]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-155, 468, -331, -37, 50]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![78, 102, 1, 0, 0], ![11, 211, 0, 1, 0], ![213, 116, 0, 0, 1]] where
  M :=![![![-155, 468, -331, -37, 50], ![300, -905, 681, 19, -74], ![-444, 1410, -1256, 163, 38], ![228, -1014, 1763, -990, 326], ![1200, -3036, 441, 1941, -1009]]]
  hmulB := by decide  
  f := ![![![-763, 1128, 527, -165, -154]], ![![-924, 1547, 193, -551, -330]], ![![-606, 972, 234, -277, -182]], ![![-817, 1375, 167, -492, -294]], ![![-1095, 1736, 496, -446, -307]]]
  g := ![![![60, 141, -331, -37, 50], ![-145, -256, 681, 19, -74], ![341, 353, -1256, 163, 38], ![-762, -38, 1763, -990, 326], ![624, -1325, 441, 1941, -1009]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [232, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 256], [0, 1]]
 g := ![![[161, 185], [195], [208], [136], [162], [187], [116], [1]], ![[0, 72], [195], [208], [136], [162], [187], [116], [1]]]
 h' := ![![[170, 256], [227, 106], [122, 130], [24, 112], [42, 81], [238, 26], [184, 207], [25, 170], [0, 1]], ![[0, 1], [0, 151], [120, 127], [46, 145], [191, 176], [32, 231], [165, 50], [141, 87], [170, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [46, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [232, 87, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2084, 948, 1578, -2910, 1428]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1546, 1122, 1578, -2910, 1428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -27, 5, 4, -2]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![11, -27, 5, 4, -2]] 
 ![![257, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![169, 0, 1, 0, 0], ![200, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![11, -27, 5, 4, -2], ![-12, 41, -33, -9, 8], ![48, -132, 72, 23, -18], ![-108, 318, -199, -54, 46], ![114, -333, 211, 50, -45]]]
  hmulB := by decide  
  f := ![![![-17, -243, 211, 218, 96]], ![![-1, -52, 42, 45, 20]], ![![-1, -183, 145, 157, 70]], ![![28, -282, 189, 224, 102]], ![![75, -198, 68, 124, 61]]]
  g := ![![![-1, -27, 5, 4, -2], ![20, 41, -33, -9, 8], ![-38, -132, 72, 23, -18], ![107, 318, -199, -54, 46], ![-109, -333, 211, 50, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![10685, -23985, 6486, 14117, 7094]] ![![-155, 468, -331, -37, 50]]
  ![![17, 243, -211, -218, -96]] where
 M := ![![![17, 243, -211, -218, -96]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![17, 243, -211, -218, -96]] ![![11, -27, 5, 4, -2]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![-257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25301, 24296, 17803, -789, -2618]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-25301, 24296, 17803, -789, -2618]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![24, 10, 141, 1, 0], ![149, 96, 59, 0, 1]] where
  M :=![![![-25301, 24296, 17803, -789, -2618], ![-15708, 13969, 10417, -523, -1578], ![-9468, 7962, 5556, -629, -1046], ![-6276, 6222, 2103, -1766, -1258], ![960, 2316, -3695, -3037, -1243]]]
  hmulB := by decide  
  f := ![![![413, -964, -157, 917, -442]], ![![-2652, 7043, -2257, -3251, 1834]], ![![11004, -30162, 12962, 10581, -6502]], ![![5688, -15578, 6651, 5509, -3376]], ![![1955, -5362, 2316, 1869, -1151]]]
  g := ![![![1459, 1078, 1078, -789, -2618], ![882, 649, 674, -523, -1578], ![614, 436, 593, -629, -1046], ![850, 550, 1237, -1766, -1258], ![985, 578, 1893, -3037, -1243]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [159, 34, 155, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [201, 243, 168], [170, 19, 95], [0, 1]]
 g := ![![[227, 128, 256], [245, 51, 104], [93, 135, 52], [104, 256], [44, 253], [183, 208], [108, 1], []], ![[68, 241, 158, 71], [161, 107, 78, 114], [159, 79, 31, 28], [46, 124], [222, 218], [160, 9], [6, 98], [140, 83]], ![[258, 199, 75, 36], [90, 257, 128, 70], [218, 69, 45, 49], [32, 207], [120, 89], [119, 39], [90, 137], [213, 83]]]
 h' := ![![[201, 243, 168], [232, 192, 16], [204, 203, 34], [125, 226, 234], [155, 6, 247], [239, 221, 187], [186, 114, 58], [0, 0, 1], [0, 1]], ![[170, 19, 95], [67, 219, 211], [38, 193, 34], [226, 106, 71], [142, 29, 178], [143, 167, 179], [134, 40, 3], [257, 40, 19], [201, 243, 168]], ![[0, 1], [214, 115, 36], [229, 130, 195], [66, 194, 221], [169, 228, 101], [24, 138, 160], [3, 109, 202], [30, 223, 243], [170, 19, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 127], []]
 b := ![[], [239, 152, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [159, 34, 155, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-121991, 281229, -84272, -151409, -66908]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![51259, 31249, 95863, -151409, -66908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![413, -964, -157, 917, -442]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![413, -964, -157, 917, -442]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![131, 122, 1, 0, 0], ![61, 238, 0, 1, 0], ![257, 48, 0, 0, 1]] where
  M :=![![![413, -964, -157, 917, -442], ![-2652, 7043, -2257, -3251, 1834], ![11004, -30162, 12962, 10581, -6502], ![-39012, 108534, -52091, -32552, 21162], ![57984, -163140, 84415, 42731, -29301]]]
  hmulB := by decide  
  f := ![![![-25301, 24296, 17803, -789, -2618]], ![![-15708, 13969, 10417, -523, -1578]], ![![-19925, 18612, 13721, -638, -2040]], ![![-20107, 18300, 13564, -663, -2040]], ![![-27587, 26300, 19284, -878, -2851]]]
  g := ![![![299, -680, -157, 917, -442], ![76, 3681, -2257, -3251, 1834], ![-2515, -14516, 12962, 10581, -6502], ![12669, 50172, -52091, -32552, 21162], ![-23105, -73100, 84415, 42731, -29301]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [11, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [217, 262], [0, 1]]
 g := ![![[52, 24], [120, 222], [72, 111], [151], [11], [148], [12], [1]], ![[0, 239], [165, 41], [226, 152], [151], [11], [148], [12], [1]]]
 h' := ![![[217, 262], [258, 200], [260, 119], [60, 30], [186, 64], [71, 167], [252, 197], [252, 217], [0, 1]], ![[0, 1], [0, 63], [46, 144], [258, 233], [135, 199], [16, 96], [132, 66], [1, 46], [217, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [248, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [11, 46, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1852, -1314, -1335, 4453, 5033]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5279, -4334, -1335, 4453, 5033]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-25301, 24296, 17803, -789, -2618]] ![![413, -964, -157, 917, -442]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, -844, 566, 102, -106]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![283, -844, 566, 102, -106]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![0, 0, 0, 269, 0], ![76, 145, 152, 131, 1]] where
  M :=![![![283, -844, 566, 102, -106], ![-636, 1873, -1272, -176, 204], ![1224, -3696, 2717, 156, -352], ![-2112, 6504, -5300, 253, 312], ![324, -1548, 2800, -1636, 429]]]
  hmulB := by decide  
  f := ![![![431, -436, -314, 14, 46]], ![![276, -259, -192, 8, 28]], ![![168, -144, -111, 4, 16]], ![![96, -72, -60, 1, 8]], ![![412, -379, -284, 11, 41]]]
  g := ![![![31, 54, 62, 52, -106], ![-60, -103, -120, -100, 204], ![104, 176, 209, 172, -352], ![-96, -144, -196, -151, 312], ![-120, -237, -232, -215, 429]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 4 2 8 [18, 227, 137, 170, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 244, 45, 33], [220, 43, 228, 76], [148, 250, 265, 160], [0, 1]]
 g := ![![[0, 5, 155, 260], [148, 207, 97], [263, 141, 208, 21], [139, 210, 261, 58], [90, 106, 21], [219, 59, 117], [1], []], ![[197, 162, 155, 94, 227, 141], [236, 241, 30], [194, 59, 189, 182, 215, 18], [14, 233, 201, 13, 69, 234], [189, 96, 170], [211, 192, 92], [27, 186, 166], [128, 222, 13]], ![[38, 194, 71, 82, 60, 139], [240, 46, 117], [254, 201, 139, 23, 23, 242], [142, 139, 62, 256, 62, 234], [2, 88, 117], [11, 191, 53], [86, 11, 30], [146, 154, 127]], ![[240, 225, 65, 245, 173, 137], [195, 13, 239], [115, 91, 259, 10, 83, 72], [200, 87, 209, 155, 245, 98], [20, 172, 58], [167, 48, 96], [200, 81, 144], [9, 216, 45]]]
 h' := ![![[0, 244, 45, 33], [123, 73, 128, 23], [108, 5, 178, 161], [188, 220, 170, 57], [109, 221, 55, 70], [148, 168, 199, 212], [251, 42, 132, 99], [0, 0, 1], [0, 1]], ![[220, 43, 228, 76], [81, 149, 21, 162], [5, 130, 76, 90], [17, 99, 194, 5], [228, 188, 223, 165], [183, 157, 202, 157], [22, 58, 91, 19], [117, 35, 249, 191], [0, 244, 45, 33]], ![[148, 250, 265, 160], [172, 189, 227, 185], [200, 130, 8, 170], [129, 51, 36, 191], [18, 121, 201, 105], [190, 97, 196, 99], [216, 4, 33, 225], [42, 222, 0, 90], [220, 43, 228, 76]], ![[0, 1], [201, 127, 162, 168], [131, 4, 7, 117], [150, 168, 138, 16], [73, 8, 59, 198], [186, 116, 210, 70], [223, 165, 13, 195], [222, 12, 19, 257], [148, 250, 265, 160]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [256, 207, 178], []]
 b := ![[], [], [105, 7, 176, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 4
  hpos := by decide
  P := [18, 227, 137, 170, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4782733067, -10623621144, 2593330454, 6501157694, 3333989461]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-924165301, -1836624881, -1874249322, -1599447813, 3333989461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 5236114321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, -436, -314, 14, 46]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![431, -436, -314, 14, 46]] 
 ![![269, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![220, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![169, 0, 0, 0, 1]] where
  M :=![![![431, -436, -314, 14, 46], ![276, -259, -192, 8, 28], ![168, -144, -111, 4, 16], ![96, -72, -60, 1, 8], ![-60, 60, 40, -4, -7]]]
  hmulB := by decide  
  f := ![![![283, -844, 566, 102, -106]], ![![5, -15, 10, 2, -2]], ![![236, -704, 473, 84, -88]], ![![70, -208, 136, 29, -28]], ![![179, -536, 366, 58, -65]]]
  g := ![![![237, -436, -314, 14, 46], ![145, -259, -192, 8, 28], ![84, -144, -111, 4, 16], ![46, -72, -60, 1, 8], ![-29, 60, 40, -4, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![283, -844, 566, 102, -106]] ![![431, -436, -314, 14, 46]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11867, 34036, -19993, -6489, 5130]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![-11867, 34036, -19993, -6489, 5130]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![105, 16, 146, 1, 0], ![194, 104, 55, 0, 1]] where
  M :=![![![-11867, 34036, -19993, -6489, 5130], ![30780, -88817, 53197, 15917, -12978], ![-77868, 225450, -137790, -37649, 31834], ![191004, -555378, 346971, 85048, -75298], ![-186960, 547512, -354515, -71233, 69131]]]
  hmulB := by decide  
  f := ![![![259531, -583576, 155499, 341905, 171986]], ![![1031916, -2320259, 618259, 1359401, 683810]], ![![4102860, -9225234, 2458192, 5404929, 2718802]], ![![2432073, -5468498, 1457156, 3203911, 1611640]], ![![1526582, -3432522, 914639, 2011060, 1011609]]]
  g := ![![![-1202, -1460, 2381, -6489, 5130], ![3237, 3713, -5745, 15917, -12978], ![-8489, -9162, 13314, -37649, 31834], ![21656, 21826, -29257, 85048, -75298], ![-22579, -20304, 23038, -71233, 69131]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [24, 58, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 27, 124], [172, 243, 147], [0, 1]]
 g := ![![[124, 35, 78], [231, 57, 163], [31, 162, 56], [175, 247, 148], [176, 10], [244, 125], [177, 1], []], ![[235, 269, 105, 8], [166, 221, 193, 158], [173, 139, 81, 134], [136, 44, 62, 179], [82, 229], [252, 8], [218, 242], [91, 200]], ![[37, 215, 143, 6], [14, 140, 143, 181], [98, 58, 230, 102], [193, 45, 152, 127], [139, 124], [119, 187], [135, 187], [68, 200]]]
 h' := ![![[5, 27, 124], [147, 22, 112], [69, 73, 200], [136, 33, 74], [193, 47, 240], [262, 245, 187], [88, 8, 106], [0, 0, 1], [0, 1]], ![[172, 243, 147], [181, 190, 134], [66, 243, 200], [154, 24, 123], [149, 171, 192], [189, 143, 212], [269, 124, 192], [9, 219, 243], [5, 27, 124]], ![[0, 1], [169, 59, 25], [100, 226, 142], [26, 214, 74], [22, 53, 110], [102, 154, 143], [178, 139, 244], [39, 52, 27], [172, 243, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 126], []]
 b := ![[], [51, 129, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [24, 58, 94, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6428808, 18250560, -9951576, -4259940, 3103676]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-595012, -872224, 1628404, -4259940, 3103676]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 19902511 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![259531, -583576, 155499, 341905, 171986]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![259531, -583576, 155499, 341905, 171986]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![147, 125, 1, 0, 0], ![53, 240, 0, 1, 0], ![37, 140, 0, 0, 1]] where
  M :=![![![259531, -583576, 155499, 341905, 171986], ![1031916, -2320259, 618259, 1359401, 683810], ![4102860, -9225234, 2458192, 5404929, 2718802], ![16312812, -36679170, 9773705, 21489806, 10809858], ![30378144, -68304912, 18200867, 40018891, 20130405]]]
  hmulB := by decide  
  f := ![![![-11867, 34036, -19993, -6489, 5130]], ![![30780, -88817, 53197, 15917, -12978]], ![![7473, -21673, 13184, 3683, -3086]], ![![25643, -74050, 44482, 13141, -10768]], ![![13591, -39216, 23444, 7074, -5749]]]
  g := ![![![-173739, -465521, 155499, 341905, 171986], ![-690780, -1850894, 618259, 1359401, 683810], ![-2746525, -7359094, 2458192, 5404929, 2718802], ![-10920097, -29259505, 9773705, 21489806, 10809858], ![-20335703, -54487837, 18200867, 40018891, 20130405]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [198, 262, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 270], [0, 1]]
 g := ![![[234, 245], [125, 252], [233, 245], [126, 211], [18], [178], [81], [1]], ![[0, 26], [225, 19], [270, 26], [128, 60], [18], [178], [81], [1]]]
 h' := ![![[9, 270], [182, 40], [207, 184], [255, 231], [15, 239], [74, 17], [131, 146], [73, 9], [0, 1]], ![[0, 1], [0, 231], [237, 87], [166, 40], [269, 32], [227, 254], [90, 125], [154, 262], [9, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [24, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [198, 262, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4079, 1122, -3850, 2839, 2543]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1201, -2048, -3850, 2839, 2543]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![-11867, 34036, -19993, -6489, 5130]] ![![259531, -583576, 155499, 341905, 171986]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 60, -11, 5, -2]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-53, 60, -11, 5, -2]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![165, 247, 144, 136, 1]] where
  M :=![![![-53, 60, -11, 5, -2], ![-12, -23, 55, -25, 10], ![60, -162, 2, 125, -50], ![-300, 810, -287, -348, 250], ![720, -1944, 855, 669, -323]]]
  hmulB := by decide  
  f := ![![![7, -24, -13, 1, 2]], ![![12, -23, -13, 1, 2]], ![![12, -18, -12, 1, 2]], ![![12, -18, -7, 2, 2]], ![![27, -53, -29, 3, 5]]]
  g := ![![![1, 2, 1, 1, -2], ![-6, -9, -5, -5, 10], ![30, 44, 26, 25, -50], ![-150, -220, -131, -124, 250], ![195, 281, 171, 161, -323]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [180, 177, 111, 60, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [194, 181, 112, 66], [53, 214, 221, 3], [247, 158, 221, 208], [0, 1]]
 g := ![![[2, 109, 237, 161], [113, 233, 40], [138, 68, 197, 276], [28, 157, 243], [184, 3, 210, 47], [101, 84, 276], [1], []], ![[128, 169, 5, 236, 258, 202], [205, 245, 220], [198, 196, 56, 245, 43, 29], [42, 117, 252], [179, 155, 133, 208, 216, 147], [154, 86, 64], [112, 199, 254], [265, 231, 201]], ![[256, 233, 245, 58, 26, 4], [13, 218, 220], [189, 176, 16, 80, 253, 194], [135, 36, 252], [6, 222, 97, 22, 196, 187], [1, 153, 243], [139, 230, 225], [27, 232, 9]], ![[109, 193, 80, 93, 201, 222], [229, 166, 40], [63, 90, 153, 26, 262, 161], [15, 246, 30], [151, 192, 127, 207, 216, 203], [262, 73, 3], [194, 165, 21], [179, 176, 52]]]
 h' := ![![[194, 181, 112, 66], [225, 27, 211, 95], [90, 215, 37, 219], [219, 48, 232, 217], [120, 194, 214, 215], [93, 253, 239, 259], [97, 100, 166, 217], [0, 0, 1], [0, 1]], ![[53, 214, 221, 3], [110, 200, 196, 151], [264, 150, 137, 135], [243, 136, 224, 206], [259, 205, 12, 254], [223, 40, 245, 219], [215, 142, 274, 269], [185, 25, 205, 114], [194, 181, 112, 66]], ![[247, 158, 221, 208], [269, 47, 249, 98], [160, 265, 57, 142], [212, 103, 235, 218], [39, 270, 80, 254], [218, 267, 186, 109], [266, 113, 80, 215], [165, 244, 273, 15], [53, 214, 221, 3]], ![[0, 1], [46, 3, 175, 210], [47, 201, 46, 58], [217, 267, 140, 190], [79, 162, 248, 108], [131, 271, 161, 244], [66, 199, 34, 130], [258, 8, 75, 148], [247, 158, 221, 208]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [151, 210, 14], []]
 b := ![[], [], [83, 43, 240, 180], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [180, 177, 111, 60, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39954571, -73793295, -3936564, 72287333, 54666105]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32418602, -49011990, -28432692, -26578711, 54666105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 24, 13, -1, -2]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-7, 24, 13, -1, -2]] 
 ![![277, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![252, 0, 1, 0, 0], ![125, 0, 0, 1, 0], ![254, 0, 0, 0, 1]] where
  M :=![![![-7, 24, 13, -1, -2], ![-12, 23, 13, -1, -2], ![-12, 18, 12, -1, -2], ![-12, 18, 7, -2, -2], ![0, 0, -3, -3, -1]]]
  hmulB := by decide  
  f := ![![![53, -60, 11, -5, 2]], ![![1, -1, 0, 0, 0]], ![![48, -54, 10, -5, 2]], ![![25, -30, 6, -1, 0]], ![![46, -48, 7, -7, 3]]]
  g := ![![![-10, 24, 13, -1, -2], ![-10, 23, 13, -1, -2], ![-9, 18, 12, -1, -2], ![-4, 18, 7, -2, -2], ![5, 0, -3, -3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-53, 60, -11, 5, -2]] ![![-7, 24, 13, -1, -2]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![-277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![155, 1448, -2189, -91, 294]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![155, 1448, -2189, -91, 294]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![120, 133, 91, 274, 1]] where
  M :=![![![155, 1448, -2189, -91, 294], ![1764, -4255, 2827, -131, -182], ![-1092, 4494, -5296, 1553, -262], ![-1572, 2838, 4737, -7130, 3106], ![9864, -26328, 8267, 12463, -6999]]]
  hmulB := by decide  
  f := ![![![2947, -6628, 1769, 3885, 1954]], ![![11724, -26363, 7027, 15447, 7770]], ![![46620, -104826, 27934, 61417, 30894]], ![![185364, -416790, 111061, 244192, 122834]], ![![203880, -458425, 122158, 268587, 135105]]]
  g := ![![![-125, -134, -103, -287, 294], ![84, 71, 69, 177, -182], ![108, 140, 66, 261, -262], ![-1332, -1460, -989, -3054, 3106], ![3024, 3219, 2296, 6869, -6999]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 4 2 8 [168, 57, 2, 251, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 9, 23, 76], [88, 86, 210, 134], [65, 185, 48, 71], [0, 1]]
 g := ![![[76, 16, 96, 5], [121, 266, 124], [57, 251, 81], [47, 6, 265, 138], [203, 59, 224, 59], [53, 185, 57], [1], []], ![[245, 0, 41, 212, 222, 22], [171, 155, 238], [110, 52, 183], [12, 0, 183, 47, 35, 174], [16, 34, 18, 34, 134, 13], [225, 56, 81], [76, 137, 158], [147, 27, 156]], ![[163, 7, 218, 170, 163, 168], [277, 48, 136], [144, 28, 32], [57, 213, 150, 182, 116, 139], [277, 40, 44, 113, 118, 189], [220, 255, 191], [114, 146, 45], [6, 83, 253]], ![[157, 207, 75, 6, 200, 270], [255, 188, 112], [224, 69, 29], [273, 155, 138, 24, 234, 74], [25, 15, 54, 256, 256, 19], [170, 280, 248], [239, 267, 1], [13, 124, 264]]]
 h' := ![![[158, 9, 23, 76], [2, 159, 124, 206], [200, 253, 162, 168], [253, 178, 238, 9], [178, 138, 47, 177], [212, 225, 273, 202], [113, 224, 279, 30], [0, 0, 1], [0, 1]], ![[88, 86, 210, 134], [246, 226, 171, 209], [84, 206, 215, 170], [166, 144, 48, 78], [139, 93, 230, 68], [3, 7, 32, 271], [46, 144, 274, 9], [268, 45, 102, 224], [158, 9, 23, 76]], ![[65, 185, 48, 71], [32, 12, 250, 38], [259, 26, 182, 97], [2, 3, 102, 34], [68, 179, 224, 111], [251, 130, 206, 109], [20, 53, 128, 219], [273, 7, 200, 56], [88, 86, 210, 134]], ![[0, 1], [189, 165, 17, 109], [275, 77, 3, 127], [147, 237, 174, 160], [221, 152, 61, 206], [226, 200, 51, 261], [168, 141, 162, 23], [74, 229, 259, 1], [65, 185, 48, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [34, 184, 154], []]
 b := ![[], [], [264, 170, 216, 175], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 4
  hpos := by decide
  P := [168, 57, 2, 251, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![261362049, 379932354, -1506540006, 1513563471, 1898249943]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-809710431, -897107865, -620097099, -1845576231, 1898249943]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 6234839521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2947, -6628, 1769, 3885, 1954]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![2947, -6628, 1769, 3885, 1954]] 
 ![![281, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![215, 0, 0, 1, 0], ![279, 0, 0, 0, 1]] where
  M :=![![![2947, -6628, 1769, 3885, 1954], ![11724, -26363, 7027, 15447, 7770], ![46620, -104826, 27934, 61417, 30894], ![185364, -416790, 111061, 244192, 122834], ![345192, -776160, 206819, 454741, 228745]]]
  hmulB := by decide  
  f := ![![![155, 1448, -2189, -91, 294]], ![![14, 57, -99, -5, 14]], ![![43, 454, -681, -22, 88]], ![![113, 1118, -1658, -95, 236]], ![![189, 1344, -2144, -46, 267]]]
  g := ![![![-5107, -6628, 1769, 3885, 1954], ![-20304, -26363, 7027, 15447, 7770], ![-80727, -104826, 27934, 61417, 30894], ![-320967, -416790, 111061, 244192, 122834], ![-597713, -776160, 206819, 454741, 228745]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![155, 1448, -2189, -91, 294]] ![![2947, -6628, 1769, 3885, 1954]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, 193, -53, -110, -56]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-85, 193, -53, -110, -56]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![247, 71, 29, 1, 0], ![239, 226, 40, 0, 1]] where
  M :=![![![-85, 193, -53, -110, -56], ![-336, 755, -197, -445, -220], ![-1320, 2964, -790, -1737, -890], ![-5340, 12030, -3223, -7020, -3474], ![-9762, 21903, -5785, -12902, -6575]]]
  hmulB := by decide  
  f := ![![![629, -277, -297, 4, 42]], ![![252, -1, -63, -3, 8]], ![![48, 132, 36, -7, -6]], ![![617, -228, -271, 2, 38]], ![![739, -216, -296, 0, 41]]]
  g := ![![![143, 73, 19, -110, -56], ![573, 290, 76, -445, -220], ![2263, 1157, 301, -1737, -890], ![9042, 4578, 1199, -7020, -3474], ![16779, 8565, 2231, -12902, -6575]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [76, 92, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 179, 59], [147, 103, 224], [0, 1]]
 g := ![![[17, 83, 137], [39, 119, 185], [230, 40], [264, 101, 73], [255, 248, 263], [32, 269], [270, 1], []], ![[209, 187, 145, 218], [261, 220, 36, 95], [256, 52], [97, 250, 270, 95], [113, 176, 105, 130], [183, 113], [263, 138], [207, 85]], ![[44, 11, 80, 20], [149, 122, 205, 229], [186, 227], [231, 242, 162, 267], [140, 20, 208, 72], [281, 251], [106, 62], [42, 85]]]
 h' := ![![[123, 179, 59], [149, 71, 49], [58, 74, 40], [29, 116, 235], [147, 216, 140], [192, 161, 65], [139, 271, 77], [0, 0, 1], [0, 1]], ![[147, 103, 224], [277, 80, 180], [39, 251, 279], [225, 134, 202], [27, 115, 279], [44, 238, 63], [59, 40, 148], [246, 135, 103], [123, 179, 59]], ![[0, 1], [61, 132, 54], [213, 241, 247], [177, 33, 129], [170, 235, 147], [102, 167, 155], [69, 255, 58], [22, 148, 179], [147, 103, 224]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 25], []]
 b := ![[], [203, 243, 249], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 3
  hpos := by decide
  P := [76, 92, 13, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![689522, -1296770, -14234, 1207116, 919172]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1827386, -1041466, -253666, 1207116, 919172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-497, 619, 291, -102, -92]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-497, 619, 291, -102, -92]] 
 ![![283, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![262, 0, 0, 1, 0], ![270, 0, 0, 0, 1]] where
  M :=![![![-497, 619, 291, -102, -92], ![-552, 883, 57, -353, -204], ![-1224, 2508, -490, -1371, -706], ![-4236, 9366, -2393, -5432, -2742], ![-7614, 17193, -4643, -10108, -5079]]]
  hmulB := by decide  
  f := ![![![-21455, 60209, -30605, -16340, 11046]], ![![-903, 2530, -1272, -701, 470]], ![![-5090, 14306, -7346, -3807, 2594]], ![![-17882, 50096, -25175, -13890, 9310]], ![![-22872, 64323, -33157, -16988, 11611]]]
  g := ![![![88, 619, 291, -102, -92], ![461, 883, 57, -353, -204], ![1906, 2508, -490, -1371, -706], ![7624, 9366, -2393, -5432, -2742], ![14217, 17193, -4643, -10108, -5079]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, -636, 242, 240, -142]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![239, -636, 242, 240, -142]] 
 ![![283, 0, 0, 0, 0], ![239, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![282, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![239, -636, 242, 240, -142], ![-852, 2369, -1106, -752, 480], ![2880, -8052, 4017, 2254, -1504], ![-9024, 25440, -13318, -6511, 4508], ![12084, -34296, 18726, 7992, -5759]]]
  hmulB := by decide  
  f := ![![![892925, -2008188, 535474, 1176772, 591910]], ![![766645, -1724179, 459740, 1010344, 508198]], ![![191883, -431520, 115043, 252854, 127186]], ![![1088166, -2447184, 652450, 1433973, 721288]], ![![675515, -1519044, 404896, 890056, 447707]]]
  g := ![![![309, -636, 242, 240, -142], ![-1243, 2369, -1106, -752, 480], ![4441, -8052, 4017, 2254, -1504], ![-14456, 25440, -13318, -6511, 4508], ![20039, -34296, 18726, 7992, -5759]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-85, 193, -53, -110, -56]] ![![-497, 619, 291, -102, -92]]
  ![![892925, -2008188, 535474, 1176772, 591910]] where
 M := ![![![892925, -2008188, 535474, 1176772, 591910]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![892925, -2008188, 535474, 1176772, 591910]] ![![239, -636, 242, 240, -142]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1, I283N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
    exact isPrimeI283N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0 ⊙ MulI283N1)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-299, 654, -145, -365, -186]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-299, 654, -145, -365, -186]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![8, 187, 126, 1, 0], ![82, 236, 67, 0, 1]] where
  M :=![![![-299, 654, -145, -365, -186], ![-1116, 2491, -641, -1447, -730], ![-4380, 9834, -2606, -5751, -2894], ![-17364, 39030, -10387, -22864, -11502], ![-32316, 72666, -19369, -42575, -21417]]]
  hmulB := by decide  
  f := ![![![89, -66, -75, 3, 10]], ![![60, -61, -13, -5, 6]], ![![36, -30, -36, 29, -10]], ![![56, -53, -26, 9, 0]], ![![82, -76, -39, 4, 5]]]
  g := ![![![61, 385, 199, -365, -186], ![240, 1520, 787, -1447, -730], ![952, 6035, 3126, -5751, -2894], ![3784, 23990, 12427, -22864, -11502], ![7046, 44671, 23140, -42575, -21417]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 3 2 8 [84, 187, 218, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [277, 11, 56], [91, 281, 237], [0, 1]]
 g := ![![[56, 134, 240], [283, 102], [84, 64, 189], [59, 224], [291, 40], [179, 78, 233], [75, 1], []], ![[209, 121, 2, 115], [223, 25], [82, 75, 149, 57], [267, 276], [113, 226], [111, 196, 20, 15], [16, 144], [274, 206]], ![[60, 99, 272, 206], [188, 15], [178, 134, 67, 198], [238, 209], [277, 255], [87, 239, 12, 156], [264, 121], [93, 206]]]
 h' := ![![[277, 11, 56], [244, 131, 151], [269, 108, 187], [168, 226, 90], [27, 150, 78], [200, 43, 115], [146, 248, 164], [0, 0, 1], [0, 1]], ![[91, 281, 237], [36, 240, 250], [4, 48, 288], [31, 148, 149], [271, 73, 139], [67, 90, 149], [167, 141, 200], [94, 254, 281], [277, 11, 56]], ![[0, 1], [65, 215, 185], [231, 137, 111], [242, 212, 54], [156, 70, 76], [34, 160, 29], [10, 197, 222], [176, 39, 11], [91, 281, 237]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [172, 233], []]
 b := ![[], [262, 101, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 3
  hpos := by decide
  P := [84, 187, 218, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20726, 71784, -36548, -18676, 18256]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4670, -2540, 3732, -18676, 18256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 25153757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3515011, -7903483, 2106013, 4630546, 2329268]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![3515011, -7903483, 2106013, 4630546, 2329268]] 
 ![![293, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![3515011, -7903483, 2106013, 4630546, 2329268], ![13975608, -31424009, 8373403, 18410889, 9261092], ![55566552, -124940772, 33292340, 73201047, 36821778], ![220930668, -496760118, 132369165, 291044786, 146402094], ![411423006, -925079985, 246501399, 541991388, 272633897]]]
  hmulB := by decide  
  f := ![![![217571, -634999, 404527, 89108, -82774]], ![![33948, -99047, 62995, 14001, -12952]], ![![33352, -97508, 62650, 13147, -12494]], ![![90113, -262351, 165058, 38908, -35044]], ![![47879, -140770, 92968, 16424, -17003]]]
  g := ![![![-1520091, -7903483, 2106013, 4630546, 2329268], ![-6043819, -31424009, 8373403, 18410889, 9261092], ![-24030007, -124940772, 33292340, 73201047, 36821778], ![-95542460, -496760118, 132369165, 291044786, 146402094], ![-177921725, -925079985, 246501399, 541991388, 272633897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1

def I293N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-780061, 1753946, -467354, -1027606, -516910]] i)))

def SI293N2: IdealEqSpanCertificate' Table ![![-780061, 1753946, -467354, -1027606, -516910]] 
 ![![293, 0, 0, 0, 0], ![119, 1, 0, 0, 0], ![196, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-780061, 1753946, -467354, -1027606, -516910], ![-3101460, 6973589, -1858210, -4085724, -2055212], ![-12331272, 27726720, -7388195, -16244694, -8171448], ![-49028688, 110240448, -29375214, -64588331, -32489388], ![-91302528, 205292706, -54703314, -120278118, -60502607]]]
  hmulB := by decide  
  f := ![![![-45713, 127454, -60662, -39278, 25346]], ![![-18047, 50311, -23904, -15554, 10026]], ![![-32188, 89800, -42975, -27418, 17752]], ![![-13316, 36896, -16634, -12367, 7748]], ![![-11048, 31190, -16334, -8030, 5553]]]
  g := ![![![60905, 1753946, -467354, -1027606, -516910], ![242189, 6973589, -1858210, -4085724, -2055212], ![962956, 27726720, -7388195, -16244694, -8171448], ![3828692, 110240448, -29375214, -64588331, -32489388], ![7129898, 205292706, -54703314, -120278118, -60502607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N2 : Nat.card (O ⧸ I293N2) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N2)

lemma isPrimeI293N2 : Ideal.IsPrime I293N2 := prime_ideal_of_norm_prime hp293.out _ NI293N2
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-299, 654, -145, -365, -186]] ![![3515011, -7903483, 2106013, 4630546, 2329268]]
  ![![-157132463633, 353310571751, -94144887064, -206999708721, -104125523926]] where
 M := ![![![-157132463633, 353310571751, -94144887064, -206999708721, -104125523926]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N1 : IdealMulLeCertificate' Table 
  ![![-157132463633, 353310571751, -94144887064, -206999708721, -104125523926]] ![![-780061, 1753946, -467354, -1027606, -516910]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![19843568209387703537, -44618039258076742323, 11889144004112652910, 26141083419345294209, 13149554769383794320]]]
 hmul := by decide  
 g := ![![![![67725488769241309, -152279997467838711, 40577283290486870, 89218714741792813, 44879026516668240]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1, I293N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
    exact isPrimeI293N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0 ⊙ MulI293N1)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 16, -3, -13, -8]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-7, 16, -3, -13, -8]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![73, 6, 1, 0, 0], ![176, 37, 0, 1, 0], ![148, 281, 0, 0, 1]] where
  M :=![![![-7, 16, -3, -13, -8], ![-48, 113, -37, -59, -26], ![-156, 342, -76, -219, -118], ![-708, 1614, -467, -902, -438], ![-1236, 2760, -701, -1657, -843]]]
  hmulB := by decide  
  f := ![![![-1669, 2396, 1537, -87, -228]], ![![-1368, 1751, 1169, -59, -174]], ![![-427, 608, 391, -22, -58]], ![![-1124, 1587, 1024, -57, -152]], ![![-2056, 2757, 1810, -96, -269]]]
  g := ![![![12, 9, -3, -13, -8], ![55, 32, -37, -59, -26], ![200, 137, -76, -219, -118], ![837, 524, -467, -902, -438], ![1519, 994, -701, -1657, -843]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 2 2 8 [291, 163, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 306], [0, 1]]
 g := ![![[9, 114], [306, 305], [134], [181], [81, 215], [62, 280], [167], [1]], ![[154, 193], [18, 2], [134], [181], [34, 92], [165, 27], [167], [1]]]
 h' := ![![[144, 306], [291, 81], [74, 199], [152, 21], [68, 190], [71, 109], [165, 105], [16, 144], [0, 1]], ![[0, 1], [289, 226], [179, 108], [106, 286], [105, 117], [110, 198], [242, 202], [183, 163], [144, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [192, 202]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 2
  hpos := by decide
  P := [291, 163, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16799, -10686, -29359, 43397, 56444]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-45054, -56355, -29359, 43397, 56444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -19, -11, 0, 2]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![19, -19, -11, 0, 2]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![164, 289, 1, 0, 0], ![189, 147, 0, 1, 0], ![144, 45, 0, 0, 1]] where
  M :=![![![19, -19, -11, 0, 2], ![12, -11, -9, 3, 0], ![0, 12, -8, -9, 6], ![36, -90, 33, 34, -18], ![-54, 147, -69, -42, 31]]]
  hmulB := by decide  
  f := ![![![-155, 199, 137, -6, -20]], ![![-120, 145, 93, -3, -12]], ![![-196, 243, 161, -6, -22]], ![![-153, 192, 129, -5, -18]], ![![-90, 114, 78, -3, -11]]]
  g := ![![![5, 10, -11, 0, 2], ![3, 7, -9, 3, 0], ![7, 11, -8, -9, 6], ![-30, -45, 33, 34, -18], ![48, 81, -69, -42, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P1 : CertificateIrreducibleZModOfList' 307 2 2 8 [168, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [226, 306], [0, 1]]
 g := ![![[302, 53], [149, 17], [183], [176], [138, 196], [292, 276], [114], [1]], ![[0, 254], [0, 290], [183], [176], [226, 111], [40, 31], [114], [1]]]
 h' := ![![[226, 306], [142, 214], [77, 289], [11, 45], [148, 207], [64, 293], [169, 176], [139, 226], [0, 1]], ![[0, 1], [0, 93], [0, 18], [50, 262], [266, 100], [277, 14], [35, 131], [253, 81], [226, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [285]]
 b := ![[], [15, 296]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N1 : CertifiedPrimeIdeal' SI307N1 307 where
  n := 2
  hpos := by decide
  P := [168, 81, 1]
  hirr := P307P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3394, -4431, -2228, 6431, 6492]
  a := ![1, 3, -7, -1, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5803, -1948, -2228, 6431, 6492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N1 B_one_repr
lemma NI307N1 : Nat.card (O ⧸ I307N1) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-511, 481, 356, -15, -52]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![-511, 481, 356, -15, -52]] 
 ![![307, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![163, 0, 1, 0, 0], ![193, 0, 0, 1, 0], ![142, 0, 0, 0, 1]] where
  M :=![![![-511, 481, 356, -15, -52], ![-312, 269, 206, -8, -30], ![-180, 138, 111, -4, -16], ![-96, 60, 54, -1, -8], ![66, -57, -46, 1, 7]]]
  hmulB := by decide  
  f := ![![![23, -85, 80, -31, -46]], ![![0, -1, 2, -2, -2]], ![![11, -43, 43, -19, -26]], ![![5, -31, 42, -30, -34]], ![![-4, -7, 30, -35, -31]]]
  g := ![![![-176, 481, 356, -15, -52], ![-102, 269, 206, -8, -30], ![-55, 138, 111, -4, -16], ![-27, 60, 54, -1, -8], ![23, -57, -46, 1, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-7, 16, -3, -13, -8]] ![![19, -19, -11, 0, 2]]
  ![![23, -85, 80, -31, -46]] where
 M := ![![![23, -85, 80, -31, -46]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![23, -85, 80, -31, -46]] ![![-511, 481, 356, -15, -52]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![307, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1, I307N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
    exact isPrimeI307N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0 ⊙ MulI307N1)


lemma PB434I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB434I6 : PrimesBelowBoundCertificateInterval O 251 307 434 where
  m := 9
  g := ![3, 2, 2, 2, 2, 2, 3, 3, 3]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB434I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1]
    · exact ![I283N0, I283N1, I283N2]
    · exact ![I293N0, I293N1, I293N2]
    · exact ![I307N0, I307N1, I307N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC257
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
    · exact PBC283
    · exact PBC293
    · exact PBC307
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![66049, 66049, 257]
    · exact ![18191447, 69169]
    · exact ![5236114321, 269]
    · exact ![19902511, 73441]
    · exact ![5887339441, 277]
    · exact ![6234839521, 281]
    · exact ![22665187, 283, 283]
    · exact ![25153757, 293, 293]
    · exact ![94249, 94249, 307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
      exact NI283N2
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
      exact NI293N2
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
  β := ![I257N2, I269N1, I277N1, I281N1, I283N1, I283N2, I293N1, I293N2, I307N2]
  Il := ![[I257N2], [], [I269N1], [], [I277N1], [I281N1], [I283N1, I283N2], [I293N1, I293N2], [I307N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
