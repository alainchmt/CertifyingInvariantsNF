
import IdealArithmetic.Examples.NF5_3_379687500_2.RI5_3_379687500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6351, -3949, -303, 1768, 9950]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![-6351, -3949, -303, 1768, 9950]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![0, 0, 467, 0, 0], ![277, 336, 19, 1, 0], ![244, 31, 132, 0, 1]] where
  M :=![![![-6351, -3949, -303, 1768, 9950], ![-21960, -14167, -922, 6632, 37014], ![-91048, -59952, -3527, 28714, 159598], ![-160794, -107010, -5934, 51889, 287754], ![9662, 6752, 276, -3446, -18939]]]
  hmulB := by decide  
  f := ![![![-229, -109, -25, 62, 398]], ![![604, 871, 130, -336, -1990]], ![![1400, -684, 71, -26, -398]], ![![347, 529, 80, -203, -1194]], ![![318, -191, 16, 2, -41]]]
  g := ![![![-6261, -1941, -2885, 1768, 9950], ![-23320, -7259, -10734, 6632, 37014], ![-100614, -31382, -46287, 28714, 159598], ![-181469, -56664, -83459, 51889, 287754], ![11960, 3751, 5494, -3446, -18939]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 3 2 8 [120, 161, 203, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [143, 276, 374], [121, 190, 93], [0, 1]]
 g := ![![[423, 177, 341], [170, 170, 25], [140, 300], [77, 59], [209, 185, 262], [201, 112], [141, 397, 113], [1]], ![[22, 293, 217, 289], [410, 231, 29, 48], [82, 352], [127, 423], [29, 231, 140, 465], [58, 225], [444, 208, 377, 213], [434, 425, 183, 284]], ![[343, 390, 361, 244], [44, 288, 450, 253], [355, 369], [342, 264], [6, 385, 170, 326], [158, 48], [186, 164, 379, 258], [192, 219, 22, 183]]]
 h' := ![![[143, 276, 374], [148, 305, 420], [21, 176, 462], [464, 21, 208], [138, 250, 153], [153, 63, 27], [359, 99, 255], [347, 306, 264], [0, 1]], ![[121, 190, 93], [295, 369, 65], [444, 422, 428], [322, 342, 207], [119, 385, 216], [350, 115, 205], [200, 139, 15], [77, 299, 220], [143, 276, 374]], ![[0, 1], [213, 260, 449], [407, 336, 44], [38, 104, 52], [89, 299, 98], [204, 289, 235], [445, 229, 197], [73, 329, 450], [121, 190, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 96], []]
 b := ![[], [446, 129, 227], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 3
  hpos := by decide
  P := [120, 161, 203, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1654214147, 1688728756, 95304539, -650096527, -3892946057]
  a := ![935, 890, 79, -369, -2189]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2423147302, 729769785, 1127015028, -650096527, -3892946057]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 101847563 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 109, 25, -62, -398]] i)))

def SI467N1: IdealEqSpanCertificate' Table ![![229, 109, 25, -62, -398]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![215, 430, 1, 0, 0], ![134, 142, 0, 1, 0], ![391, 393, 0, 0, 1]] where
  M :=![![![229, 109, 25, -62, -398], ![-604, -871, -130, 336, 1990], ![-1400, 684, -71, 26, 398], ![4062, 2424, 744, -1415, -8358], ![-858, -686, -170, 346, 2033]]]
  hmulB := by decide  
  f := ![![![6351, 3949, 303, -1768, -9950]], ![![21960, 14167, 922, -6632, -37014]], ![![23339, 14991, 996, -6982, -39004]], ![![8844, 5670, 380, -2635, -14726]], ![![23777, 15214, 1029, -7054, -39439]]]
  g := ![![![340, 331, 25, -62, -398], ![-1704, -1659, -130, 336, 1990], ![-311, -276, -71, 26, 398], ![7070, 6784, 744, -1415, -8358], ![-1725, -1661, -170, 346, 2033]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P1 : CertificateIrreducibleZModOfList' 467 2 2 8 [27, 368, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 466], [0, 1]]
 g := ![![[152, 173], [261, 411], [425], [22], [129, 362], [193], [293, 155], [99, 1]], ![[0, 294], [321, 56], [425], [22], [8, 105], [193], [227, 312], [198, 466]]]
 h' := ![![[99, 466], [425, 241], [269, 187], [370, 110], [253, 402], [243, 431], [28, 367], [129, 434], [0, 1]], ![[0, 1], [0, 226], [102, 280], [52, 357], [356, 65], [415, 36], [402, 100], [131, 33], [99, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [36, 254]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N1 : CertifiedPrimeIdeal' SI467N1 467 where
  n := 2
  hpos := by decide
  P := [27, 368, 1]
  hirr := P467P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2712000, -2942678, -198428, 1111050, 6709956]
  a := ![-1313, -1315, -111, 518, 3074]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5851228, -5808138, -198428, 1111050, 6709956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N1 B_one_repr
lemma NI467N1 : Nat.card (O ⧸ I467N1) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N1
def MulI467N0 : IdealMulLeCertificate' Table 
  ![![-6351, -3949, -303, 1768, 9950]] ![![229, 109, 25, -62, -398]]
  ![![467, 0, 0, 0, 0]] where
 M := ![![![-467, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC467 : ContainsPrimesAboveP 467 ![I467N0, I467N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
    exact isPrimeI467N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 467 (by decide) (𝕀 ⊙ MulI467N0)
instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2309, 3649, 216, -1161, -7474]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![2309, 3649, 216, -1161, -7474]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![182, 388, 315, 1, 0], ![194, 164, 315, 0, 1]] where
  M :=![![![2309, 3649, 216, -1161, -7474], ![-11902, -18881, -1142, 6020, 38680], ![59640, 95898, 5717, -30444, -195600], ![-180480, -290565, -17121, 92087, 592044], ![30636, 49387, 2901, -15642, -100577]]]
  hmulB := by decide  
  f := ![![![-1665, -950, -101, 377, 2174]], ![![-3218, -1867, -184, 766, 4388]], ![![-7356, -4446, -377, 1920, 10872]], ![![-8092, -4807, -436, 2031, 11556]], ![![-6616, -3949, -352, 1678, 9535]]]
  g := ![![![3473, 3507, 5679, -1161, -7474], ![-17978, -18159, -29398, 6020, 38680], ![90912, 91830, 148663, -30444, -195600], ![-275150, -277903, -449934, 92087, 592044], ![46742, 47209, 76434, -15642, -100577]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 3 2 8 [283, 176, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [360, 169, 170], [113, 309, 309], [0, 1]]
 g := ![![[256, 126, 365], [335, 430, 49], [14, 132, 28], [439, 308, 214], [171, 38, 4], [333, 231], [374, 459, 36], [1]], ![[148, 278, 419, 106], [32, 214, 345, 260], [184, 356, 99, 470], [194, 343, 85, 268], [337, 324, 11, 29], [435, 105], [326, 400, 418, 285], [244, 74, 308, 376]], ![[242, 281, 1, 224], [123, 329, 231, 462], [43, 166, 469, 277], [130, 277, 461, 326], [101, 383, 352, 231], [97, 392], [26, 79, 255, 100], [447, 434, 170, 103]]]
 h' := ![![[360, 169, 170], [37, 68, 172], [349, 257, 7], [303, 65, 76], [465, 389, 385], [413, 224, 477], [17, 286, 173], [196, 303, 473], [0, 1]], ![[113, 309, 309], [372, 84, 43], [389, 360, 348], [79, 96, 46], [259, 237, 201], [43, 415, 100], [66, 322, 50], [366, 196, 319], [360, 169, 170]], ![[0, 1], [27, 327, 264], [387, 341, 124], [71, 318, 357], [259, 332, 372], [71, 319, 381], [106, 350, 256], [104, 459, 166], [113, 309, 309]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [351, 113], []]
 b := ![[], [400, 145, 329], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 3
  hpos := by decide
  P := [283, 176, 6, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5092526, 4603485, 256614, -1881569, -11052838]
  a := ![129, 120, 11, -51, -302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5202064, 5317991, 8506461, -1881569, -11052838]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 109902239 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1665, 950, 101, -377, -2174]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![1665, 950, 101, -377, -2174]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![154, 329, 1, 0, 0], ![456, 398, 0, 1, 0], ![132, 392, 0, 0, 1]] where
  M :=![![![1665, 950, 101, -377, -2174], ![3218, 1867, 184, -766, -4388], ![7356, 4446, 377, -1920, -10872], ![7314, 4767, 315, -2227, -12432], ![1162, 593, 83, -200, -1197]]]
  hmulB := by decide  
  f := ![![![-2309, -3649, -216, 1161, 7474]], ![![11902, 18881, 1142, -6020, -38680]], ![![7308, 11595, 703, -3698, -23756]], ![![8068, 12821, 779, -4089, -26260]], ![![9040, 14343, 869, -4574, -29385]]]
  g := ![![![929, 2025, 101, -377, -2174], ![1886, 4105, 184, -766, -4388], ![4718, 10243, 377, -1920, -10872], ![5460, 11818, 315, -2227, -12432], ![496, 1090, 83, -200, -1197]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P1 : CertificateIrreducibleZModOfList' 479 2 2 8 [285, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [418, 478], [0, 1]]
 g := ![![[254, 73], [293, 56], [284, 378], [151, 181], [445, 2], [132], [268, 183], [418, 1]], ![[112, 406], [230, 423], [218, 101], [127, 298], [323, 477], [132], [122, 296], [357, 478]]]
 h' := ![![[418, 478], [320, 297], [11, 321], [75, 162], [110, 77], [282, 187], [260, 236], [141, 83], [0, 1]], ![[0, 1], [405, 182], [69, 158], [252, 317], [203, 402], [371, 292], [234, 243], [347, 396], [418, 478]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [206]]
 b := ![[], [28, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N1 : CertifiedPrimeIdeal' SI479N1 479 where
  n := 2
  hpos := by decide
  P := [285, 61, 1]
  hirr := P479P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2946715, -2710128, -173042, 1097710, 6534348]
  a := ![-1401, -1316, -119, 552, 3280]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2796217, -6146414, -173042, 1097710, 6534348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N1 B_one_repr
lemma NI479N1 : Nat.card (O ⧸ I479N1) = 229441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N1
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![2309, 3649, 216, -1161, -7474]] ![![1665, 950, 101, -377, -2174]]
  ![![479, 0, 0, 0, 0]] where
 M := ![![![-479, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC479 : ContainsPrimesAboveP 479 ![I479N0, I479N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI479N0
    exact isPrimeI479N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 479 (by decide) (𝕀 ⊙ MulI479N0)
instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 117, 3, -28, -188]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![21, 117, 3, -28, -188]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![470, 437, 354, 1, 0], ![62, 284, 126, 0, 1]] where
  M :=![![![21, 117, 3, -28, -188], ![-504, -707, -24, 226, 1452], ![2236, 3540, 235, -1104, -7336], ![-9982, -13932, -954, 4703, 29728], ![1626, 2358, 168, -788, -4997]]]
  hmulB := by decide  
  f := ![![![-2933, -1647, -183, 638, 3696]], ![![-4972, -2801, -312, 1086, 6292]], ![![-8444, -4728, -527, 1840, 10664]], ![![-13436, -7543, -840, 2929, 16972]], ![![-5464, -3070, -342, 1192, 6907]]]
  g := ![![![51, 135, 69, -28, -188], ![-404, -1051, -540, 226, 1452], ![2004, 5276, 2701, -1104, -7336], ![-8344, -21585, -11112, 4703, 29728], ![1400, 3626, 1866, -788, -4997]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 3 2 8 [15, 7, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [284, 277, 118], [160, 209, 369], [0, 1]]
 g := ![![[46, 322, 135], [61, 95, 256], [373, 440, 162], [396, 289], [338, 102], [462, 274, 55], [70, 476, 388], [1]], ![[122, 15, 192, 163], [50, 37, 382, 190], [354, 285, 376, 231], [437, 313], [87, 447], [94, 143, 368, 321], [447, 307, 29, 105], [391, 271, 386, 381]], ![[422, 77, 79, 301], [407, 366, 369, 253], [200, 236, 7, 473], [451, 146], [268, 146], [215, 194, 205, 439], [166, 382, 165, 299], [53, 7, 211, 106]]]
 h' := ![![[284, 277, 118], [59, 248, 302], [249, 277, 471], [219, 137, 155], [169, 105, 17], [375, 380, 383], [411, 387, 223], [472, 480, 444], [0, 1]], ![[160, 209, 369], [38, 104, 339], [166, 237, 122], [334, 374, 348], [404, 174, 359], [380, 97, 215], [425, 245, 230], [238, 316, 414], [284, 277, 118]], ![[0, 1], [94, 135, 333], [456, 460, 381], [74, 463, 471], [316, 208, 111], [165, 10, 376], [439, 342, 34], [22, 178, 116], [160, 209, 369]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198, 251], []]
 b := ![[], [77, 286, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 3
  hpos := by decide
  P := [15, 7, 43, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9863073251, 10433765619, 597627085, -3945951306, -23805624393]
  a := ![1656, 1578, 142, -652, -3877]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6859155851, 17444788119, 9028692121, -3945951306, -23805624393]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 115501303 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1365, 911, 50, -443, -2456]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![1365, 911, 50, -443, -2456]] 
 ![![487, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![310, 0, 1, 0, 0], ![106, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![1365, 911, 50, -443, -2456], ![6542, 4363, 238, -2122, -11762], ![31404, 20970, 1145, -10194, -56502], ![59760, 39903, 2187, -19399, -107538], ![-4760, -3181, -175, 1546, 8571]]]
  hmulB := by decide  
  f := ![![![-4033, -1472, -231, 663, 3620]], ![![-868, -329, -50, 146, 802]], ![![-2554, -890, -145, 408, 2210]], ![![-1012, -521, -63, 209, 1202]], ![![-643, -211, -36, 99, 531]]]
  g := ![![![275, 911, 50, -443, -2456], ![1318, 4363, 238, -2122, -11762], ![6328, 20970, 1145, -10194, -56502], ![12040, 39903, 2187, -19399, -107538], ![-959, -3181, -175, 1546, 8571]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI487N1 : Nat.card (O ⧸ I487N1) = 487 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI487N1)

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := prime_ideal_of_norm_prime hp487.out _ NI487N1

def I487N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1411, 2322, 135, -737, -4742]] i)))

def SI487N2: IdealEqSpanCertificate' Table ![![1411, 2322, 135, -737, -4742]] 
 ![![487, 0, 0, 0, 0], ![165, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![482, 0, 0, 1, 0], ![299, 0, 0, 0, 1]] where
  M :=![![![1411, 2322, 135, -737, -4742], ![-7486, -11971, -714, 3790, 24388], ![38564, 61398, 3629, -19556, -125576], ![-115086, -185445, -10995, 58727, 377940], ![19598, 31581, 1869, -10010, -64401]]]
  hmulB := by decide  
  f := ![![![-64587, -95967, -15588, 37709, 220106]], ![![-22391, -32536, -5316, 12851, 75110]], ![![-3947, -6885, -1075, 2613, 15114]], ![![-63630, -97695, -15735, 38103, 221980]], ![![-39923, -58500, -9537, 23061, 134717]]]
  g := ![![![2844, 2322, 135, -737, -4742], ![-14615, -11971, -714, 3790, 24388], ![75381, 61398, 3629, -19556, -125576], ![-226510, -185445, -10995, 58727, 377940], ![38607, 31581, 1869, -10010, -64401]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI487N2 : Nat.card (O ⧸ I487N2) = 487 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI487N2)

lemma isPrimeI487N2 : Ideal.IsPrime I487N2 := prime_ideal_of_norm_prime hp487.out _ NI487N2
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![21, 117, 3, -28, -188]] ![![1365, 911, 50, -443, -2456]]
  ![![109891, 73256, 3995, -35635, -197520]] where
 M := ![![![109891, 73256, 3995, -35635, -197520]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI487N1 : IdealMulLeCertificate' Table 
  ![![109891, 73256, 3995, -35635, -197520]] ![![1411, 2322, 135, -737, -4742]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![-9182385, -6042209, -329699, 2962908, 16381706]]]
 hmul := by decide  
 g := ![![![![-18855, -12407, -677, 6084, 33638]]]]
 hle2 := by decide  


def PBC487 : ContainsPrimesAboveP 487 ![I487N0, I487N1, I487N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
    exact isPrimeI487N1
    exact isPrimeI487N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 487 (by decide) (𝕀 ⊙ MulI487N0 ⊙ MulI487N1)
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1573, -2723, -157, 850, 5442]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![-1573, -2723, -157, 850, 5442]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![0, 0, 491, 0, 0], ![470, 118, 413, 1, 0], ![397, 62, 260, 0, 1]] where
  M :=![![![-1573, -2723, -157, 850, 5442], ![7876, 13103, 696, -4076, -26314], ![-43872, -68604, -4003, 21830, 140790], ![137446, 215196, 13158, -68873, -442690], ![-23638, -36866, -2284, 11828, 75981]]]
  hmulB := by decide  
  f := ![![![-4383, -2963, -151, 1460, 8074]], ![![-22128, -14831, -792, 7244, 40122]], ![![-108064, -72240, -3917, 35178, 194938]], ![![-100832, -67446, -3645, 32865, 182100]], ![![-63527, -42499, -2295, 20712, 114759]]]
  g := ![![![-5217, -897, -3597, 850, 5442], ![25194, 4329, 17364, -4076, -26314], ![-134822, -23164, -92923, 21830, 140790], ![424146, 72890, 292377, -68873, -442690], ![-72805, -12512, -50188, 11828, 75981]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 3 2 8 [165, 479, 230, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [283, 299, 147], [469, 191, 344], [0, 1]]
 g := ![![[156, 76, 393], [189, 312, 106], [165, 80], [164, 251, 289], [129, 12], [38, 372, 407], [422, 352, 363], [1]], ![[257, 104, 489, 469], [42, 367, 43, 240], [414, 372], [253, 426, 483, 123], [339, 256], [171, 375, 181, 324], [402, 171, 442, 393], [211, 55, 411, 244]], ![[31, 216, 106, 34], [438, 420, 393, 231], [113, 156], [135, 26, 122, 412], [77, 401], [306, 70, 190, 116], [353, 239, 216, 323], [96, 435, 65, 247]]]
 h' := ![![[283, 299, 147], [239, 129, 324], [350, 475, 149], [436, 407, 97], [322, 276, 474], [113, 77, 226], [92, 232, 429], [326, 12, 261], [0, 1]], ![[469, 191, 344], [318, 107, 323], [122, 83, 84], [316, 42, 287], [78, 466, 9], [192, 6, 475], [366, 290, 167], [182, 481, 60], [283, 299, 147]], ![[0, 1], [133, 255, 335], [55, 424, 258], [459, 42, 107], [229, 240, 8], [64, 408, 281], [42, 460, 386], [26, 489, 170], [469, 191, 344]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [285, 312], []]
 b := ![[], [75, 381, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 3
  hpos := by decide
  P := [165, 479, 230, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49768657, -81788070, -4519624, 25621042, 165153682]
  a := ![-170, -162, -16, 62, 398]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-158162261, -27178410, -109014190, 25621042, 165153682]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 118370771 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4383, 2963, 151, -1460, -8074]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![4383, 2963, 151, -1460, -8074]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![339, 157, 1, 0, 0], ![224, 287, 0, 1, 0], ![165, 92, 0, 0, 1]] where
  M :=![![![4383, 2963, 151, -1460, -8074], ![22128, 14831, 792, -7244, -40122], ![108064, 72240, 3917, -35178, -194938], ![206966, 138198, 7548, -67209, -372530], ![-16870, -11224, -626, 5436, 30153]]]
  hmulB := by decide  
  f := ![![![1573, 2723, 157, -850, -5442]], ![![-7876, -13103, -696, 4076, 26314]], ![![-1343, -2170, -106, 672, 4370]], ![![-4166, -6855, -362, 2135, 13800]], ![![-899, -1465, -73, 454, 2947]]]
  g := ![![![3284, 2324, 151, -1460, -8074], ![16286, 11529, 792, -7244, -40122], ![79073, 55983, 3917, -35178, -194938], ![151060, 106955, 7548, -67209, -372530], ![-12215, -8650, -626, 5436, 30153]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P1 : CertificateIrreducibleZModOfList' 491 2 2 8 [143, 425, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 490], [0, 1]]
 g := ![![[415, 388], [365, 65], [245], [71, 163], [472], [346, 320], [339, 210], [66, 1]], ![[0, 103], [236, 426], [245], [27, 328], [472], [353, 171], [451, 281], [132, 490]]]
 h' := ![![[66, 490], [342, 218], [240, 89], [158, 47], [265, 431], [113, 392], [132, 297], [382, 285], [0, 1]], ![[0, 1], [0, 273], [222, 402], [314, 444], [233, 60], [453, 99], [94, 194], [43, 206], [66, 490]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [341]]
 b := ![[], [20, 416]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N1 : CertifiedPrimeIdeal' SI491N1 491 where
  n := 2
  hpos := by decide
  P := [143, 425, 1]
  hirr := P491P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12363399, -11389522, -759314, 4644654, 27503006]
  a := ![-2743, -2614, -230, 1086, 6422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10862229, -7648614, -759314, 4644654, 27503006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N1 B_one_repr
lemma NI491N1 : Nat.card (O ⧸ I491N1) = 241081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N1
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![-1573, -2723, -157, 850, 5442]] ![![4383, 2963, 151, -1460, -8074]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![-491, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC491 : ContainsPrimesAboveP 491 ![I491N0, I491N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 491 (by decide) (𝕀 ⊙ MulI491N0)
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-595, -442, -25, 201, 1136]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![-595, -442, -25, 201, 1136]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![0, 0, 499, 0, 0], ![204, 92, 411, 1, 0], ![71, 181, 175, 0, 1]] where
  M :=![![![-595, -442, -25, 201, 1136], ![-2362, -1349, -74, 720, 3886], ![-13592, -10194, -565, 4626, 26198], ![-19642, -9633, -495, 5691, 29842], ![1198, 209, 5, -274, -1227]]]
  hmulB := by decide  
  f := ![![![-173, -125, -18, 51, 300]], ![![-270, -35, -8, 30, 198]], ![![444, 414, 101, -214, -1326]], ![![244, 281, 74, -149, -928]], ![![33, 115, 30, -57, -351]]]
  g := ![![![-245, -450, -564, 201, 1136], ![-852, -1545, -1956, 720, 3886], ![-5646, -10376, -12999, 4626, 26198], ![-6612, -11893, -15154, 5691, 29842], ![289, 496, 656, -274, -1227]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 3 2 8 [327, 384, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [131, 106, 289], [286, 392, 210], [0, 1]]
 g := ![![[346, 392, 387], [377, 485, 413], [377, 476], [36, 142], [246, 141, 215], [434, 301, 122], [197, 129, 237], [1]], ![[77, 244, 234, 358], [425, 450, 325, 225], [252, 365], [158, 209], [257, 372, 458, 427], [139, 284, 448, 29], [339, 136, 424, 70], [186, 244, 251, 440]], ![[224, 290, 105, 149], [452, 417, 10, 333], [115, 299], [425, 187], [316, 144, 469, 206], [445, 497, 6, 252], [384, 268, 477, 460], [382, 214, 183, 59]]]
 h' := ![![[131, 106, 289], [473, 166, 214], [253, 303, 377], [334, 309, 436], [396, 33, 56], [297, 194, 240], [451, 76, 163], [172, 115, 417], [0, 1]], ![[286, 392, 210], [198, 99, 126], [147, 65, 322], [117, 459, 234], [197, 435, 52], [343, 237, 446], [114, 486, 32], [152, 119, 93], [131, 106, 289]], ![[0, 1], [248, 234, 159], [375, 131, 299], [183, 230, 328], [89, 31, 391], [116, 68, 312], [318, 436, 304], [372, 265, 488], [286, 392, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [379, 404], []]
 b := ![[], [71, 372, 154], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 3
  hpos := by decide
  P := [327, 384, 82, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7569220, -10265334, -603435, 3473296, 21831760]
  a := ![-129, -126, -11, 50, 302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4541436, -8579874, -10518409, 3473296, 21831760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 124251499 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 3, 1, -2, -12]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![7, 3, 1, -2, -12]] 
 ![![499, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![450, 0, 1, 0, 0], ![196, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![7, 3, 1, -2, -12], ![4, -5, -2, 2, 8], ![-116, -96, -13, 40, 260], ![298, 390, 42, -143, -880], ![-50, -72, -8, 26, 159]]]
  hmulB := by decide  
  f := ![![![4589, 2595, 283, -1012, -5848]], ![![81, 46, 5, -18, -104]], ![![4170, 2358, 257, -920, -5316]], ![![1822, 1032, 112, -403, -2328]], ![![64, 36, 4, -14, -81]]]
  g := ![![![0, 3, 1, -2, -12], ![1, -5, -2, 2, 8], ![-6, -96, -13, 40, 260], ![24, 390, 42, -143, -880], ![-4, -72, -8, 26, 159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N1 : Nat.card (O ⧸ I499N1) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N1)

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := prime_ideal_of_norm_prime hp499.out _ NI499N1

def I499N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-597, -332, -37, 129, 748]] i)))

def SI499N2: IdealEqSpanCertificate' Table ![![-597, -332, -37, 129, 748]] 
 ![![499, 0, 0, 0, 0], ![170, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![401, 0, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![-597, -332, -37, 129, 748], ![-986, -551, -60, 212, 1226], ![-1712, -1002, -113, 386, 2234], ![-678, -345, -45, 145, 858], ![-610, -347, -37, 132, 761]]]
  hmulB := by decide  
  f := ![![![65, -577, -32, 99, 848]], ![![36, -181, -10, 28, 254]], ![![2, -84, -5, 16, 130]], ![![223, -248, -13, 4, 214]], ![![-5, -196, -11, 39, 309]]]
  g := ![![![-200, -332, -37, 129, 748], ![-326, -551, -60, 212, 1226], ![-594, -1002, -113, 386, 2234], ![-239, -345, -45, 145, 858], ![-201, -347, -37, 132, 761]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI499N2 : Nat.card (O ⧸ I499N2) = 499 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI499N2)

lemma isPrimeI499N2 : Ideal.IsPrime I499N2 := prime_ideal_of_norm_prime hp499.out _ NI499N2
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![-595, -442, -25, 201, 1136]] ![![7, 3, 1, -2, -12]]
  ![![65, -577, -32, 99, 848]] where
 M := ![![![65, -577, -32, 99, 848]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI499N1 : IdealMulLeCertificate' Table 
  ![![65, -577, -32, 99, 848]] ![![-597, -332, -37, 129, 748]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![499, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC499 : ContainsPrimesAboveP 499 ![I499N0, I499N1, I499N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI499N0
    exact isPrimeI499N1
    exact isPrimeI499N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 499 (by decide) (𝕀 ⊙ MulI499N0 ⊙ MulI499N1)
instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23445, 13206, 1466, -5114, -29644]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![23445, 13206, 1466, -5114, -29644]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![475, 423, 1, 0, 0], ![403, 347, 0, 1, 0], ![267, 97, 0, 0, 1]] where
  M :=![![![23445, 13206, 1466, -5114, -29644], ![39348, 21881, 2450, -8508, -49224], ![68088, 39372, 4279, -15164, -88176], ![20432, 8178, 1152, -3583, -19652], ![25356, 14802, 1604, -5670, -33037]]]
  hmulB := by decide  
  f := ![![![147, 6210, 754, -1898, -10268]], ![![35156, 20119, 4630, -10812, -67448]], ![![29603, 22581, 4575, -10810, -65988]], ![![24075, 18859, 3780, -8941, -54472]], ![![6935, 7193, 1300, -3108, -18561]]]
  g := ![![![18495, 8038, 1466, -5114, -29644], ![30710, 13345, 2450, -8508, -49224], ![55049, 23945, 4279, -15164, -88176], ![12255, 5309, 1152, -3583, -19652], ![20615, 8963, 1604, -5670, -33037]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 2 2 8 [419, 296, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [207, 502], [0, 1]]
 g := ![![[236, 242], [43, 441], [115, 354], [472], [293, 364], [172, 117], [181, 498], [207, 1]], ![[30, 261], [287, 62], [458, 149], [472], [191, 139], [247, 386], [152, 5], [414, 502]]]
 h' := ![![[207, 502], [91, 218], [103, 21], [130, 417], [468, 391], [364, 80], [114, 135], [286, 178], [0, 1]], ![[0, 1], [450, 285], [426, 482], [436, 86], [422, 112], [325, 423], [394, 368], [413, 325], [207, 502]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [255]]
 b := ![[], [259, 379]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 2
  hpos := by decide
  P := [419, 296, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4919657, -4769355, -310327, 1889027, 11306119]
  a := ![-1738, -1656, -145, 684, 4069]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7231662, -3231982, -310327, 1889027, 11306119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 253009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, -37, -8, 19, 118]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![-59, -37, -8, 19, 118]] 
 ![![503, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![331, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![391, 0, 0, 0, 1]] where
  M :=![![![-59, -37, -8, 19, 118], ![74, 167, 24, -60, -344], ![568, 162, 59, -128, -832], ![-1052, -1077, -207, 475, 2816], ![196, 239, 43, -100, -587]]]
  hmulB := by decide  
  f := ![![![-1993, -784, -209, 89, 782]], ![![-149, -53, -17, 1, 30]], ![![-1193, -434, -134, 17, 286]], ![![-87, 43, -28, -74, -358]], ![![-1583, -631, -164, 79, 663]]]
  g := ![![![-87, -37, -8, 19, 118], ![249, 167, 24, -60, -344], ![619, 162, 59, -128, -832], ![-2053, -1077, -207, 475, 2816], ![427, 239, 43, -100, -587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N1 : Nat.card (O ⧸ I503N1) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N1)

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := prime_ideal_of_norm_prime hp503.out _ NI503N1

def I503N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-865, -1262, -206, 498, 2910]] i)))

def SI503N2: IdealEqSpanCertificate' Table ![![-865, -1262, -206, 498, 2910]] 
 ![![503, 0, 0, 0, 0], ![236, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![113, 0, 0, 1, 0], ![216, 0, 0, 0, 1]] where
  M :=![![![-865, -1262, -206, 498, 2910], ![-3180, -61, -208, 446, 3234], ![14732, 15120, 2743, -6554, -39170], ![1344, -17700, -2040, 5173, 27534], ![-1604, 2776, 232, -624, -2945]]]
  hmulB := by decide  
  f := ![![![19873, 41458, 2178, -12818, -83646]], ![![9000, 18963, 992, -5858, -38246]], ![![6875, 13678, 733, -4248, -27652]], ![![-113, 1978, 54, -553, -3828]], ![![9292, 19040, 1008, -5896, -38441]]]
  g := ![![![-715, -1262, -206, 498, 2910], ![-1410, -61, -208, 446, 3234], ![10481, 15120, 2743, -6554, -39170], ![-4123, -17700, -2040, 5173, 27534], ![36, 2776, 232, -624, -2945]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N2 : Nat.card (O ⧸ I503N2) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N2)

lemma isPrimeI503N2 : Ideal.IsPrime I503N2 := prime_ideal_of_norm_prime hp503.out _ NI503N2

def I503N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 54, 3, -29, -156]] i)))

def SI503N3: IdealEqSpanCertificate' Table ![![97, 54, 3, -29, -156]] 
 ![![503, 0, 0, 0, 0], ![306, 1, 0, 0, 0], ![425, 0, 1, 0, 0], ![404, 0, 0, 1, 0], ![148, 0, 0, 0, 1]] where
  M :=![![![97, 54, 3, -29, -156], ![562, 427, 24, -192, -1090], ![2120, 1146, 61, -634, -3386], ![5426, 4437, 249, -1921, -11042], ![-506, -477, -27, 192, 1131]]]
  hmulB := by decide  
  f := ![![![3159, 495, 234, -543, -3688]], ![![1900, 277, 138, -320, -2182]], ![![2637, 447, 199, -463, -3130]], ![![2716, 513, 213, -495, -3326]], ![![892, 117, 63, -146, -1001]]]
  g := ![![![34, 54, 3, -29, -156], ![196, 427, 24, -192, -1090], ![761, 1146, 61, -634, -3386], ![1893, 4437, 249, -1921, -11042], ![-175, -477, -27, 192, 1131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N3 : Nat.card (O ⧸ I503N3) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N3)

lemma isPrimeI503N3 : Ideal.IsPrime I503N3 := prime_ideal_of_norm_prime hp503.out _ NI503N3
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![23445, 13206, 1466, -5114, -29644]] ![![-59, -37, -8, 19, 118]]
  ![![-3619, -1709, -216, 697, 3938]] where
 M := ![![![-3619, -1709, -216, 697, 3938]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI503N1 : IdealMulLeCertificate' Table 
  ![![-3619, -1709, -216, 697, 3938]] ![![-865, -1262, -206, 498, 2910]]
  ![![3159, 495, 234, -543, -3688]] where
 M := ![![![3159, 495, 234, -543, -3688]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI503N2 : IdealMulLeCertificate' Table 
  ![![3159, 495, 234, -543, -3688]] ![![97, 54, 3, -29, -156]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![503, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC503 : ContainsPrimesAboveP 503 ![I503N0, I503N1, I503N2, I503N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
    exact isPrimeI503N2
    exact isPrimeI503N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 503 (by decide) (𝕀 ⊙ MulI503N0 ⊙ MulI503N1 ⊙ MulI503N2)
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1291989, 862403, 47155, -419298, -2324210]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![1291989, 862403, 47155, -419298, -2324210]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![0, 0, 509, 0, 0], ![0, 0, 0, 509, 0], ![47, 161, 63, 429, 1]] where
  M :=![![![1291989, 862403, 47155, -419298, -2324210], ![6202780, 4140385, 226398, -2013048, -11158534], ![29779208, 19877604, 1086901, -9664498, -53571326], ![56594162, 37776576, 2065548, -18366991, -101810018], ![-4503342, -3005962, -164354, 1461506, 8101261]]]
  hmulB := by decide  
  f := ![![![89, 77, 7, -28, -174]], ![![-112, -247, -18, 80, 514]], ![![792, 1320, 77, -410, -2598]], ![![-1918, -3426, -162, 1041, 6742]], ![![-1545, -2794, -132, 849, 5505]]]
  g := ![![![217151, 736857, 287765, 1958088, -2324210], ![1042542, 3537651, 1381560, 9400782, -11158534], ![5005170, 16984010, 6632771, 45132484, -53571326], ![9512112, 32277386, 12605298, 85772359, -101810018], ![-756901, -2568387, -1003033, -6825107, 8101261]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 4 2 8 [113, 187, 83, 508, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [316, 353, 121, 212], [351, 148, 441, 180], [352, 7, 456, 117], [0, 1]]
 g := ![![[299, 69, 504, 66], [148, 215, 20], [327, 428, 397, 109], [302, 431, 444, 413], [161, 450, 105, 465], [0, 407, 505, 80], [157, 427, 1, 1], []], ![[31, 433, 334, 70, 94, 300], [492, 357, 96], [312, 453, 168, 183, 298, 378], [367, 355, 342, 99, 456, 201], [373, 44, 116, 359, 174, 15], [169, 391, 494, 478, 495, 7], [489, 58, 115, 77, 62, 226], [371, 120, 497, 209, 361, 157]], ![[470, 136, 70, 41, 75, 109], [61, 229, 158], [25, 388, 382, 236, 99, 156], [279, 240, 115, 355, 266, 472], [394, 140, 156, 380, 429, 493], [86, 490, 337, 427, 206, 121], [14, 1, 401, 140, 93, 350], [241, 144, 308, 146, 152, 387]], ![[22, 497, 120, 367, 141, 255], [466, 266, 465], [247, 328, 386, 374, 412, 369], [355, 136, 385, 298, 30, 151], [100, 377, 78, 347, 85, 178], [439, 8, 466, 308, 241, 240], [230, 473, 282, 399, 247, 334], [53, 232, 330, 266, 232, 299]]]
 h' := ![![[316, 353, 121, 212], [262, 483, 155, 228], [206, 451, 303, 23], [486, 41, 233, 88], [131, 483, 57, 353], [0, 205, 507, 90], [74, 267, 154, 46], [0, 0, 0, 1], [0, 1]], ![[351, 148, 441, 180], [250, 17, 340, 245], [460, 488, 174, 128], [341, 413, 474, 289], [241, 443, 172, 79], [80, 127, 166, 409], [336, 349, 356, 278], [383, 239, 455, 191], [316, 353, 121, 212]], ![[352, 7, 456, 117], [4, 283, 1, 407], [332, 134, 62, 448], [485, 488, 506, 411], [296, 441, 389, 203], [456, 63, 30, 285], [400, 379, 149, 140], [182, 282, 189, 367], [351, 148, 441, 180]], ![[0, 1], [187, 235, 13, 138], [390, 454, 479, 419], [471, 76, 314, 230], [68, 160, 400, 383], [485, 114, 315, 234], [245, 23, 359, 45], [153, 497, 374, 459], [352, 7, 456, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [186, 406, 313], []]
 b := ![[], [], [220, 58, 378, 216], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 4
  hpos := by decide
  P := [113, 187, 83, 508, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6143991998686, -6732606696426, -386144754597, 2508550649030, 15189906545228]
  a := ![-1061, -1010, -91, 418, 2484]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1414675048378, -4817893046126, -1880845298829, -12797566517198, 15189906545228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 67122964561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def I509N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, -77, -7, 28, 174]] i)))

def SI509N1: IdealEqSpanCertificate' Table ![![-89, -77, -7, 28, 174]] 
 ![![509, 0, 0, 0, 0], ![349, 1, 0, 0, 0], ![359, 0, 1, 0, 0], ![291, 0, 0, 1, 0], ![417, 0, 0, 0, 1]] where
  M :=![![![-89, -77, -7, 28, 174], ![112, 247, 18, -80, -514], ![-792, -1320, -77, 410, 2598], ![1918, 3426, 162, -1041, -6742], ![-370, -596, -28, 182, 1175]]]
  hmulB := by decide  
  f := ![![![-1291989, -862403, -47155, 419298, 2324210]], ![![-898049, -599448, -32777, 291450, 1615536]], ![![-969751, -647309, -35394, 314720, 1744524]], ![![-849829, -567261, -31017, 275801, 1528792]], ![![-1049619, -700621, -38309, 340640, 1888201]]]
  g := ![![![-101, -77, -7, 28, 174], ![285, 247, 18, -80, -514], ![-1405, -1320, -77, 410, 2598], ![3659, 3426, 162, -1041, -6742], ![-639, -596, -28, 182, 1175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI509N1 : Nat.card (O ⧸ I509N1) = 509 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI509N1)

lemma isPrimeI509N1 : Ideal.IsPrime I509N1 := prime_ideal_of_norm_prime hp509.out _ NI509N1
def MulI509N0 : IdealMulLeCertificate' Table 
  ![![1291989, 862403, 47155, -419298, -2324210]] ![![-89, -77, -7, 28, 174]]
  ![![509, 0, 0, 0, 0]] where
 M := ![![![-509, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC509 : ContainsPrimesAboveP 509 ![I509N0, I509N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI509N0
    exact isPrimeI509N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 509 (by decide) (𝕀 ⊙ MulI509N0)
instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![423, 196, 50, -116, -736]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![423, 196, 50, -116, -736]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![497, 278, 1, 0, 0], ![222, 282, 0, 1, 0], ![115, 246, 0, 0, 1]] where
  M :=![![![423, 196, 50, -116, -736], ![-888, -1393, -222, 540, 3144], ![-3768, -336, -283, 612, 4272], ![9672, 8520, 1650, -3889, -23460], ![-1916, -1952, -358, 850, 5077]]]
  hmulB := by decide  
  f := ![![![9503, 5308, 602, -2036, -11824]], ![![15048, 8263, 978, -3108, -18120]], ![![17135, 9494, 1099, -3608, -20992]], ![![12186, 6726, 786, -2545, -14820]], ![![9225, 5086, 596, -1922, -11195]]]
  g := ![![![165, 384, 50, -116, -736], ![-714, -1661, -222, 540, 3144], ![-941, -2198, -283, 612, 4272], ![5280, 12318, 1650, -3889, -23460], ![-1145, -2670, -358, 850, 5077]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 2 2 9 [280, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [448, 520], [0, 1]]
 g := ![![[311, 325], [144], [273], [345, 317], [185], [210], [419], [119], [1]], ![[31, 196], [144], [273], [128, 204], [185], [210], [419], [119], [1]]]
 h' := ![![[448, 520], [327, 357], [3, 509], [306, 362], [494, 472], [359, 145], [478, 335], [274, 412], [241, 448], [0, 1]], ![[0, 1], [316, 164], [358, 12], [451, 159], [424, 49], [194, 376], [510, 186], [416, 109], [360, 73], [448, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [343]]
 b := ![[], [138, 432]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 2
  hpos := by decide
  P := [280, 73, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1847176, -1698417, -111951, 691834, 4099330]
  a := ![-1099, -1047, -93, 435, 2573]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1096387, -2253567, -111951, 691834, 4099330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 271441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 61, 9, -24, -140]] i)))

def SI521N1: IdealEqSpanCertificate' Table ![![63, 61, 9, -24, -140]] 
 ![![521, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![238, 0, 1, 0, 0], ![305, 0, 0, 1, 0], ![509, 0, 0, 0, 1]] where
  M :=![![![63, 61, 9, -24, -140], ![160, 31, 10, -26, -172], ![-396, -444, -85, 196, 1176], ![2, 612, 72, -183, -980], ![86, -74, -6, 14, 59]]]
  hmulB := by decide  
  f := ![![![14895, 10063, 553, -4854, -26968]], ![![2536, 1711, 94, -826, -4588]], ![![7462, 5042, 277, -2432, -13512]], ![![9937, 6685, 367, -3233, -17948]], ![![14457, 9771, 537, -4712, -26181]]]
  g := ![![![137, 61, 9, -24, -140], ![174, 31, 10, -26, -172], ![-1154, -444, -85, 196, 1176], ![933, 612, 72, -183, -980], ![-51, -74, -6, 14, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N1 : Nat.card (O ⧸ I521N1) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N1)

lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := prime_ideal_of_norm_prime hp521.out _ NI521N1

def I521N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3071, 2051, 112, -997, -5526]] i)))

def SI521N2: IdealEqSpanCertificate' Table ![![3071, 2051, 112, -997, -5526]] 
 ![![521, 0, 0, 0, 0], ![235, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![403, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![3071, 2051, 112, -997, -5526], ![14762, 9857, 540, -4792, -26564], ![70848, 47274, 2585, -22988, -127428], ![134564, 89823, 4905, -43671, -242060], ![-10700, -7141, -389, 3472, 19243]]]
  hmulB := by decide  
  f := ![![![-7713, -8110, -593, 2727, 16966]], ![![-3457, -3609, -265, 1215, 7554]], ![![-221, -320, -20, 103, 658]], ![![-5417, -5387, -406, 1828, 11314]], ![![-1110, -1215, -87, 406, 2535]]]
  g := ![![![573, 2051, 112, -997, -5526], ![2755, 9857, 540, -4792, -26564], ![13221, 47274, 2585, -22988, -127428], ![25107, 89823, 4905, -43671, -242060], ![-1996, -7141, -389, 3472, 19243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N2 : Nat.card (O ⧸ I521N2) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N2)

lemma isPrimeI521N2 : Ideal.IsPrime I521N2 := prime_ideal_of_norm_prime hp521.out _ NI521N2

def I521N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3031, 2429, 212, -863, -5226]] i)))

def SI521N3: IdealEqSpanCertificate' Table ![![3031, 2429, 212, -863, -5226]] 
 ![![521, 0, 0, 0, 0], ![445, 1, 0, 0, 0], ![476, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![367, 0, 0, 0, 1]] where
  M :=![![![3031, 2429, 212, -863, -5226], ![382, -3491, -92, 952, 6668], ![24864, 32862, 2141, -10700, -67860], ![-52972, -87339, -5109, 27621, 177940], ![11892, 16481, 1049, -5328, -33917]]]
  hmulB := by decide  
  f := ![![![-104765, -113596, -20241, 48445, 288466]], ![![-89787, -96787, -17279, 41347, 246298]], ![![-92896, -101518, -18043, 43196, 257076]], ![![-28902, -33779, -5877, 14103, 83560]], ![![-73685, -79261, -14160, 33881, 201853]]]
  g := ![![![1644, 2429, 212, -863, -5226], ![-1879, -3491, -92, 952, 6668], ![20618, 32862, 2141, -10700, -67860], ![-53389, -87339, -5109, 27621, 177940], ![10270, 16481, 1049, -5328, -33917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N3 : Nat.card (O ⧸ I521N3) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N3)

lemma isPrimeI521N3 : Ideal.IsPrime I521N3 := prime_ideal_of_norm_prime hp521.out _ NI521N3
def MulI521N0 : IdealMulLeCertificate' Table 
  ![![423, 196, 50, -116, -736]] ![![63, 61, 9, -24, -140]]
  ![![-25319, -6849, -2419, 5476, 36124]] where
 M := ![![![-25319, -6849, -2419, 5476, 36124]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI521N1 : IdealMulLeCertificate' Table 
  ![![-25319, -6849, -2419, 5476, 36124]] ![![3071, 2051, 112, -997, -5526]]
  ![![104765, 113596, 20241, -48445, -288466]] where
 M := ![![![104765, 113596, 20241, -48445, -288466]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI521N2 : IdealMulLeCertificate' Table 
  ![![104765, 113596, 20241, -48445, -288466]] ![![3031, 2429, 212, -863, -5226]]
  ![![521, 0, 0, 0, 0]] where
 M := ![![![-521, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC521 : ContainsPrimesAboveP 521 ![I521N0, I521N1, I521N2, I521N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
    exact isPrimeI521N1
    exact isPrimeI521N2
    exact isPrimeI521N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 521 (by decide) (𝕀 ⊙ MulI521N0 ⊙ MulI521N1 ⊙ MulI521N2)
instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8627, 2840, 885, -2019, -13134]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![8627, 2840, 885, -2019, -13134]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![336, 264, 1, 0, 0], ![458, 229, 0, 1, 0], ![195, 286, 0, 0, 1]] where
  M :=![![![8627, 2840, 885, -2019, -13134], ![-24522, -32047, -5392, 12990, 76416], ![-68652, 10746, -3041, 5980, 50148], ![228098, 177993, 35745, -84505, -515012], ![-46846, -42205, -8019, 19064, 114981]]]
  hmulB := by decide  
  f := ![![![-3251, -4709, -338, 1395, 9154]], ![![19162, 27071, 1490, -9300, -58108]], ![![7496, 10446, 523, -3744, -23084]], ![![6112, 8524, 403, -3117, -19104]], ![![9177, 12918, 681, -4523, -28093]]]
  g := ![![![6113, 7625, 885, -2019, -13134], ![-36450, -44815, -5392, 12990, 76416], ![-22112, -28486, -3041, 5980, 50148], ![243496, 300930, 35745, -84505, -515012], ![-54503, -67257, -8019, 19064, 114981]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 2 2 9 [159, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [286, 522], [0, 1]]
 g := ![![[337, 81], [312, 289], [16], [180, 290], [304], [312], [124], [208], [1]], ![[491, 442], [332, 234], [16], [486, 233], [304], [312], [124], [208], [1]]]
 h' := ![![[286, 522], [77, 514], [176, 506], [145, 4], [424, 381], [512, 345], [459, 151], [54, 443], [364, 286], [0, 1]], ![[0, 1], [118, 9], [21, 17], [243, 519], [83, 142], [335, 178], [236, 372], [186, 80], [49, 237], [286, 522]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [515, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 2
  hpos := by decide
  P := [159, 237, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4879167, -4897889, -284734, 1892729, 11372722]
  a := ![1838, 1754, 146, -722, -4303]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5724205, -6913502, -284734, 1892729, 11372722]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N0 B_one_repr
lemma NI523N0 : Nat.card (O ⧸ I523N0) = 273529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N0

def I523N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4497, 2508, 278, -972, -5632]] i)))

def SI523N1: IdealEqSpanCertificate' Table ![![4497, 2508, 278, -972, -5632]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![393, 8, 1, 0, 0], ![62, 422, 0, 1, 0], ![138, 371, 0, 0, 1]] where
  M :=![![![4497, 2508, 278, -972, -5632], ![7544, 4265, 470, -1644, -9512], ![13144, 7536, 859, -2932, -17008], ![4536, 2184, 246, -887, -5196], ![4748, 2736, 302, -1050, -6069]]]
  hmulB := by decide  
  f := ![![![1387, 2076, 122, -676, -4304]], ![![-5592, -9613, -574, 2972, 19320]], ![![1025, 1516, 89, -496, -3152]], ![![-4522, -7802, -466, 2409, 15668]], ![![-3570, -6221, -372, 1914, 12467]]]
  g := ![![![1401, 4780, 278, -972, -5632], ![2366, 8075, 470, -1644, -9512], ![4215, 14432, 859, -2932, -17008], ![1300, 4402, 246, -887, -5196], ![1508, 5153, 302, -1050, -6069]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P1 : CertificateIrreducibleZModOfList' 523 2 2 9 [296, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [349, 522], [0, 1]]
 g := ![![[96, 235], [183, 497], [122], [263, 151], [111], [64], [165], [465], [1]], ![[0, 288], [0, 26], [122], [139, 372], [111], [64], [165], [465], [1]]]
 h' := ![![[349, 522], [224, 374], [463, 180], [79, 301], [480, 257], [424, 57], [183, 515], [184, 132], [227, 349], [0, 1]], ![[0, 1], [0, 149], [0, 343], [5, 222], [217, 266], [443, 466], [6, 8], [228, 391], [169, 174], [349, 522]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [491]]
 b := ![[], [177, 507]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N1 : CertifiedPrimeIdeal' SI523N1 523 where
  n := 2
  hpos := by decide
  P := [296, 174, 1]
  hirr := P523P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1760863, -1699419, -101905, 670160, 4005652]
  a := ![1149, 1098, 95, -453, -2690]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1063178, -3383917, -101905, 670160, 4005652]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N1 : Ideal.IsPrime I523N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N1 B_one_repr
lemma NI523N1 : Nat.card (O ⧸ I523N1) = 273529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N1

def I523N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99, -18, -5, 11, 52]] i)))

def SI523N2: IdealEqSpanCertificate' Table ![![-99, -18, -5, 11, 52]] 
 ![![523, 0, 0, 0, 0], ![251, 1, 0, 0, 0], ![282, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![397, 0, 0, 0, 1]] where
  M :=![![![-99, -18, -5, 11, 52], ![-414, -425, -32, 144, 894], ![552, 1290, 65, -394, -2586], ![-2990, -4659, -279, 1483, 9518], ![342, 699, 37, -216, -1409]]]
  hmulB := by decide  
  f := ![![![2031, 1455, 22, -683, -3656]], ![![1001, 718, 12, -337, -1806]], ![![1222, 864, 17, -408, -2194]], ![![320, 213, 5, -103, -558]], ![![1529, 1098, 17, -515, -2757]]]
  g := ![![![-29, -18, -5, 11, 52], ![-467, -425, -32, 144, 894], ![1334, 1290, 65, -394, -2586], ![-4935, -4659, -279, 1483, 9518], ![728, 699, 37, -216, -1409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI523N2 : Nat.card (O ⧸ I523N2) = 523 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI523N2)

lemma isPrimeI523N2 : Ideal.IsPrime I523N2 := prime_ideal_of_norm_prime hp523.out _ NI523N2
def MulI523N0 : IdealMulLeCertificate' Table 
  ![![8627, 2840, 885, -2019, -13134]] ![![4497, 2508, 278, -972, -5632]]
  ![![334603, 74356, 30179, -67671, -452454]] where
 M := ![![![334603, 74356, 30179, -67671, -452454]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI523N1 : IdealMulLeCertificate' Table 
  ![![334603, 74356, 30179, -67671, -452454]] ![![-99, -18, -5, 11, 52]]
  ![![523, 0, 0, 0, 0]] where
 M := ![![![346749, 320599, 48639, -128658, -754166]]]
 hmul := by decide  
 g := ![![![![663, 613, 93, -246, -1442]]]]
 hle2 := by decide  


def PBC523 : ContainsPrimesAboveP 523 ![I523N0, I523N1, I523N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI523N0
    exact isPrimeI523N1
    exact isPrimeI523N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 523 (by decide) (𝕀 ⊙ MulI523N0 ⊙ MulI523N1)


lemma PB953I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB953I10 : PrimesBelowBoundCertificateInterval O 463 523 953 where
  m := 9
  g := ![2, 2, 3, 2, 3, 4, 2, 4, 3]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB953I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1]
    · exact ![I479N0, I479N1]
    · exact ![I487N0, I487N1, I487N2]
    · exact ![I491N0, I491N1]
    · exact ![I499N0, I499N1, I499N2]
    · exact ![I503N0, I503N1, I503N2, I503N3]
    · exact ![I509N0, I509N1]
    · exact ![I521N0, I521N1, I521N2, I521N3]
    · exact ![I523N0, I523N1, I523N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC467
    · exact PBC479
    · exact PBC487
    · exact PBC491
    · exact PBC499
    · exact PBC503
    · exact PBC509
    · exact PBC521
    · exact PBC523
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![101847563, 218089]
    · exact ![109902239, 229441]
    · exact ![115501303, 487, 487]
    · exact ![118370771, 241081]
    · exact ![124251499, 499, 499]
    · exact ![253009, 503, 503, 503]
    · exact ![67122964561, 509]
    · exact ![271441, 521, 521, 521]
    · exact ![273529, 273529, 523]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
      exact NI467N1
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
      exact NI487N2
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
      exact NI499N2
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
      exact NI503N2
      exact NI503N3
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
      exact NI509N1
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
      exact NI521N1
      exact NI521N2
      exact NI521N3
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
      exact NI523N1
      exact NI523N2
  β := ![I487N1, I487N2, I499N1, I499N2, I503N1, I503N2, I503N3, I509N1, I521N1, I521N2, I521N3, I523N2]
  Il := ![[], [], [I487N1, I487N2], [], [I499N1, I499N2], [I503N1, I503N2, I503N3], [I509N1], [I521N1, I521N2, I521N3], [I523N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
