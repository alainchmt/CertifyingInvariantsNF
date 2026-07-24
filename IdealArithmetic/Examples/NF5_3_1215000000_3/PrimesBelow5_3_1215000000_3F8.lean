
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1054, -602, -77, 75, 155]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![-1054, -602, -77, 75, 155]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![7, 107, 1, 0, 0], ![176, 335, 0, 1, 0], ![243, 311, 0, 0, 1]] where
  M :=![![![-1054, -602, -77, 75, 155], ![-1860, -1051, -132, 156, 300], ![-3600, -1848, -163, 336, 624], ![-2814, -1212, 54, 383, 522], ![-3831, -1842, -87, 495, 770]]]
  hmulB := by decide  
  f := ![![![2213696, -1346890, -193735, -162585, 346369]], ![![-4156428, 2528915, 363756, 305268, -650340]], ![![-1148332, 698685, 100498, 84339, -179675]], ![![-2746706, 1671191, 240382, 201731, -429766]], ![![-2041947, 1242391, 178704, 149970, -319495]]]
  g := ![![![-140, -179, -77, 75, 155], ![-276, -361, -132, 156, 300], ![-581, -793, -163, 336, 624], ![-538, -811, 54, 383, 522], ![-756, -1084, -87, 495, 770]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 2 2 8 [151, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [254, 366], [0, 1]]
 g := ![![[324, 175], [171, 52], [89, 234], [174, 240], [364], [355, 215], [142, 291], [1]], ![[0, 192], [167, 315], [71, 133], [212, 127], [364], [282, 152], [289, 76], [1]]]
 h' := ![![[254, 366], [236, 132], [140, 230], [150, 97], [248, 314], [344, 200], [211, 248], [216, 254], [0, 1]], ![[0, 1], [0, 235], [207, 137], [199, 270], [365, 53], [131, 167], [79, 119], [140, 113], [254, 366]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [231]]
 b := ![[], [195, 299]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where
  n := 2
  hpos := by decide
  P := [151, 113, 1]
  hirr := P367P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34268, -3638, 8617, 4569, 2391]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4032, -8719, 8617, 4569, 2391]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 134689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-487, -220, 18, 24, 28]] i)))

def SI367N1: IdealEqSpanCertificate' Table ![![-487, -220, 18, 24, 28]] 
 ![![367, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![194, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![257, 0, 0, 0, 1]] where
  M :=![![![-487, -220, 18, 24, 28], ![-336, -465, -156, 92, 96], ![-1152, -488, -265, -120, 368], ![-2040, -232, 690, 57, -288], ![204, -784, -546, 164, 265]]]
  hmulB := by decide  
  f := ![![![-552967945, 336445196, 48393654, 40612776, -86520836]], ![![-153870344, 93620143, 13466148, 11301020, -24075520]], ![![-297616334, 181080272, 26046251, 21858456, -46566920]], ![![-201342400, 122503816, 17620722, 14787609, -31503296]], ![![-390853619, 237809124, 34206024, 28706276, -61155411]]]
  g := ![![![23, -220, 18, 24, 28], ![112, -465, -156, 92, 96], ![62, -488, -265, -120, 368], ![-124, -232, 690, 57, -288], ![265, -784, -546, 164, 265]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI367N1 : Nat.card (O ⧸ I367N1) = 367 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI367N1)

lemma isPrimeI367N1 : Ideal.IsPrime I367N1 := prime_ideal_of_norm_prime hp367.out _ NI367N1

def I367N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52, 2, -15, -5, -3]] i)))

def SI367N2: IdealEqSpanCertificate' Table ![![52, 2, -15, -5, -3]] 
 ![![367, 0, 0, 0, 0], ![232, 1, 0, 0, 0], ![125, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![262, 0, 0, 0, 1]] where
  M :=![![![52, 2, -15, -5, -3], ![36, 39, 0, -36, -20], ![240, 52, 31, -40, -144], ![846, 64, -222, -95, -70], ![339, 198, 9, -175, -172]]]
  hmulB := by decide  
  f := ![![![-4837682, 2943330, 423363, 355303, -756913]], ![![-3033404, 1845575, 265464, 222788, -474612]], ![![-1694182, 1030770, 148264, 124429, -265075]], ![![-812378, 494264, 71094, 59665, -127106]], ![![-3485321, 2120530, 305013, 255979, -545320]]]
  g := ![![![7, 2, -15, -5, -3], ![-4, 39, 0, -36, -20], ![67, 52, 31, -40, -144], ![104, 64, -222, -95, -70], ![26, 198, 9, -175, -172]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI367N2 : Nat.card (O ⧸ I367N2) = 367 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI367N2)

lemma isPrimeI367N2 : Ideal.IsPrime I367N2 := prime_ideal_of_norm_prime hp367.out _ NI367N2

def I367N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -14, 18, 6, -12]] i)))

def SI367N3: IdealEqSpanCertificate' Table ![![-7, -14, 18, 6, -12]] 
 ![![367, 0, 0, 0, 0], ![291, 1, 0, 0, 0], ![96, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![333, 0, 0, 0, 1]] where
  M :=![![![-7, -14, 18, 6, -12], ![144, -7, -74, 12, 24], ![-288, 82, 65, -100, 48], ![-360, -34, 274, 107, -212], ![528, -62, -260, -16, 137]]]
  hmulB := by decide  
  f := ![![![-39337, -24038, -3886, 2066, 5324]], ![![-31365, -19169, -3100, 1646, 4244]], ![![-10560, -6466, -1051, 548, 1424]], ![![-1816, -1134, -194, 83, 236]], ![![-35883, -21956, -3562, 1870, 4845]]]
  g := ![![![17, -14, 18, 6, -12], ![3, -7, -74, 12, 24], ![-122, 82, 65, -100, 48], ![142, -34, 274, 107, -212], ![-5, -62, -260, -16, 137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI367N3 : Nat.card (O ⧸ I367N3) = 367 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI367N3)

lemma isPrimeI367N3 : Ideal.IsPrime I367N3 := prime_ideal_of_norm_prime hp367.out _ NI367N3
def MulI367N0 : IdealMulLeCertificate' Table 
  ![![-1054, -602, -77, 75, 155]] ![![-487, -220, 18, 24, 28]]
  ![![682894, 410466, 62465, -41745, -96165]] where
 M := ![![![682894, 410466, 62465, -41745, -96165]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI367N1 : IdealMulLeCertificate' Table 
  ![![682894, 410466, 62465, -41745, -96165]] ![![52, 2, -15, -5, -3]]
  ![![-2637341, -1090208, 94910, 104804, 209568]] where
 M := ![![![-2637341, -1090208, 94910, 104804, 209568]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI367N2 : IdealMulLeCertificate' Table 
  ![![-2637341, -1090208, 94910, 104804, 209568]] ![![-7, -14, 18, 6, -12]]
  ![![367, 0, 0, 0, 0]] where
 M := ![![![-92940181, 35780298, 13601020, -30536602, 16531148]]]
 hmul := by decide  
 g := ![![![![-253243, 97494, 37060, -83206, 45044]]]]
 hle2 := by decide  


def PBC367 : ContainsPrimesAboveP 367 ![I367N0, I367N1, I367N2, I367N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI367N0
    exact isPrimeI367N1
    exact isPrimeI367N2
    exact isPrimeI367N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 367 (by decide) (𝕀 ⊙ MulI367N0 ⊙ MulI367N1 ⊙ MulI367N2)
instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1667380, -978655, -140636, 107955, 241713]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![-1667380, -978655, -140636, 107955, 241713]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![0, 0, 373, 0, 0], ![0, 0, 0, 373, 0], ![158, 218, 247, 59, 1]] where
  M :=![![![-1667380, -978655, -140636, 107955, 241713], ![-2900556, -1674258, -227713, 202154, 431820], ![-5181840, -2898603, -351286, 408214, 808616], ![-3401418, -1729233, -126427, 356253, 600518], ![-5117613, -2688761, -242488, 491691, 868516]]]
  hmulB := by decide  
  f := ![![![146, 133, -218, -59, 137]], ![![-1644, 124, 799, -162, -236]], ![![2832, -919, -496, 1126, -648]], ![![4710, 219, -3281, -1063, 2370]], ![![1705, -443, -465, 458, -138]]]
  g := ![![![-106858, -143893, -160439, -37944, 241713], ![-190692, -256866, -286561, -67762, 431820], ![-356416, -480367, -536406, -126810, 808616], ![-263494, -355609, -398001, -94033, 600518], ![-381617, -514813, -575780, -136061, 868516]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 4 2 8 [207, 259, 217, 68, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 104, 348, 37], [365, 75, 139, 250], [239, 193, 259, 86], [0, 1]]
 g := ![![[333, 21, 181, 283], [218, 291, 83], [291, 222, 343, 108], [63, 311, 356], [135, 30, 188, 55], [288, 257, 202, 285], [305, 1], []], ![[101, 337, 137, 212, 134, 28], [47, 295, 109], [290, 84, 168, 144, 132, 122], [202, 268, 170], [225, 151, 68, 19, 232, 249], [197, 362, 315, 250, 43, 364], [272, 326, 105, 329, 87, 124], [122, 173, 250]], ![[5, 348, 312, 163, 204, 101], [254, 52, 22], [149, 326, 213, 249, 241, 119], [129, 277, 83], [124, 43, 368, 265, 195, 3], [358, 210, 299, 92, 211, 325], [99, 91, 201, 168, 329, 70], [161, 84, 209]], ![[207, 191, 336, 42, 194, 273], [145, 230, 27], [293, 46, 249, 64, 156, 366], [302, 137, 324], [337, 234, 297, 16, 298, 17], [333, 13, 187, 92, 277, 170], [230, 155, 234, 190, 87, 198], [122, 37, 309]]]
 h' := ![![[74, 104, 348, 37], [293, 59, 6, 220], [189, 151, 137, 249], [168, 79, 179, 333], [30, 221, 309, 27], [64, 54, 39, 146], [275, 247, 323, 304], [0, 0, 1], [0, 1]], ![[365, 75, 139, 250], [338, 238, 193, 216], [165, 243, 348, 286], [262, 273, 40, 31], [182, 343, 139, 115], [155, 218, 58, 356], [45, 327, 54, 75], [364, 203, 88, 97], [74, 104, 348, 37]], ![[239, 193, 259, 86], [230, 167, 319, 13], [31, 353, 294, 231], [122, 332, 77, 165], [84, 218, 116, 249], [288, 334, 278, 188], [236, 56, 187, 251], [307, 139, 52, 310], [365, 75, 139, 250]], ![[0, 1], [50, 282, 228, 297], [358, 372, 340, 353], [2, 62, 77, 217], [358, 337, 182, 355], [226, 140, 371, 56], [82, 116, 182, 116], [162, 31, 232, 339], [239, 193, 259, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [161, 76, 357], []]
 b := ![[], [], [156, 276, 254, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where
  n := 4
  hpos := by decide
  P := [207, 259, 217, 68, 1]
  hirr := P373P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32857475039466, -8611700249388, 3600862590795, 8157618525547, 9697688553574]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4195957819046, -5690905643240, -6412139973571, -1512080445403, 9697688553574]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 19356878641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-146, -133, 218, 59, -137]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![-146, -133, 218, 59, -137]] 
 ![![373, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![254, 0, 1, 0, 0], ![250, 0, 0, 1, 0], ![271, 0, 0, 0, 1]] where
  M :=![![![-146, -133, 218, 59, -137], ![1644, -124, -799, 162, 236], ![-2832, 919, 496, -1126, 648], ![-4710, -219, 3281, 1063, -2370], ![6105, -787, -2908, -67, 1446]]]
  hmulB := by decide  
  f := ![![![1667380, 978655, 140636, -107955, -241713]], ![![620192, 363941, 52265, -40193, -89937]], ![![1149320, 674201, 96710, -74608, -166766]], ![![1126666, 660571, 94599, -73311, -163616]], ![![1225141, 718242, 102828, -79752, -177943]]]
  g := ![![![-40, -133, 218, 59, -137], ![314, -124, -799, 162, 236], ![-399, 919, 496, -1126, 648], ![-1157, -219, 3281, 1063, -2370], ![1280, -787, -2908, -67, 1446]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N1 : Nat.card (O ⧸ I373N1) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N1)

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := prime_ideal_of_norm_prime hp373.out _ NI373N1
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![-1667380, -978655, -140636, 107955, 241713]] ![![-146, -133, 218, 59, -137]]
  ![![373, 0, 0, 0, 0]] where
 M := ![![![-373, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC373 : ContainsPrimesAboveP 373 ![I373N0, I373N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI373N0
    exact isPrimeI373N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 373 (by decide) (𝕀 ⊙ MulI373N0)
instance hp379 : Fact (Nat.Prime 379) := {out := by norm_num}

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4891, 3009, 423, 430, -826]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![-4891, 3009, 423, 430, -826]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![170, 45, 1, 0, 0], ![344, 210, 0, 1, 0], ![256, 304, 0, 0, 1]] where
  M :=![![![-4891, 3009, 423, 430, -826], ![9912, -5724, -1155, -806, 1720], ![-20640, 11283, 2768, 1130, -3224], ![14388, -8251, -1359, -53, 1400], ![-12042, 7831, 459, 384, -1235]]]
  hmulB := by decide  
  f := ![![![1149131, 686807, 104331, -68122, -161626]], ![![1939512, 1159958, 176547, -114590, -272488]], ![![754354, 450959, 68549, -44668, -106060]], ![![2122372, 1268929, 192957, -125593, -298336]], ![![2339450, 1398863, 212781, -138364, -328791]]]
  g := ![![![-35, 382, 423, 430, -826], ![114, -811, -1155, -806, 1720], ![-144, 1661, 2768, 1130, -3224], ![-250, -954, -1359, -53, 1400], ![248, 744, 459, 384, -1235]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 2 2 8 [150, 258, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 378], [0, 1]]
 g := ![![[123, 331], [269, 311], [211], [275, 94], [233, 341], [209, 45], [199, 239], [1]], ![[0, 48], [0, 68], [211], [279, 285], [183, 38], [348, 334], [314, 140], [1]]]
 h' := ![![[121, 378], [203, 346], [117, 93], [61, 127], [297, 241], [107, 290], [91, 117], [229, 121], [0, 1]], ![[0, 1], [0, 33], [0, 286], [268, 252], [275, 138], [329, 89], [225, 262], [89, 258], [121, 378]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [112, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where
  n := 2
  hpos := by decide
  P := [150, 258, 1]
  hirr := P379P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18182, -2162, 4926, 1596, -622]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3286, -976, 4926, 1596, -622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 143641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def I379N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1001, 184, 396, -92, -118]] i)))

def SI379N1: IdealEqSpanCertificate' Table ![![-1001, 184, 396, -92, -118]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![329, 110, 1, 0, 0], ![97, 179, 0, 1, 0], ![128, 273, 0, 0, 1]] where
  M :=![![![-1001, 184, 396, -92, -118], ![1416, -631, -104, 556, -368], ![4416, 388, -3215, -944, 2224], ![-14052, 2500, 5638, -1269, -1704], ![7674, -2176, -2078, 1634, -249]]]
  hmulB := by decide  
  f := ![![![6241, 744, -1232, -1896, -2086]], ![![25032, 4819, -3808, -6636, -7584]], ![![12923, 2098, -2207, -3632, -4082]], ![![13807, 2559, -2162, -3713, -4226]], ![![20606, 3833, -3218, -5534, -6301]]]
  g := ![![![-283, 14, 396, -92, -118], ![76, 31, -104, 556, -368], ![2293, -222, -3215, -944, 2224], ![-4031, 197, 5638, -1269, -1704], ![1490, 5, -2078, 1634, -249]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P1 : CertificateIrreducibleZModOfList' 379 2 2 8 [179, 294, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 378], [0, 1]]
 g := ![![[351, 36], [168, 266], [362], [64, 297], [1, 203], [239, 62], [35, 24], [1]], ![[0, 343], [38, 113], [362], [295, 82], [201, 176], [203, 317], [180, 355], [1]]]
 h' := ![![[85, 378], [248, 6], [206, 32], [293, 236], [200, 353], [46, 348], [178, 21], [200, 85], [0, 1]], ![[0, 1], [0, 373], [273, 347], [266, 143], [264, 26], [64, 31], [68, 358], [224, 294], [85, 378]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [333]]
 b := ![[], [30, 356]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N1 : CertifiedPrimeIdeal' SI379N1 379 where
  n := 2
  hpos := by decide
  P := [179, 294, 1]
  hirr := P379P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448545, -57676, 83833, 73209, 102648]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-127361, -132999, 83833, 73209, 102648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N1 : Ideal.IsPrime I379N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N1 B_one_repr
lemma NI379N1 : Nat.card (O ⧸ I379N1) = 143641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N1

def I379N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![116449, -70855, -10191, -8552, 18222]] i)))

def SI379N2: IdealEqSpanCertificate' Table ![![116449, -70855, -10191, -8552, 18222]] 
 ![![379, 0, 0, 0, 0], ![224, 1, 0, 0, 0], ![231, 0, 1, 0, 0], ![167, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![116449, -70855, -10191, -8552, 18222], ![-218664, 133032, 19137, 16062, -34208], ![410496, -249797, -35924, -30142, 64248], ![-276156, 167965, 24171, 20293, -43180], ![280122, -170505, -24513, -20560, 43865]]]
  hmulB := by decide  
  f := ![![![-2749625, -1642329, -249039, 163540, 387206]], ![![-1637368, -977986, -148299, 97386, 230576]], ![![-1696605, -1013370, -153665, 100910, 238918]], ![![-1222945, -730456, -110766, 72737, 172218]], ![![-779997, -465884, -70644, 46392, 109839]]]
  g := ![![![47116, -70855, -10191, -8552, 18222], ![-88467, 133032, 19137, 16062, -34208], ![166098, -249797, -35924, -30142, 64248], ![-111712, 167965, 24171, 20293, -43180], ![113360, -170505, -24513, -20560, 43865]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI379N2 : Nat.card (O ⧸ I379N2) = 379 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI379N2)

lemma isPrimeI379N2 : Ideal.IsPrime I379N2 := prime_ideal_of_norm_prime hp379.out _ NI379N2
def MulI379N0 : IdealMulLeCertificate' Table 
  ![![-4891, 3009, 423, 430, -826]] ![![-1001, 184, 396, -92, -118]]
  ![![-1356481, 237877, 531051, -171690, -116468]] where
 M := ![![![-1356481, 237877, 531051, -171690, -116468]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI379N1 : IdealMulLeCertificate' Table 
  ![![-1356481, 237877, 531051, -171690, -116468]] ![![116449, -70855, -10191, -8552, 18222]]
  ![![379, 0, 0, 0, 0]] where
 M := ![![![22806293543, -13875766838, -1996265010, -1675056446, 3568576830]]]
 hmul := by decide  
 g := ![![![![60174917, -36611522, -5267190, -4419674, 9415770]]]]
 hle2 := by decide  


def PBC379 : ContainsPrimesAboveP 379 ![I379N0, I379N1, I379N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI379N0
    exact isPrimeI379N1
    exact isPrimeI379N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 379 (by decide) (𝕀 ⊙ MulI379N0 ⊙ MulI379N1)
instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19439, 11612, 1762, -1156, -2738]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![19439, 11612, 1762, -1156, -2738]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![0, 0, 383, 0, 0], ![128, 360, 286, 1, 0], ![80, 41, 364, 0, 1]] where
  M :=![![![19439, 11612, 1762, -1156, -2738], ![32856, 19619, 2972, -1952, -4624], ![55488, 33156, 5027, -3304, -7808], ![30420, 18196, 2780, -1805, -4296], ![48846, 29160, 4412, -2898, -6865]]]
  hmulB := by decide  
  f := ![![![229, -140, -22, -16, 38]], ![![-456, 261, 44, 32, -64]], ![![768, -508, -59, -40, 128]], ![![220, -180, -10, -5, 48]], ![![730, -485, -56, -38, 123]]]
  g := ![![![1009, 1410, 3470, -1156, -2738], ![1704, 2381, 5860, -1952, -4624], ![2880, 4028, 9901, -3304, -7808], ![1580, 2204, 5438, -1805, -4296], ![2530, 3535, 8700, -2898, -6865]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P0 : CertificateIrreducibleZModOfList' 383 3 2 8 [13, 143, 204, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 212, 278], [43, 170, 105], [0, 1]]
 g := ![![[19, 189, 272], [81, 124, 243], [374, 151, 6], [186, 19, 63], [226, 79, 292], [320, 87, 75], [109, 179, 1], []], ![[365, 236, 72, 101], [284, 166, 81, 309], [93, 169, 249, 201], [351, 169, 309, 232], [298, 159, 144, 256], [228, 130, 148, 174], [85, 217, 352, 9], [167, 301]], ![[291, 356, 314, 89], [56, 374, 6, 30], [320, 365, 99, 297], [216, 302, 204, 253], [13, 181, 164, 197], [280, 368, 244, 120], [91, 373, 275, 177], [340, 301]]]
 h' := ![![[136, 212, 278], [96, 111, 80], [117, 319, 282], [263, 138, 48], [126, 104, 281], [53, 38, 296], [115, 87, 29], [0, 0, 1], [0, 1]], ![[43, 170, 105], [225, 232, 30], [212, 241, 274], [246, 339, 181], [233, 242, 82], [131, 361, 370], [111, 327, 8], [239, 379, 170], [136, 212, 278]], ![[0, 1], [264, 40, 273], [43, 206, 210], [370, 289, 154], [272, 37, 20], [160, 367, 100], [152, 352, 346], [110, 4, 212], [43, 170, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 167], []]
 b := ![[], [380, 302, 370], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N0 : CertifiedPrimeIdeal' SI383N0 383 where
  n := 3
  hpos := by decide
  P := [13, 143, 204, 1]
  hirr := P383P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10968719, 3406941, 6908279, -1927510, -4537904]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1563407, 2306435, 5770165, -1927510, -4537904]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N0 B_one_repr
lemma NI383N0 : Nat.card (O ⧸ I383N0) = 56181887 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N0

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-445, -251, -31, 34, 68]] i)))

def SI383N1: IdealEqSpanCertificate' Table ![![-445, -251, -31, 34, 68]] 
 ![![383, 0, 0, 0, 0], ![245, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![106, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-445, -251, -31, 34, 68], ![-816, -442, -47, 74, 136], ![-1632, -801, -46, 178, 296], ![-1368, -559, 37, 213, 288], ![-1884, -825, 7, 270, 395]]]
  hmulB := by decide  
  f := ![![![6851749, -4168841, -599643, -503226, 1072068]], ![![4349383, -2646315, -380644, -319440, 680532]], ![![1959374, -1192151, -171478, -143906, 306576]], ![![1853894, -1127973, -162247, -136159, 290072]], ![![704963, -428924, -61696, -51776, 110303]]]
  g := ![![![152, -251, -31, 34, 68], ![260, -442, -47, 74, 136], ![443, -801, -46, 178, 296], ![257, -559, 37, 213, 288], ![408, -825, 7, 270, 395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N1 : Nat.card (O ⧸ I383N1) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N1)

lemma isPrimeI383N1 : Ideal.IsPrime I383N1 := prime_ideal_of_norm_prime hp383.out _ NI383N1

def I383N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, -11, -4, -5, -1]] i)))

def SI383N2: IdealEqSpanCertificate' Table ![![-16, -11, -4, -5, -1]] 
 ![![383, 0, 0, 0, 0], ![332, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![342, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![-16, -11, -4, -5, -1], ![12, -16, -5, -10, -20], ![240, -3, -76, -50, -40], ![234, 95, -29, -111, -90], ![393, 51, -50, -87, -136]]]
  hmulB := by decide  
  f := ![![![-10172546, 6189331, 890262, 747123, -1591659]], ![![-8768108, 5334822, 767351, 643974, -1371912]], ![![-2218448, 1349781, 194150, 162934, -347112]], ![![-9020610, 5488453, 789449, 662519, -1411420]], ![![-2162161, 1315534, 189224, 158800, -338305]]]
  g := ![![![15, -11, -4, -5, -1], ![28, -16, -5, -10, -20], ![72, -3, -76, -50, -40], ![42, 95, -29, -111, -90], ![73, 51, -50, -87, -136]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N2 : Nat.card (O ⧸ I383N2) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N2)

lemma isPrimeI383N2 : Ideal.IsPrime I383N2 := prime_ideal_of_norm_prime hp383.out _ NI383N2
def MulI383N0 : IdealMulLeCertificate' Table 
  ![![19439, 11612, 1762, -1156, -2738]] ![![-445, -251, -31, 34, 68]]
  ![![-14261531, -8518001, -1291363, 848362, 2008198]] where
 M := ![![![-14261531, -8518001, -1291363, 848362, 2008198]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI383N1 : IdealMulLeCertificate' Table 
  ![![-14261531, -8518001, -1291363, 848362, 2008198]] ![![-16, -11, -4, -5, -1]]
  ![![383, 0, 0, 0, 0]] where
 M := ![![![803779886, 480051434, 72767319, -47825593, -113191437]]]
 hmul := by decide  
 g := ![![![![2098642, 1253398, 189993, -124871, -295539]]]]
 hle2 := by decide  


def PBC383 : ContainsPrimesAboveP 383 ![I383N0, I383N1, I383N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI383N0
    exact isPrimeI383N1
    exact isPrimeI383N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 383 (by decide) (𝕀 ⊙ MulI383N0 ⊙ MulI383N1)
instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![682, -446, -55, -43, 127]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![682, -446, -55, -43, 127]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![0, 0, 389, 0, 0], ![0, 0, 0, 389, 0], ![36, 70, 361, 162, 1]] where
  M :=![![![682, -446, -55, -43, 127], ![-1524, 797, 148, 144, -172], ![2064, -1692, -179, -48, 576], ![-2694, 856, 280, 325, -10], ![681, -1334, -11, 147, 570]]]
  hmulB := by decide  
  f := ![![![8, 6, 1, -1, -1]], ![![12, 9, 4, 0, -4]], ![![48, 12, -7, 0, 0]], ![![-6, 16, 4, -7, 2]], ![![45, 20, -4, -3, 0]]]
  g := ![![![-10, -24, -118, -53, 127], ![12, 33, 160, 72, -172], ![-48, -108, -535, -240, 576], ![-6, 4, 10, 5, -10], ![-51, -106, -529, -237, 570]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 4 2 8 [218, 232, 245, 179, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [319, 194, 167, 303], [352, 357, 112, 267], [317, 226, 110, 208], [0, 1]]
 g := ![![[243, 155, 291, 340], [99, 284, 296], [385, 183, 151, 304], [273, 20, 94], [137, 245, 111], [203, 32, 122], [287, 210, 1], []], ![[290, 246, 166, 243, 387, 35], [376, 278, 62], [179, 17, 108, 219, 163, 142], [51, 78, 73], [43, 267, 1], [328, 351, 354], [253, 185, 80], [144, 99, 105, 183, 119, 348]], ![[238, 93, 214, 20, 167, 9], [224, 79, 44], [158, 295, 260, 154, 124, 302], [30, 247, 113], [28, 140, 142], [148, 195, 164], [15, 229, 267], [381, 76, 136, 19, 102, 4]], ![[314, 111, 138, 105, 22, 248], [93, 148, 361], [312, 61, 337, 45, 104, 216], [266, 324, 315], [19, 182, 30], [374, 263, 175], [163, 89, 73], [326, 91, 42, 274, 226, 175]]]
 h' := ![![[319, 194, 167, 303], [91, 109, 85, 362], [94, 61, 44, 234], [72, 263, 207, 191], [153, 142, 266, 77], [171, 179, 42, 82], [63, 57, 170, 30], [0, 0, 0, 1], [0, 1]], ![[352, 357, 112, 267], [380, 152, 259, 309], [293, 145, 385, 134], [284, 155, 63, 348], [11, 27, 227, 292], [7, 343, 223, 1], [18, 348, 6, 350], [215, 289, 226, 45], [319, 194, 167, 303]], ![[317, 226, 110, 208], [244, 182, 382, 206], [134, 15, 221, 40], [342, 147, 332, 243], [293, 341, 72, 180], [259, 175, 97, 232], [364, 319, 15, 220], [105, 128, 303, 51], [352, 357, 112, 267]], ![[0, 1], [125, 335, 52, 290], [343, 168, 128, 370], [38, 213, 176, 385], [264, 268, 213, 229], [317, 81, 27, 74], [114, 54, 198, 178], [311, 361, 249, 292], [317, 226, 110, 208]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [237, 153, 263], []]
 b := ![[], [], [345, 282, 161, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where
  n := 4
  hpos := by decide
  P := [218, 232, 245, 179, 1]
  hirr := P389P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5879509846, 642768128, 2791143740, -159690876, -1164642392]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![92667394, 211228112, 1087987268, 484607652, -1164642392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 22898045041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def I389N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, -6, -1, 1, 1]] i)))

def SI389N1: IdealEqSpanCertificate' Table ![![-8, -6, -1, 1, 1]] 
 ![![389, 0, 0, 0, 0], ![130, 1, 0, 0, 0], ![216, 0, 1, 0, 0], ![288, 0, 0, 1, 0], ![311, 0, 0, 0, 1]] where
  M :=![![![-8, -6, -1, 1, 1], ![-12, -9, -4, 0, 4], ![-48, -12, 7, 0, 0], ![6, -16, -4, 7, -2], ![-21, -10, -7, -3, 8]]]
  hmulB := by decide  
  f := ![![![-682, 446, 55, 43, -127]], ![![-224, 147, 18, 14, -42]], ![![-384, 252, 31, 24, -72]], ![![-498, 328, 40, 31, -94]], ![![-547, 360, 44, 34, -103]]]
  g := ![![![1, -6, -1, 1, 1], ![2, -9, -4, 0, 4], ![0, -12, 7, 0, 0], ![4, -16, -4, 7, -2], ![3, -10, -7, -3, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N1 : Nat.card (O ⧸ I389N1) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N1)

lemma isPrimeI389N1 : Ideal.IsPrime I389N1 := prime_ideal_of_norm_prime hp389.out _ NI389N1
def MulI389N0 : IdealMulLeCertificate' Table 
  ![![682, -446, -55, -43, 127]] ![![-8, -6, -1, 1, 1]]
  ![![389, 0, 0, 0, 0]] where
 M := ![![![-389, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC389 : ContainsPrimesAboveP 389 ![I389N0, I389N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI389N0
    exact isPrimeI389N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 389 (by decide) (𝕀 ⊙ MulI389N0)
instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6125, 3752, 536, 446, -970]] i)))

def SI397N0: IdealEqSpanCertificate' Table ![![-6125, 3752, 536, 446, -970]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![238, 370, 1, 0, 0], ![37, 152, 0, 1, 0], ![206, 29, 0, 0, 1]] where
  M :=![![![-6125, 3752, 536, 446, -970], ![11640, -7005, -1020, -868, 1784], ![-21408, 13272, 1867, 1528, -3472], ![15012, -8768, -1326, -1171, 2164], ![-14286, 9140, 1236, 966, -2461]]]
  hmulB := by decide  
  f := ![![![-965, 128, 484, -14, -222]], ![![2664, -689, -732, 524, -56]], ![![1906, -562, -397, 476, -180]], ![![895, -248, -218, 199, -50]], ![![-280, 11, 188, 34, -117]]]
  g := ![![![125, -590, 536, 446, -970], ![-204, 1135, -1020, -868, 1784], ![486, -2038, 1867, 1528, -3472], ![-181, 1504, -1326, -1171, 2164], ![410, -1319, 1236, 966, -2461]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P0 : CertificateIrreducibleZModOfList' 397 2 2 8 [152, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [343, 396], [0, 1]]
 g := ![![[319, 14], [268], [128, 253], [150, 4], [179], [73], [225], [343, 1]], ![[357, 383], [268], [361, 144], [331, 393], [179], [73], [225], [289, 396]]]
 h' := ![![[343, 396], [164, 111], [394, 150], [226, 359], [290, 2], [361, 373], [306, 57], [268, 382], [0, 1]], ![[0, 1], [125, 286], [234, 247], [293, 38], [182, 395], [69, 24], [7, 340], [284, 15], [343, 396]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [387, 279]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N0 : CertifiedPrimeIdeal' SI397N0 397 where
  n := 2
  hpos := by decide
  P := [152, 54, 1]
  hirr := P397P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33540, -3386, 12044, 5185, -1432]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7045, -13114, 12044, 5185, -1432]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N0 : Ideal.IsPrime I397N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N0 B_one_repr
lemma NI397N0 : Nat.card (O ⧸ I397N0) = 157609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N0

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2297, -1568, -54, -164, 304]] i)))

def SI397N1: IdealEqSpanCertificate' Table ![![2297, -1568, -54, -164, 304]] 
 ![![397, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![126, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![361, 0, 0, 0, 1]] where
  M :=![![![2297, -1568, -54, -164, 304], ![-3648, 2711, -24, 500, -656], ![7872, -4828, -913, -1360, 2000], ![-10176, 3804, 2958, 837, -2392], ![10200, -4348, -2322, -272, 1673]]]
  hmulB := by decide  
  f := ![![![11338805, 6788408, 1036362, -666332, -1590192]], ![![1818862, 1088999, 166284, -106852, -255056]], ![![3679278, 2203084, 336491, -216040, -515856]], ![![985449, 590620, 90456, -57583, -137944]], ![![10380185, 6215252, 949200, -609612, -1455447]]]
  g := ![![![5, -1568, -54, -164, 304], ![130, 2711, -24, 500, -656], ![-642, -4828, -913, -1360, 2000], ![547, 3804, 2958, 837, -2392], ![-57, -4348, -2322, -272, 1673]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N1 : Nat.card (O ⧸ I397N1) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N1)

lemma isPrimeI397N1 : Ideal.IsPrime I397N1 := prime_ideal_of_norm_prime hp397.out _ NI397N1

def I397N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1141492, 694524, 99899, 83837, -178605]] i)))

def SI397N2: IdealEqSpanCertificate' Table ![![-1141492, 694524, 99899, 83837, -178605]] 
 ![![397, 0, 0, 0, 0], ![142, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![388, 0, 0, 1, 0], ![198, 0, 0, 0, 1]] where
  M :=![![![-1141492, 694524, 99899, 83837, -178605], ![2143260, -1304035, -187570, -157412, 335348], ![-4024176, 2448450, 352181, 295556, -629648], ![2706258, -1646582, -236842, -198761, 423438], ![-2746587, 1671120, 240371, 201723, -429748]]]
  hmulB := by decide  
  f := ![![![422, -1604, -1041, -941, -829]], ![![176, -575, -380, -346, -306]], ![![202, -318, -238, -231, -211]], ![![626, -1522, -1046, -973, -874]], ![![465, -748, -557, -535, -488]]]
  g := ![![![-265039, 694524, 99899, 83837, -178605], ![497636, -1304035, -187570, -157412, 335348], ![-934359, 2448450, 352181, 295556, -629648], ![628356, -1646582, -236842, -198761, 423438], ![-637720, 1671120, 240371, 201723, -429748]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N2 : Nat.card (O ⧸ I397N2) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N2)

lemma isPrimeI397N2 : Ideal.IsPrime I397N2 := prime_ideal_of_norm_prime hp397.out _ NI397N2

def I397N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, -2, -2, -2]] i)))

def SI397N3: IdealEqSpanCertificate' Table ![![1, -2, -2, -2, -2]] 
 ![![397, 0, 0, 0, 0], ![220, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![221, 0, 0, 0, 1]] where
  M :=![![![1, -2, -2, -2, -2], ![24, -1, -6, -8, -8], ![96, 18, -17, -28, -32], ![180, 38, -24, -45, -52], ![210, 46, -30, -54, -63]]]
  hmulB := by decide  
  f := ![![![97, 34, -106, -14, 58]], ![![52, 19, -58, -8, 32]], ![![10, 2, -9, 0, 4]], ![![36, 10, -36, -5, 20]], ![![47, 20, -56, -8, 31]]]
  g := ![![![3, -2, -2, -2, -2], ![8, -1, -6, -8, -8], ![18, 18, -17, -28, -32], ![24, 38, -24, -45, -52], ![29, 46, -30, -54, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N3 : Nat.card (O ⧸ I397N3) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N3)

lemma isPrimeI397N3 : Ideal.IsPrime I397N3 := prime_ideal_of_norm_prime hp397.out _ NI397N3
def MulI397N0 : IdealMulLeCertificate' Table 
  ![![-6125, 3752, 536, 446, -970]] ![![2297, -1568, -54, -164, 304]]
  ![![-37969525, 23102008, 3322942, 2788682, -5940954]] where
 M := ![![![-37969525, 23102008, 3322942, 2788682, -5940954]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI397N1 : IdealMulLeCertificate' Table 
  ![![-37969525, 23102008, 3322942, 2788682, -5940954]] ![![-1141492, 694524, 99899, 83837, -178605]]
  ![![103347655247542, -62880356676884, -9044594258211, -7590377191713, 16170422435301]] where
 M := ![![![103347655247542, -62880356676884, -9044594258211, -7590377191713, 16170422435301]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI397N2 : IdealMulLeCertificate' Table 
  ![![103347655247542, -62880356676884, -9044594258211, -7590377191713, 16170422435301]] ![![1, -2, -2, -2, -2]]
  ![![397, 0, 0, 0, 0]] where
 M := ![![![-244541136881060, 148787448272754, 21401311497889, 17960344270727, -38262440272147]]]
 hmul := by decide  
 g := ![![![![-615972636980, 374779466682, 53907585637, 45240161891, -96378942751]]]]
 hle2 := by decide  


def PBC397 : ContainsPrimesAboveP 397 ![I397N0, I397N1, I397N2, I397N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI397N0
    exact isPrimeI397N1
    exact isPrimeI397N2
    exact isPrimeI397N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 397 (by decide) (𝕀 ⊙ MulI397N0 ⊙ MulI397N1 ⊙ MulI397N2)
instance hp401 : Fact (Nat.Prime 401) := {out := by norm_num}

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11165, -2053, 1761, 3014, 3428]] i)))

def SI401N0: IdealEqSpanCertificate' Table ![![-11165, -2053, 1761, 3014, 3428]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![0, 0, 401, 0, 0], ![350, 233, 152, 1, 0], ![267, 362, 235, 0, 1]] where
  M :=![![![-11165, -2053, 1761, 3014, 3428], ![-41136, -8990, 5631, 10378, 12056], ![-144672, -33827, 18478, 35374, 41512], ![-228504, -55533, 27921, 54801, 64720], ![-276780, -66827, 34083, 66602, 78571]]]
  hmulB := by decide  
  f := ![![![491, -241, -81, -2, 60]], ![![-720, 472, 3, -42, -8]], ![![96, -683, 524, -10, -168]], ![![50, -195, 128, -29, -16]], ![![-267, -135, 256, -46, -65]]]
  g := ![![![-4941, -4851, -3147, 3014, 3428], ![-17188, -16936, -10985, 10378, 12056], ![-58876, -58113, -37690, 35374, 41512], ![-91494, -90406, -58631, 54801, 64720], ![-111137, -109795, -71206, 66602, 78571]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P0 : CertificateIrreducibleZModOfList' 401 3 2 8 [279, 37, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [189, 373, 43], [143, 27, 358], [0, 1]]
 g := ![![[64, 96, 80], [360, 73], [201, 195], [396, 144], [210, 11, 146], [299, 169], [204, 350], [1]], ![[21, 145, 11, 160], [54, 172], [300, 303], [256, 32], [326, 135, 309, 164], [6, 145], [179, 366], [328, 364, 370, 109]], ![[173, 249, 373, 224], [21, 69], [96, 345], [171, 301], [155, 181, 75, 345], [60, 14], [360, 178], [218, 315, 98, 292]]]
 h' := ![![[189, 373, 43], [109, 49, 311], [353, 83, 262], [123, 299, 51], [357, 171, 389], [103, 124, 149], [73, 59, 13], [122, 364, 332], [0, 1]], ![[143, 27, 358], [395, 315, 78], [285, 179, 217], [300, 149, 199], [335, 142, 212], [13, 209, 132], [379, 292, 81], [350, 311, 155], [189, 373, 43]], ![[0, 1], [73, 37, 12], [39, 139, 323], [208, 354, 151], [105, 88, 201], [280, 68, 120], [86, 50, 307], [245, 127, 315], [143, 27, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [399, 309], []]
 b := ![[], [56, 253, 170], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N0 : CertifiedPrimeIdeal' SI401N0 401 where
  n := 3
  hpos := by decide
  P := [279, 37, 69, 1]
  hirr := P401P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76030, -15644, -29090, -690, 15023]
  a := ![-1, -4, -2, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9211, -13200, -8615, -690, 15023]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N0 : Ideal.IsPrime I401N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N0 B_one_repr
lemma NI401N0 : Nat.card (O ⧸ I401N0) = 64481201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N0

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-491, 241, 81, 2, -60]] i)))

def SI401N1: IdealEqSpanCertificate' Table ![![-491, 241, 81, 2, -60]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![117, 97, 1, 0, 0], ![140, 367, 0, 1, 0], ![251, 206, 0, 0, 1]] where
  M :=![![![-491, 241, 81, 2, -60], ![720, -472, -3, 42, 8], ![-96, 683, -524, 10, 168], ![-1368, 5, 669, -377, 16], ![84, 147, -57, 358, -291]]]
  hmulB := by decide  
  f := ![![![11165, 2053, -1761, -3014, -3428]], ![![41136, 8990, -5631, -10378, -12056]], ![![13569, 2858, -1922, -3478, -4020]], ![![42116, 9083, -5838, -10687, -12392]], ![![28811, 6070, -4080, -7384, -8535]]]
  g := ![![![12, 10, 81, 2, -60], ![-17, -43, -3, 42, 8], ![44, 33, -524, 10, 168], ![-77, 175, 669, -377, 16], ![74, -164, -57, 358, -291]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P1 : CertificateIrreducibleZModOfList' 401 2 2 8 [209, 171, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [230, 400], [0, 1]]
 g := ![![[256, 321], [47], [64], [70], [51, 138], [315], [337], [230, 1]], ![[302, 80], [47], [64], [70], [112, 263], [315], [337], [59, 400]]]
 h' := ![![[230, 400], [157, 205], [254, 122], [361, 393], [168, 291], [359, 277], [237, 77], [50, 160], [0, 1]], ![[0, 1], [390, 196], [244, 279], [125, 8], [131, 110], [310, 124], [303, 324], [359, 241], [230, 400]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [316]]
 b := ![[], [276, 158]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N1 : CertifiedPrimeIdeal' SI401N1 401 where
  n := 2
  hpos := by decide
  P := [209, 171, 1]
  hirr := P401P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75961, -12179, 20109, 11906, 12456]
  a := ![3, -11, -14, -1, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18010, -22190, 20109, 11906, 12456]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N1 : Ideal.IsPrime I401N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N1 B_one_repr
lemma NI401N1 : Nat.card (O ⧸ I401N1) = 160801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N1
def MulI401N0 : IdealMulLeCertificate' Table 
  ![![-11165, -2053, 1761, 3014, 3428]] ![![-491, 241, 81, 2, -60]]
  ![![401, 0, 0, 0, 0]] where
 M := ![![![-401, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC401 : ContainsPrimesAboveP 401 ![I401N0, I401N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI401N0
    exact isPrimeI401N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 401 (by decide) (𝕀 ⊙ MulI401N0)
instance hp409 : Fact (Nat.Prime 409) := {out := by norm_num}

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 0, 0, 0, 0]] i)))

def SI409N0: IdealEqSpanCertificate' Table ![![409, 0, 0, 0, 0]] 
 ![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![0, 0, 409, 0, 0], ![0, 0, 0, 409, 0], ![0, 0, 0, 0, 409]] where
  M :=![![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![0, 0, 409, 0, 0], ![0, 0, 0, 409, 0], ![0, 0, 0, 0, 409]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P409P0 : CertificateIrreducibleZModOfList' 409 5 2 8 [298, 253, 379, 33, 364, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [273, 87, 113, 127, 51], [280, 249, 203, 178, 309], [228, 372, 1, 30, 90], [82, 109, 92, 74, 368], [0, 1]]
 g := ![![[113, 74, 404, 34, 205], [141, 304, 180, 167], [17, 73, 325, 41], [90, 350, 138, 13, 136], [384, 223, 152, 62, 401], [267, 352, 61, 355], [45, 1], []], ![[217, 29, 365, 252, 112, 292, 47, 49], [215, 81, 366, 138], [110, 225, 93, 276], [26, 22, 49, 22, 123, 82, 140, 150], [323, 360, 145, 144, 70, 102, 304, 135], [314, 149, 312, 369], [42, 350, 351, 200], [204, 203, 341, 305, 63, 30, 323, 135]], ![[400, 16, 298, 359, 258, 231, 79, 382], [44, 329, 308, 334], [181, 17, 392, 384], [143, 282, 362, 316, 402, 153, 389, 92], [256, 144, 293, 149, 367, 386, 117, 338], [30, 188, 232, 1], [311, 17, 125, 212], [403, 406, 181, 101, 403, 324, 321, 5]], ![[26, 121, 390, 121, 205, 25, 10, 243], [314, 13, 295, 8], [382, 94, 312, 192], [11, 43, 183, 325, 246, 18, 399, 40], [1, 354, 213, 149, 336, 170, 126, 197], [163, 363, 110, 318], [118, 357, 400, 160], [123, 157, 353, 164, 368, 154, 90, 162]], ![[165, 106, 324, 366, 31, 135, 294, 20], [113, 70, 349, 301], [273, 275, 8, 270], [6, 48, 334, 302, 317, 184, 304, 2], [179, 402, 122, 68, 387, 407, 208, 15], [191, 185, 228, 182], [151, 175, 28, 153], [103, 377, 121, 311, 170, 318, 176, 200]]]
 h' := ![![[273, 87, 113, 127, 51], [336, 277, 39, 158, 156], [261, 34, 214, 25, 385], [174, 102, 283, 276, 181], [88, 163, 407, 138, 172], [396, 39, 229, 301, 70], [87, 178, 279, 181, 356], [0, 0, 0, 1], [0, 1]], ![[280, 249, 203, 178, 309], [161, 406, 192, 92, 81], [118, 52, 180, 17, 189], [282, 90, 128, 366, 72], [116, 166, 188, 18, 95], [360, 153, 174, 337, 51], [376, 284, 318, 307, 134], [43, 398, 355, 59, 152], [273, 87, 113, 127, 51]], ![[228, 372, 1, 30, 90], [0, 1, 134, 207, 214], [281, 211, 86, 198, 283], [244, 341, 123, 57, 103], [383, 8, 137, 142, 234], [399, 287, 21, 178, 250], [147, 241, 227, 111, 408], [304, 48, 394, 303, 301], [280, 249, 203, 178, 309]], ![[82, 109, 92, 74, 368], [293, 246, 5, 295, 17], [222, 249, 16, 81, 194], [360, 399, 120, 109, 292], [386, 196, 362, 72, 272], [241, 143, 357, 164, 86], [12, 301, 189, 332, 225], [97, 162, 198, 66, 122], [228, 372, 1, 30, 90]], ![[0, 1], [181, 297, 39, 66, 350], [114, 272, 322, 88, 176], [167, 295, 164, 10, 170], [116, 285, 133, 39, 45], [366, 196, 37, 247, 361], [281, 223, 214, 296, 104], [17, 210, 280, 389, 243], [82, 109, 92, 74, 368]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [191, 93, 175, 318], [], [], []]
 b := ![[], [211, 70, 361, 37, 90], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N0 : CertifiedPrimeIdeal' SI409N0 409 where
  n := 5
  hpos := by decide
  P := [298, 253, 379, 33, 364, 1]
  hirr := P409P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-719745086233, -112611127470, 119549416967, 118012693537, 152778071453]
  a := ![1, -6, -8, -2, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1759767937, -275332830, 292296863, 288539593, 373540517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI409N0 : Ideal.IsPrime I409N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI409N0 B_one_repr
lemma NI409N0 : Nat.card (O ⧸ I409N0) = 11445019581049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI409N0

def PBC409 : ContainsPrimesAboveP 409 ![I409N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI409N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![409, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 409 (by decide) 𝕀

instance hp419 : Fact (Nat.Prime 419) := {out := by norm_num}

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![886247, 529860, 80578, -52438, -124566]] i)))

def SI419N0: IdealEqSpanCertificate' Table ![![886247, 529860, 80578, -52438, -124566]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![0, 0, 419, 0, 0], ![0, 0, 0, 419, 0], ![54, 199, 343, 256, 1]] where
  M :=![![![886247, 529860, 80578, -52438, -124566], ![1494792, 894697, 136472, -87976, -209752], ![2517024, 1509488, 231641, -146560, -351904], ![1364028, 824312, 129260, -76275, -188244], ![2196942, 1323748, 205910, -124766, -304665]]]
  hmulB := by decide  
  f := ![![![-551, 100, 218, -54, -62]], ![![744, -341, -40, 312, -216]], ![![2592, 176, -1829, -512, 1248]], ![![-7860, 1432, 3116, -737, -916]], ![![-2388, 867, 413, -726, 351]]]
  g := ![![![18169, 60426, 102164, 75982, -124566], ![30600, 101755, 172032, 127944, -209752], ![51360, 170736, 288627, 214656, -351904], ![27516, 91372, 154408, 114831, -188244], ![44508, 147857, 249895, 185846, -304665]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P0 : CertificateIrreducibleZModOfList' 419 4 2 8 [221, 347, 11, 311, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 120, 18, 345], [323, 252, 295, 107], [113, 46, 106, 386], [0, 1]]
 g := ![![[320, 309, 311, 388], [310, 386, 70, 141], [31, 209, 264], [389, 199, 108], [275, 179, 134], [314, 69, 368, 121], [340, 108, 1], []], ![[226, 56, 308, 163, 242, 364], [339, 47, 273, 175, 375, 348], [205, 359, 203], [156, 75, 348], [239, 32, 333], [81, 111, 135, 383, 223, 80], [356, 397, 202], [339, 179, 33, 215, 248, 368]], ![[125, 319, 408, 211, 63, 196], [163, 9, 75, 62, 331, 107], [0, 290, 318], [398, 253, 36], [231, 319, 318], [205, 162, 400, 399, 165, 243], [245, 56, 110], [184, 177, 267, 408, 54, 306]], ![[29, 232, 304, 224, 388, 116], [44, 4, 10, 11, 347, 269], [69, 97, 289], [24, 205, 166], [249, 20, 117], [358, 215, 249, 383, 275, 28], [300, 347, 166], [302, 396, 298, 78, 209, 97]]]
 h' := ![![[91, 120, 18, 345], [206, 37, 156, 236], [43, 210, 92, 159], [367, 369, 83, 39], [21, 409, 169, 245], [160, 283, 193, 103], [280, 193, 44, 408], [0, 0, 0, 1], [0, 1]], ![[323, 252, 295, 107], [184, 274, 277, 118], [92, 206, 186, 61], [101, 161, 316, 363], [122, 366, 192, 102], [203, 397, 138, 137], [139, 414, 409, 57], [291, 327, 14, 88], [91, 120, 18, 345]], ![[113, 46, 106, 386], [197, 4, 228, 149], [59, 191, 46, 418], [267, 344, 177, 34], [167, 114, 151, 6], [409, 213, 334, 385], [236, 165, 284, 174], [171, 273, 2, 396], [323, 252, 295, 107]], ![[0, 1], [155, 104, 177, 335], [406, 231, 95, 200], [350, 383, 262, 402], [292, 368, 326, 66], [348, 364, 173, 213], [43, 66, 101, 199], [159, 238, 403, 353], [113, 46, 106, 386]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [270, 137, 252], []]
 b := ![[], [], [172, 340, 276, 307], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N0 : CertifiedPrimeIdeal' SI419N0 419 where
  n := 4
  hpos := by decide
  P := [221, 347, 11, 311, 1]
  hirr := P419P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17027931, 6951084, 10911524, -4165978, -7699532]
  a := ![4, 2, 2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![951663, 3673408, 6329000, 4694306, -7699532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N0 : Ideal.IsPrime I419N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N0 B_one_repr
lemma NI419N0 : Nat.card (O ⧸ I419N0) = 30821664721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N0

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![551, -100, -218, 54, 62]] i)))

def SI419N1: IdealEqSpanCertificate' Table ![![551, -100, -218, 54, 62]] 
 ![![419, 0, 0, 0, 0], ![233, 1, 0, 0, 0], ![181, 0, 1, 0, 0], ![166, 0, 0, 1, 0], ![221, 0, 0, 0, 1]] where
  M :=![![![551, -100, -218, 54, 62], ![-744, 341, 40, -312, 216], ![-2592, -176, 1829, 512, -1248], ![7860, -1432, -3116, 737, 916], ![-4230, 1228, 1114, -922, 167]]]
  hmulB := by decide  
  f := ![![![-886247, -529860, -80578, 52438, 124566]], ![![-496397, -296783, -45134, 29370, 69770]], ![![-388849, -232492, -35361, 23002, 54650]], ![![-354370, -211888, -32232, 20957, 49800]], ![![-472691, -282632, -42992, 27956, 66429]]]
  g := ![![![97, -100, -218, 54, 62], ![-199, 341, 40, -312, 216], ![-243, -176, 1829, 512, -1248], ![1386, -1432, -3116, 737, 916], ![-897, 1228, 1114, -922, 167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI419N1 : Nat.card (O ⧸ I419N1) = 419 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI419N1)

lemma isPrimeI419N1 : Ideal.IsPrime I419N1 := prime_ideal_of_norm_prime hp419.out _ NI419N1
def MulI419N0 : IdealMulLeCertificate' Table 
  ![![886247, 529860, 80578, -52438, -124566]] ![![551, -100, -218, 54, 62]]
  ![![419, 0, 0, 0, 0]] where
 M := ![![![-419, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC419 : ContainsPrimesAboveP 419 ![I419N0, I419N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI419N0
    exact isPrimeI419N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 419 (by decide) (𝕀 ⊙ MulI419N0)


lemma PB1705I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)

def PB1705I8 : PrimesBelowBoundCertificateInterval O 359 419 1705 where
  m := 9
  g := ![4, 2, 3, 3, 2, 4, 2, 1, 2]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB1705I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0, I367N1, I367N2, I367N3]
    · exact ![I373N0, I373N1]
    · exact ![I379N0, I379N1, I379N2]
    · exact ![I383N0, I383N1, I383N2]
    · exact ![I389N0, I389N1]
    · exact ![I397N0, I397N1, I397N2, I397N3]
    · exact ![I401N0, I401N1]
    · exact ![I409N0]
    · exact ![I419N0, I419N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC367
    · exact PBC373
    · exact PBC379
    · exact PBC383
    · exact PBC389
    · exact PBC397
    · exact PBC401
    · exact PBC409
    · exact PBC419
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![134689, 367, 367, 367]
    · exact ![19356878641, 373]
    · exact ![143641, 143641, 379]
    · exact ![56181887, 383, 383]
    · exact ![22898045041, 389]
    · exact ![157609, 397, 397, 397]
    · exact ![64481201, 160801]
    · exact ![11445019581049]
    · exact ![30821664721, 419]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
      exact NI367N1
      exact NI367N2
      exact NI367N3
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
      exact NI379N1
      exact NI379N2
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
      exact NI383N2
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
      exact NI389N1
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
      exact NI397N2
      exact NI397N3
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
      exact NI401N1
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
  β := ![I367N1, I367N2, I367N3, I373N1, I379N2, I383N1, I383N2, I389N1, I397N1, I397N2, I397N3, I419N1]
  Il := ![[I367N1, I367N2, I367N3], [I373N1], [I379N2], [I383N1, I383N2], [I389N1], [I397N1, I397N2, I397N3], [], [], [I419N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
