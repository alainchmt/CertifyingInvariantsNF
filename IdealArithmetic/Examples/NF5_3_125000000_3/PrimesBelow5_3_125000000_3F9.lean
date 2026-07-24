
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 13, 44, 21, 63]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![-8, 13, 44, 21, 63]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![405, 74, 97, 1, 0], ![199, 29, 376, 0, 1]] where
  M :=![![![-8, 13, 44, 21, 63], ![-252, -111, 328, 172, 588], ![-1776, -840, 1965, 1056, 3664], ![-5218, -2554, 5600, 2999, 10522], ![1481, 721, -1596, -857, -3000]]]
  hmulB := by decide  
  f := ![![![-22, 29, -12, -9, -41]], ![![52, -27, -8, -4, -28]], ![![-16, 8, 25, 32, 144]], ![![-16, 25, -7, -2, -11]], ![![-21, 19, 16, 24, 107]]]
  g := ![![![-50, -8, -61, 21, 63], ![-444, -71, -564, 172, 588], ![-2752, -440, -3511, 1056, 3664], ![-7871, -1258, -10075, 2999, 10522], ![2246, 359, 2873, -857, -3000]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 3 2 8 [17, 337, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 14, 274], [332, 406, 147], [0, 1]]
 g := ![![[371, 252, 401], [1, 106], [97, 320, 74], [354, 309], [343, 75], [50, 72, 220], [146, 246], [1]], ![[364, 395, 97, 79], [378, 241], [183, 139, 195, 49], [92, 289], [275, 337], [281, 124, 393, 118], [266, 26], [58, 114, 326, 343]], ![[96, 288, 247, 315], [294, 404], [220, 389, 252, 377], [57, 191], [310, 282], [348, 89, 348, 79], [204, 254], [155, 45, 102, 78]]]
 h' := ![![[8, 14, 274], [366, 138, 233], [35, 231, 384], [7, 232, 186], [127, 420, 149], [413, 195, 51], [333, 174, 124], [404, 84, 340], [0, 1]], ![[332, 406, 147], [123, 276, 216], [281, 400, 278], [74, 336, 154], [96, 134, 17], [267, 71, 40], [392, 214, 348], [368, 149, 234], [8, 14, 274]], ![[0, 1], [9, 7, 393], [282, 211, 180], [54, 274, 81], [38, 288, 255], [405, 155, 330], [47, 33, 370], [97, 188, 268], [332, 406, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [411, 387], []]
 b := ![[], [74, 268, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 3
  hpos := by decide
  P := [17, 337, 81, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2361901680, 1198087576, -2564738124, -1370166900, -4850024132]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3616233488, 577769924, 4641212648, -1370166900, -4850024132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 74618461 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def I421N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 26, -26, -10, -62]] i)))

def SI421N1: IdealEqSpanCertificate' Table ![![-3, 26, -26, -10, -62]] 
 ![![421, 0, 0, 0, 0], ![249, 1, 0, 0, 0], ![307, 0, 1, 0, 0], ![386, 0, 0, 1, 0], ![382, 0, 0, 0, 1]] where
  M :=![![![-3, 26, -26, -10, -62], ![-8, -87, 100, 36, 232], ![64, 336, -415, -152, -976], ![-124, -640, 798, 303, 1916], ![-2, -4, 4, -2, -3]]]
  hmulB := by decide  
  f := ![![![-2355, -1738, 598, 442, 2006]], ![![-1399, -1033, 354, 262, 1190]], ![![-1717, -1270, 427, 318, 1450]], ![![-2130, -1580, 514, 387, 1776]], ![![-2144, -1580, 552, 406, 1837]]]
  g := ![![![69, 26, -26, -10, -62], ![-265, -87, 100, 36, 232], ![1129, 336, -415, -152, -976], ![-2220, -640, 798, 303, 1916], ![4, -4, 4, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N1 : Nat.card (O ⧸ I421N1) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N1)

lemma isPrimeI421N1 : Ideal.IsPrime I421N1 := prime_ideal_of_norm_prime hp421.out _ NI421N1

def I421N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, 23, -10, -7, -31]] i)))

def SI421N2: IdealEqSpanCertificate' Table ![![28, 23, -10, -7, -31]] 
 ![![421, 0, 0, 0, 0], ![399, 1, 0, 0, 0], ![358, 0, 1, 0, 0], ![160, 0, 0, 1, 0], ![225, 0, 0, 0, 1]] where
  M :=![![![28, 23, -10, -7, -31], ![44, 27, -12, -8, -36], ![48, 40, -9, -8, -32], ![10, 18, -6, -5, -30], ![-5, -9, 0, 1, 4]]]
  hmulB := by decide  
  f := ![![![-6, 247, -258, -97, -615]], ![![-6, 232, -242, -91, -577]], ![![-4, 218, -229, -86, -546]], ![![-6, 78, -78, -29, -186]], ![![-3, 132, -138, -52, -329]]]
  g := ![![![6, 23, -10, -7, -31], ![7, 27, -12, -8, -36], ![-10, 40, -9, -8, -32], ![6, 18, -6, -5, -30], ![6, -9, 0, 1, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N2 : Nat.card (O ⧸ I421N2) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N2)

lemma isPrimeI421N2 : Ideal.IsPrime I421N2 := prime_ideal_of_norm_prime hp421.out _ NI421N2
def MulI421N0 : IdealMulLeCertificate' Table 
  ![![-8, 13, 44, 21, 63]] ![![-3, 26, -26, -10, -62]]
  ![![6, -247, 258, 97, 615]] where
 M := ![![![6, -247, 258, 97, 615]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI421N1 : IdealMulLeCertificate' Table 
  ![![6, -247, 258, 97, 615]] ![![28, 23, -10, -7, -31]]
  ![![421, 0, 0, 0, 0]] where
 M := ![![![-421, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC421 : ContainsPrimesAboveP 421 ![I421N0, I421N1, I421N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
    exact isPrimeI421N1
    exact isPrimeI421N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 421 (by decide) (𝕀 ⊙ MulI421N0 ⊙ MulI421N1)
instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-156, -1559, 1836, 703, 4473]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![-156, -1559, 1836, 703, 4473]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![0, 0, 431, 0, 0], ![0, 0, 0, 431, 0], ![200, 120, 199, 237, 1]] where
  M :=![![![-156, -1559, 1836, 703, 4473], ![1020, 6215, -7562, -2972, -18140], ![-1232, -22634, 26203, 9884, 64368], ![9618, 44216, -54912, -21975, -130282], ![-1153, 515, 10, 209, -732]]]
  hmulB := by decide  
  f := ![![![-34, -1, 0, -1, -5]], ![![4, -35, -2, 4, 4]], ![![-80, -58, 81, 44, 240]], ![![-50, 80, -76, -49, -250]], ![![-79, 7, -5, -6, -28]]]
  g := ![![![-2076, -1249, -2061, -2458, 4473], ![8420, 5065, 8358, 9968, -18140], ![-29872, -17974, -29659, -35372, 64368], ![60478, 36376, 60026, 71589, -130282], ![337, 205, 338, 403, -732]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 4 2 8 [167, 105, 262, 62, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 14, 252, 296], [246, 310, 286, 337], [34, 106, 324, 229], [0, 1]]
 g := ![![[224, 205, 290, 179], [201, 211, 291, 90], [11, 227, 100, 302], [303, 247, 14, 329], [381, 225, 97], [383, 376, 153, 157], [134, 369, 1], []], ![[199, 197, 56, 204, 259, 321], [368, 228, 367, 324, 250, 349], [298, 343, 76, 26, 265, 7], [280, 203, 365, 69, 154, 155], [397, 364, 384], [52, 147, 390, 62, 70, 133], [377, 84, 173], [29, 211, 360, 351, 174, 204]], ![[381, 134, 397, 352, 335, 36], [322, 337, 20, 215, 117, 232], [284, 428, 190, 104, 100, 242], [199, 399, 297, 107, 334, 88], [410, 230, 90], [110, 145, 204, 117, 428, 223], [99, 190, 396], [215, 211, 290, 111, 326, 384]], ![[209, 158, 0, 345, 218, 114], [346, 415, 209, 239, 140, 361], [298, 352, 178, 116, 161, 184], [25, 345, 115, 250, 258, 305], [379, 430, 38], [308, 128, 375, 241, 396, 59], [267, 335, 357], [272, 419, 3, 272, 360, 36]]]
 h' := ![![[89, 14, 252, 296], [51, 389, 323, 67], [318, 263, 180, 63], [257, 141, 31, 248], [351, 162, 115, 85], [258, 296, 5, 236], [34, 163, 112, 73], [0, 0, 0, 1], [0, 1]], ![[246, 310, 286, 337], [414, 41, 215, 300], [120, 310, 337, 368], [352, 261, 307, 222], [302, 424, 115, 80], [398, 67, 48, 162], [335, 177, 331, 203], [182, 27, 349, 76], [89, 14, 252, 296]], ![[34, 106, 324, 229], [239, 280, 216, 220], [189, 303, 37, 366], [403, 184, 236, 258], [249, 78, 175, 103], [173, 425, 94, 63], [62, 146, 423, 363], [64, 273, 276, 62], [246, 310, 286, 337]], ![[0, 1], [357, 152, 108, 275], [256, 417, 308, 65], [264, 276, 288, 134], [113, 198, 26, 163], [7, 74, 284, 401], [304, 376, 427, 223], [345, 131, 237, 292], [34, 106, 324, 229]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [169, 9, 6], []]
 b := ![[], [], [78, 13, 66, 266], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 4
  hpos := by decide
  P := [167, 105, 262, 62, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-356360589610449203, -176866343721320464, 382533667980040082, 205119987260063674, 720713992329589430]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-335264870198441613, -201073191237290144, -331878308133661848, -395833169825644156, 720713992329589430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 34507149121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34, -1, 0, -1, -5]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![-34, -1, 0, -1, -5]] 
 ![![431, 0, 0, 0, 0], ![106, 1, 0, 0, 0], ![401, 0, 1, 0, 0], ![244, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-34, -1, 0, -1, -5], ![4, -35, -2, 4, 4], ![-80, -58, 81, 44, 240], ![-50, 80, -76, -49, -250], ![41, -1, -22, -9, -58]]]
  hmulB := by decide  
  f := ![![![-156, -1559, 1836, 703, 4473]], ![![-36, -369, 434, 166, 1058]], ![![-148, -1503, 1769, 677, 4311]], ![![-66, -780, 912, 347, 2230]], ![![-11, -82, 98, 38, 237]]]
  g := ![![![1, -1, 0, -1, -5], ![8, -35, -2, 4, 4], ![-99, -58, 81, 44, 240], ![92, 80, -76, -49, -250], ![29, -1, -22, -9, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N1 : Nat.card (O ⧸ I431N1) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N1)

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := prime_ideal_of_norm_prime hp431.out _ NI431N1
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![-156, -1559, 1836, 703, 4473]] ![![-34, -1, 0, -1, -5]]
  ![![431, 0, 0, 0, 0]] where
 M := ![![![431, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-464, 651, -410, -301, -1441]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![-464, 651, -410, -301, -1441]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![0, 0, 433, 0, 0], ![327, 65, 237, 1, 0], ![45, 4, 211, 0, 1]] where
  M :=![![![-464, 651, -410, -301, -1441], ![1460, -919, -98, 128, 180], ![-2352, -350, 2429, 1132, 6848], ![-618, 3440, -3718, -2275, -11858], ![1557, -695, -462, -73, -936]]]
  hmulB := by decide  
  f := ![![![178, 147, -78, -47, -221]], ![![244, 109, 2, -24, -36]], ![![432, 558, -503, -236, -1248]], ![![408, 432, -333, -168, -853]], ![![231, 288, -253, -120, -631]]]
  g := ![![![376, 60, 866, -301, -1441], ![-112, -23, -158, 128, 180], ![-1572, -234, -3951, 1132, 6848], ![2949, 459, 7015, -2275, -11858], ![156, 18, 495, -73, -936]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 3 2 8 [159, 146, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [171, 224, 183], [240, 208, 250], [0, 1]]
 g := ![![[195, 259, 13], [311, 424], [159, 420], [302, 13], [296, 219, 409], [303, 228, 297], [106, 51], [1]], ![[307, 378, 337, 76], [68, 369], [272, 411], [266, 25], [240, 28, 199, 228], [411, 45, 122, 173], [367, 68], [187, 2, 259, 238]], ![[205, 329, 113, 195], [318, 408], [373, 327], [202, 37], [218, 4, 390, 346], [77, 317, 259, 299], [284, 115], [246, 307, 163, 195]]]
 h' := ![![[171, 224, 183], [311, 127, 130], [194, 165, 104], [414, 214, 112], [133, 342, 130], [319, 212, 323], [200, 327, 348], [274, 287, 411], [0, 1]], ![[240, 208, 250], [169, 341, 53], [270, 272, 300], [376, 432, 106], [384, 5, 428], [176, 59, 328], [380, 246, 160], [71, 71, 315], [171, 224, 183]], ![[0, 1], [103, 398, 250], [2, 429, 29], [361, 220, 215], [431, 86, 308], [225, 162, 215], [321, 293, 358], [331, 75, 140], [240, 208, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [223, 33], []]
 b := ![[], [56, 187, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 3
  hpos := by decide
  P := [159, 146, 22, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1590337219, 818390932, -1740111619, -927436621, -3298413570]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1046860792, 171582969, 2110918316, -927436621, -3298413570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 81182737 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![178, 147, -78, -47, -221]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![178, 147, -78, -47, -221]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![228, 392, 1, 0, 0], ![344, 140, 0, 1, 0], ![402, 178, 0, 0, 1]] where
  M :=![![![178, 147, -78, -47, -221], ![244, 109, 2, -24, -36], ![432, 558, -503, -236, -1248], ![214, -344, 398, 117, 1034], ![-115, -85, 86, 47, 194]]]
  hmulB := by decide  
  f := ![![![-464, 651, -410, -301, -1441]], ![![1460, -919, -98, 128, 180]], ![![1072, -490, -299, -40, -580]], ![![102, 228, -366, -203, -1114]], ![![173, 225, -422, -227, -1266]]]
  g := ![![![284, 177, -78, -47, -221], ![52, 21, 2, -24, -36], ![1612, 1046, -503, -236, -1248], ![-1262, -824, 398, 117, 1034], ![-263, -173, 86, 47, 194]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P1 : CertificateIrreducibleZModOfList' 433 2 2 8 [349, 256, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [177, 432], [0, 1]]
 g := ![![[265, 98], [367], [96], [109], [193, 235], [22, 401], [312], [177, 1]], ![[291, 335], [367], [96], [109], [220, 198], [420, 32], [312], [354, 432]]]
 h' := ![![[177, 432], [181, 143], [410, 223], [172, 23], [191, 242], [116, 318], [327, 157], [146, 237], [0, 1]], ![[0, 1], [378, 290], [45, 210], [346, 410], [158, 191], [112, 115], [404, 276], [94, 196], [177, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [402]]
 b := ![[], [181, 201]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N1 : CertifiedPrimeIdeal' SI433N1 433 where
  n := 2
  hpos := by decide
  P := [349, 256, 1]
  hirr := P433P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16702609, -11223964, 21247736, 10864950, 41999492]
  a := ![-995, -783, 1516, 663, 3151]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-58851097, -40040044, 21247736, 10864950, 41999492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N1 B_one_repr
lemma NI433N1 : Nat.card (O ⧸ I433N1) = 187489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N1
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![-464, 651, -410, -301, -1441]] ![![178, 147, -78, -47, -221]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![433, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0)
instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-686, 725, -358, -295, -1347]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![-686, 725, -358, -295, -1347]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![0, 0, 439, 0, 0], ![0, 0, 0, 439, 0], ![257, 49, 129, 83, 1]] where
  M :=![![![-686, 725, -358, -295, -1347], ![1692, -827, -466, -48, -868], ![-2320, -1334, 3521, 1772, 10240], ![-1630, 4660, -4378, -2759, -14150], ![1775, -461, -918, -315, -2294]]]
  hmulB := by decide  
  f := ![![![-4, -5, 2, 1, 7]], ![![4, 7, -18, -8, -36]], ![![48, -6, -29, -20, -32]], ![![174, 132, -242, -121, -486]], ![![45, 21, -55, -29, -101]]]
  g := ![![![787, 152, 395, 254, -1347], ![512, 95, 254, 164, -868], ![-6000, -1146, -3001, -1932, 10240], ![8280, 1590, 4148, 2669, -14150], ![1347, 255, 672, 433, -2294]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 4 2 8 [292, 316, 156, 173, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [323, 261, 94, 82], [112, 257, 31, 393], [270, 359, 314, 403], [0, 1]]
 g := ![![[265, 369, 154, 282], [397, 194, 171, 325], [85, 193, 263, 77], [22, 405, 347], [378, 201, 309, 182], [396, 271, 31, 206], [360, 266, 1], []], ![[299, 99, 340, 363, 362, 165], [303, 412, 36, 5, 383, 23], [102, 15, 28, 118, 261, 375], [108, 7, 280], [332, 293, 223, 402, 256, 423], [8, 244, 371, 91, 171, 132], [5, 121, 138], [176, 163, 299, 58, 261, 423]], ![[437, 331, 132, 414, 425, 292], [273, 401, 410, 72, 151, 342], [382, 82, 88, 351, 161, 26], [38, 286, 225], [151, 90, 354, 431, 86, 364], [408, 145, 403, 364, 94, 334], [438, 78, 116], [90, 286, 292, 218, 82, 122]], ![[344, 162, 104, 163, 127, 389], [249, 253, 121, 369, 209, 299], [293, 231, 99, 406, 74, 46], [129, 409, 32], [45, 165, 66, 7, 282, 136], [170, 116, 64, 88, 30, 300], [206, 421, 291], [314, 223, 425, 49, 7, 317]]]
 h' := ![![[323, 261, 94, 82], [411, 28, 193, 54], [203, 294, 414, 312], [10, 66, 316, 266], [252, 428, 416, 404], [264, 397, 428, 211], [240, 411, 411, 390], [0, 0, 0, 1], [0, 1]], ![[112, 257, 31, 393], [288, 191, 10, 235], [367, 190, 151, 249], [90, 78, 80, 164], [376, 437, 349, 104], [64, 105, 195, 357], [115, 282, 105, 104], [159, 1, 316, 279], [323, 261, 94, 82]], ![[270, 359, 314, 403], [122, 228, 321, 387], [207, 349, 366, 60], [356, 76, 72, 277], [113, 85, 151, 15], [113, 259, 66, 288], [77, 172, 372, 105], [188, 247, 273, 217], [112, 257, 31, 393]], ![[0, 1], [205, 431, 354, 202], [66, 45, 386, 257], [391, 219, 410, 171], [389, 367, 401, 355], [430, 117, 189, 22], [399, 13, 429, 279], [59, 191, 289, 381], [270, 359, 314, 403]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [68, 227, 389], []]
 b := ![[], [], [297, 121, 373, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 4
  hpos := by decide
  P := [292, 316, 156, 173, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13376077846646, -6729776064207, 14461383191279, 7737260927348, 27308012322006]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16017164566292, -3063376719459, -7991508442705, -5145393534850, 27308012322006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 37141383841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -5, 2, 1, 7]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![-4, -5, 2, 1, 7]] 
 ![![439, 0, 0, 0, 0], ![293, 1, 0, 0, 0], ![195, 0, 1, 0, 0], ![260, 0, 0, 1, 0], ![304, 0, 0, 0, 1]] where
  M :=![![![-4, -5, 2, 1, 7], ![4, 7, -18, -8, -36], ![48, -6, -29, -20, -32], ![174, 132, -242, -121, -486], ![-47, -21, 50, 27, 92]]]
  hmulB := by decide  
  f := ![![![-686, 725, -358, -295, -1347]], ![![-454, 482, -240, -197, -901]], ![![-310, 319, -151, -127, -575]], ![![-410, 440, -222, -181, -830]], ![![-471, 501, -250, -205, -938]]]
  g := ![![![-3, -5, 2, 1, 7], ![33, 7, -18, -8, -36], ![51, -6, -29, -20, -32], ![428, 132, -242, -121, -486], ![-88, -21, 50, 27, 92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N1 : Nat.card (O ⧸ I439N1) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N1)

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := prime_ideal_of_norm_prime hp439.out _ NI439N1
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![-686, 725, -358, -295, -1347]] ![![-4, -5, 2, 1, 7]]
  ![![439, 0, 0, 0, 0]] where
 M := ![![![439, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0)
instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1893, -1432, 632, 436, 1930]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![-1893, -1432, 632, 436, 1930]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![0, 0, 443, 0, 0], ![59, 295, 31, 1, 0], ![114, 147, 25, 0, 1]] where
  M :=![![![-1893, -1432, 632, 436, 1930], ![-2744, -1825, 754, 520, 2256], ![-3456, -2846, 1103, 804, 3424], ![-1428, -1054, 688, 427, 2032], ![626, 652, -278, -202, -877]]]
  hmulB := by decide  
  f := ![![![37, 312, -372, -144, -902]], ![![-152, -1207, 1442, 560, 3488]], ![![512, 4602, -5463, -2108, -13248]], ![![-63, -459, 551, 215, 1330]], ![![-12, -61, 75, 30, 179]]]
  g := ![![![-559, -934, -138, 436, 1930], ![-656, -1099, -162, 520, 2256], ![-996, -1678, -247, 804, 3424], ![-583, -961, -143, 427, 2032], ![254, 427, 63, -202, -877]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 3 2 8 [18, 136, 325, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [352, 188, 12], [209, 254, 431], [0, 1]]
 g := ![![[325, 191, 319], [225, 382, 423], [422, 192], [80, 287, 10], [332, 105, 90], [0, 144, 409], [188, 191], [1]], ![[400, 149, 37, 181], [294, 84, 17, 146], [243, 365], [376, 165, 314, 153], [27, 24, 329, 3], [272, 31, 128, 48], [33, 144], [73, 67, 271, 399]], ![[157, 349, 22, 429], [185, 357, 396, 54], [318, 68], [182, 315, 289, 23], [8, 118, 434, 26], [98, 165, 182, 329], [204, 161], [94, 94, 183, 44]]]
 h' := ![![[352, 188, 12], [380, 376, 177], [295, 48, 167], [332, 33, 39], [226, 359, 240], [0, 418, 166], [41, 255, 267], [425, 307, 118], [0, 1]], ![[209, 254, 431], [103, 319, 297], [2, 88, 23], [302, 32, 113], [301, 68, 147], [174, 437, 222], [18, 131, 441], [430, 319, 431], [352, 188, 12]], ![[0, 1], [121, 191, 412], [256, 307, 253], [211, 378, 291], [37, 16, 56], [264, 31, 55], [110, 57, 178], [65, 260, 337], [209, 254, 431]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [384, 137], []]
 b := ![[], [37, 161, 247], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where
  n := 3
  hpos := by decide
  P := [18, 136, 325, 1]
  hirr := P443P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-388373710, -551380272, 821804076, 373751484, 1792013272]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-511804118, -844772052, -125428496, 373751484, 1792013272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 86938307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 2, -8, -4, -12]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![11, 2, -8, -4, -12]] 
 ![![443, 0, 0, 0, 0], ![110, 1, 0, 0, 0], ![304, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![275, 0, 0, 0, 1]] where
  M :=![![![11, 2, -8, -4, -12], ![48, 31, -58, -32, -112], ![320, 150, -337, -180, -640], ![856, 406, -896, -481, -1664], ![-252, -116, 262, 140, 491]]]
  hmulB := by decide  
  f := ![![![1505, 1346, -804, -452, -2236]], ![![378, 335, -198, -112, -552]], ![![1040, 938, -565, -316, -1568]], ![![201, 164, -88, -53, -252]], ![![933, 834, -498, -280, -1385]]]
  g := ![![![13, 2, -8, -4, -12], ![106, 31, -58, -32, -112], ![616, 150, -337, -180, -640], ![1613, 406, -896, -481, -1664], ![-475, -116, 262, 140, 491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N1 : Nat.card (O ⧸ I443N1) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N1)

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := prime_ideal_of_norm_prime hp443.out _ NI443N1

def I443N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -2, 1, 1, 5]] i)))

def SI443N2: IdealEqSpanCertificate' Table ![![2, -2, 1, 1, 5]] 
 ![![443, 0, 0, 0, 0], ![271, 1, 0, 0, 0], ![97, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![353, 0, 0, 0, 1]] where
  M :=![![![2, -2, 1, 1, 5], ![-4, 4, -1, -2, -4], ![32, 17, -40, -18, -88], ![42, -11, -7, -7, 22], ![-21, -2, 15, 7, 26]]]
  hmulB := by decide  
  f := ![![![-2524, -1834, 741, 525, 2267]], ![![-1552, -1128, 456, 323, 1395]], ![![-564, -409, 165, 117, 505]], ![![-66, -49, 20, 14, 61]], ![![-2009, -1460, 590, 418, 1805]]]
  g := ![![![-3, -2, 1, 1, 5], ![1, 4, -1, -2, -4], ![69, 17, -40, -18, -88], ![-9, -11, -7, -7, 22], ![-23, -2, 15, 7, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N2 : Nat.card (O ⧸ I443N2) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N2)

lemma isPrimeI443N2 : Ideal.IsPrime I443N2 := prime_ideal_of_norm_prime hp443.out _ NI443N2
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![-1893, -1432, 632, 436, 1930]] ![![11, 2, -8, -4, -12]]
  ![![-463, -242, 220, 120, 746]] where
 M := ![![![-463, -242, 220, 120, 746]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI443N1 : IdealMulLeCertificate' Table 
  ![![-463, -242, 220, 120, 746]] ![![2, -2, 1, 1, 5]]
  ![![443, 0, 0, 0, 0]] where
 M := ![![![-3544, 886, 1329, 443, 1329]]]
 hmul := by decide  
 g := ![![![![-8, 2, 3, 1, 3]]]]
 hle2 := by decide  


def PBC443 : ContainsPrimesAboveP 443 ![I443N0, I443N1, I443N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI443N0
    exact isPrimeI443N1
    exact isPrimeI443N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 443 (by decide) (𝕀 ⊙ MulI443N0 ⊙ MulI443N1)
instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![449, 0, 0, 0, 0]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![449, 0, 0, 0, 0]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![0, 0, 449, 0, 0], ![0, 0, 0, 449, 0], ![0, 0, 0, 0, 449]] where
  M :=![![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![0, 0, 449, 0, 0], ![0, 0, 0, 449, 0], ![0, 0, 0, 0, 449]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 5 2 8 [289, 159, 113, 433, 286, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [343, 23, 221, 105, 226], [12, 84, 111, 145, 269], [263, 188, 292, 379, 108], [443, 153, 274, 269, 295], [0, 1]]
 g := ![![[207, 404, 415, 63, 368], [421, 282, 183, 394], [437, 214, 368, 242], [200, 83, 398, 44], [326, 443, 191, 156], [373, 309, 100, 244], [94, 163, 1], []], ![[85, 98, 366, 417, 426, 68, 140, 66], [125, 335, 281, 50], [203, 132, 313, 89], [371, 361, 88, 441], [247, 229, 345, 247], [20, 46, 413, 204], [381, 70, 3, 240, 311, 86, 113, 432], [110, 316, 247, 341, 207, 32, 417, 284]], ![[134, 28, 35, 38, 288, 51, 94, 87], [243, 254, 283, 228], [71, 353, 82, 252], [145, 41, 329, 220], [338, 234, 289, 180], [78, 252, 353, 439], [323, 402, 153, 188, 91, 212, 428, 440], [419, 12, 53, 323, 222, 20, 404, 61]], ![[61, 329, 134, 396, 275, 431, 102, 363], [381, 149, 223, 22], [407, 148, 214, 403], [117, 420, 278, 408], [53, 148, 375, 247], [287, 106, 95, 88], [23, 13, 170, 438, 32, 75, 2, 216], [121, 331, 325, 436, 272, 272, 272, 267]], ![[31, 97, 440, 326, 76, 247, 354, 46], [76, 196, 205, 315], [267, 274, 419, 372], [104, 243, 299, 22], [216, 316, 228, 154], [233, 37, 348, 81], [311, 104, 336, 203, 279, 123, 100, 53], [121, 101, 326, 390, 292, 447, 377, 351]]]
 h' := ![![[343, 23, 221, 105, 226], [98, 366, 52, 11, 154], [375, 290, 381, 333, 247], [299, 356, 82, 398, 119], [133, 206, 136, 196, 237], [302, 284, 381, 88, 400], [223, 358, 439, 437, 306], [0, 0, 0, 1], [0, 1]], ![[12, 84, 111, 145, 269], [22, 94, 243, 336, 237], [423, 310, 350, 95, 150], [69, 223, 411, 23, 199], [339, 173, 310, 31, 428], [55, 50, 112, 78, 78], [235, 402, 331, 297, 334], [270, 154, 7, 126, 360], [343, 23, 221, 105, 226]], ![[263, 188, 292, 379, 108], [154, 324, 86, 125, 160], [225, 117, 431, 401, 155], [293, 61, 83, 193, 387], [428, 290, 132, 105, 128], [155, 433, 421, 54, 259], [371, 346, 327, 22, 341], [71, 323, 324, 435, 371], [12, 84, 111, 145, 269]], ![[443, 153, 274, 269, 295], [109, 91, 136, 36, 73], [303, 369, 198, 185, 412], [89, 278, 141, 413, 292], [26, 271, 301, 200, 142], [102, 19, 77, 130, 78], [97, 421, 260, 251, 375], [265, 446, 382, 28, 419], [263, 188, 292, 379, 108]], ![[0, 1], [155, 23, 381, 390, 274], [93, 261, 436, 333, 383], [320, 429, 181, 320, 350], [309, 407, 19, 366, 412], [188, 112, 356, 99, 83], [351, 269, 439, 340, 440], [286, 424, 185, 308, 197], [443, 153, 274, 269, 295]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [353, 296, 66, 278], [], [], []]
 b := ![[], [39, 256, 296, 334, 114], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where
  n := 5
  hpos := by decide
  P := [289, 159, 113, 433, 286, 1]
  hirr := P449P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-440559364885104, -215541176345497, 469396599234048, 252286362724917, 882249609781835]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-981201258096, -480047163353, 1045426724352, 561884994933, 1964921179915]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 18248690477249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def PBC449 : ContainsPrimesAboveP 449 ![I449N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI449N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![449, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 449 (by decide) 𝕀

instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 11, -20, -11, -37]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![24, 11, -20, -11, -37]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![335, 407, 1, 0, 0], ![149, 289, 0, 1, 0], ![21, 299, 0, 0, 1]] where
  M :=![![![24, 11, -20, -11, -37], ![116, 65, -126, -68, -244], ![656, 306, -675, -364, -1264], ![1782, 888, -1912, -1025, -3598], ![-515, -247, 542, 291, 1016]]]
  hmulB := by decide  
  f := ![![![42, 59, -56, -37, -185]], ![![148, -51, 22, 36, 148]], ![![162, -2, -21, 5, -3]], ![![108, -12, -6, 10, 29]], ![![99, -31, 12, 22, 89]]]
  g := ![![![20, 49, -20, -11, -37], ![126, 315, -126, -68, -244], ![673, 1659, -675, -364, -1264], ![1905, 4707, -1912, -1025, -3598], ![-540, -1332, 542, 291, 1016]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 2 2 8 [132, 231, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [226, 456], [0, 1]]
 g := ![![[116, 389], [345], [313], [181, 225], [72], [262], [134, 18], [226, 1]], ![[286, 68], [345], [313], [304, 232], [72], [262], [89, 439], [452, 456]]]
 h' := ![![[226, 456], [239, 128], [203, 227], [329, 63], [59, 442], [93, 23], [135, 165], [330, 217], [0, 1]], ![[0, 1], [376, 329], [321, 230], [400, 394], [325, 15], [264, 434], [408, 292], [16, 240], [226, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [300, 240]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where
  n := 2
  hpos := by decide
  P := [132, 231, 1]
  hirr := P457P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-58461, -31825, 63890, 34811, 120415]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63845, -157767, 63890, 34811, 120415]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 208849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 5, -3, -2, -8]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![5, 5, -3, -2, -8]] 
 ![![457, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![451, 0, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![5, 5, -3, -2, -8], ![16, 8, -11, -6, -24], ![48, 23, -40, -22, -72], ![112, 65, -127, -69, -248], ![-32, -17, 33, 18, 61]]]
  hmulB := by decide  
  f := ![![![-75, -203, 327, 118, 776]], ![![-4, -10, 17, 6, 40]], ![![-22, -67, 104, 38, 248]], ![![-73, -184, 304, 109, 720]], ![![-23, -62, 100, 36, 237]]]
  g := ![![![5, 5, -3, -2, -8], ![16, 8, -11, -6, -24], ![54, 23, -40, -22, -72], ![177, 65, -127, -69, -248], ![-45, -17, 33, 18, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N1 : Nat.card (O ⧸ I457N1) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N1)

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := prime_ideal_of_norm_prime hp457.out _ NI457N1

def I457N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44, -112, 101, 65, 331]] i)))

def SI457N2: IdealEqSpanCertificate' Table ![![44, -112, 101, 65, 331]] 
 ![![457, 0, 0, 0, 0], ![159, 1, 0, 0, 0], ![311, 0, 1, 0, 0], ![331, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![44, -112, 101, 65, 331], ![-236, 234, -89, -82, -356], ![544, -191, -226, -66, -536], ![-162, -403, 637, 359, 1958], ![-279, 218, -33, -55, -196]]]
  hmulB := by decide  
  f := ![![![-80626, -58876, 24799, 17263, 75415]], ![![-28298, -20664, 8704, 6059, 26469]], ![![-55214, -40319, 16985, 11823, 51649]], ![![-58520, -42731, 18004, 12532, 54743]], ![![-11927, -8710, 3667, 2553, 11154]]]
  g := ![![![-126, -112, 101, 65, 331], ![91, 234, -89, -82, -356], ![349, -191, -226, -66, -536], ![-845, -403, 637, 359, 1958], ![15, 218, -33, -55, -196]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N2 : Nat.card (O ⧸ I457N2) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N2)

lemma isPrimeI457N2 : Ideal.IsPrime I457N2 := prime_ideal_of_norm_prime hp457.out _ NI457N2

def I457N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-194, -140, 59, 41, 179]] i)))

def SI457N3: IdealEqSpanCertificate' Table ![![-194, -140, 59, 41, 179]] 
 ![![457, 0, 0, 0, 0], ![320, 1, 0, 0, 0], ![425, 0, 1, 0, 0], ![390, 0, 0, 1, 0], ![367, 0, 0, 0, 1]] where
  M :=![![![-194, -140, 59, 41, 179], ![-268, -198, 83, 58, 252], ![-384, -279, 126, 86, 376], ![-146, -95, 51, 33, 134], ![81, 56, -29, -19, -82]]]
  hmulB := by decide  
  f := ![![![76, 1312, -1499, -581, -3625]], ![![52, 908, -1037, -402, -2508]], ![![76, 1261, -1443, -559, -3489]], ![![54, 1045, -1189, -461, -2876]], ![![61, 1052, -1202, -466, -2907]]]
  g := ![![![-136, -140, 59, 41, 179], ![-191, -198, 83, 58, 252], ![-298, -279, 126, 86, 376], ![-117, -95, 51, 33, 134], ![70, 56, -29, -19, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N3 : Nat.card (O ⧸ I457N3) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N3)

lemma isPrimeI457N3 : Ideal.IsPrime I457N3 := prime_ideal_of_norm_prime hp457.out _ NI457N3
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![24, 11, -20, -11, -37]] ![![5, 5, -3, -2, -8]]
  ![![-712, -338, 783, 419, 1455]] where
 M := ![![![-712, -338, 783, 419, 1455]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI457N1 : IdealMulLeCertificate' Table 
  ![![-712, -338, 783, 419, 1455]] ![![44, -112, 101, 65, 331]]
  ![![569, -568, 100, 154, 190]] where
 M := ![![![569, -568, 100, 154, 190]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI457N2 : IdealMulLeCertificate' Table 
  ![![569, -568, 100, 154, 190]] ![![-194, -140, 59, 41, 179]]
  ![![457, 0, 0, 0, 0]] where
 M := ![![![-3656, 914, 1371, 457, 1371]]]
 hmul := by decide  
 g := ![![![![-8, 2, 3, 1, 3]]]]
 hle2 := by decide  


def PBC457 : ContainsPrimesAboveP 457 ![I457N0, I457N1, I457N2, I457N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI457N0
    exact isPrimeI457N1
    exact isPrimeI457N2
    exact isPrimeI457N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 457 (by decide) (𝕀 ⊙ MulI457N0 ⊙ MulI457N1 ⊙ MulI457N2)
instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![461, 0, 0, 0, 0]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![461, 0, 0, 0, 0]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![0, 0, 461, 0, 0], ![0, 0, 0, 461, 0], ![0, 0, 0, 0, 461]] where
  M :=![![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![0, 0, 461, 0, 0], ![0, 0, 0, 461, 0], ![0, 0, 0, 0, 461]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P0 : CertificateIrreducibleZModOfList' 461 5 2 8 [85, 396, 146, 351, 238, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [347, 313, 68, 318, 388], [102, 33, 349, 75, 372], [336, 128, 423, 241, 108], [360, 447, 82, 288, 54], [0, 1]]
 g := ![![[61, 357, 119, 325, 357], [425, 289, 361, 359], [404, 394, 444, 313, 121], [437, 179, 233, 66, 294], [347, 220, 62, 245], [378, 39, 304, 294], [51, 223, 1], []], ![[48, 314, 295, 195, 292, 243, 391, 256], [249, 346, 79, 167], [66, 425, 288, 252, 299, 188, 278, 295], [381, 407, 428, 460, 445, 311, 263, 39], [100, 147, 438, 385], [115, 12, 435, 203], [62, 303, 333, 17, 70, 431, 173, 215], [460, 269, 70, 161, 202, 406, 147, 67]], ![[379, 460, 300, 437, 226, 244, 288, 110], [49, 106, 460, 196], [156, 53, 215, 239, 374, 433, 126, 369], [12, 97, 270, 244, 293, 27, 165, 393], [226, 326, 98, 189], [104, 180, 133, 289], [242, 259, 243, 252, 107, 12, 432, 393], [129, 224, 281, 426, 213, 169, 288, 361]], ![[295, 304, 289, 416, 116, 405, 386, 116], [246, 67, 31, 125], [214, 192, 418, 229, 213, 19, 206, 235], [274, 425, 336, 337, 374, 33, 234, 48], [298, 158, 77, 370], [438, 213, 431, 268], [321, 50, 303, 443, 16, 113, 81, 69], [189, 416, 28, 440, 0, 181, 354, 260]], ![[159, 441, 159, 262, 376, 447, 441, 324], [121, 371, 268, 5], [109, 284, 455, 113, 447, 179, 222, 76], [10, 339, 131, 37, 352, 217, 155, 393], [162, 127, 187, 298], [395, 410, 452, 268], [358, 260, 442, 375, 187, 226, 329, 373], [27, 50, 139, 53, 24, 13, 161, 263]]]
 h' := ![![[347, 313, 68, 318, 388], [199, 219, 349, 386, 295], [235, 299, 166, 303, 153], [196, 370, 413, 416, 450], [114, 89, 193, 360, 201], [161, 309, 323, 338, 160], [275, 34, 49, 316, 260], [0, 0, 0, 1], [0, 1]], ![[102, 33, 349, 75, 372], [35, 179, 147, 406, 33], [334, 332, 91, 331, 33], [155, 340, 381, 393, 349], [304, 457, 147, 143, 208], [129, 243, 309, 8, 107], [195, 81, 69, 31, 184], [195, 233, 211, 20, 457], [347, 313, 68, 318, 388]], ![[336, 128, 423, 241, 108], [387, 109, 149, 410, 44], [314, 422, 360, 425, 447], [437, 154, 45, 287, 115], [8, 198, 251, 153, 343], [115, 302, 107, 9, 97], [447, 244, 343, 88, 17], [85, 70, 373, 56, 118], [102, 33, 349, 75, 372]], ![[360, 447, 82, 288, 54], [146, 234, 140, 177, 192], [174, 36, 291, 232, 246], [204, 44, 219, 459, 47], [432, 83, 131, 363, 153], [381, 391, 52, 9, 56], [379, 415, 74, 117, 434], [202, 60, 94, 318, 311], [336, 128, 423, 241, 108]], ![[0, 1], [106, 181, 137, 4, 358], [333, 294, 14, 92, 43], [30, 14, 325, 289, 422], [19, 95, 200, 364, 17], [322, 138, 131, 97, 41], [385, 148, 387, 370, 27], [44, 98, 244, 66, 36], [360, 447, 82, 288, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168, 99, 409, 447], [], [], []]
 b := ![[], [194, 327, 245, 226, 164], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N0 : CertifiedPrimeIdeal' SI461N0 461 where
  n := 5
  hpos := by decide
  P := [85, 396, 146, 351, 238, 1]
  hirr := P461P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-548760781154068155, -269261048860500438, 585565426752864354, 314574493366790796, 1101130900967774716]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1190370458034855, -584080366291758, 1270206999463914, 682374172162236, 2388570284094956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N0 B_one_repr
lemma NI461N0 : Nat.card (O ⧸ I461N0) = 20821145878301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N0

def PBC461 : ContainsPrimesAboveP 461 ![I461N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI461N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![461, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 461 (by decide) 𝕀

instance hp463 : Fact (Nat.Prime 463) := {out := by norm_num}

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -21, 29, 18, 96]] i)))

def SI463N0: IdealEqSpanCertificate' Table ![![37, -21, 29, 18, 96]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![37, 368, 1, 0, 0], ![137, 368, 0, 1, 0], ![359, 27, 0, 0, 1]] where
  M :=![![![37, -21, 29, 18, 96], ![-48, 108, -45, -38, -168], ![240, -43, -84, -26, -200], ![-64, -129, 233, 127, 696], ![-104, 75, -17, -22, -83]]]
  hmulB := by decide  
  f := ![![![35, 269, -315, -122, -768]], ![![-144, -1034, 1253, 490, 3016]], ![![-111, -792, 961, 376, 2312]], ![![-107, -758, 922, 361, 2216]], ![![19, 148, -171, -66, -419]]]
  g := ![![![-82, -43, 29, 18, 96], ![145, 76, -45, -38, -168], ![170, 99, -84, -26, -200], ![-596, -327, 233, 127, 696], ![72, 36, -17, -22, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P0 : CertificateIrreducibleZModOfList' 463 2 2 8 [32, 159, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [304, 462], [0, 1]]
 g := ![![[222, 246], [270, 124], [81, 315], [189, 272], [143], [315], [190, 356], [304, 1]], ![[0, 217], [0, 339], [0, 148], [0, 191], [143], [315], [72, 107], [145, 462]]]
 h' := ![![[304, 462], [157, 199], [186, 106], [434, 93], [367, 244], [123, 148], [402, 93], [458, 247], [0, 1]], ![[0, 1], [0, 264], [0, 357], [0, 370], [0, 219], [204, 315], [431, 370], [77, 216], [304, 462]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [279]]
 b := ![[], [94, 371]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N0 : CertifiedPrimeIdeal' SI463N0 463 where
  n := 2
  hpos := by decide
  P := [32, 159, 1]
  hirr := P463P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-435695, -319355, 586134, 293797, 1175791]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1046397, -768640, 586134, 293797, 1175791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N0 : Ideal.IsPrime I463N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N0 B_one_repr
lemma NI463N0 : Nat.card (O ⧸ I463N0) = 214369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N0

def I463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 453, -537, -208, -1300]] i)))

def SI463N1: IdealEqSpanCertificate' Table ![![51, 453, -537, -208, -1300]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![368, 126, 1, 0, 0], ![429, 349, 0, 1, 0], ![19, 244, 0, 0, 1]] where
  M :=![![![51, 453, -537, -208, -1300], ![-208, -1734, 2065, 798, 4992], ![816, 6663, -7950, -3070, -19224], ![-1504, -11983, 14323, 5539, 34636], ![-32, -317, 373, 142, 899]]]
  hmulB := by decide  
  f := ![![![1941, 1451, -605, -424, -1852]], ![![2768, 1984, -849, -586, -2592]], ![![2304, 1699, -714, -498, -2184]], ![![3887, 2842, -1201, -835, -3672]], ![![1537, 1104, -472, -326, -1441]]]
  g := ![![![673, 989, -537, -208, -1300], ![-2586, -3798, 2065, 798, 4992], ![9954, 14623, -7950, -3070, -19224], ![-17941, -26352, 14323, 5539, 34636], ![-465, -683, 373, 142, 899]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P1 : CertificateIrreducibleZModOfList' 463 2 2 8 [225, 420, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 462], [0, 1]]
 g := ![![[434, 356], [245, 425], [48, 225], [28, 247], [67], [131], [284, 128], [43, 1]], ![[0, 107], [0, 38], [0, 238], [0, 216], [67], [131], [232, 335], [86, 462]]]
 h' := ![![[43, 462], [435, 216], [312, 305], [182, 448], [413, 55], [193, 175], [457, 69], [48, 235], [0, 1]], ![[0, 1], [0, 247], [0, 158], [0, 15], [0, 408], [310, 288], [183, 394], [430, 228], [43, 462]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [181]]
 b := ![[], [22, 322]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N1 : CertifiedPrimeIdeal' SI463N1 463 where
  n := 2
  hpos := by decide
  P := [225, 420, 1]
  hirr := P463P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49527, -27516, 59436, 31317, 115922]
  a := ![-32, -23, 49, 25, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-81122, -100931, 59436, 31317, 115922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N1 : Ideal.IsPrime I463N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N1 B_one_repr
lemma NI463N1 : Nat.card (O ⧸ I463N1) = 214369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N1

def I463N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -36, 14, 10, 44]] i)))

def SI463N2: IdealEqSpanCertificate' Table ![![-49, -36, 14, 10, 44]] 
 ![![463, 0, 0, 0, 0], ![432, 1, 0, 0, 0], ![428, 0, 1, 0, 0], ![399, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![-49, -36, 14, 10, 44], ![-64, -49, 16, 12, 56], ![-64, -52, -9, 0, 16], ![64, 20, -90, -47, -156], ![-8, 0, 24, 12, 39]]]
  hmulB := by decide  
  f := ![![![225, -276, 162, 150, 676]], ![![208, -257, 152, 140, 632]], ![![212, -252, 143, 136, 608]], ![![193, -248, 152, 135, 616]], ![![64, -80, 48, 44, 199]]]
  g := ![![![-1, -36, 14, 10, 44], ![4, -49, 16, 12, 56], ![52, -52, -9, 0, 16], ![151, 20, -90, -47, -156], ![-44, 0, 24, 12, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N2 : Nat.card (O ⧸ I463N2) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N2)

lemma isPrimeI463N2 : Ideal.IsPrime I463N2 := prime_ideal_of_norm_prime hp463.out _ NI463N2
def MulI463N0 : IdealMulLeCertificate' Table 
  ![![37, -21, 29, 18, 96]] ![![51, 453, -537, -208, -1300]]
  ![![-225, 276, -162, -150, -676]] where
 M := ![![![-225, 276, -162, -150, -676]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI463N1 : IdealMulLeCertificate' Table 
  ![![-225, 276, -162, -150, -676]] ![![-49, -36, 14, 10, 44]]
  ![![463, 0, 0, 0, 0]] where
 M := ![![![-463, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC463 : ContainsPrimesAboveP 463 ![I463N0, I463N1, I463N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI463N0
    exact isPrimeI463N1
    exact isPrimeI463N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 463 (by decide) (𝕀 ⊙ MulI463N0 ⊙ MulI463N1)


lemma PB547I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)

def PB547I9 : PrimesBelowBoundCertificateInterval O 419 463 547 where
  m := 9
  g := ![3, 2, 2, 2, 3, 1, 4, 1, 3]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB547I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0, I421N1, I421N2]
    · exact ![I431N0, I431N1]
    · exact ![I433N0, I433N1]
    · exact ![I439N0, I439N1]
    · exact ![I443N0, I443N1, I443N2]
    · exact ![I449N0]
    · exact ![I457N0, I457N1, I457N2, I457N3]
    · exact ![I461N0]
    · exact ![I463N0, I463N1, I463N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC421
    · exact PBC431
    · exact PBC433
    · exact PBC439
    · exact PBC443
    · exact PBC449
    · exact PBC457
    · exact PBC461
    · exact PBC463
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![74618461, 421, 421]
    · exact ![34507149121, 431]
    · exact ![81182737, 187489]
    · exact ![37141383841, 439]
    · exact ![86938307, 443, 443]
    · exact ![18248690477249]
    · exact ![208849, 457, 457, 457]
    · exact ![20821145878301]
    · exact ![214369, 214369, 463]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
      exact NI421N1
      exact NI421N2
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
      exact NI443N2
    · dsimp ; intro j
      fin_cases j
      exact NI449N0
    · dsimp ; intro j
      fin_cases j
      exact NI457N0
      exact NI457N1
      exact NI457N2
      exact NI457N3
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
      exact NI463N1
      exact NI463N2
  β := ![I421N1, I421N2, I431N1, I439N1, I443N1, I443N2, I457N1, I457N2, I457N3, I463N2]
  Il := ![[I421N1, I421N2], [I431N1], [], [I439N1], [I443N1, I443N2], [], [I457N1, I457N2, I457N3], [], [I463N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
