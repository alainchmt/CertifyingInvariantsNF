
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1367, -706, -602, -640, -250]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![-1367, -706, -602, -640, -250]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![0, 0, 367, 0, 0], ![192, 293, 274, 1, 0], ![85, 342, 217, 0, 1]] where
  M :=![![![-1367, -706, -602, -640, -250], ![-7204, -3655, -3116, -3332, -1280], ![-18476, -9470, -8051, -8576, -3332], ![-10598, -5382, -4586, -4897, -1878], ![-34118, -17460, -14874, -15848, -6135]]]
  hmulB := by decide  
  f := ![![![235, -6, 10, 40, -26]], ![![-604, 31, -44, -124, 80]], ![![916, 18, 67, 152, -124]], ![![322, 35, 20, 35, -42]], ![![35, 38, 1, -16, -5]]]
  g := ![![![389, 742, 624, -640, -250], ![2020, 3843, 3236, -3332, -1280], ![5208, 9926, 8351, -8576, -3332], ![2968, 5645, 4754, -4897, -1878], ![9619, 18322, 15419, -15848, -6135]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 3 2 8 [245, 270, 270, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 152, 58], [42, 214, 309], [0, 1]]
 g := ![![[202, 149, 240], [287, 187, 220], [113, 177, 174], [112, 13, 364], [182, 134], [149, 40, 364], [331, 97, 1], []], ![[360, 203, 114, 42], [127, 89, 27, 315], [105, 148, 134, 321], [301, 319, 36, 198], [16, 110], [261, 110, 244, 293], [78, 24, 231, 189], [61, 61]], ![[281, 61, 7, 345], [311, 311, 270, 145], [316, 166, 267, 46], [11, 167, 293, 120], [61, 191], [79, 100, 220, 213], [197, 159, 14, 252], [177, 61]]]
 h' := ![![[55, 152, 58], [149, 284, 314], [207, 144, 68], [85, 185, 305], [41, 102, 167], [195, 26, 177], [12, 268, 167], [0, 0, 1], [0, 1]], ![[42, 214, 309], [141, 290, 359], [196, 316, 150], [253, 57, 31], [114, 154, 183], [200, 196, 117], [40, 63, 269], [191, 352, 214], [55, 152, 58]], ![[0, 1], [250, 160, 61], [351, 274, 149], [134, 125, 31], [231, 111, 17], [297, 145, 73], [201, 36, 298], [237, 15, 152], [42, 214, 309]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [252, 302], []]
 b := ![[], [192, 0, 134], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where
  n := 3
  hpos := by decide
  P := [245, 270, 270, 1]
  hirr := P367P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9290043, -4668270, -3825465, -3941302, -1316502]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2341533, 4360700, 3710551, -3941302, -1316502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 49430863 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![235, -6, 10, 40, -26]] i)))

def SI367N1: IdealEqSpanCertificate' Table ![![235, -6, 10, 40, -26]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![162, 280, 1, 0, 0], ![118, 163, 0, 1, 0], ![136, 274, 0, 0, 1]] where
  M :=![![![235, -6, 10, 40, -26], ![-604, 31, -44, -124, 80], ![916, 18, 67, 152, -124], ![-958, -18, -46, -151, 114], ![666, -52, 26, 152, -77]]]
  hmulB := by decide  
  f := ![![![-1367, -706, -602, -640, -250]], ![![-7204, -3655, -3116, -3332, -1280]], ![![-6150, -3126, -2665, -2848, -1096]], ![![-3668, -1865, -1590, -1699, -654]], ![![-5978, -3038, -2590, -2768, -1065]]]
  g := ![![![-7, -6, 10, 40, -26], ![28, 29, -44, -124, 80], ![-30, -26, 67, 152, -124], ![24, 17, -46, -151, 114], ![-30, -30, 26, 152, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P1 : CertificateIrreducibleZModOfList' 367 2 2 8 [89, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [290, 366], [0, 1]]
 g := ![![[339, 33], [193, 74], [221, 41], [119, 135], [224], [92, 144], [142, 57], [1]], ![[0, 334], [0, 293], [0, 326], [0, 232], [224], [14, 223], [157, 310], [1]]]
 h' := ![![[290, 366], [72, 20], [149, 21], [52, 96], [33, 315], [253, 195], [207, 355], [278, 290], [0, 1]], ![[0, 1], [0, 347], [0, 346], [0, 271], [0, 52], [285, 172], [30, 12], [335, 77], [290, 366]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [259]]
 b := ![[], [123, 313]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N1 : CertifiedPrimeIdeal' SI367N1 367 where
  n := 2
  hpos := by decide
  P := [89, 77, 1]
  hirr := P367P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![745467, 424922, 403808, 431282, 196826]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-387823, -645424, 403808, 431282, 196826]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N1 : Ideal.IsPrime I367N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N1 B_one_repr
lemma NI367N1 : Nat.card (O ⧸ I367N1) = 134689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N1
def MulI367N0 : IdealMulLeCertificate' Table 
  ![![-1367, -706, -602, -640, -250]] ![![235, -6, 10, 40, -26]]
  ![![367, 0, 0, 0, 0]] where
 M := ![![![367, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC367 : ContainsPrimesAboveP 367 ![I367N0, I367N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI367N0
    exact isPrimeI367N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 367 (by decide) (𝕀 ⊙ MulI367N0)
instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8405, -98, -284, -1896, 1254]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![-8405, -98, -284, -1896, 1254]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![0, 0, 373, 0, 0], ![0, 0, 0, 373, 0], ![366, 154, 20, 102, 1]] where
  M :=![![![-8405, -98, -284, -1896, 1254], ![29528, 1269, 1744, 7104, -3792], ![-43760, 380, -779, -9456, 7104], ![50466, 2034, 2880, 12077, -6570], ![-40258, 1666, 352, -8052, 7403]]]
  hmulB := by decide  
  f := ![![![43, 10, 4, 0, -6]], ![![-136, -15, 16, 0, 0]], ![![16, -76, 1, 48, 0]], ![![-42, 30, -24, -31, 18]], ![![-24, 8, 4, -6, -1]]]
  g := ![![![-1253, -518, -68, -348, 1254], ![3800, 1569, 208, 1056, -3792], ![-7088, -2932, -383, -1968, 7104], ![6582, 2718, 360, 1829, -6570], ![-7372, -3052, -396, -2046, 7403]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 4 2 8 [7, 279, 52, 117, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 114, 103, 209], [271, 22, 3, 315], [299, 236, 267, 222], [0, 1]]
 g := ![![[258, 232, 53, 101], [156, 358, 220], [159, 18, 235, 309], [255, 333, 252], [81, 264, 283, 169], [26, 281, 294, 40], [256, 1], []], ![[71, 117, 196, 76, 270, 63], [294, 83, 86], [158, 24, 60, 293, 145, 215], [201, 100, 148], [211, 310, 367, 116, 258, 137], [315, 46, 197, 249, 190, 194], [107, 281, 42, 69, 147, 261], [274, 328, 40]], ![[66, 237, 2, 149, 105, 211], [131, 362, 286], [57, 39, 39, 128, 178, 8], [113, 346, 217], [33, 235, 306, 147, 315, 15], [176, 314, 243, 331, 272, 365], [344, 157, 122, 56, 348, 359], [98, 325, 7]], ![[244, 182, 140, 61, 226, 92], [335, 311, 243], [239, 306, 341, 5, 126, 20], [147, 306, 364], [149, 76, 204, 369, 188, 205], [220, 41, 103, 48, 210, 42], [209, 204, 273, 27, 24, 76], [240, 286, 48]]]
 h' := ![![[59, 114, 103, 209], [63, 322, 238, 108], [6, 257, 69, 81], [43, 27, 40, 287], [179, 98, 7, 25], [191, 211, 32, 360], [73, 185, 210, 209], [0, 0, 1], [0, 1]], ![[271, 22, 3, 315], [250, 62, 371, 317], [280, 99, 300, 163], [232, 192, 241, 303], [171, 316, 150, 68], [322, 354, 284, 202], [135, 170, 91, 205], [71, 358, 51, 181], [59, 114, 103, 209]], ![[299, 236, 267, 222], [109, 266, 309, 258], [186, 189, 200, 189], [321, 35, 260, 254], [309, 294, 109, 219], [92, 314, 150, 100], [60, 130, 123, 67], [20, 211, 286, 295], [271, 22, 3, 315]], ![[0, 1], [119, 96, 201, 63], [253, 201, 177, 313], [253, 119, 205, 275], [324, 38, 107, 61], [17, 240, 280, 84], [330, 261, 322, 265], [66, 177, 35, 270], [299, 236, 267, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [309, 209, 292], []]
 b := ![[], [], [343, 122, 331, 288], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where
  n := 4
  hpos := by decide
  P := [7, 279, 52, 117, 1]
  hirr := P373P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![251917666, 128497524, 107693218, 114652142, 44518590]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-43007738, -18035832, -2098334, -11866606, 44518590]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 19356878641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 10, 4, 0, -6]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![43, 10, 4, 0, -6]] 
 ![![373, 0, 0, 0, 0], ![169, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![173, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![43, 10, 4, 0, -6], ![-136, -15, 16, 0, 0], ![16, -76, 1, 48, 0], ![-42, 30, -24, -31, 18], ![218, 94, -8, -36, -13]]]
  hmulB := by decide  
  f := ![![![-8405, -98, -284, -1896, 1254]], ![![-3729, -41, -124, -840, 558]], ![![-1920, -20, -63, -432, 288]], ![![-3763, -40, -124, -847, 564]], ![![-491, 0, -12, -108, 77]]]
  g := ![![![-5, 10, 4, 0, -6], ![3, -15, 16, 0, 0], ![12, -76, 1, 48, 0], ![5, 30, -24, -31, 18], ![-23, 94, -8, -36, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N1 : Nat.card (O ⧸ I373N1) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N1)

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := prime_ideal_of_norm_prime hp373.out _ NI373N1
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![-8405, -98, -284, -1896, 1254]] ![![43, 10, 4, 0, -6]]
  ![![373, 0, 0, 0, 0]] where
 M := ![![![373, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4783, -75, -178, -1088, 700]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![-4783, -75, -178, -1088, 700]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![0, 0, 379, 0, 0], ![288, 46, 251, 1, 0], ![84, 295, 287, 0, 1]] where
  M :=![![![-4783, -75, -178, -1088, 700], ![16444, 607, 894, 3908, -2176], ![-25218, -63, -675, -5578, 3908], ![28148, 989, 1490, 6663, -3758], ![-23680, 435, -236, -5000, 3993]]]
  hmulB := by decide  
  f := ![![![63, -1, 36, 20, -28]], ![![-600, -205, 14, 64, 40]], ![![494, -95, -151, 58, 64]], ![![302, -88, -71, 61, 26]], ![![-78, -231, -95, 98, 73]]]
  g := ![![![659, -413, 190, -1088, 700], ![-2444, 1221, -938, 3908, -2176], ![3306, -2365, 733, -5578, 3908], ![-4156, 2119, -1563, 6663, -3758], ![2852, -2500, 287, -5000, 3993]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 3 2 8 [31, 362, 273, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [276, 185, 173], [209, 193, 206], [0, 1]]
 g := ![![[40, 308, 173], [83, 42, 350], [100, 203], [267, 332, 371], [113, 165, 121], [367, 325, 361], [262, 106, 1], []], ![[64, 128, 87, 350], [82, 202, 264, 165], [100, 326], [357, 373, 312, 143], [338, 89, 104, 193], [4, 206, 85, 169], [264, 367, 337, 319], [203, 367]], ![[119, 202, 177, 174], [291, 378, 264, 47], [83, 224], [88, 90, 377, 75], [120, 282, 228, 287], [21, 333, 33, 374], [311, 332, 155, 192], [170, 367]]]
 h' := ![![[276, 185, 173], [80, 307, 141], [242, 209, 352], [61, 58, 31], [287, 266, 139], [372, 372, 11], [216, 31, 360], [0, 0, 1], [0, 1]], ![[209, 193, 206], [177, 2, 355], [139, 238, 247], [160, 316, 99], [144, 351, 77], [57, 169, 154], [294, 2, 180], [147, 202, 193], [276, 185, 173]], ![[0, 1], [233, 70, 262], [185, 311, 159], [357, 5, 249], [324, 141, 163], [361, 217, 214], [18, 346, 218], [132, 177, 185], [209, 193, 206]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [219, 22], []]
 b := ![[], [283, 373, 254], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where
  n := 3
  hpos := by decide
  P := [31, 362, 273, 1]
  hirr := P379P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![663804058, 353224747, 311505288, 331760612, 138523025]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-281053262, -147155820, -323790281, 331760612, 138523025]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 54439939 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def I379N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 28, 16, -12, -11]] i)))

def SI379N1: IdealEqSpanCertificate' Table ![![4, 28, 16, -12, -11]] 
 ![![379, 0, 0, 0, 0], ![148, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![187, 0, 0, 1, 0], ![298, 0, 0, 0, 1]] where
  M :=![![![4, 28, 16, -12, -11], ![-232, -123, 66, 76, -24], ![-222, -219, -81, 74, 76], ![311, 146, -42, -63, -1], ![373, 348, 28, -166, -52]]]
  hmulB := by decide  
  f := ![![![-54734, 1696, -3184, -7850, 6293]], ![![-20992, 655, -1218, -3008, 2416]], ![![-6104, 195, -351, -872, 705]], ![![-26515, 828, -1538, -3799, 3052]], ![![-43339, 1356, -2512, -6208, 4990]]]
  g := ![![![2, 28, 16, -12, -11], ![22, -123, 66, 76, -24], ![-3, -219, -81, 74, 76], ![-20, 146, -42, -63, -1], ![-15, 348, 28, -166, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI379N1 : Nat.card (O ⧸ I379N1) = 379 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI379N1)

lemma isPrimeI379N1 : Ideal.IsPrime I379N1 := prime_ideal_of_norm_prime hp379.out _ NI379N1

def I379N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1225, -37, 76, 172, -136]] i)))

def SI379N2: IdealEqSpanCertificate' Table ![![1225, -37, 76, 172, -136]] 
 ![![379, 0, 0, 0, 0], ![243, 1, 0, 0, 0], ![227, 0, 1, 0, 0], ![373, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![1225, -37, 76, 172, -136], ![-3112, 97, -194, -432, 344], ![3934, -127, 247, 538, -432], ![-3884, 127, -244, -529, 426], ![2540, -89, 162, 336, -275]]]
  hmulB := by decide  
  f := ![![![783, 561, 2, -232, -48]], ![![499, 360, 4, -148, -32]], ![![457, 328, 3, -134, -28]], ![![777, 554, 0, -229, -46]], ![![89, 60, -2, -24, -3]]]
  g := ![![![-176, -37, 76, 172, -136], ![441, 97, -194, -432, 344], ![-548, -127, 247, 538, -432], ![538, 127, -244, -529, 426], ![-340, -89, 162, 336, -275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI379N2 : Nat.card (O ⧸ I379N2) = 379 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI379N2)

lemma isPrimeI379N2 : Ideal.IsPrime I379N2 := prime_ideal_of_norm_prime hp379.out _ NI379N2
def MulI379N0 : IdealMulLeCertificate' Table 
  ![![-4783, -75, -178, -1088, 700]] ![![4, 28, 16, -12, -11]]
  ![![-39484, -965, -1764, -9132, 5573]] where
 M := ![![![-39484, -965, -1764, -9132, 5573]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI379N1 : IdealMulLeCertificate' Table 
  ![![-39484, -965, -1764, -9132, 5573]] ![![1225, -37, 76, 172, -136]]
  ![![379, 0, 0, 0, 0]] where
 M := ![![![-2680288, -64430, -118248, -620044, 377105]]]
 hmul := by decide  
 g := ![![![![-7072, -170, -312, -1636, 995]]]]
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

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2541, -1097, -948, -1086, -324]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![-2541, -1097, -948, -1086, -324]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![0, 0, 383, 0, 0], ![0, 0, 0, 383, 0], ![288, 293, 315, 53, 1]] where
  M :=![![![-2541, -1097, -948, -1086, -324], ![-9672, -5595, -4738, -4812, -2172], ![-30802, -14647, -12505, -13746, -4812], ![-13914, -8243, -6960, -6989, -3232], ![-54822, -26961, -23026, -24938, -9135]]]
  hmulB := by decide  
  f := ![![![-203, 5, -14, -30, 24]], ![![548, -3, 30, 72, -60]], ![![-690, 25, -33, -102, 72]], ![![666, -29, 42, 105, -76]], ![![-210, 18, -9, -37, 21]]]
  g := ![![![237, 245, 264, 42, -324], ![1608, 1647, 1774, 288, -2172], ![3538, 3643, 3925, 630, -4812], ![2394, 2451, 2640, 429, -3232], ![6726, 6918, 7453, 1199, -9135]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P0 : CertificateIrreducibleZModOfList' 383 4 2 8 [95, 37, 311, 333, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 268, 369, 234], [185, 138, 324, 59], [208, 359, 73, 90], [0, 1]]
 g := ![![[181, 47, 39, 174], [339, 199, 344, 8], [219, 56, 324, 27], [217, 244, 355, 87], [309, 359, 379, 207], [137, 240, 7, 8], [50, 1], []], ![[339, 165, 86, 237, 338, 151], [31, 110, 194, 78, 98, 312], [236, 240, 24, 43, 112, 247], [332, 317, 126, 8, 246, 90], [253, 64, 352, 166, 183, 327], [318, 220, 177, 217, 208, 37], [234, 181, 313, 9, 57, 332], [129, 75, 370]], ![[179, 171, 195, 257, 0, 83], [134, 120, 328, 148, 53, 375], [55, 338, 318, 322, 351, 382], [288, 309, 300, 176, 237, 131], [28, 358, 349, 156, 237, 60], [166, 172, 81, 223, 82, 365], [240, 194, 71, 324, 201, 163], [20, 100, 34]], ![[14, 196, 290, 381, 159, 287], [167, 219, 323, 38, 196, 82], [350, 10, 159, 368, 221, 164], [58, 329, 316, 339, 43, 381], [177, 2, 9, 288, 72, 249], [269, 74, 133, 233, 31, 285], [218, 112, 107, 366, 156, 345], [313, 287, 57]]]
 h' := ![![[40, 268, 369, 234], [350, 150, 178, 108], [260, 258, 193, 109], [67, 309, 254, 289], [136, 88, 227, 262], [7, 60, 367, 156], [229, 353, 116, 274], [0, 0, 1], [0, 1]], ![[185, 138, 324, 59], [85, 202, 151, 27], [217, 220, 333, 277], [1, 68, 89, 143], [36, 52, 273, 345], [259, 43, 127, 25], [73, 131, 371, 10], [69, 350, 320, 184], [40, 268, 369, 234]], ![[208, 359, 73, 90], [255, 24, 313, 167], [60, 338, 309, 155], [245, 262, 74, 149], [378, 266, 138, 139], [381, 129, 305, 321], [264, 144, 34, 342], [153, 222, 150, 232], [185, 138, 324, 59]], ![[0, 1], [158, 7, 124, 81], [307, 333, 314, 225], [162, 127, 349, 185], [283, 360, 128, 20], [132, 151, 350, 264], [130, 138, 245, 140], [124, 194, 295, 350], [208, 359, 73, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [278, 85, 380], []]
 b := ![[], [], [174, 99, 48, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N0 : CertifiedPrimeIdeal' SI383N0 383 where
  n := 4
  hpos := by decide
  P := [95, 37, 311, 333, 1]
  hirr := P383P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15495870455, 7576804885, 6564891614, 7092232778, 2462023472]
  a := ![-7, -18, -1, 12, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1810879607, -1863697317, -2007761102, -322180186, 2462023472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N0 B_one_repr
lemma NI383N0 : Nat.card (O ⧸ I383N0) = 21517662721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N0

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-203, 5, -14, -30, 24]] i)))

def SI383N1: IdealEqSpanCertificate' Table ![![-203, 5, -14, -30, 24]] 
 ![![383, 0, 0, 0, 0], ![277, 1, 0, 0, 0], ![127, 0, 1, 0, 0], ![269, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-203, 5, -14, -30, 24], ![548, -3, 30, 72, -60], ![-690, 25, -33, -102, 72], ![666, -29, 42, 105, -76], ![-478, -5, -36, -62, 59]]]
  hmulB := by decide  
  f := ![![![-2541, -1097, -948, -1086, -324]], ![![-1863, -808, -698, -798, -240]], ![![-923, -402, -347, -396, -120]], ![![-1821, -792, -684, -781, -236]], ![![-309, -142, -122, -136, -45]]]
  g := ![![![20, 5, -14, -30, 24], ![-53, -3, 30, 72, -60], ![58, 25, -33, -102, 72], ![-60, -29, 42, 105, -76], ![54, -5, -36, -62, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N1 : Nat.card (O ⧸ I383N1) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N1)

lemma isPrimeI383N1 : Ideal.IsPrime I383N1 := prime_ideal_of_norm_prime hp383.out _ NI383N1
def MulI383N0 : IdealMulLeCertificate' Table 
  ![![-2541, -1097, -948, -1086, -324]] ![![-203, 5, -14, -30, 24]]
  ![![383, 0, 0, 0, 0]] where
 M := ![![![383, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC383 : ContainsPrimesAboveP 383 ![I383N0, I383N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI383N0
    exact isPrimeI383N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 383 (by decide) (𝕀 ⊙ MulI383N0)
instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 7, -6, -6, 4]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![9, 7, -6, -6, 4]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![221, 320, 1, 0, 0], ![212, 288, 0, 1, 0], ![360, 233, 0, 0, 1]] where
  M :=![![![9, 7, -6, -6, 4], ![84, 45, 10, -8, -12], ![-134, -21, 43, 14, -8], ![38, -27, -6, 29, 4], ![38, 5, -40, -6, 39]]]
  hmulB := by decide  
  f := ![![![-3883, 103, -236, -570, 440]], ![![10088, -257, 614, 1484, -1140]], ![![6059, -152, 369, 892, -684]], ![![5386, -135, 328, 793, -608]], ![![2426, -58, 148, 358, -273]]]
  g := ![![![3, 7, -6, -6, 4], ![10, 5, 10, -8, -12], ![-25, -41, 43, 14, -8], ![-16, -19, -6, 29, 4], ![-10, 14, -40, -6, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 2 2 8 [344, 235, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [154, 388], [0, 1]]
 g := ![![[38, 121], [87], [385, 63], [220], [99], [175], [246], [154, 1]], ![[0, 268], [87], [362, 326], [220], [99], [175], [246], [308, 388]]]
 h' := ![![[154, 388], [138, 378], [209, 101], [168, 29], [204, 61], [149, 60], [305, 211], [317, 32], [0, 1]], ![[0, 1], [0, 11], [203, 288], [355, 360], [262, 328], [53, 329], [123, 178], [188, 357], [154, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [375]]
 b := ![[], [150, 382]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where
  n := 2
  hpos := by decide
  P := [344, 235, 1]
  hirr := P389P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38948, 10110, -4774, -29358, 10626]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8778, 19324, -4774, -29358, 10626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 151321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def I389N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78, 60, 48, 48, 25]] i)))

def SI389N1: IdealEqSpanCertificate' Table ![![78, 60, 48, 48, 25]] 
 ![![389, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![358, 0, 0, 1, 0], ![166, 0, 0, 0, 1]] where
  M :=![![![78, 60, 48, 48, 25], ![696, 303, 266, 292, 96], ![1418, 793, 665, 698, 292], ![1007, 446, 390, 427, 143], ![2765, 1460, 1236, 1310, 522]]]
  hmulB := by decide  
  f := ![![![-1148, -704, -136, 210, 203]], ![![-180, -115, -26, 34, 35]], ![![-70, -37, -9, 8, 13]], ![![-1061, -652, -122, 197, 185]], ![![-519, -316, -56, 96, 88]]]
  g := ![![![-68, 60, 48, 48, 25], ![-377, 303, 266, 292, 96], ![-942, 793, 665, 698, 292], ![-553, 446, 390, 427, 143], ![-1751, 1460, 1236, 1310, 522]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N1 : Nat.card (O ⧸ I389N1) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N1)

lemma isPrimeI389N1 : Ideal.IsPrime I389N1 := prime_ideal_of_norm_prime hp389.out _ NI389N1

def I389N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 67, -26, -36, 6]] i)))

def SI389N2: IdealEqSpanCertificate' Table ![![127, 67, -26, -36, 6]] 
 ![![389, 0, 0, 0, 0], ![216, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![119, 0, 0, 1, 0], ![385, 0, 0, 0, 1]] where
  M :=![![![127, 67, -26, -36, 6], ![92, 171, 94, -60, -72], ![-770, -355, 193, 198, -60], ![54, -93, -114, 23, 72], ![758, 241, -296, -168, 131]]]
  hmulB := by decide  
  f := ![![![-13789, 683, -604, -1848, 1746]], ![![-7552, 381, -326, -1008, 960]], ![![-530, 35, -17, -66, 72]], ![![-4081, 212, -172, -541, 522]], ![![-13695, 698, -586, -1824, 1745]]]
  g := ![![![-31, 67, -26, -36, 6], ![-8, 171, 94, -60, -72], ![188, -355, 193, 198, -60], ![-23, -93, -114, 23, 72], ![-201, 241, -296, -168, 131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N2 : Nat.card (O ⧸ I389N2) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N2)

lemma isPrimeI389N2 : Ideal.IsPrime I389N2 := prime_ideal_of_norm_prime hp389.out _ NI389N2

def I389N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3848, 102, -234, -564, 435]] i)))

def SI389N3: IdealEqSpanCertificate' Table ![![-3848, 102, -234, -564, 435]] 
 ![![389, 0, 0, 0, 0], ![246, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![200, 0, 0, 1, 0], ![373, 0, 0, 0, 1]] where
  M :=![![![-3848, 102, -234, -564, 435], ![9972, -263, 606, 1464, -1128], ![-12930, 339, -785, -1902, 1464], ![12849, -336, 780, 1891, -1455], ![-8817, 228, -534, -1302, 1000]]]
  hmulB := by decide  
  f := ![![![86, 282, 234, -42, -123]], ![![48, 175, 150, -24, -78]], ![![18, 57, 49, -6, -24]], ![![53, 150, 120, -23, -63]], ![![97, 282, 228, -42, -119]]]
  g := ![![![-151, 102, -234, -564, 435], ![390, -263, 606, 1464, -1128], ![-504, 339, -785, -1902, 1464], ![500, -336, 780, 1891, -1455], ![-341, 228, -534, -1302, 1000]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N3 : Nat.card (O ⧸ I389N3) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N3)

lemma isPrimeI389N3 : Ideal.IsPrime I389N3 := prime_ideal_of_norm_prime hp389.out _ NI389N3
def MulI389N0 : IdealMulLeCertificate' Table 
  ![![9, 7, -6, -6, 4]] ![![78, 60, 48, 48, 25]]
  ![![2084, 1067, 908, 966, 375]] where
 M := ![![![2084, 1067, 908, 966, 375]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI389N1 : IdealMulLeCertificate' Table 
  ![![2084, 1067, 908, 966, 375]] ![![127, 67, -26, -36, 6]]
  ![![86, 282, 234, -42, -123]] where
 M := ![![![86, 282, 234, -42, -123]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI389N2 : IdealMulLeCertificate' Table 
  ![![86, 282, 234, -42, -123]] ![![-3848, 102, -234, -564, 435]]
  ![![389, 0, 0, 0, 0]] where
 M := ![![![389, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC389 : ContainsPrimesAboveP 389 ![I389N0, I389N1, I389N2, I389N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI389N0
    exact isPrimeI389N1
    exact isPrimeI389N2
    exact isPrimeI389N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 389 (by decide) (𝕀 ⊙ MulI389N0 ⊙ MulI389N1 ⊙ MulI389N2)
instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10345, -285, 632, 1498, -1164]] i)))

def SI397N0: IdealEqSpanCertificate' Table ![![10345, -285, 632, 1498, -1164]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![0, 0, 397, 0, 0], ![214, 290, 328, 1, 0], ![376, 118, 161, 0, 1]] where
  M :=![![![10345, -285, 632, 1498, -1164], ![-26672, 735, -1634, -3860, 2996], ![34318, -967, 2097, 4950, -3860], ![-34074, 945, -2092, -4919, 3824], ![23058, -665, 1402, 3302, -2593]]]
  hmulB := by decide  
  f := ![![![-19, -21, -10, 6, 8]], ![![172, 69, -46, -40, 12]], ![![98, 143, 35, -74, -40]], ![![196, 157, -10, -87, -20]], ![![72, 58, -9, -36, -5]]]
  g := ![![![321, -749, -764, 1498, -1164], ![-824, 1931, 1970, -3860, 2996], ![1074, -2471, -2519, 4950, -3860], ![-1056, 2459, 2508, -4919, 3824], ![734, -1643, -1673, 3302, -2593]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P0 : CertificateIrreducibleZModOfList' 397 3 2 8 [333, 168, 175, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [281, 213, 354], [338, 183, 43], [0, 1]]
 g := ![![[23, 199, 81], [6, 246], [90, 259, 370], [376, 38, 141], [290, 104], [163, 388], [169, 56], [1]], ![[284, 283, 1, 230], [179, 141], [47, 291, 358, 350], [236, 377, 364, 126], [49, 176], [93, 237], [138, 33], [109, 56, 105, 290]], ![[212, 360, 164, 124], [148, 107], [109, 228, 131, 372], [188, 322, 121, 173], [66, 353], [266, 85], [148, 34], [39, 241, 303, 107]]]
 h' := ![![[281, 213, 354], [297, 216, 388], [202, 251, 342], [244, 181, 207], [42, 381, 183], [214, 191, 223], [223, 137, 189], [64, 229, 222], [0, 1]], ![[338, 183, 43], [339, 8, 181], [334, 274, 183], [273, 39, 323], [129, 34, 35], [384, 268, 42], [369, 299, 112], [335, 119, 210], [281, 213, 354]], ![[0, 1], [308, 173, 225], [129, 269, 269], [302, 177, 264], [346, 379, 179], [253, 335, 132], [200, 358, 96], [381, 49, 362], [338, 183, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [364, 20], []]
 b := ![[], [49, 195, 379], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N0 : CertifiedPrimeIdeal' SI397N0 397 where
  n := 3
  hpos := by decide
  P := [333, 168, 175, 1]
  hirr := P397P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![370443218, 190482243, 170923440, 182076444, 68487315]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-162078454, -152879571, -177774831, 182076444, 68487315]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N0 : Ideal.IsPrime I397N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N0 B_one_repr
lemma NI397N0 : Nat.card (O ⧸ I397N0) = 62570773 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N0

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -21, -10, 6, 8]] i)))

def SI397N1: IdealEqSpanCertificate' Table ![![-19, -21, -10, 6, 8]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![221, 208, 1, 0, 0], ![87, 235, 0, 1, 0], ![159, 230, 0, 0, 1]] where
  M :=![![![-19, -21, -10, 6, 8], ![172, 69, -46, -40, 12], ![98, 143, 35, -74, -40], ![-146, -91, 30, 49, -12], ![-346, -243, -20, 86, 31]]]
  hmulB := by decide  
  f := ![![![10345, -285, 632, 1498, -1164]], ![![-26672, 735, -1634, -3860, 2996]], ![![-8129, 224, -499, -1176, 912]], ![![-13607, 375, -834, -1969, 1528]], ![![-11251, 310, -690, -1628, 1263]]]
  g := ![![![1, -3, -10, 6, 8], ![30, 41, -46, -40, 12], ![13, 49, 35, -74, -40], ![-23, -38, 30, 49, -12], ![-21, -59, -20, 86, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P1 : CertificateIrreducibleZModOfList' 397 2 2 8 [293, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [367, 396], [0, 1]]
 g := ![![[328, 355], [31], [122, 297], [43, 173], [314], [273], [33], [367, 1]], ![[0, 42], [31], [343, 100], [14, 224], [314], [273], [33], [337, 396]]]
 h' := ![![[367, 396], [304, 116], [381, 141], [105, 164], [327, 215], [15, 255], [216, 298], [56, 210], [0, 1]], ![[0, 1], [0, 281], [121, 256], [346, 233], [229, 182], [305, 142], [10, 99], [108, 187], [367, 396]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [181]]
 b := ![[], [365, 289]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N1 : CertifiedPrimeIdeal' SI397N1 397 where
  n := 2
  hpos := by decide
  P := [293, 30, 1]
  hirr := P397P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1614, 855, 746, 547, 227]
  a := ![-4, 0, -4, -9, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-622, -844, 746, 547, 227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N1 : Ideal.IsPrime I397N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N1 B_one_repr
lemma NI397N1 : Nat.card (O ⧸ I397N1) = 157609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N1
def MulI397N0 : IdealMulLeCertificate' Table 
  ![![10345, -285, 632, 1498, -1164]] ![![-19, -21, -10, 6, 8]]
  ![![397, 0, 0, 0, 0]] where
 M := ![![![397, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC397 : ContainsPrimesAboveP 397 ![I397N0, I397N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI397N0
    exact isPrimeI397N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 397 (by decide) (𝕀 ⊙ MulI397N0)
instance hp401 : Fact (Nat.Prime 401) := {out := by norm_num}

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 0, 0, 0, 0]] i)))

def SI401N0: IdealEqSpanCertificate' Table ![![401, 0, 0, 0, 0]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![0, 0, 401, 0, 0], ![0, 0, 0, 401, 0], ![0, 0, 0, 0, 401]] where
  M :=![![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![0, 0, 401, 0, 0], ![0, 0, 0, 401, 0], ![0, 0, 0, 0, 401]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P0 : CertificateIrreducibleZModOfList' 401 5 2 8 [167, 307, 114, 165, 190, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [370, 132, 169, 214, 313], [353, 152, 124, 203, 207], [316, 89, 390, 354, 41], [375, 27, 119, 31, 241], [0, 1]]
 g := ![![[29, 177, 49, 396, 391], [312, 351, 215, 16], [167, 249, 356, 343], [238, 297, 54, 50], [254, 365, 156, 58, 321], [62, 218, 21, 366], [211, 1], []], ![[38, 79, 244, 147, 363, 7, 159, 252], [10, 159, 64, 394], [111, 302, 103, 154], [154, 8, 209, 1], [341, 396, 288, 237, 264, 186, 384, 351], [214, 2, 134, 41], [33, 390, 399, 362], [282, 241, 67, 42, 267, 95, 38, 228]], ![[102, 387, 46, 134, 384, 301, 147, 304], [348, 178, 35, 299], [351, 103, 257, 1], [83, 62, 179, 223], [208, 309, 145, 161, 334, 83, 369, 104], [223, 252, 390, 57], [18, 2, 240, 329], [373, 203, 45, 40, 151, 183, 218, 24]], ![[234, 319, 75, 203, 132, 141, 101, 111], [312, 335, 324, 1], [69, 396, 50, 221], [209, 322, 99, 299], [133, 375, 365, 67, 280, 356, 150, 178], [27, 350, 154, 94], [364, 208, 339, 318], [41, 203, 104, 82, 375, 66, 36, 350]], ![[77, 122, 279, 309, 120, 122, 133, 250], [313, 74, 193, 2], [383, 54, 267, 356], [56, 293, 280, 350], [141, 226, 378, 86, 39, 331, 112, 301], [323, 159, 84, 7], [57, 142, 176, 179], [158, 108, 181, 250, 82, 298, 115, 215]]]
 h' := ![![[370, 132, 169, 214, 313], [371, 83, 100, 248, 191], [250, 1, 175, 345, 397], [78, 387, 263, 80, 194], [88, 125, 201, 386, 136], [267, 130, 391, 123, 196], [51, 18, 100, 359, 246], [0, 0, 0, 1], [0, 1]], ![[353, 152, 124, 203, 207], [246, 89, 20, 123, 198], [134, 57, 304, 370, 305], [386, 95, 322, 122, 168], [29, 183, 292, 400, 1], [266, 258, 61, 122, 254], [324, 7, 88, 233, 344], [107, 303, 190, 182, 222], [370, 132, 169, 214, 313]], ![[316, 89, 390, 354, 41], [193, 9, 338, 297, 227], [287, 152, 204, 70, 48], [165, 209, 377, 378, 400], [60, 287, 348, 5, 285], [229, 89, 0, 101, 4], [99, 97, 276, 250, 247], [349, 363, 194, 281, 56], [353, 152, 124, 203, 207]], ![[375, 27, 119, 31, 241], [140, 222, 243, 285, 161], [142, 271, 190, 144, 400], [6, 14, 187, 287, 294], [35, 18, 62, 338, 48], [12, 22, 167, 327, 100], [215, 145, 121, 124, 50], [177, 293, 400, 131, 362], [316, 89, 390, 354, 41]], ![[0, 1], [278, 399, 101, 250, 25], [242, 321, 330, 274, 53], [92, 97, 54, 336, 147], [294, 189, 300, 74, 332], [305, 303, 183, 129, 248], [355, 134, 217, 237, 316], [148, 244, 18, 207, 162], [375, 27, 119, 31, 241]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 245, 276, 101], [], [], []]
 b := ![[], [29, 261, 151, 12, 270], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N0 : CertifiedPrimeIdeal' SI401N0 401 where
  n := 5
  hpos := by decide
  P := [167, 307, 114, 165, 190, 1]
  hirr := P401P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163589252755166, 83766565949425, 71461444629746, 76136634728322, 29500584640344]
  a := ![15, 17, 12, 6, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![407953248766, 208894179425, 178208091346, 189866919522, 73567542744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N0 : Ideal.IsPrime I401N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N0 B_one_repr
lemma NI401N0 : Nat.card (O ⧸ I401N0) = 10368641602001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N0

def PBC401 : ContainsPrimesAboveP 401 ![I401N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI401N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![401, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 401 (by decide) 𝕀

instance hp409 : Fact (Nat.Prime 409) := {out := by norm_num}

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1645, -245, -238, -478, 96]] i)))

def SI409N0: IdealEqSpanCertificate' Table ![![-1645, -245, -238, -478, 96]] 
 ![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![0, 0, 409, 0, 0], ![378, 58, 315, 1, 0], ![131, 86, 356, 0, 1]] where
  M :=![![![-1645, -245, -238, -478, 96], ![1828, -1021, -774, -88, -956], ![-12246, -3045, -2751, -4146, -88], ![3666, -1479, -1094, 99, -1544], ![-16870, -5487, -4824, -6326, -967]]]
  hmulB := by decide  
  f := ![![![-77, 55, -24, -50, 20]], ![![432, 77, 102, 36, -100]], ![![-1098, -267, 79, 70, 36]], ![![-854, -144, 53, 13, 32]], ![![-889, -198, 82, 52, 17]]]
  g := ![![![407, 47, 284, -478, 96], ![392, 211, 898, -88, -956], ![3830, 599, 3263, -4146, -88], ![412, 307, 1265, 99, -1544], ![6115, 1087, 5702, -6326, -967]]]
  hle1 := by decide   
  hle2 := by decide  


def P409P0 : CertificateIrreducibleZModOfList' 409 3 2 8 [401, 67, 316, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [221, 57, 317], [281, 351, 92], [0, 1]]
 g := ![![[181, 7, 202], [374, 182], [176, 69], [180, 363, 318], [337, 168, 327], [314, 23], [71, 60], [1]], ![[27, 239, 271, 317], [190, 83], [326, 164], [49, 141, 397, 154], [273, 367, 75, 15], [169, 178], [276, 259], [230, 303, 267, 48]], ![[250, 188, 406, 242], [218, 89], [382, 345], [256, 125, 86, 17], [138, 318, 126, 68], [246, 197], [399, 389], [109, 353, 108, 361]]]
 h' := ![![[221, 57, 317], [26, 30, 171], [151, 62, 104], [213, 328, 36], [242, 84, 184], [298, 48, 209], [223, 377, 380], [8, 342, 93], [0, 1]], ![[281, 351, 92], [17, 348, 1], [71, 266, 125], [288, 198, 47], [117, 359, 5], [65, 117, 231], [211, 330, 127], [146, 133, 361], [221, 57, 317]], ![[0, 1], [396, 31, 237], [346, 81, 180], [166, 292, 326], [289, 375, 220], [163, 244, 378], [223, 111, 311], [254, 343, 364], [281, 351, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [291, 184], []]
 b := ![[], [42, 54, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N0 : CertifiedPrimeIdeal' SI409N0 409 where
  n := 3
  hpos := by decide
  P := [401, 67, 316, 1]
  hirr := P409P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13535243, 8919912, 7313198, 7438846, 4688698]
  a := ![6, 12, 2, -5, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8343687, -2018976, -9792420, 7438846, 4688698]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI409N0 : Ideal.IsPrime I409N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI409N0 B_one_repr
lemma NI409N0 : Nat.card (O ⧸ I409N0) = 68417929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI409N0

def I409N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40, 28, -4, -14, -1]] i)))

def SI409N1: IdealEqSpanCertificate' Table ![![40, 28, -4, -14, -1]] 
 ![![409, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![349, 0, 1, 0, 0], ![186, 0, 0, 1, 0], ![285, 0, 0, 0, 1]] where
  M :=![![![40, 28, -4, -14, -1], ![-32, 21, 46, 0, -28], ![-290, -165, 39, 82, 0], ![91, 8, -46, -11, 23], ![337, 164, -84, -92, 26]]]
  hmulB := by decide  
  f := ![![![-6566, -56, -236, -1440, 961]], ![![-314, -1, -10, -68, 47]], ![![-5684, -47, -203, -1246, 833]], ![![-2893, -22, -102, -633, 425]], ![![-4649, -36, -164, -1018, 683]]]
  g := ![![![9, 28, -4, -14, -1], ![-21, 21, 46, 0, -28], ![-62, -165, 39, 82, 0], ![28, 8, -46, -11, 23], ![87, 164, -84, -92, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI409N1 : Nat.card (O ⧸ I409N1) = 409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI409N1)

lemma isPrimeI409N1 : Ideal.IsPrime I409N1 := prime_ideal_of_norm_prime hp409.out _ NI409N1

def I409N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100, -3, 6, 14, -11]] i)))

def SI409N2: IdealEqSpanCertificate' Table ![![100, -3, 6, 14, -11]] 
 ![![409, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![251, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![100, -3, 6, 14, -11], ![-252, 9, -16, -36, 28], ![320, -10, 21, 44, -36], ![-319, 9, -20, -43, 35], ![207, -9, 12, 28, -22]]]
  hmulB := by decide  
  f := ![![![-86, -15, -48, -60, 7]], ![![-28, -5, -16, -20, 2]], ![![-8, -2, -3, -4, 0]], ![![-53, -10, -30, -37, 4]], ![![-33, -7, -18, -22, 2]]]
  g := ![![![-4, -3, 6, 14, -11], ![10, 9, -16, -36, 28], ![-12, -10, 21, 44, -36], ![12, 9, -20, -43, 35], ![-7, -9, 12, 28, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI409N2 : Nat.card (O ⧸ I409N2) = 409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI409N2)

lemma isPrimeI409N2 : Ideal.IsPrime I409N2 := prime_ideal_of_norm_prime hp409.out _ NI409N2
def MulI409N0 : IdealMulLeCertificate' Table 
  ![![-1645, -245, -238, -478, 96]] ![![40, 28, -4, -14, -1]]
  ![![-86, -15, -48, -60, 7]] where
 M := ![![![-86, -15, -48, -60, 7]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI409N1 : IdealMulLeCertificate' Table 
  ![![-86, -15, -48, -60, 7]] ![![100, -3, 6, 14, -11]]
  ![![409, 0, 0, 0, 0]] where
 M := ![![![409, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC409 : ContainsPrimesAboveP 409 ![I409N0, I409N1, I409N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI409N0
    exact isPrimeI409N1
    exact isPrimeI409N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 409 (by decide) (𝕀 ⊙ MulI409N0 ⊙ MulI409N1)
instance hp419 : Fact (Nat.Prime 419) := {out := by norm_num}

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![118, -11, 14, 42, -23]] i)))

def SI419N0: IdealEqSpanCertificate' Table ![![118, -11, 14, 42, -23]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![258, 254, 1, 0, 0], ![417, 171, 0, 1, 0], ![294, 103, 0, 0, 1]] where
  M :=![![![118, -11, 14, 42, -23], ![-524, -61, -40, -92, 84], ![968, 90, -17, 140, -92], ![-823, 13, -12, -201, 99], ![615, -17, 108, 208, -144]]]
  hmulB := by decide  
  f := ![![![32, -205, -140, -116, -115]], ![![-3040, -979, -920, -1068, -232]], ![![-1832, -726, -649, -724, -214]], ![![-1219, -607, -518, -555, -210]], ![![-745, -396, -334, -354, -142]]]
  g := ![![![-34, -20, 14, 42, -23], ![56, 41, -40, -92, 84], ![-62, -24, -17, 140, -92], ![136, 65, -12, -201, 99], ![-171, -115, 108, 208, -144]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P0 : CertificateIrreducibleZModOfList' 419 2 2 8 [225, 168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [251, 418], [0, 1]]
 g := ![![[146, 365], [317, 164], [192], [28], [114], [55, 38], [29], [251, 1]], ![[0, 54], [0, 255], [192], [28], [114], [375, 381], [29], [83, 418]]]
 h' := ![![[251, 418], [324, 391], [291, 99], [300, 232], [224, 228], [195, 372], [318, 244], [90, 345], [0, 1]], ![[0, 1], [0, 28], [0, 320], [291, 187], [49, 191], [130, 47], [388, 175], [371, 74], [251, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [386]]
 b := ![[], [290, 193]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N0 : CertifiedPrimeIdeal' SI419N0 419 where
  n := 2
  hpos := by decide
  P := [225, 168, 1]
  hirr := P419P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23705, 11827, 12962, 15897, 8249]
  a := ![12, 6, 8, 15, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29534, -16345, 12962, 15897, 8249]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N0 : Ideal.IsPrime I419N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N0 B_one_repr
lemma NI419N0 : Nat.card (O ⧸ I419N0) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N0

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100, 6, 4, 18, -13]] i)))

def SI419N1: IdealEqSpanCertificate' Table ![![100, 6, 4, 18, -13]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![159, 289, 1, 0, 0], ![273, 23, 0, 1, 0], ![387, 217, 0, 0, 1]] where
  M :=![![![100, 6, 4, 18, -13], ![-304, -3, -6, -64, 36], ![426, -19, 27, 118, -64], ![-473, -6, -30, -111, 71], ![501, 38, 8, 84, -58]]]
  hmulB := by decide  
  f := ![![![146, 22, 28, 40, -1]], ![![32, 149, 98, 84, 80]], ![![80, 112, 79, 74, 55]], ![![97, 23, 24, 31, 4]], ![![155, 99, 78, 82, 41]]]
  g := ![![![-1, 3, 4, 18, -13], ![10, -11, -6, -64, 36], ![-27, 8, 27, 118, -64], ![17, -10, -30, -111, 71], ![-3, 20, 8, 84, -58]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P1 : CertificateIrreducibleZModOfList' 419 2 2 8 [22, 379, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 418], [0, 1]]
 g := ![![[341, 400], [303, 125], [266], [137], [269], [162, 107], [386], [40, 1]], ![[0, 19], [275, 294], [266], [137], [269], [252, 312], [386], [80, 418]]]
 h' := ![![[40, 418], [38, 20], [223, 214], [48, 162], [59, 239], [207, 93], [395, 208], [377, 321], [0, 1]], ![[0, 1], [0, 399], [403, 205], [243, 257], [401, 180], [156, 326], [335, 211], [228, 98], [40, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [337, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N1 : CertifiedPrimeIdeal' SI419N1 419 where
  n := 2
  hpos := by decide
  P := [22, 379, 1]
  hirr := P419P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124810, 68693, 58820, 55060, 14760]
  a := ![-25, -6, -33, -52, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-71530, -51073, 58820, 55060, 14760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N1 : Ideal.IsPrime I419N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N1 B_one_repr
lemma NI419N1 : Nat.card (O ⧸ I419N1) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N1

def I419N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 16, 48, 2, -28]] i)))

def SI419N2: IdealEqSpanCertificate' Table ![![-49, 16, 48, 2, -28]] 
 ![![419, 0, 0, 0, 0], ![171, 1, 0, 0, 0], ![254, 0, 1, 0, 0], ![317, 0, 0, 1, 0], ![363, 0, 0, 0, 1]] where
  M :=![![![-49, 16, 48, 2, -28], ![-576, -347, 72, 172, 4], ![120, -220, -271, 52, 172], ![478, 342, -20, -163, -30], ![386, 548, 236, -206, -195]]]
  hmulB := by decide  
  f := ![![![95329, -2660, 5736, 13862, -10816]], ![![38313, -1071, 2304, 5570, -4348]], ![![58546, -1636, 3521, 8512, -6644]], ![![71361, -1994, 4292, 10375, -8098]], ![![83095, -2324, 4996, 12080, -9431]]]
  g := ![![![-13, 16, 48, 2, -28], ![-37, -347, 72, 172, 4], ![66, -220, -271, 52, 172], ![23, 342, -20, -163, -30], ![-41, 548, 236, -206, -195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI419N2 : Nat.card (O ⧸ I419N2) = 419 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI419N2)

lemma isPrimeI419N2 : Ideal.IsPrime I419N2 := prime_ideal_of_norm_prime hp419.out _ NI419N2
def MulI419N0 : IdealMulLeCertificate' Table 
  ![![118, -11, 14, 42, -23]] ![![100, 6, 4, 18, -13]]
  ![![-10281, -651, -528, -2114, 1490]] where
 M := ![![![-10281, -651, -528, -2114, 1490]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI419N1 : IdealMulLeCertificate' Table 
  ![![-10281, -651, -528, -2114, 1490]] ![![-49, 16, 48, 2, -28]]
  ![![419, 0, 0, 0, 0]] where
 M := ![![![380033, 271093, -3352, -122348, -32682]]]
 hmul := by decide  
 g := ![![![![907, 647, -8, -292, -78]]]]
 hle2 := by decide  


def PBC419 : ContainsPrimesAboveP 419 ![I419N0, I419N1, I419N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI419N0
    exact isPrimeI419N1
    exact isPrimeI419N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 419 (by decide) (𝕀 ⊙ MulI419N0 ⊙ MulI419N1)


lemma PB519I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)

def PB519I8 : PrimesBelowBoundCertificateInterval O 359 419 519 where
  m := 9
  g := ![2, 2, 3, 2, 4, 2, 1, 3, 3]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB519I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0, I367N1]
    · exact ![I373N0, I373N1]
    · exact ![I379N0, I379N1, I379N2]
    · exact ![I383N0, I383N1]
    · exact ![I389N0, I389N1, I389N2, I389N3]
    · exact ![I397N0, I397N1]
    · exact ![I401N0]
    · exact ![I409N0, I409N1, I409N2]
    · exact ![I419N0, I419N1, I419N2]
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
    · exact ![49430863, 134689]
    · exact ![19356878641, 373]
    · exact ![54439939, 379, 379]
    · exact ![21517662721, 383]
    · exact ![151321, 389, 389, 389]
    · exact ![62570773, 157609]
    · exact ![10368641602001]
    · exact ![68417929, 409, 409]
    · exact ![175561, 175561, 419]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
      exact NI367N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
      exact NI389N1
      exact NI389N2
      exact NI389N3
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
      exact NI409N1
      exact NI409N2
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
      exact NI419N2
  β := ![I373N1, I379N1, I379N2, I383N1, I389N1, I389N2, I389N3, I409N1, I409N2, I419N2]
  Il := ![[], [I373N1], [I379N1, I379N2], [I383N1], [I389N1, I389N2, I389N3], [], [], [I409N1, I409N2], [I419N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
