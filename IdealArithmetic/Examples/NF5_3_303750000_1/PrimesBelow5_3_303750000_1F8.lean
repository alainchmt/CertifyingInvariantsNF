
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-423, 816, -2710, 1797, -2331]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![-423, 816, -2710, 1797, -2331]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![0, 0, 367, 0, 0], ![0, 0, 0, 367, 0], ![302, 318, 223, 336, 1]] where
  M :=![![![-423, 816, -2710, 1797, -2331], ![564, -5492, 10831, -8635, 9714], ![-2136, 5120, -15759, 10714, -13676], ![2744, -31543, 60491, -48784, 54398], ![-4834, 2753, -21307, 11793, -17807]]]
  hmulB := by decide  
  f := ![![![-63, -46, -90, -5, 37]], ![![-28, 188, -77, -43, 34]], ![![128, 54, 237, 24, -96]], ![![64, -317, 139, 74, -62]], ![![60, -133, 130, 41, -55]]]
  g := ![![![1917, 2022, 1409, 2139, -2331], ![-7992, -8432, -5873, -8917, 9714], ![11248, 11864, 8267, 12550, -13676], ![-44756, -47221, -32889, -49936, 54398], ![14640, 15437, 10762, 16335, -17807]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 4 2 8 [176, 170, 102, 86, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 120, 120, 275], [146, 178, 283, 243], [128, 68, 331, 216], [0, 1]]
 g := ![![[319, 125, 219, 178], [177, 160, 118, 288], [89, 196, 131, 347], [117, 332, 208, 37], [125, 308, 89], [172, 184, 291, 281], [281, 1], []], ![[311, 205, 321, 130, 332, 193], [325, 276, 203, 353, 38, 167], [288, 319, 121, 329, 359, 312], [37, 174, 217, 40, 250, 358], [361, 40, 61], [234, 115, 225, 232, 173, 147], [58, 238, 157, 125, 173, 17], [92, 164, 23]], ![[271, 168, 240, 71, 314, 179], [291, 186, 73, 257, 271, 223], [78, 267, 246, 342, 133, 365], [357, 296, 93, 46, 65, 335], [263, 254, 217], [152, 96, 83, 326, 242, 183], [7, 319, 179, 50, 11, 318], [34, 245, 329]], ![[233, 294, 24, 52, 295, 321], [296, 283, 246, 54, 171, 171], [170, 222, 200, 13, 213, 22], [15, 252, 206, 237, 347, 266], [264, 88, 324], [354, 73, 28, 362, 233, 130], [63, 124, 334, 288, 250, 115], [8, 224, 47]]]
 h' := ![![[7, 120, 120, 275], [43, 213, 228, 59], [117, 51, 53, 214], [327, 195, 145, 54], [142, 281, 85, 279], [189, 246, 348, 312], [89, 131, 161, 321], [0, 0, 1], [0, 1]], ![[146, 178, 283, 243], [329, 252, 98, 243], [183, 183, 273, 255], [109, 260, 142, 299], [29, 304, 98, 361], [21, 203, 62, 309], [243, 39, 53, 136], [5, 115, 91, 63], [7, 120, 120, 275]], ![[128, 68, 331, 216], [271, 151, 83, 103], [208, 253, 239, 252], [353, 59, 70, 176], [49, 223, 148, 30], [126, 229, 200, 95], [215, 21, 352, 279], [285, 140, 288, 147], [146, 178, 283, 243]], ![[0, 1], [100, 118, 325, 329], [355, 247, 169, 13], [254, 220, 10, 205], [293, 293, 36, 64], [191, 56, 124, 18], [351, 176, 168, 365], [296, 112, 354, 157], [128, 68, 331, 216]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [34, 24, 137], []]
 b := ![[], [], [47, 58, 313, 229], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where
  n := 4
  hpos := by decide
  P := [176, 170, 102, 86, 1]
  hirr := P367P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![330779728130, 400852147950, 505554381150, 20722385507, 347218269418]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-284820538518, -299767186722, -209602505992, -317832741523, 347218269418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 18141126721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 46, 90, 5, -37]] i)))

def SI367N1: IdealEqSpanCertificate' Table ![![63, 46, 90, 5, -37]] 
 ![![367, 0, 0, 0, 0], ![246, 1, 0, 0, 0], ![224, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![320, 0, 0, 0, 1]] where
  M :=![![![63, 46, 90, 5, -37], ![28, -188, 77, 43, -34], ![-128, -54, -237, -24, 96], ![-64, 317, -139, -74, 62], ![98, 233, 179, -15, -69]]]
  hmulB := by decide  
  f := ![![![423, -816, 2710, -1797, 2331]], ![![282, -532, 1787, -1181, 1536]], ![![264, -512, 1697, -1126, 1460]], ![![49, -23, 197, -107, 163]], ![![382, -719, 2421, -1599, 2081]]]
  g := ![![![-54, 46, 90, 5, -37], ![103, -188, 77, 43, -34], ![100, -54, -237, -24, 96], ![-172, 317, -139, -74, 62], ![-203, 233, 179, -15, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI367N1 : Nat.card (O ⧸ I367N1) = 367 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI367N1)

lemma isPrimeI367N1 : Ideal.IsPrime I367N1 := prime_ideal_of_norm_prime hp367.out _ NI367N1
def MulI367N0 : IdealMulLeCertificate' Table 
  ![![-423, 816, -2710, 1797, -2331]] ![![63, 46, 90, 5, -37]]
  ![![367, 0, 0, 0, 0]] where
 M := ![![![-367, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-479, -686, -634, -139, -417]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![-479, -686, -634, -139, -417]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![0, 0, 373, 0, 0], ![0, 0, 0, 373, 0], ![155, 236, 167, 249, 1]] where
  M :=![![![-479, -686, -634, -139, -417], ![-2484, -3450, -3083, -773, -1946], ![-2224, -3006, -2851, -608, -1824], ![-15584, -21603, -19363, -4840, -12282], ![-11414, -15687, -14437, -3327, -9235]]]
  hmulB := by decide  
  f := ![![![27, 8, 14, 1, -7]], ![![4, -18, 15, 5, -6]], ![![-24, -12, -29, -2, 12]], ![![-24, 29, -29, -10, 14]], ![![-13, 6, -17, -4, 8]]]
  g := ![![![172, 262, 185, 278, -417], ![802, 1222, 863, 1297, -1946], ![752, 1146, 809, 1216, -1824], ![5062, 7713, 5447, 8186, -12282], ![3807, 5801, 4096, 6156, -9235]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 4 2 8 [226, 291, 229, 233, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [248, 139, 352, 269], [313, 260, 57, 108], [325, 346, 337, 369], [0, 1]]
 g := ![![[362, 71, 47, 209], [190, 352, 124], [120, 166, 345, 285], [151, 193, 372], [289, 168, 199, 363], [355, 248, 67, 252], [140, 1], []], ![[182, 203, 14, 116, 291, 42], [89, 86, 164], [225, 13, 147, 30, 285, 191], [335, 157, 287], [50, 322, 176, 13, 104, 129], [198, 189, 40, 96, 11, 319], [336, 104, 79, 205, 249, 207], [75, 125, 372]], ![[235, 281, 43, 230, 270, 209], [217, 57, 348], [24, 363, 219, 312, 245, 364], [209, 27, 324], [252, 270, 347, 336, 13, 184], [204, 146, 26, 68, 35, 257], [47, 339, 94, 352, 63, 337], [235, 342, 101]], ![[290, 204, 59, 225, 345, 189], [168, 359, 39], [185, 33, 102, 109, 320, 75], [107, 308, 160], [153, 146, 292, 136, 207, 160], [195, 272, 335, 158, 127, 292], [149, 2, 189, 354, 245, 343], [29, 290, 16]]]
 h' := ![![[248, 139, 352, 269], [273, 26, 2, 250], [109, 143, 220, 314], [219, 62, 208, 69], [334, 10, 158, 269], [338, 40, 105, 322], [65, 64, 100, 348], [0, 0, 1], [0, 1]], ![[313, 260, 57, 108], [192, 297, 336, 316], [110, 65, 130, 110], [5, 190, 154, 344], [165, 269, 22, 167], [202, 324, 86, 354], [89, 26, 285, 195], [167, 219, 341, 90], [248, 139, 352, 269]], ![[325, 346, 337, 369], [278, 26, 198, 286], [97, 194, 158, 147], [85, 347, 160, 216], [135, 6, 47, 355], [339, 350, 276, 341], [356, 175, 188, 21], [99, 298, 227, 59], [313, 260, 57, 108]], ![[0, 1], [185, 24, 210, 267], [73, 344, 238, 175], [322, 147, 224, 117], [107, 88, 146, 328], [289, 32, 279, 102], [350, 108, 173, 182], [226, 229, 177, 224], [325, 346, 337, 369]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [139, 175, 362], []]
 b := ![[], [], [20, 282, 361, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where
  n := 4
  hpos := by decide
  P := [226, 291, 229, 233, 1]
  hirr := P373P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1062860209336, 1286390253879, 1626049698805, 65527718811, 1116128847410]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-460957402518, -702734631997, -495355141605, -744907654923, 1116128847410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 19356878641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -8, -14, -1, 7]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![-27, -8, -14, -1, 7]] 
 ![![373, 0, 0, 0, 0], ![244, 1, 0, 0, 0], ![162, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-27, -8, -14, -1, 7], ![-4, 18, -15, -5, 6], ![24, 12, 29, 2, -12], ![24, -29, 29, 10, -14], ![-6, -29, -13, 3, 5]]]
  hmulB := by decide  
  f := ![![![479, 686, 634, 139, 417]], ![![320, 458, 423, 93, 278]], ![![214, 306, 283, 62, 186]], ![![97, 137, 125, 29, 81]], ![![55, 77, 71, 16, 46]]]
  g := ![![![11, -8, -14, -1, 7], ![-5, 18, -15, -5, 6], ![-20, 12, 29, 2, -12], ![6, -29, 29, 10, -14], ![24, -29, -13, 3, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N1 : Nat.card (O ⧸ I373N1) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N1)

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := prime_ideal_of_norm_prime hp373.out _ NI373N1
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![-479, -686, -634, -139, -417]] ![![-27, -8, -14, -1, 7]]
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

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7835, -373, -1867, -316, 1217]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![-7835, -373, -1867, -316, 1217]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![115, 317, 1, 0, 0], ![86, 153, 0, 1, 0], ![301, 105, 0, 0, 1]] where
  M :=![![![-7835, -373, -1867, -316, 1217], ![1056, 13, 328, -18, -94], ![3604, 214, 741, 230, -668], ![4212, -14, 1436, -175, -258], ![702, 64, 26, 118, -239]]]
  hmulB := by decide  
  f := ![![![-1451, 931, -2991, -578, 1229]], ![![3164, 8111, 5632, -606, -2166]], ![![2213, 7054, 3818, -678, -1445]], ![![934, 3449, 1570, -373, -586]], ![![-291, 2980, -845, -630, 388]]]
  g := ![![![-349, 1351, -1867, -316, 1217], ![-18, -241, 328, -18, -94], ![263, -527, 741, 230, -668], ![-180, -1059, 1436, -175, -258], ![157, -3, 26, 118, -239]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 2 2 8 [10, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [361, 378], [0, 1]]
 g := ![![[305, 22], [181, 139], [203], [322, 92], [241, 33], [79, 364], [213, 324], [1]], ![[288, 357], [332, 240], [203], [182, 287], [26, 346], [349, 15], [66, 55], [1]]]
 h' := ![![[361, 378], [85, 207], [341, 229], [191, 31], [243, 146], [347, 135], [144, 227], [369, 361], [0, 1]], ![[0, 1], [149, 172], [9, 150], [12, 348], [268, 233], [191, 244], [227, 152], [314, 18], [361, 378]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [72, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where
  n := 2
  hpos := by decide
  P := [10, 18, 1]
  hirr := P379P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5723, 6403, 9974, -875, 7608]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8855, -10080, 9974, -875, 7608]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 143641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def I379N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 2, 14, -4, 2]] i)))

def SI379N1: IdealEqSpanCertificate' Table ![![7, 2, 14, -4, 2]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![366, 123, 1, 0, 0], ![186, 356, 0, 1, 0], ![277, 231, 0, 0, 1]] where
  M :=![![![7, 2, 14, -4, 2], ![0, -5, -20, 24, -28], ![-8, -20, 15, -28, 40], ![-24, 88, -172, 107, -132], ![12, 4, 56, -32, 31]]]
  hmulB := by decide  
  f := ![![![181, -14, 30, 4, -46]], ![![-112, -127, -116, -24, -60]], ![![138, -55, -9, -4, -64]], ![![-18, -128, -96, -21, -80]], ![![63, -89, -50, -12, -71]]]
  g := ![![![-13, -2, 14, -4, 2], ![28, 1, -20, 24, -28], ![-30, -3, 15, -28, 40], ![210, 36, -172, 107, -132], ![-61, -7, 56, -32, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P1 : CertificateIrreducibleZModOfList' 379 2 2 8 [158, 376, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 378], [0, 1]]
 g := ![![[343, 304], [248, 251], [218], [134, 115], [155, 372], [284, 187], [216, 9], [1]], ![[118, 75], [243, 128], [218], [100, 264], [134, 7], [87, 192], [243, 370], [1]]]
 h' := ![![[3, 378], [232, 243], [96, 177], [52, 225], [145, 194], [229, 55], [361, 313], [221, 3], [0, 1]], ![[0, 1], [203, 136], [248, 202], [348, 154], [348, 185], [15, 324], [163, 66], [230, 376], [3, 378]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [219, 233]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N1 : CertifiedPrimeIdeal' SI379N1 379 where
  n := 2
  hpos := by decide
  P := [158, 376, 1]
  hirr := P379P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![441516, 506575, 796018, -108567, 684244]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1214362, -572069, 796018, -108567, 684244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N1 : Ideal.IsPrime I379N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N1 B_one_repr
lemma NI379N1 : Nat.card (O ⧸ I379N1) = 143641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N1

def I379N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 81, -85, -26, 35]] i)))

def SI379N2: IdealEqSpanCertificate' Table ![![-39, 81, -85, -26, 35]] 
 ![![379, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![201, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-39, 81, -85, -26, 35], ![180, 259, 340, 2, -138], ![36, -286, 99, 62, -48], ![-328, -478, -604, -9, 214], ![-226, 38, -448, -74, 165]]]
  hmulB := by decide  
  f := ![![![17721, -595, 7731, -1908, 467]], ![![6395, -198, 2749, -658, 131]], ![![9383, -339, 4152, -1054, 301]], ![![4111, -43, 1561, -269, -105]], ![![2434, -108, 1126, -310, 123]]]
  g := ![![![17, 81, -85, -26, 35], ![-255, 259, 340, 2, -138], ![43, -286, 99, 62, -48], ![465, -478, -604, -9, 214], ![218, 38, -448, -74, 165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI379N2 : Nat.card (O ⧸ I379N2) = 379 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI379N2)

lemma isPrimeI379N2 : Ideal.IsPrime I379N2 := prime_ideal_of_norm_prime hp379.out _ NI379N2
def MulI379N0 : IdealMulLeCertificate' Table 
  ![![-7835, -373, -1867, -316, 1217]] ![![7, 2, 14, -4, 2]]
  ![![-17721, 595, -7731, 1908, -467]] where
 M := ![![![-17721, 595, -7731, 1908, -467]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI379N1 : IdealMulLeCertificate' Table 
  ![![-17721, 595, -7731, 1908, -467]] ![![-39, 81, -85, -26, 35]]
  ![![379, 0, 0, 0, 0]] where
 M := ![![![-379, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383, 0, 0, 0, 0]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![383, 0, 0, 0, 0]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![0, 0, 383, 0, 0], ![0, 0, 0, 383, 0], ![0, 0, 0, 0, 383]] where
  M :=![![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![0, 0, 383, 0, 0], ![0, 0, 0, 383, 0], ![0, 0, 0, 0, 383]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P0 : CertificateIrreducibleZModOfList' 383 5 2 8 [295, 72, 135, 247, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 37, 214, 365, 41], [219, 206, 163, 120, 122], [213, 140, 377, 381, 210], [324, 382, 12, 283, 10], [0, 1]]
 g := ![![[135, 323, 253, 341, 146], [26, 259, 347, 50, 101], [207, 163, 214, 99, 196], [364, 103, 277, 42, 162], [277, 238, 207, 236, 2], [82, 46, 79, 306, 9], [1], []], ![[222, 35, 375, 306, 161, 113, 134, 239], [134, 214, 51, 153, 222, 119, 359, 208], [187, 27, 253, 231, 298, 212, 97, 364], [201, 66, 15, 370, 59, 322, 353, 366], [301, 284, 243, 357, 251, 138, 245, 356], [95, 288, 376, 187, 219, 236, 315, 52], [77, 284, 147, 233, 136, 60, 326, 241], [208, 243, 375, 149]], ![[264, 15, 181, 312, 340, 109, 301, 59], [350, 365, 8, 49, 56, 122, 328, 218], [191, 77, 183, 171, 311, 36, 139, 318], [93, 239, 146, 165, 98, 299, 230, 237], [211, 10, 30, 218, 242, 191, 214, 154], [253, 296, 167, 157, 148, 301, 108, 316], [331, 162, 123, 63, 268, 18, 19, 135], [195, 11, 331, 330]], ![[246, 151, 272, 332, 55, 301, 92, 307], [259, 213, 141, 10, 335, 282, 126, 257], [198, 65, 99, 235, 147, 321, 76, 352], [195, 225, 159, 5, 1, 233, 146, 364], [184, 342, 197, 172, 81, 28, 168, 315], [239, 178, 52, 9, 367, 178, 136, 123], [203, 6, 99, 243, 382, 116, 349, 80], [320, 319, 144, 55]], ![[12, 127, 239, 309, 349, 124, 261, 94], [293, 99, 112, 113, 98, 184, 37, 382], [208, 362, 127, 75, 307, 120, 295, 241], [135, 70, 170, 346, 242, 51, 288, 79], [104, 133, 2, 109, 167, 373, 299, 328], [187, 91, 306, 222, 317, 51, 371, 176], [180, 138, 196, 93, 150, 296, 96, 307], [360, 100, 381, 100]]]
 h' := ![![[7, 37, 214, 365, 41], [373, 120, 144, 58, 360], [215, 273, 60, 156, 22], [243, 203, 79, 175, 14], [247, 125, 242, 161, 299], [322, 143, 197, 329, 246], [88, 311, 248, 136, 380], [0, 0, 1], [0, 1]], ![[219, 206, 163, 120, 122], [352, 335, 364, 138, 333], [99, 131, 341, 241, 70], [379, 118, 58, 14, 342], [75, 292, 138, 142, 172], [137, 115, 273, 92, 119], [98, 136, 238, 276, 348], [352, 32, 215, 243, 23], [7, 37, 214, 365, 41]], ![[213, 140, 377, 381, 210], [45, 254, 313, 218, 258], [328, 94, 320, 172, 223], [206, 345, 248, 351, 59], [327, 54, 221, 48, 181], [329, 249, 162, 226, 195], [92, 136, 233, 311, 36], [11, 173, 175, 206, 248], [219, 206, 163, 120, 122]], ![[324, 382, 12, 283, 10], [213, 237, 225, 350, 362], [374, 23, 294, 284, 348], [351, 361, 305, 5, 31], [137, 310, 79, 83, 181], [298, 4, 129, 141, 24], [342, 135, 278, 377, 20], [376, 328, 316, 55, 337], [213, 140, 377, 381, 210]], ![[0, 1], [350, 203, 103, 2, 219], [304, 245, 134, 296, 103], [234, 122, 76, 221, 320], [304, 368, 86, 332, 316], [152, 255, 5, 361, 182], [323, 48, 152, 49, 365], [308, 233, 59, 262, 158], [324, 382, 12, 283, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [381, 328, 223, 3], [], [], []]
 b := ![[], [358, 169, 20, 162, 84], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N0 : CertifiedPrimeIdeal' SI383N0 383 where
  n := 5
  hpos := by decide
  P := [295, 72, 135, 247, 3, 1]
  hirr := P383P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3824883821578251, -4636460002339336, -5841488183162706, -244125848631160, -4008840224070782]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9986641831797, -12105639692792, -15251927371182, -637404304520, -10466945754754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N0 B_one_repr
lemma NI383N0 : Nat.card (O ⧸ I383N0) = 8241264822143 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N0

def PBC383 : ContainsPrimesAboveP 383 ![I383N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI383N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![383, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 383 (by decide) 𝕀

instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1517, 13951, -4347, -3002, 1977]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![-1517, 13951, -4347, -3002, 1977]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![0, 0, 389, 0, 0], ![0, 0, 0, 389, 0], ![62, 205, 241, 125, 1]] where
  M :=![![![-1517, 13951, -4347, -3002, 1977], ![25852, 19637, 50120, 3634, -20062], ![-4100, -40410, -4631, 6290, 1264], ![-43960, -34198, -85096, -6023, 34050], ![-19798, 24950, -41884, -10138, 17399]]]
  hmulB := by decide  
  f := ![![![-11, -43, -5, -24, -1]], ![![-136, -127, -264, 42, -194]], ![![-100, -206, 1, -134, 36]], ![![-844, -826, -1588, 213, -1158]], ![![-408, -469, -651, 3, -453]]]
  g := ![![![-319, -1006, -1236, -643, 1977], ![3264, 10623, 12558, 6456, -20062], ![-212, -770, -795, -390, 1264], ![-5540, -18032, -21314, -10957, 34050], ![-2824, -9105, -10887, -5617, 17399]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 4 2 8 [92, 189, 16, 351, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 306, 383, 118], [361, 337, 225, 60], [37, 134, 170, 211], [0, 1]]
 g := ![![[376, 281, 220, 383], [247, 11, 171], [40, 247, 269, 166], [42, 21, 369], [380, 57, 230], [265, 142, 323], [261, 38, 1], []], ![[58, 373, 198, 88, 359, 332], [19, 82, 353], [43, 125, 43, 368, 304, 318], [176, 93, 52], [195, 340, 309], [135, 41, 232], [198, 149, 41], [168, 234, 162, 334, 211, 285]], ![[276, 81, 116, 310, 165, 107], [355, 388, 69], [236, 67, 216, 152, 304, 336], [330, 222, 63], [261, 216, 91], [108, 206, 344], [135, 334, 361], [150, 213, 146, 35, 17, 105]], ![[157, 81, 285, 299, 61, 80], [7, 335, 361], [285, 54, 40, 317, 236, 86], [118, 321, 267], [2, 212, 42], [153, 215, 4], [259, 377, 295], [344, 303, 268, 286, 196, 359]]]
 h' := ![![[29, 306, 383, 118], [370, 133, 142, 281], [210, 288, 365, 46], [273, 3, 251, 339], [161, 201, 122, 59], [82, 279, 256, 116], [106, 79, 220, 174], [0, 0, 0, 1], [0, 1]], ![[361, 337, 225, 60], [106, 186, 324, 385], [197, 8, 216, 88], [135, 382, 11, 367], [34, 60, 20, 21], [344, 258, 133, 118], [263, 298, 21, 319], [375, 275, 349, 110], [29, 306, 383, 118]], ![[37, 134, 170, 211], [286, 251, 86, 91], [222, 367, 109, 236], [294, 164, 225, 151], [199, 357, 185, 360], [320, 71, 122, 296], [157, 330, 35, 283], [36, 132, 127, 370], [361, 337, 225, 60]], ![[0, 1], [277, 208, 226, 21], [210, 115, 88, 19], [292, 229, 291, 310], [373, 160, 62, 338], [107, 170, 267, 248], [314, 71, 113, 2], [333, 371, 302, 297], [37, 134, 170, 211]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [320, 329, 361], []]
 b := ![[], [], [65, 131, 377, 182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where
  n := 4
  hpos := by decide
  P := [92, 189, 16, 351, 1]
  hirr := P389P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1663807390, -3609031768, 11627437318, -7778176346, 9978979040]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1586202810, -5268122712, -6152458898, -3226608114, 9978979040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 22898045041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def I389N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -43, -5, -24, -1]] i)))

def SI389N1: IdealEqSpanCertificate' Table ![![-11, -43, -5, -24, -1]] 
 ![![389, 0, 0, 0, 0], ![165, 1, 0, 0, 0], ![155, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![368, 0, 0, 0, 1]] where
  M :=![![![-11, -43, -5, -24, -1], ![-136, -127, -264, 42, -194], ![-100, -206, 1, -134, 36], ![-844, -826, -1588, 213, -1158], ![-550, -844, -550, -286, -311]]]
  hmulB := by decide  
  f := ![![![-1517, 13951, -4347, -3002, 1977]], ![![-577, 5968, -1715, -1264, 787]], ![![-615, 5455, -1744, -1180, 791]], ![![-230, 988, -554, -247, 240]], ![![-1486, 13262, -4220, -2866, 1915]]]
  g := ![![![23, -43, -5, -24, -1], ![339, -127, -264, 42, -194], ![63, -206, 1, -134, 36], ![2060, -826, -1588, 213, -1158], ![892, -844, -550, -286, -311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N1 : Nat.card (O ⧸ I389N1) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N1)

lemma isPrimeI389N1 : Ideal.IsPrime I389N1 := prime_ideal_of_norm_prime hp389.out _ NI389N1
def MulI389N0 : IdealMulLeCertificate' Table 
  ![![-1517, 13951, -4347, -3002, 1977]] ![![-11, -43, -5, -24, -1]]
  ![![389, 0, 0, 0, 0]] where
 M := ![![![389, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 54, -134, 100, -124]] i)))

def SI397N0: IdealEqSpanCertificate' Table ![![3, 54, -134, 100, -124]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![159, 176, 1, 0, 0], ![132, 73, 0, 1, 0], ![322, 182, 0, 0, 1]] where
  M :=![![![3, 54, -134, 100, -124], ![60, -253, 626, -458, 552], ![-96, 316, -819, 588, -716], ![340, -1430, 3526, -2581, 3108], ![-116, 352, -968, 682, -845]]]
  hmulB := by decide  
  f := ![![![-201, -38, -450, -56, 180]], ![![172, 1123, 254, -158, -88]], ![![-3, 482, -65, -92, 32]], ![![-36, 189, -104, -47, 44]], ![![-86, 482, -252, -118, 107]]]
  g := ![![![121, 98, -134, 100, -124], ![-546, -447, 626, -458, 552], ![713, 584, -819, 588, -716], ![-3074, -2517, 3526, -2581, 3108], ![846, 692, -968, 682, -845]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P0 : CertificateIrreducibleZModOfList' 397 2 2 8 [89, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [320, 396], [0, 1]]
 g := ![![[99, 270], [293], [200, 257], [322, 33], [3], [108], [124], [320, 1]], ![[350, 127], [293], [261, 140], [163, 364], [3], [108], [124], [243, 396]]]
 h' := ![![[320, 396], [380, 238], [65, 154], [323, 329], [159, 210], [279, 20], [177, 277], [104, 282], [0, 1]], ![[0, 1], [316, 159], [117, 243], [1, 68], [266, 187], [327, 377], [286, 120], [225, 115], [320, 396]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [185]]
 b := ![[], [286, 291]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N0 : CertifiedPrimeIdeal' SI397N0 397 where
  n := 2
  hpos := by decide
  P := [89, 77, 1]
  hirr := P397P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![646321, 750044, 1079978, -62497, 857051]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1105267, -858305, 1079978, -62497, 857051]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N0 : Ideal.IsPrime I397N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N0 B_one_repr
lemma NI397N0 : Nat.card (O ⧸ I397N0) = 157609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N0

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 5, -9, 15, -20]] i)))

def SI397N1: IdealEqSpanCertificate' Table ![![3, 5, -9, 15, -20]] 
 ![![397, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![281, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![3, 5, -9, 15, -20], ![0, -58, 69, -59, 80], ![-20, 56, -127, 74, -88], ![64, -145, 501, -348, 408], ![4, 59, -93, 95, -125]]]
  hmulB := by decide  
  f := ![![![6459, 7133, 6777, 1577, 3908]], ![![633, 717, 678, 158, 396]], ![![4627, 5127, 4868, 1133, 2812]], ![![547, 716, 660, 155, 412]], ![![424, 549, 507, 119, 315]]]
  g := ![![![6, 5, -9, 15, -20], ![-44, -58, 69, -59, 80], ![85, 56, -127, 74, -88], ![-342, -145, 501, -348, 408], ![61, 59, -93, 95, -125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N1 : Nat.card (O ⧸ I397N1) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N1)

lemma isPrimeI397N1 : Ideal.IsPrime I397N1 := prime_ideal_of_norm_prime hp397.out _ NI397N1

def I397N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 3, 11, 0, -3]] i)))

def SI397N2: IdealEqSpanCertificate' Table ![![5, 3, 11, 0, -3]] 
 ![![397, 0, 0, 0, 0], ![127, 1, 0, 0, 0], ![105, 0, 1, 0, 0], ![395, 0, 0, 1, 0], ![378, 0, 0, 0, 1]] where
  M :=![![![5, 3, 11, 0, -3], ![0, -21, -2, 8, -6], ![-12, -4, -19, -8, 16], ![-4, 50, -34, 13, -22], ![14, 20, 32, -6, -3]]]
  hmulB := by decide  
  f := ![![![-2381, -335, -727, -142, 215]], ![![-763, -110, -235, -46, 67]], ![![-629, -91, -194, -38, 55]], ![![-2379, -351, -739, -145, 203]], ![![-2276, -332, -704, -138, 197]]]
  g := ![![![-1, 3, 11, 0, -3], ![5, -21, -2, 8, -6], ![-1, -4, -19, -8, 16], ![1, 50, -34, 13, -22], ![-6, 20, 32, -6, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N2 : Nat.card (O ⧸ I397N2) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N2)

lemma isPrimeI397N2 : Ideal.IsPrime I397N2 := prime_ideal_of_norm_prime hp397.out _ NI397N2

def I397N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-213, -69, -421, -47, 170]] i)))

def SI397N3: IdealEqSpanCertificate' Table ![![-213, -69, -421, -47, 170]] 
 ![![397, 0, 0, 0, 0], ![326, 1, 0, 0, 0], ![346, 0, 1, 0, 0], ![227, 0, 0, 1, 0], ![238, 0, 0, 0, 1]] where
  M :=![![![-213, -69, -421, -47, 170], ![108, 1018, 127, -157, -36], ![492, -142, 999, 164, -408], ![-172, -1729, -193, 270, 52], ![-628, -799, -1189, -29, 471]]]
  hmulB := by decide  
  f := ![![![-39237, -1873, -9099, -1713, 6326]], ![![-32206, -1536, -7469, -1405, 5192]], ![![-34150, -1630, -7917, -1492, 5508]], ![![-22379, -1060, -5192, -971, 3606]], ![![-23510, -1119, -5447, -1027, 3795]]]
  g := ![![![348, -69, -421, -47, 170], ![-835, 1018, 127, -157, -36], ![-602, -142, 999, 164, -408], ![1402, -1729, -193, 270, 52], ![1425, -799, -1189, -29, 471]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N3 : Nat.card (O ⧸ I397N3) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N3)

lemma isPrimeI397N3 : Ideal.IsPrime I397N3 := prime_ideal_of_norm_prime hp397.out _ NI397N3
def MulI397N0 : IdealMulLeCertificate' Table 
  ![![3, 54, -134, 100, -124]] ![![3, 5, -9, 15, -20]]
  ![![8593, -32437, 82349, -59637, 72352]] where
 M := ![![![8593, -32437, 82349, -59637, 72352]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI397N1 : IdealMulLeCertificate' Table 
  ![![8593, -32437, 82349, -59637, 72352]] ![![5, 3, 11, 0, -3]]
  ![![306253, -1157250, 2937688, -2127681, 2581385]] where
 M := ![![![306253, -1157250, 2937688, -2127681, 2581385]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI397N2 : IdealMulLeCertificate' Table 
  ![![306253, -1157250, 2937688, -2127681, 2581385]] ![![-213, -69, -421, -47, 170]]
  ![![397, 0, 0, 0, 0]] where
 M := ![![![-21041, -129819, 222717, -258844, 340229]]]
 hmul := by decide  
 g := ![![![![-53, -327, 561, -652, 857]]]]
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

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1273, -67, -297, -52, 199]] i)))

def SI401N0: IdealEqSpanCertificate' Table ![![-1273, -67, -297, -52, 199]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![39, 340, 1, 0, 0], ![210, 270, 0, 1, 0], ![149, 223, 0, 0, 1]] where
  M :=![![![-1273, -67, -297, -52, 199], ![160, -5, 20, 6, -18], ![588, 46, 135, 22, -92], ![700, 54, 200, 27, -118], ![130, 0, 50, 10, -29]]]
  hmulB := by decide  
  f := ![![![205, 287, 257, 62, 161]], ![![1020, 1387, 1300, 294, 818]], ![![887, 1207, 1130, 256, 711]], ![![810, 1106, 1030, 235, 648]], ![![655, 894, 833, 190, 524]]]
  g := ![![![-21, 176, -297, -52, 199], ![2, -11, 20, 6, -18], ![11, -78, 135, 22, -92], ![12, -122, 200, 27, -118], ![1, -33, 50, 10, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P0 : CertificateIrreducibleZModOfList' 401 2 2 8 [290, 259, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [142, 400], [0, 1]]
 g := ![![[265, 289], [332], [351], [70], [225, 289], [22], [99], [142, 1]], ![[0, 112], [332], [351], [70], [361, 112], [22], [99], [284, 400]]]
 h' := ![![[142, 400], [393, 17], [189, 44], [88, 314], [113, 110], [38, 17], [53, 35], [123, 225], [0, 1]], ![[0, 1], [0, 384], [21, 357], [165, 87], [94, 291], [46, 384], [211, 366], [394, 176], [142, 400]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [355]]
 b := ![[], [29, 378]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N0 : CertifiedPrimeIdeal' SI401N0 401 where
  n := 2
  hpos := by decide
  P := [290, 259, 1]
  hirr := P401P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![428020, 475993, 786849, -115878, 666379]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-262382, -958524, 786849, -115878, 666379]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N0 : Ideal.IsPrime I401N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N0 B_one_repr
lemma NI401N0 : Nat.card (O ⧸ I401N0) = 160801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N0

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-295, -14, -70, -12, 46]] i)))

def SI401N1: IdealEqSpanCertificate' Table ![![-295, -14, -70, -12, 46]] 
 ![![401, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![286, 0, 1, 0, 0], ![316, 0, 0, 1, 0], ![352, 0, 0, 0, 1]] where
  M :=![![![-295, -14, -70, -12, 46], ![40, 1, 12, 0, -4], ![136, 8, 29, 8, -24], ![160, 4, 52, -3, -12], ![28, 4, 4, 4, -7]]]
  hmulB := by decide  
  f := ![![![257, 38, 510, 68, -198]], ![![13, -1, 26, 4, -10]], ![![182, 28, 361, 48, -140]], ![![204, 36, 404, 53, -156]], ![![228, 36, 452, 60, -175]]]
  g := ![![![19, -14, -70, -12, 46], ![-5, 1, 12, 0, -4], ![-6, 8, 29, 8, -24], ![-24, 4, 52, -3, -12], ![0, 4, 4, 4, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N1 : Nat.card (O ⧸ I401N1) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N1)

lemma isPrimeI401N1 : Ideal.IsPrime I401N1 := prime_ideal_of_norm_prime hp401.out _ NI401N1

def I401N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 6, 0, -2]] i)))

def SI401N2: IdealEqSpanCertificate' Table ![![19, 0, 6, 0, -2]] 
 ![![401, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![364, 0, 1, 0, 0], ![390, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![19, 0, 6, 0, -2], ![-4, 1, -8, 4, -4], ![-8, -2, 5, -6, 8], ![-12, 14, -32, 23, -28], ![0, -4, 10, -6, 7]]]
  hmulB := by decide  
  f := ![![![-21, -36, -46, -24, -70]], ![![-4, -7, -8, -4, -12]], ![![-20, -34, -43, -22, -64]], ![![-26, -42, -52, -25, -72]], ![![-8, -12, -14, -6, -17]]]
  g := ![![![-5, 0, 6, 0, -2], ![4, 1, -8, 4, -4], ![0, -2, 5, -6, 8], ![10, 14, -32, 23, -28], ![-4, -4, 10, -6, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N2 : Nat.card (O ⧸ I401N2) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N2)

lemma isPrimeI401N2 : Ideal.IsPrime I401N2 := prime_ideal_of_norm_prime hp401.out _ NI401N2

def I401N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95, -107, -181, -7, 72]] i)))

def SI401N3: IdealEqSpanCertificate' Table ![![-95, -107, -181, -7, 72]] 
 ![![401, 0, 0, 0, 0], ![160, 1, 0, 0, 0], ![177, 0, 1, 0, 0], ![87, 0, 0, 1, 0], ![339, 0, 0, 0, 1]] where
  M :=![![![-95, -107, -181, -7, 72], ![-84, 390, -203, -95, 88], ![260, 144, 509, 46, -204], ![148, -657, 353, 164, -156], ![-200, -519, -355, 39, 137]]]
  hmulB := by decide  
  f := ![![![-46923, -1991, -10847, -1921, 7600]], ![![-18704, -790, -4321, -765, 3032]], ![![-20655, -873, -4772, -845, 3348]], ![![-10101, -406, -2318, -409, 1652]], ![![-39645, -1666, -9152, -1620, 6433]]]
  g := ![![![63, -107, -181, -7, 72], ![-120, 390, -203, -95, 88], ![-119, 144, 509, 46, -204], ![203, -657, 353, 164, -156], ![239, -519, -355, 39, 137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N3 : Nat.card (O ⧸ I401N3) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N3)

lemma isPrimeI401N3 : Ideal.IsPrime I401N3 := prime_ideal_of_norm_prime hp401.out _ NI401N3
def MulI401N0 : IdealMulLeCertificate' Table 
  ![![-1273, -67, -297, -52, 199]] ![![-295, -14, -70, -12, 46]]
  ![![329715, 15967, 77785, 13852, -51931]] where
 M := ![![![329715, 15967, 77785, 13852, -51931]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI401N1 : IdealMulLeCertificate' Table 
  ![![329715, 15967, 77785, 13852, -51931]] ![![19, 0, 6, 0, -2]]
  ![![5412213, 262049, 1276905, 227340, -852391]] where
 M := ![![![5412213, 262049, 1276905, 227340, -852391]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI401N2 : IdealMulLeCertificate' Table 
  ![![5412213, 262049, 1276905, 227340, -852391]] ![![-95, -107, -181, -7, 72]]
  ![![401, 0, 0, 0, 0]] where
 M := ![![![-52531, -4812, -12030, -2005, 8421]]]
 hmul := by decide  
 g := ![![![![-131, -12, -30, -5, 21]]]]
 hle2 := by decide  


def PBC401 : ContainsPrimesAboveP 401 ![I401N0, I401N1, I401N2, I401N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI401N0
    exact isPrimeI401N1
    exact isPrimeI401N2
    exact isPrimeI401N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 401 (by decide) (𝕀 ⊙ MulI401N0 ⊙ MulI401N1 ⊙ MulI401N2)
instance hp409 : Fact (Nat.Prime 409) := {out := by norm_num}

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-793, 1251, -1699, -453, 708]] i)))

def SI409N0: IdealEqSpanCertificate' Table ![![-793, 1251, -1699, -453, 708]] 
 ![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![0, 0, 409, 0, 0], ![218, 272, 403, 1, 0], ![184, 181, 29, 0, 1]] where
  M :=![![![-793, 1251, -1699, -453, 708], ![3012, 5046, 5599, -85, -2208], ![1020, -4648, 2459, 1138, -1076], ![-5140, -8731, -9517, 160, 3668], ![-3952, 203, -7921, -1155, 3183]]]
  hmulB := by decide  
  f := ![![![-209477, -10145, -49417, -8803, 32996]], ![![28096, 1362, 6621, 1185, -4432]], ![![96772, 4682, 22837, 4060, -15236]], ![![2658, 125, 630, 108, -416]], ![![-74896, -3627, -17671, -3146, 11795]]]
  g := ![![![-79, -9, 392, -453, 708], ![1046, 1046, 254, -85, -2208], ![-120, -292, -1039, 1138, -1076], ![-1748, -1751, -441, 160, 3668], ![-826, -640, 893, -1155, 3183]]]
  hle1 := by decide   
  hle2 := by decide  


def P409P0 : CertificateIrreducibleZModOfList' 409 3 2 8 [95, 65, 253, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [270, 328, 307], [295, 80, 102], [0, 1]]
 g := ![![[277, 7, 349], [337, 30], [143, 80], [300, 82, 100], [275, 387, 245], [26, 250], [248, 205], [1]], ![[315, 251, 118, 162], [347, 9], [129, 363], [66, 376, 345, 200], [127, 56, 88, 242], [21, 355], [220, 90], [57, 227, 294, 147]], ![[284, 185, 170, 6], [241, 379], [333, 36], [205, 334, 389, 68], [394, 243, 367, 109], [206, 391], [300, 213], [395, 405, 396, 262]]]
 h' := ![![[270, 328, 307], [100, 66, 198], [43, 398, 216], [130, 260, 191], [51, 326, 399], [122, 264, 177], [189, 68, 357], [314, 344, 156], [0, 1]], ![[295, 80, 102], [391, 378, 110], [148, 108, 406], [71, 78, 212], [5, 113, 304], [387, 316, 320], [199, 202, 356], [186, 405, 296], [270, 328, 307]], ![[0, 1], [6, 374, 101], [107, 312, 196], [268, 71, 6], [305, 379, 115], [328, 238, 321], [343, 139, 105], [366, 69, 366], [295, 80, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 114], []]
 b := ![[], [171, 193, 362], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N0 : CertifiedPrimeIdeal' SI409N0 409 where
  n := 3
  hpos := by decide
  P := [95, 65, 253, 1]
  hirr := P409P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![165588267, 185721169, 281273224, -15633686, 204599395]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-83306985, -79692926, 1585003, -15633686, 204599395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI409N0 : Ideal.IsPrime I409N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI409N0 B_one_repr
lemma NI409N0 : Nat.card (O ⧸ I409N0) = 68417929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI409N0

def I409N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, -4, -14, -4, 12]] i)))

def SI409N1: IdealEqSpanCertificate' Table ![![-67, -4, -14, -4, 12]] 
 ![![409, 0, 0, 0, 0], ![83, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![227, 0, 0, 1, 0], ![178, 0, 0, 0, 1]] where
  M :=![![![-67, -4, -14, -4, 12], ![8, 3, -6, 6, -8], ![32, -2, 17, -6, 4], ![32, 20, -34, 33, -44], ![8, -4, 14, -8, 9]]]
  hmulB := by decide  
  f := ![![![109, 192, 190, 8, -20]], ![![23, 39, 40, 2, -4]], ![![26, 46, 45, 2, -4]], ![![63, 112, 108, 5, -8]], ![![50, 88, 86, 4, -7]]]
  g := ![![![1, -4, -14, -4, 12], ![1, 3, -6, 6, -8], ![-2, -2, 17, -6, 4], ![5, 20, -34, 33, -44], ![-2, -4, 14, -8, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI409N1 : Nat.card (O ⧸ I409N1) = 409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI409N1)

lemma isPrimeI409N1 : Ideal.IsPrime I409N1 := prime_ideal_of_norm_prime hp409.out _ NI409N1

def I409N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3551, 171, 837, 149, -560]] i)))

def SI409N2: IdealEqSpanCertificate' Table ![![3551, 171, 837, 149, -560]] 
 ![![409, 0, 0, 0, 0], ![332, 1, 0, 0, 0], ![378, 0, 1, 0, 0], ![368, 0, 0, 1, 0], ![151, 0, 0, 0, 1]] where
  M :=![![![3551, 171, 837, 149, -560], ![-480, -28, -117, -21, 72], ![-1644, -84, -391, -70, 256], ![-1920, -123, -477, -86, 280], ![-348, -39, -99, -19, 39]]]
  hmulB := by decide  
  f := ![![![-61, -1569, 27, 259, -16]], ![![-56, -1276, 9, 209, -8]], ![![-54, -1440, 29, 238, -16]], ![![-44, -1407, 45, 236, -24]], ![![-19, -588, 18, 98, -9]]]
  g := ![![![-831, 171, 837, 149, -560], ![122, -28, -117, -21, 72], ![394, -84, -391, -70, 256], ![510, -123, -477, -86, 280], ![125, -39, -99, -19, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI409N2 : Nat.card (O ⧸ I409N2) = 409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI409N2)

lemma isPrimeI409N2 : Ideal.IsPrime I409N2 := prime_ideal_of_norm_prime hp409.out _ NI409N2
def MulI409N0 : IdealMulLeCertificate' Table 
  ![![-793, 1251, -1699, -453, 708]] ![![-67, -4, -14, -4, 12]]
  ![![-61, -1569, 27, 259, -16]] where
 M := ![![![-61, -1569, 27, 259, -16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI409N1 : IdealMulLeCertificate' Table 
  ![![-61, -1569, 27, 259, -16]] ![![3551, 171, 837, 149, -560]]
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

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, 57, 81, 17, 50]] i)))

def SI419N0: IdealEqSpanCertificate' Table ![![-125, 57, 81, 17, 50]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![0, 0, 419, 0, 0], ![0, 0, 0, 419, 0], ![207, 395, 10, 59, 1]] where
  M :=![![![-125, 57, 81, 17, 50], ![248, 202, 265, 97, 236], ![268, 394, 185, 44, 228], ![1848, 2573, 2245, 466, 1272], ![1344, 1757, 1747, 377, 887]]]
  hmulB := by decide  
  f := ![![![-3, 3, -7, 5, -6]], ![![4, -14, 33, -23, 28]], ![![-4, 16, -43, 30, -36]], ![![20, -69, 181, -132, 160]], ![![5, -21, 52, -37, 45]]]
  g := ![![![-25, -47, -1, -7, 50], ![-116, -222, -5, -33, 236], ![-112, -214, -5, -32, 228], ![-624, -1193, -25, -178, 1272], ![-435, -832, -17, -124, 887]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P0 : CertificateIrreducibleZModOfList' 419 4 2 8 [378, 223, 276, 59, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [206, 100, 398, 261], [49, 274, 52, 310], [105, 44, 388, 267], [0, 1]]
 g := ![![[97, 222, 322, 170], [157, 308, 309, 377], [99, 375, 369], [282, 116, 35], [144, 154, 122], [159, 405, 321, 169], [272, 360, 1], []], ![[283, 168, 107, 137, 308, 388], [24, 275, 41, 51, 139, 151], [53, 252, 170], [17, 392, 91], [219, 93, 363], [31, 411, 394, 134, 185, 377], [399, 45, 334], [163, 271, 236, 315, 326, 154]], ![[290, 131, 295, 40, 86, 115], [200, 297, 336, 180, 158, 139], [220, 393, 36], [309, 229, 206], [262, 389, 235], [18, 112, 23, 189, 252, 349], [15, 187, 259], [412, 318, 138, 387, 165, 100]], ![[346, 344, 80, 42, 315, 313], [399, 0, 211, 342, 21, 410], [377, 33, 260], [328, 163, 269], [199, 383, 411], [342, 139, 33, 380, 307, 258], [193, 174, 12], [219, 190, 57, 272, 294, 250]]]
 h' := ![![[206, 100, 398, 261], [152, 399, 141, 111], [72, 365, 180, 193], [56, 209, 209, 61], [324, 48, 399, 354], [234, 365, 16, 125], [258, 194, 138, 13], [0, 0, 0, 1], [0, 1]], ![[49, 274, 52, 310], [3, 126, 257, 199], [20, 378, 291, 114], [400, 403, 116, 308], [125, 224, 165, 133], [153, 356, 81, 319], [255, 292, 318, 116], [198, 225, 127, 119], [206, 100, 398, 261]], ![[105, 44, 388, 267], [39, 41, 26, 385], [197, 220, 342, 276], [298, 114, 105, 6], [306, 322, 189, 25], [36, 286, 133, 167], [284, 229, 233, 281], [42, 66, 46, 241], [49, 274, 52, 310]], ![[0, 1], [272, 272, 414, 143], [75, 294, 25, 255], [408, 112, 408, 44], [309, 244, 85, 326], [207, 250, 189, 227], [303, 123, 149, 9], [108, 128, 246, 58], [105, 44, 388, 267]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [25, 249, 280], []]
 b := ![[], [], [115, 232, 34, 337], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N0 : CertifiedPrimeIdeal' SI419N0 419 where
  n := 4
  hpos := by decide
  P := [378, 223, 276, 59, 1]
  hirr := P419P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![315209856565, 398998132638, 454245547380, 43623654492, 305945806800]
  a := ![21, 37, 37, -19, 92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-150395160265, -287469201798, -6217690980, -42976560732, 305945806800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N0 : Ideal.IsPrime I419N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N0 B_one_repr
lemma NI419N0 : Nat.card (O ⧸ I419N0) = 30821664721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N0

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -3, 7, -5, 6]] i)))

def SI419N1: IdealEqSpanCertificate' Table ![![3, -3, 7, -5, 6]] 
 ![![419, 0, 0, 0, 0], ![364, 1, 0, 0, 0], ![96, 0, 1, 0, 0], ![293, 0, 0, 1, 0], ![175, 0, 0, 0, 1]] where
  M :=![![![3, -3, 7, -5, 6], ![-4, 14, -33, 23, -28], ![4, -16, 43, -30, 36], ![-20, 69, -181, 132, -160], ![4, -21, 47, -35, 43]]]
  hmulB := by decide  
  f := ![![![125, -57, -81, -17, -50]], ![![108, -50, -71, -15, -44]], ![![28, -14, -19, -4, -12]], ![![83, -46, -62, -13, -38]], ![![49, -28, -38, -8, -23]]]
  g := ![![![2, -3, 7, -5, 6], ![-9, 14, -33, 23, -28], ![10, -16, 43, -30, 36], ![-44, 69, -181, 132, -160], ![14, -21, 47, -35, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI419N1 : Nat.card (O ⧸ I419N1) = 419 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI419N1)

lemma isPrimeI419N1 : Ideal.IsPrime I419N1 := prime_ideal_of_norm_prime hp419.out _ NI419N1
def MulI419N0 : IdealMulLeCertificate' Table 
  ![![-125, 57, 81, 17, 50]] ![![3, -3, 7, -5, 6]]
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


lemma PB853I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)

def PB853I8 : PrimesBelowBoundCertificateInterval O 359 419 853 where
  m := 9
  g := ![2, 2, 3, 1, 2, 4, 4, 3, 2]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB853I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0, I367N1]
    · exact ![I373N0, I373N1]
    · exact ![I379N0, I379N1, I379N2]
    · exact ![I383N0]
    · exact ![I389N0, I389N1]
    · exact ![I397N0, I397N1, I397N2, I397N3]
    · exact ![I401N0, I401N1, I401N2, I401N3]
    · exact ![I409N0, I409N1, I409N2]
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
    · exact ![18141126721, 367]
    · exact ![19356878641, 373]
    · exact ![143641, 143641, 379]
    · exact ![8241264822143]
    · exact ![22898045041, 389]
    · exact ![157609, 397, 397, 397]
    · exact ![160801, 401, 401, 401]
    · exact ![68417929, 409, 409]
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
      exact NI401N2
      exact NI401N3
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
      exact NI409N1
      exact NI409N2
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
  β := ![I367N1, I373N1, I379N2, I389N1, I397N1, I397N2, I397N3, I401N1, I401N2, I401N3, I409N1, I409N2, I419N1]
  Il := ![[I367N1], [I373N1], [I379N2], [], [I389N1], [I397N1, I397N2, I397N3], [I401N1, I401N2, I401N3], [I409N1, I409N2], [I419N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
