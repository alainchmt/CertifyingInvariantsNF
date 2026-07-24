
import IdealArithmetic.Examples.NF5_3_42187500_1.RI5_3_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2120, 437, 3, -183, -430]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![2120, 437, 3, -183, -430]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![0, 0, 0, 311, 0], ![24, 127, 277, 208, 1]] where
  M :=![![![2120, 437, 3, -183, -430], ![6633, 1084, 11, -671, -1162], ![5734, 1238, -89, -480, -1342], ![13172, 1852, -104, -1431, -2302], ![11155, 1973, -227, -1081, -2399]]]
  hmulB := by decide  
  f := ![![![36, -13, -9, 3, 2]], ![![-33, 32, -13, -17, 14]], ![![-80, -4, 59, 18, -34]], ![![206, -86, -38, 25, 2]], ![![56, -49, 21, 26, -23]]]
  g := ![![![40, 177, 383, 287, -430], ![111, 478, 1035, 775, -1162], ![122, 552, 1195, 896, -1342], ![220, 946, 2050, 1535, -2302], ![221, 986, 2136, 1601, -2399]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 4 2 8 [101, 295, 303, 41, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 20, 21, 17], [16, 283, 53, 118], [140, 7, 237, 176], [0, 1]]
 g := ![![[276, 298, 203, 120], [219, 146, 140, 21], [161, 228, 92, 113], [171, 14, 208], [231, 182, 136, 175], [19, 236, 87, 126], [1], []], ![[55, 184, 278, 305, 180, 269], [283, 122, 94, 33, 164, 220], [208, 129, 279, 22, 300, 227], [194, 85, 54], [182, 299, 131, 107, 73, 276], [8, 153, 199, 152, 157, 17], [219, 294, 47], [310, 61, 289]], ![[7, 30, 106, 25, 44, 194], [160, 300, 113, 77, 141, 69], [25, 299, 301, 264, 124, 247], [175, 143, 3], [91, 133, 69, 108, 248, 298], [189, 72, 254, 68, 87, 246], [52, 45, 135], [71, 180, 240]], ![[85, 238, 215, 266, 12, 204], [40, 33, 216, 46, 199, 191], [79, 149, 262, 287, 222, 298], [103, 294, 42], [248, 93, 29, 293, 206, 99], [19, 74, 50, 264, 46, 46], [284, 92, 256], [26, 184, 187]]]
 h' := ![![[114, 20, 21, 17], [273, 100, 204, 149], [222, 180, 276, 79], [181, 164, 275, 51], [305, 252, 256, 239], [258, 42, 306, 233], [210, 16, 8, 270], [0, 0, 1], [0, 1]], ![[16, 283, 53, 118], [145, 287, 279, 20], [93, 282, 258, 209], [192, 48, 181, 76], [82, 248, 201, 285], [110, 195, 135, 41], [254, 259, 180, 1], [35, 249, 292, 228], [114, 20, 21, 17]], ![[140, 7, 237, 176], [237, 154, 288, 31], [237, 261, 206, 67], [131, 158, 72, 258], [214, 162, 279, 25], [202, 71, 290, 114], [77, 17, 100, 35], [238, 98, 37, 67], [16, 283, 53, 118]], ![[0, 1], [280, 81, 162, 111], [107, 210, 193, 267], [0, 252, 94, 237], [105, 271, 197, 73], [22, 3, 202, 234], [295, 19, 23, 5], [180, 275, 292, 16], [140, 7, 237, 176]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [48, 226, 159], []]
 b := ![[], [], [183, 61, 53, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 4
  hpos := by decide
  P := [101, 295, 303, 41, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20726097083, -4975153504, 1567140032, 1613932064, 7800237728]
  a := ![15, -20, -8, 12, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-668591005, -3201303360, -6942439584, -5211689760, 7800237728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 9354951841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, 13, 9, -3, -2]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![-36, 13, 9, -3, -2]] 
 ![![311, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![237, 0, 1, 0, 0], ![242, 0, 0, 1, 0], ![283, 0, 0, 0, 1]] where
  M :=![![![-36, 13, 9, -3, -2], ![33, -32, 13, 17, -14], ![80, 4, -59, -18, 34], ![-206, 86, 38, -25, -2], ![-55, -5, 41, 13, -23]]]
  hmulB := by decide  
  f := ![![![-2120, -437, -3, 183, 430]], ![![-703, -144, -1, 61, 142]], ![![-1634, -337, -2, 141, 332]], ![![-1692, -346, -2, 147, 342]], ![![-1965, -404, -2, 170, 399]]]
  g := ![![![-7, 13, 9, -3, -2], ![0, -32, 13, 17, -14], ![27, 4, -59, -18, 34], ![-36, 86, 38, -25, -2], ![-19, -5, 41, 13, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![2120, 437, 3, -183, -430]] ![![-36, 13, 9, -3, -2]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![-311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4668, -497, 228, 565, 990]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![-4668, -497, 228, 565, 990]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![203, 12, 289, 1, 0], ![139, 201, 31, 0, 1]] where
  M :=![![![-4668, -497, 228, 565, 990], ![-15415, -1630, 758, 1871, 3250], ![-17603, -1897, 862, 2137, 3742], ![-37935, -4017, 1845, 4604, 8016], ![-38008, -4046, 1867, 4604, 8047]]]
  hmulB := by decide  
  f := ![![![313, 78, 17, -22, -56]], ![![862, 201, 27, -56, -144]], ![![677, 187, 30, -61, -112]], ![![865, 232, 40, -73, -146]], ![![763, 183, 28, -52, -129]]]
  g := ![![![-821, -659, -619, 565, 990], ![-2706, -2164, -2047, 1871, 3250], ![-3104, -2491, -2341, 2137, 3742], ![-6667, -5337, -5039, 4604, 8016], ![-6681, -5357, -5042, 4604, 8047]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 3 2 8 [8, 266, 188, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [282, 9, 5], [156, 303, 308], [0, 1]]
 g := ![![[43, 69, 8], [282, 155], [143, 119], [152, 33, 50], [125, 188, 255], [44, 14, 171], [125, 1], []], ![[91, 104, 239, 59], [110, 163], [238, 200], [131, 257, 62, 186], [119, 6, 254, 273], [293, 141, 46, 180], [31, 100], [85, 25]], ![[192, 208, 110, 188], [65, 35], [294, 25], [243, 118, 20, 46], [71, 63, 23, 136], [19, 299, 93, 149], [61, 81], [95, 25]]]
 h' := ![![[282, 9, 5], [190, 120, 240], [152, 0, 74], [36, 272, 256], [252, 258, 287], [274, 43, 152], [252, 233, 22], [0, 0, 1], [0, 1]], ![[156, 303, 308], [58, 155, 78], [288, 93, 199], [1, 105, 52], [285, 166, 298], [24, 62, 260], [150, 69, 6], [281, 107, 303], [282, 9, 5]], ![[0, 1], [269, 38, 308], [114, 220, 40], [90, 249, 5], [1, 202, 41], [111, 208, 214], [10, 11, 285], [101, 206, 9], [156, 303, 308]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 143], []]
 b := ![[], [105, 184, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 3
  hpos := by decide
  P := [8, 266, 188, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32437657775, 5489216253, -3136032625, -4011410055, -9047897433]
  a := ![120, -180, -58, 54, -477]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6723359879, 5981640642, 4589924261, -4011410055, -9047897433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 30664297 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -1, 1, 1, 0]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![-4, -1, 1, 1, 0]] 
 ![![313, 0, 0, 0, 0], ![176, 1, 0, 0, 0], ![74, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![285, 0, 0, 0, 1]] where
  M :=![![![-4, -1, 1, 1, 0], ![-1, -4, -3, 1, 4], ![-30, 6, 3, 0, 2], ![-30, -6, 8, 5, 2], ![-17, -7, -1, 5, 5]]]
  hmulB := by decide  
  f := ![![![-836, -189, -37, 65, 140]], ![![-477, -108, -21, 37, 80]], ![![-204, -46, -9, 16, 34]], ![![-272, -62, -12, 21, 46]], ![![-771, -174, -34, 60, 129]]]
  g := ![![![0, -1, 1, 1, 0], ![-1, -4, -3, 1, 4], ![-6, 6, 3, 0, 2], ![-2, -6, 8, 5, 2], ![-2, -7, -1, 5, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 21, -12, -13, 12]] i)))

def SI313N2: IdealEqSpanCertificate' Table ![![-16, 21, -12, -13, 12]] 
 ![![313, 0, 0, 0, 0], ![185, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![175, 0, 0, 0, 1]] where
  M :=![![![-16, 21, -12, -13, 12], ![-167, 28, 78, 13, -40], ![377, -137, -90, 25, 26], ![-19, 103, -111, -64, 76], ![-236, 86, 67, -24, -13]]]
  hmulB := by decide  
  f := ![![![91449, 9920, -4355, -11028, -19290]], ![![55011, 5967, -2620, -6634, -11604]], ![![4019, 435, -192, -485, -848]], ![![7904, 855, -378, -954, -1668]], ![![53486, 5799, -2549, -6451, -11283]]]
  g := ![![![-18, 21, -12, -13, 12], ![2, 28, 78, 13, -40], ![69, -137, -90, 25, 26], ![-96, 103, -111, -64, 76], ![-45, 86, 67, -24, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N2 : Nat.card (O ⧸ I313N2) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N2)

lemma isPrimeI313N2 : Ideal.IsPrime I313N2 := prime_ideal_of_norm_prime hp313.out _ NI313N2
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![-4668, -497, 228, 565, 990]] ![![-4, -1, 1, 1, 0]]
  ![![-21451, -2296, 1037, 2610, 4548]] where
 M := ![![![-21451, -2296, 1037, 2610, 4548]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N1 : IdealMulLeCertificate' Table 
  ![![-21451, -2296, 1037, 2610, 4548]] ![![-16, 21, -12, -13, 12]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-5321, 3130, 0, -1252, 626]]]
 hmul := by decide  
 g := ![![![![-17, 10, 0, -4, 2]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1, I313N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
    exact isPrimeI313N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0 ⊙ MulI313N1)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1385, 336, 45, -102, -252]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![1385, 336, 45, -102, -252]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![101, 66, 12, 1, 0], ![53, 138, 278, 0, 1]] where
  M :=![![![1385, 336, 45, -102, -252], ![3882, 863, 123, -312, -660], ![3165, 795, 80, -225, -624], ![6375, 1329, 171, -544, -1074], ![5133, 1185, 108, -399, -979]]]
  hmulB := by decide  
  f := ![![![-38, 39, -18, -21, 18]], ![![-249, 34, 132, 21, -66]], ![![609, -213, -164, 45, 42]], ![![-41, 12, 15, -1, -6]], ![![418, -165, -89, 45, 11]]]
  g := ![![![79, 132, 225, -102, -252], ![222, 355, 591, -312, -660], ![186, 321, 556, -225, -624], ![373, 585, 963, -544, -1074], ![307, 513, 874, -399, -979]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [102, 83, 231, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [147, 61, 123], [256, 255, 194], [0, 1]]
 g := ![![[213, 296, 82], [110, 95], [249, 228, 148], [143, 245, 234], [27, 15, 96], [4, 122, 167], [86, 1], []], ![[131, 192, 28, 173], [175, 218], [211, 24, 180, 156], [48, 222, 75, 144], [89, 90, 104, 34], [287, 286, 250, 34], [71, 40], [233, 230]], ![[249, 136, 285, 247], [222, 141], [155, 85, 35, 92], [287, 228, 56, 182], [226, 298, 247, 260], [220, 63, 144, 292], [310, 234], [162, 230]]]
 h' := ![![[147, 61, 123], [51, 73, 84], [279, 156, 27], [313, 204, 103], [99, 72, 256], [226, 259, 276], [104, 51, 22], [0, 0, 1], [0, 1]], ![[256, 255, 194], [140, 68, 284], [159, 57, 79], [232, 29, 3], [244, 191, 275], [253, 259, 163], [89, 53, 154], [62, 178, 255], [147, 61, 123]], ![[0, 1], [165, 176, 266], [122, 104, 211], [243, 84, 211], [40, 54, 103], [248, 116, 195], [310, 213, 141], [194, 139, 61], [256, 255, 194]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 34], []]
 b := ![[], [119, 239, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [102, 83, 231, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8720862, 3276852, -38328, -1580075, -2822679]
  a := ![11, -15, -5, 6, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1002872, 1568112, 2535102, -1580075, -2822679]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, -39, 18, 21, -18]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![38, -39, 18, 21, -18]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![5, 147, 1, 0, 0], ![60, 255, 0, 1, 0], ![249, 24, 0, 0, 1]] where
  M :=![![![38, -39, 18, 21, -18], ![249, -34, -132, -21, 66], ![-609, 213, 164, -45, -42], ![33, -177, 171, 122, -132], ![420, -150, -117, 30, 35]]]
  hmulB := by decide  
  f := ![![![-1385, -336, -45, 102, 252]], ![![-3882, -863, -123, 312, 660]], ![![-1832, -408, -58, 147, 312]], ![![-3405, -762, -108, 272, 582]], ![![-1398, -333, -45, 105, 251]]]
  g := ![![![10, -24, 18, 21, -18], ![-45, 73, -132, -21, 66], ![37, -36, 164, -45, -42], ![78, -168, 171, 122, -132], ![-30, 27, -117, 30, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P1 : CertificateIrreducibleZModOfList' 317 2 2 8 [306, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [276, 316], [0, 1]]
 g := ![![[198, 144], [316], [282, 259], [265, 253], [278, 252], [205, 232], [96], [1]], ![[0, 173], [316], [124, 58], [36, 64], [90, 65], [203, 85], [96], [1]]]
 h' := ![![[276, 316], [175, 12], [249, 203], [62, 24], [205, 278], [36, 209], [226, 234], [11, 276], [0, 1]], ![[0, 1], [0, 305], [168, 114], [29, 293], [219, 39], [26, 108], [142, 83], [107, 41], [276, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163]]
 b := ![[], [165, 240]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N1 : CertifiedPrimeIdeal' SI317N1 317 where
  n := 2
  hpos := by decide
  P := [306, 41, 1]
  hirr := P317P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1193315, -89693, 231398, 81161, 364172]
  a := ![-52, 75, 27, -35, 209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-308829, -200446, 231398, 81161, 364172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N1 B_one_repr
lemma NI317N1 : Nat.card (O ⧸ I317N1) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N1
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![1385, 336, 45, -102, -252]] ![![38, -39, 18, 21, -18]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![-317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0)


lemma PB318I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 317 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 317 (by omega)

def PB318I7 : PrimesBelowBoundCertificateInterval O 307 317 318 where
  m := 3
  g := ![2, 3, 2]
  P := ![311, 313, 317]
  hP := PB318I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1, I313N2]
    · exact ![I317N0, I317N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
    · exact PBC317
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![9354951841, 311]
    · exact ![30664297, 313, 313]
    · exact ![31855013, 100489]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
      exact NI313N2
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
  β := ![I311N1, I313N1, I313N2]
  Il := ![[I311N1], [I313N1, I313N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
