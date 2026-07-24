
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-771, 5402, -967, 181, -708]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![-771, 5402, -967, 181, -708]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![0, 0, 0, 311, 0], ![150, 118, 268, 110, 1]] where
  M :=![![![-771, 5402, -967, 181, -708], ![-362, 2423, -427, 87, -330], ![-174, 1132, -286, 59, -138], ![-118, 496, 67, -128, 78], ![-46, 478, 121, -13, -133]]]
  hmulB := by decide  
  f := ![![![7, -14, -3, -1, 0]], ![![2, 5, -17, -1, -6]], ![![2, 24, -52, -3, -18]], ![![6, 68, -147, -10, -54]], ![![8, 40, -105, -7, -37]]]
  g := ![![![339, 286, 607, 251, -708], ![158, 133, 283, 117, -330], ![66, 56, 118, 49, -138], ![-38, -28, -67, -28, 78], ![64, 52, 115, 47, -133]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 4 2 8 [16, 50, 41, 198, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 262, 63, 199], [110, 294, 174, 8], [144, 65, 74, 104], [0, 1]]
 g := ![![[106, 237], [27, 74, 35, 277], [273, 308, 151, 294], [98, 98, 229], [299, 212, 64, 28], [109, 309, 232, 18], [1], []], ![[216, 226, 224, 229, 178, 295], [150, 64, 263, 240, 237, 152], [258, 255, 34, 161, 127, 310], [111, 92, 2], [124, 48, 259, 260, 57, 206], [132, 174, 4, 129, 114, 248], [2, 183, 201], [265, 128, 104]], ![[276, 256, 271, 289, 49, 27], [200, 26, 242, 204, 111, 268], [48, 86, 209, 85, 186, 73], [180, 57, 126], [166, 14, 141, 89, 111, 229], [310, 277, 98, 224, 51, 173], [87, 80, 64], [91, 64, 64]], ![[173, 6, 57, 61, 261, 294], [28, 198, 119, 15, 158, 8], [78, 241, 303, 174, 11, 252], [66, 83, 235], [12, 98, 172, 162, 75, 89], [184, 57, 122, 231, 162, 197], [137, 131, 163], [241, 131, 242]]]
 h' := ![![[170, 262, 63, 199], [190, 150, 248], [297, 166, 42, 272], [153, 161, 41, 268], [192, 274, 86, 134], [122, 125, 50, 280], [295, 261, 270, 113], [0, 0, 1], [0, 1]], ![[110, 294, 174, 8], [53, 54, 125, 20], [187, 101, 109, 86], [270, 27, 239, 306], [231, 265, 277, 66], [142, 88, 175, 187], [163, 48, 281, 234], [91, 75, 227, 123], [170, 262, 63, 199]], ![[144, 65, 74, 104], [151, 174, 116, 149], [298, 75, 175, 74], [79, 125, 192, 211], [212, 309, 66, 41], [59, 5, 169, 277], [87, 31, 131, 52], [70, 16, 136, 303], [110, 294, 174, 8]], ![[0, 1], [200, 244, 133, 142], [212, 280, 296, 190], [203, 309, 150, 148], [126, 85, 193, 70], [92, 93, 228, 189], [228, 282, 251, 223], [86, 220, 258, 196], [144, 65, 74, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [21, 5, 264], []]
 b := ![[], [], [209, 301, 131, 278], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 4
  hpos := by decide
  P := [16, 50, 41, 198, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-925051732, 3502809706, -4265633440, 86560432, 1595880264]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-772691612, -594247786, -1388943872, -564180928, 1595880264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 9354951841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 14, 3, 1, 0]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![-7, 14, 3, 1, 0]] 
 ![![311, 0, 0, 0, 0], ![271, 1, 0, 0, 0], ![266, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-7, 14, 3, 1, 0], ![-2, -5, 17, 1, 6], ![-2, -24, 52, 3, 18], ![-6, -68, 147, 10, 54], ![-6, -38, 93, 5, 35]]]
  hmulB := by decide  
  f := ![![![771, -5402, 967, -181, 708]], ![![673, -4715, 844, -158, 618]], ![![660, -4624, 828, -155, 606]], ![![164, -1148, 205, -38, 150]], ![![77, -540, 96, -18, 71]]]
  g := ![![![-15, 14, 3, 1, 0], ![-11, -5, 17, 1, 6], ![-26, -24, 52, 3, 18], ![-74, -68, 147, 10, 54], ![-51, -38, 93, 5, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![-771, 5402, -967, 181, -708]] ![![-7, 14, 3, 1, 0]]
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

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -95, 76, 41, -70]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![33, -95, 76, 41, -70]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![144, 203, 183, 1, 0], ![142, 4, 200, 0, 1]] where
  M :=![![![33, -95, 76, 41, -70], ![-82, 395, -602, 134, 106], ![-268, -238, 1751, -1082, 1016], ![2164, -6496, 5660, 1883, -4460], ![266, 1752, -5594, 2940, -1657]]]
  hmulB := by decide  
  f := ![![![-76237, 196379, -33598, 7525, -25072]], ![![-15050, 39101, -6694, 1496, -4994]], ![![-2992, 7918, -1357, 302, -1012]], ![![-46586, 120341, -20593, 4609, -15366]], ![![-36752, 94808, -16222, 3632, -12105]]]
  g := ![![![13, -26, 21, 41, -70], ![-110, -87, -148, 134, 106], ![36, 688, -11, -1082, 1016], ![1164, -1185, 1767, 1883, -4460], ![-600, -1880, -678, 2940, -1657]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 3 2 8 [155, 231, 281, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 169, 271], [216, 143, 42], [0, 1]]
 g := ![![[86, 293, 58], [219, 75], [17, 302], [161, 251, 241], [228, 214, 208], [20, 289, 32], [32, 1], []], ![[35, 206, 145, 141], [167, 286], [147, 291], [90, 297, 7, 5], [291, 75, 288, 59], [40, 13, 137, 145], [128, 104], [310, 199]], ![[35, 256, 245, 290], [260, 107], [259, 103], [184, 205, 7, 236], [299, 145, 214, 266], [39, 311, 26, 61], [217, 78], [226, 199]]]
 h' := ![![[129, 169, 271], [242, 249, 44], [208, 181, 211], [85, 178, 176], [29, 198, 159], [30, 152, 55], [48, 278, 167], [0, 0, 1], [0, 1]], ![[216, 143, 42], [23, 56, 216], [245, 207, 35], [107, 15, 164], [102, 105, 23], [184, 153, 229], [179, 94, 311], [204, 304, 143], [129, 169, 271]], ![[0, 1], [292, 8, 53], [284, 238, 67], [129, 120, 286], [185, 10, 131], [281, 8, 29], [3, 254, 148], [45, 9, 169], [216, 143, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [200, 41], []]
 b := ![[], [211, 201, 232], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 3
  hpos := by decide
  P := [155, 231, 281, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1728829, -3934617, 2580973, 2223405, -4143441]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![862387, -1401636, 1355866, 2223405, -4143441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 30664297 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![76237, -196379, 33598, -7525, 25072]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![76237, -196379, 33598, -7525, 25072]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![113, 130, 1, 0, 0], ![21, 115, 0, 1, 0], ![184, 146, 0, 0, 1]] where
  M :=![![![76237, -196379, 33598, -7525, 25072], ![15050, -39101, 6694, -1496, 4994], ![2992, -7918, 1357, -302, 1012], ![604, -1660, 284, -63, 212], ![19122, -49082, 8394, -1882, 6265]]]
  hmulB := by decide  
  f := ![![![-33, 95, -76, -41, 70]], ![![82, -395, 602, -134, -106]], ![![23, -129, 217, -67, -22]], ![![21, -118, 198, -58, -20]], ![![18, -134, 254, -96, -3]]]
  g := ![![![-26120, -23512, 33598, -7525, 25072], ![-5204, -4685, 6694, -1496, 4994], ![-1055, -950, 1357, -302, 1012], ![-221, -199, 284, -63, 212], ![-6526, -5874, 8394, -1882, 6265]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P1 : CertificateIrreducibleZModOfList' 313 2 2 8 [118, 296, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 312], [0, 1]]
 g := ![![[98, 305], [301], [194], [266, 169], [37, 83], [275, 192], [289], [1]], ![[275, 8], [301], [194], [9, 144], [196, 230], [96, 121], [289], [1]]]
 h' := ![![[17, 312], [203, 53], [189, 81], [225, 173], [16, 300], [102, 205], [167, 275], [195, 17], [0, 1]], ![[0, 1], [165, 260], [1, 232], [36, 140], [108, 13], [144, 108], [147, 38], [171, 296], [17, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [260]]
 b := ![[], [147, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N1 : CertifiedPrimeIdeal' SI313N1 313 where
  n := 2
  hpos := by decide
  P := [118, 296, 1]
  hirr := P313P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![389, -992, 26, -88, -458]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![267, 232, 26, -88, -458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N1 B_one_repr
lemma NI313N1 : Nat.card (O ⧸ I313N1) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N1
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![33, -95, 76, 41, -70]] ![![76237, -196379, 33598, -7525, 25072]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, 246, -98, 14, 8]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![-91, 246, -98, 14, 8]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![0, 0, 0, 317, 0], ![266, 110, 67, 81, 1]] where
  M :=![![![-91, 246, -98, 14, 8], ![-28, -95, 360, -142, 100], ![284, -712, 379, 444, -652], ![-888, 3780, -5248, 795, 1360], ![-724, 940, 976, -1498, 1997]]]
  hmulB := by decide  
  f := ![![![1817, -11646, 2086, -398, 1528]], ![![796, -5091, 912, -174, 668]], ![![348, -2224, 399, -76, 292]], ![![152, -972, 176, -33, 128]], ![![1914, -12262, 2197, -419, 1609]]]
  g := ![![![-7, -2, -2, -2, 8], ![-84, -35, -20, -26, 100], ![548, 224, 139, 168, -652], ![-1144, -460, -304, -345, 1360], ![-1678, -690, -419, -515, 1997]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 4 2 8 [170, 272, 311, 69, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [309, 228, 35, 171], [151, 37, 40, 137], [105, 51, 242, 9], [0, 1]]
 g := ![![[235, 161, 54, 100], [227, 311, 306], [23, 303, 14, 217], [71, 290, 136, 260], [247, 262, 220, 77], [183, 310, 26, 6], [1], []], ![[177, 183, 81, 300, 170, 224], [141, 155, 142], [36, 196, 78, 201, 150, 5], [114, 47, 67, 135, 168, 98], [74, 257, 272, 33, 101, 255], [254, 30, 194, 280, 19, 50], [103, 292, 218], [96, 0, 77]], ![[128, 72, 233, 190, 92, 190], [256, 62, 213], [75, 72, 277, 112, 239, 303], [119, 185, 63, 184, 250, 226], [4, 271, 52, 11, 99, 201], [162, 154, 309, 100, 216, 62], [124, 23, 66], [289, 66, 66]], ![[170, 167, 207, 169, 291, 136], [54, 303, 281], [176, 168, 95, 257, 90, 61], [20, 184, 41, 117, 132, 218], [195, 263, 279, 172, 20, 266], [244, 146, 171, 81, 63, 124], [167, 155, 57], [176, 35, 81]]]
 h' := ![![[309, 228, 35, 171], [225, 121, 1, 307], [211, 187, 152, 132], [293, 254, 69, 189], [171, 211, 244, 102], [273, 285, 83, 146], [147, 45, 6, 248], [0, 0, 1], [0, 1]], ![[151, 37, 40, 137], [225, 254, 313, 219], [145, 95, 47, 116], [7, 164, 228, 184], [285, 174, 298, 124], [90, 0, 115, 282], [238, 219, 168, 315], [228, 38, 236, 238], [309, 228, 35, 171]], ![[105, 51, 242, 9], [95, 256, 229, 243], [249, 313, 74, 119], [291, 213, 189, 235], [284, 55, 36, 223], [53, 181, 224, 216], [166, 185, 136, 64], [299, 279, 276, 180], [151, 37, 40, 137]], ![[0, 1], [260, 3, 91, 182], [105, 39, 44, 267], [197, 3, 148, 26], [109, 194, 56, 185], [91, 168, 212, 307], [232, 185, 7, 7], [125, 0, 121, 216], [105, 51, 242, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [257, 5, 148], []]
 b := ![[], [], [246, 48, 308, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 4
  hpos := by decide
  P := [170, 272, 311, 69, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11419027492, 38134405875, -40596992555, -3205957420, 21965987585]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18468049606, -7501969175, -4770719750, -5622873665, 21965987585]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 10098039121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1817, 11646, -2086, 398, -1528]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![-1817, 11646, -2086, 398, -1528]] 
 ![![317, 0, 0, 0, 0], ![146, 1, 0, 0, 0], ![240, 0, 1, 0, 0], ![147, 0, 0, 1, 0], ![107, 0, 0, 0, 1]] where
  M :=![![![-1817, 11646, -2086, 398, -1528], ![-796, 5091, -912, 174, -668], ![-348, 2224, -399, 76, -292], ![-152, 972, -176, 33, -128], ![-228, 1468, -264, 50, -193]]]
  hmulB := by decide  
  f := ![![![91, -246, 98, -14, -8]], ![![42, -113, 44, -6, -4]], ![![68, -184, 73, -12, -4]], ![![45, -126, 62, -9, -8]], ![![33, -86, 30, 0, -9]]]
  g := ![![![-3459, 11646, -2086, 398, -1528], ![-1512, 5091, -912, 174, -668], ![-660, 2224, -399, 76, -292], ![-287, 972, -176, 33, -128], ![-435, 1468, -264, 50, -193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N1 : Nat.card (O ⧸ I317N1) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N1)

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := prime_ideal_of_norm_prime hp317.out _ NI317N1
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![-91, 246, -98, 14, 8]] ![![-1817, 11646, -2086, 398, -1528]]
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
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![128475, -835685, 169835, -26974, 116214]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![128475, -835685, 169835, -26974, 116214]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![0, 0, 0, 331, 0], ![192, 93, 11, 306, 1]] where
  M :=![![![128475, -835685, 169835, -26974, 116214], ![53948, -390329, 129319, -8645, 70584], ![17290, -245678, 218992, 5441, 89298], ![-10882, -329020, 574327, 29514, 211242], ![2732, -268090, 372235, 16477, 140903]]]
  hmulB := by decide  
  f := ![![![19, -85, 85, -50, 48]], ![![100, -273, 197, 89, -204]], ![![-178, 1094, -1842, 427, 126]], ![![-854, 172, 3509, -2948, 2814]], ![![-754, 59, 3302, -2717, 2573]]]
  g := ![![![-67023, -35177, -3349, -107518, 116214], ![-40780, -21011, -1955, -65279, 70584], ![-51746, -25832, -2306, -82537, 89298], ![-122566, -60346, -5285, -195198, 211242], ![-81724, -40399, -3558, -130211, 140903]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 4 2 8 [90, 282, 1, 273, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [220, 7, 102, 69], [239, 281, 290, 285], [261, 42, 270, 308], [0, 1]]
 g := ![![[255, 150, 317, 203], [75, 154, 228, 143], [182, 2, 172], [45, 270, 3, 105], [138, 42, 216], [54, 109, 161], [58, 1], []], ![[259, 65, 251, 114, 301, 144], [76, 297, 240, 136, 26, 195], [166, 114, 146], [114, 148, 242, 277, 89, 118], [194, 173, 143], [144, 68, 214], [312, 147, 119, 251, 117, 291], [58, 258, 127]], ![[72, 54, 208, 301, 254, 93], [33, 326, 86, 259, 108, 90], [176, 243, 14], [61, 306, 117, 309, 35, 75], [256, 41, 276], [35, 201, 131], [220, 240, 116, 108, 189, 42], [247, 58, 130]], ![[87, 95, 126, 17, 75, 143], [151, 202, 214, 161, 100, 163], [229, 2, 196], [206, 196, 254, 63, 7, 64], [320, 228, 239], [293, 156, 9], [87, 225, 173, 175, 55, 324], [263, 57, 198]]]
 h' := ![![[220, 7, 102, 69], [201, 308, 31, 269], [296, 286, 231, 229], [253, 173, 324, 145], [129, 109, 147, 84], [254, 38, 245, 215], [76, 104, 322, 53], [0, 0, 1], [0, 1]], ![[239, 281, 290, 285], [212, 87, 237, 133], [305, 170, 284, 276], [130, 294, 121, 198], [295, 61, 303, 110], [132, 205, 327, 229], [281, 4, 144, 187], [150, 245, 74, 73], [220, 7, 102, 69]], ![[261, 42, 270, 308], [158, 125, 257, 151], [112, 204, 179, 231], [8, 220, 221, 305], [98, 313, 71, 96], [31, 284, 119, 40], [99, 39, 257, 88], [136, 195, 277, 102], [239, 281, 290, 285]], ![[0, 1], [312, 142, 137, 109], [0, 2, 299, 257], [95, 306, 327, 14], [50, 179, 141, 41], [265, 135, 302, 178], [174, 184, 270, 3], [97, 222, 310, 156], [261, 42, 270, 308]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [114, 261, 27], []]
 b := ![[], [], [295, 157, 235, 310], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 4
  hpos := by decide
  P := [90, 282, 1, 273, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26625201394, 76127387251, -62665430233, -22034553180, 56736355063]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32990952790, -15711038168, -2074819746, -52517701518, 56736355063]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 12003612721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -85, 85, -50, 48]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![19, -85, 85, -50, 48]] 
 ![![331, 0, 0, 0, 0], ![148, 1, 0, 0, 0], ![273, 0, 1, 0, 0], ![309, 0, 0, 1, 0], ![294, 0, 0, 0, 1]] where
  M :=![![![19, -85, 85, -50, 48], ![100, -273, 197, 89, -204], ![-178, 1094, -1842, 427, 126], ![-854, 172, 3509, -2948, 2814], ![760, -3428, 4829, -613, -1051]]]
  hmulB := by decide  
  f := ![![![128475, -835685, 169835, -26974, 116214]], ![![57608, -374839, 76329, -12087, 52176]], ![![106015, -689993, 140737, -22231, 96120]], ![![119903, -781135, 160282, -25092, 109128]], ![![114122, -743080, 151975, -23909, 103649]]]
  g := ![![![-28, -85, 85, -50, 48], ![58, -273, 197, 89, -204], ![519, 1094, -1842, 427, 126], ![-2721, 172, 3509, -2948, 2814], ![-942, -3428, 4829, -613, -1051]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N1 : Nat.card (O ⧸ I331N1) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N1)

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := prime_ideal_of_norm_prime hp331.out _ NI331N1
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![128475, -835685, 169835, -26974, 116214]] ![![19, -85, 85, -50, 48]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC331 : ContainsPrimesAboveP 331 ![I331N0, I331N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
    exact isPrimeI331N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 331 (by decide) (𝕀 ⊙ MulI331N0)
instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90379, -579163, 106562, -19575, 76908]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![90379, -579163, 106562, -19575, 76908]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![0, 0, 0, 337, 0], ![43, 133, 235, 23, 1]] where
  M :=![![![90379, -579163, 106562, -19575, 76908], ![39150, -256403, 54284, -8104, 36366], ![16208, -122522, 46579, -2240, 24108], ![4480, -84704, 87730, 2843, 34776], ![9518, -96050, 62848, 326, 27487]]]
  hmulB := by decide  
  f := ![![![121, -309, 56, -7, 30]], ![![14, -13, -60, 10, 18]], ![![-20, -38, 179, -116, 96]], ![![232, -636, 478, 219, -504]], ![![23, -114, 139, -62, 43]]]
  g := ![![![-9545, -32071, -53314, -5307, 76908], ![-4524, -15113, -25198, -2506, 36366], ![-3028, -9878, -16673, -1652, 24108], ![-4424, -13976, -23990, -2365, 34776], ![-3479, -11133, -18981, -1875, 27487]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 4 2 8 [209, 91, 44, 300, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [304, 13, 217, 73], [19, 47, 111, 267], [51, 276, 9, 334], [0, 1]]
 g := ![![[213, 100, 182, 209], [298, 16, 110], [34, 158, 167], [183, 151, 158], [4, 271, 217, 48], [54, 243, 192], [37, 1], []], ![[290, 36, 204, 197, 192, 286], [167, 218, 312], [230, 286, 155], [83, 232, 190], [53, 169, 299, 287, 71, 276], [55, 308, 182], [188, 89, 192, 327, 25, 157], [34, 32, 274]], ![[241, 266, 147, 254, 189, 238], [316, 132, 288], [107, 265, 55], [316, 180, 237], [304, 264, 96, 319, 268, 161], [126, 76, 296], [47, 62, 329, 134, 86, 59], [149, 293, 182]], ![[292, 152, 83, 83, 144, 331], [274, 243, 7], [170, 151, 170], [5, 191, 28], [178, 136, 26, 307, 225, 84], [215, 129, 263], [39, 31, 240, 327, 82, 167], [264, 279, 9]]]
 h' := ![![[304, 13, 217, 73], [91, 158, 214, 117], [99, 284, 277, 309], [129, 81, 98, 308], [175, 293, 83, 256], [159, 239, 185, 157], [18, 131, 303, 314], [0, 0, 1], [0, 1]], ![[19, 47, 111, 267], [273, 213, 171, 202], [129, 252, 336, 271], [285, 90, 41, 250], [67, 185, 50, 114], [328, 301, 249, 127], [99, 260, 147, 267], [49, 144, 335, 4], [304, 13, 217, 73]], ![[51, 276, 9, 334], [108, 85, 32, 329], [10, 176, 197, 312], [145, 267, 117, 27], [275, 36, 67, 205], [127, 248, 204, 214], [258, 141, 326, 188], [224, 119, 211, 9], [19, 47, 111, 267]], ![[0, 1], [279, 218, 257, 26], [167, 299, 201, 119], [66, 236, 81, 89], [327, 160, 137, 99], [334, 223, 36, 176], [59, 142, 235, 242], [334, 74, 127, 324], [51, 276, 9, 334]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [225, 142, 336], []]
 b := ![[], [], [292, 254, 196, 207], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 4
  hpos := by decide
  P := [209, 91, 44, 300, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2435629489, -13836728510, 44834848750, -22526138672, 14296992390]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1831472707, -5683491740, -9836671700, -1042602266, 14296992390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 12897917761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, -309, 56, -7, 30]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![121, -309, 56, -7, 30]] 
 ![![337, 0, 0, 0, 0], ![197, 1, 0, 0, 0], ![283, 0, 1, 0, 0], ![191, 0, 0, 1, 0], ![325, 0, 0, 0, 1]] where
  M :=![![![121, -309, 56, -7, 30], ![14, -13, -60, 10, 18], ![-20, -38, 179, -116, 96], ![232, -636, 478, 219, -504], ![50, 156, -644, 300, -161]]]
  hmulB := by decide  
  f := ![![![90379, -579163, 106562, -19575, 76908]], ![![52949, -339322, 62454, -11467, 45066]], ![![75945, -486723, 89625, -16445, 64656]], ![![51237, -328501, 60656, -11086, 43692]], ![![87189, -558825, 102954, -18877, 74251]]]
  g := ![![![109, -309, 56, -7, 30], ![35, -13, -60, 10, 18], ![-155, -38, 179, -116, 96], ![333, -636, 478, 219, -504], ![435, 156, -644, 300, -161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![90379, -579163, 106562, -19575, 76908]] ![![121, -309, 56, -7, 30]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 154, 12, 50]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-1, 2, 154, 12, 50]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![29, 255, 1, 0, 0], ![239, 240, 0, 1, 0], ![235, 87, 0, 0, 1]] where
  M :=![![![-1, 2, 154, 12, 50], ![-24, -177, 488, 30, 172], ![-60, -652, 1461, 84, 524], ![-168, -1988, 4316, 245, 1552], ![-100, -1258, 2716, 154, 977]]]
  hmulB := by decide  
  f := ![![![21, -42, 30, -20, 22]], ![![40, -107, 96, 26, -76]], ![![31, -81, 71, 18, -54]], ![![41, -102, 90, 1, -34]], ![![25, -59, 50, -8, -5]]]
  g := ![![![-55, -134, 154, 12, 50], ![-178, -423, 488, 30, 172], ![-535, -1265, 1461, 84, 524], ![-1581, -3736, 4316, 245, 1552], ![-995, -2351, 2716, 154, 977]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 2 2 8 [343, 231, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 346], [0, 1]]
 g := ![![[29, 277], [209, 206], [185], [207, 149], [218, 95], [197], [324, 270], [1]], ![[237, 70], [162, 141], [185], [141, 198], [134, 252], [197], [67, 77], [1]]]
 h' := ![![[116, 346], [142, 113], [305, 30], [134, 78], [178, 146], [230, 147], [255, 163], [4, 116], [0, 1]], ![[0, 1], [64, 234], [315, 317], [160, 269], [111, 201], [279, 200], [78, 184], [274, 231], [116, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [330]]
 b := ![[], [146, 165]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 2
  hpos := by decide
  P := [343, 231, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1611, -25325, 71904, -18521, 22646]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8594, -45781, 71904, -18521, 22646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -71, 108, 5, 40]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![5, -71, 108, 5, 40]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![246, 253, 1, 0, 0], ![222, 85, 0, 1, 0], ![167, 172, 0, 0, 1]] where
  M :=![![![5, -71, 108, 5, 40], ![-10, -145, 304, 18, 110], ![-36, -414, 899, 48, 328], ![-96, -1252, 2682, 147, 944], ![-58, -782, 1660, 104, 589]]]
  hmulB := by decide  
  f := ![![![-4115, 26689, -4782, 911, -3502]], ![![-1822, 11715, -2096, 400, -1538]], ![![-4248, 27477, -4921, 938, -3606]], ![![-3080, 19951, -3574, 681, -2618]], ![![-2885, 18661, -3342, 637, -2449]]]
  g := ![![![-99, -100, 108, 5, 40], ![-280, -281, 304, 18, 110], ![-826, -831, 899, 48, 328], ![-2450, -2463, 2682, 147, 944], ![-1527, -1530, 1660, 104, 589]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P1 : CertificateIrreducibleZModOfList' 347 2 2 8 [4, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [250, 346], [0, 1]]
 g := ![![[111, 87], [118, 130], [268], [22, 133], [280, 12], [3], [19, 40], [1]], ![[0, 260], [0, 217], [268], [307, 214], [157, 335], [3], [303, 307], [1]]]
 h' := ![![[250, 346], [222, 174], [79, 287], [259, 105], [268, 39], [212, 190], [271, 95], [343, 250], [0, 1]], ![[0, 1], [0, 173], [0, 60], [137, 242], [302, 308], [173, 157], [78, 252], [36, 97], [250, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [289]]
 b := ![[], [155, 318]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N1 : CertifiedPrimeIdeal' SI347N1 347 where
  n := 2
  hpos := by decide
  P := [4, 97, 1]
  hirr := P347P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![200, -1583, 1886, -223, -224]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1086, -1214, 1886, -223, -224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N1 B_one_repr
lemma NI347N1 : Nat.card (O ⧸ I347N1) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N1

def I347N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, -721, 128, -25, 96]] i)))

def SI347N2: IdealEqSpanCertificate' Table ![![109, -721, 128, -25, 96]] 
 ![![347, 0, 0, 0, 0], ![186, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![310, 0, 0, 0, 1]] where
  M :=![![![109, -721, 128, -25, 96], ![50, -325, 68, -14, 42], ![28, -146, 11, 12, 0], ![-24, 52, -110, -13, 72], ![2, -98, 88, -52, 53]]]
  hmulB := by decide  
  f := ![![![9621, 118099, -254130, -14387, -91470]], ![![5240, 64303, -138376, -7834, -49806]], ![![3128, 38338, -82517, -4672, -29700]], ![![3160, 38616, -83154, -4709, -29928]], ![![9048, 110958, -238800, -13520, -85951]]]
  g := ![![![269, -721, 128, -25, 96], ![120, -325, 68, -14, 42], ![72, -146, 11, 12, 0], ![-56, 52, -110, -13, 72], ![-8, -98, 88, -52, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N2 : Nat.card (O ⧸ I347N2) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N2)

lemma isPrimeI347N2 : Ideal.IsPrime I347N2 := prime_ideal_of_norm_prime hp347.out _ NI347N2
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-1, 2, 154, 12, 50]] ![![5, -71, 108, 5, 40]]
  ![![-9621, -118099, 254130, 14387, 91470]] where
 M := ![![![-9621, -118099, 254130, 14387, 91470]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI347N1 : IdealMulLeCertificate' Table 
  ![![-9621, -118099, 254130, 14387, 91470]] ![![109, -721, 128, -25, 96]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![-347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1, I347N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
    exact isPrimeI347N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0 ⊙ MulI347N1)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, -207, -73, 48, -6]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![113, -207, -73, 48, -6]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![206, 5, 24, 1, 0], ![175, 249, 146, 0, 1]] where
  M :=![![![113, -207, -73, 48, -6], ![-96, 233, -117, -157, 276], ![314, -1514, 2246, -355, -390], ![710, 1164, -6089, 3736, -2910], ![-1096, 4302, -5441, 201, 1897]]]
  hmulB := by decide  
  f := ![![![-313, -3529, 7823, 448, 2808]], ![![-896, -10649, 23087, 1311, 8304]], ![![-2622, -31490, 68020, 3857, 24474]], ![![-400, -4667, 10200, 581, 3666]], ![![-1907, -22708, 49211, 2794, 17701]]]
  g := ![![![-25, 3, -1, 48, -6], ![-46, -194, -105, -157, 276], ![406, 279, 194, -355, -390], ![-744, 2026, 943, 3736, -2910], ![-1073, -1344, -823, 201, 1897]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 3 2 8 [191, 67, 330, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 68, 58], [295, 280, 291], [0, 1]]
 g := ![![[334, 299, 340], [33, 22], [101, 100, 171], [346, 266, 266], [321, 154, 233], [337, 168], [294, 19, 1], []], ![[186, 153, 252, 114], [285, 25], [220, 187, 108, 50], [21, 263, 147, 339], [214, 338, 223, 209], [324, 20], [310, 327, 220, 79], [259, 223]], ![[232, 298, 330, 156], [144, 158], [311, 284, 214, 98], [310, 318, 42, 235], [145, 98, 43, 222], [158, 223], [282, 80, 104, 189], [26, 223]]]
 h' := ![![[73, 68, 58], [121, 67, 290], [253, 228, 303], [224, 205, 223], [113, 64, 148], [27, 207, 294], [35, 56, 283], [0, 0, 1], [0, 1]], ![[295, 280, 291], [148, 286, 279], [103, 19, 344], [158, 6, 342], [110, 139, 131], [187, 288, 96], [72, 315, 124], [183, 238, 280], [73, 68, 58]], ![[0, 1], [189, 345, 129], [226, 102, 51], [13, 138, 133], [28, 146, 70], [40, 203, 308], [40, 327, 291], [44, 111, 68], [295, 280, 291]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [204, 93], []]
 b := ![[], [279, 303, 209], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 3
  hpos := by decide
  P := [191, 67, 330, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10512707, -1167290, -47559430, 41670528, -34864494]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7084039, 24274324, 11583278, 41670528, -34864494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 42508549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 229, -41, 8, -30]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![-41, 229, -41, 8, -30]] 
 ![![349, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![213, 0, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![-41, 229, -41, 8, -30], ![-16, 95, -17, 3, -12], ![-6, 38, -4, 1, -6], ![-2, 20, -13, 6, -6], ![-8, 38, -13, 1, -1]]]
  hmulB := by decide  
  f := ![![![-143, 39, 559, 48, 180]], ![![-56, 13, 223, 19, 72]], ![![-1, -7, 17, 1, 6]], ![![-89, 3, 386, 32, 126]], ![![-59, 3, 254, 21, 83]]]
  g := ![![![-82, 229, -41, 8, -30], ![-34, 95, -17, 3, -12], ![-13, 38, -4, 1, -6], ![-9, 20, -13, 6, -6], ![-15, 38, -13, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N1 : Nat.card (O ⧸ I349N1) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N1)

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := prime_ideal_of_norm_prime hp349.out _ NI349N1

def I349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7735, 93054, -200880, -11388, -72282]] i)))

def SI349N2: IdealEqSpanCertificate' Table ![![7735, 93054, -200880, -11388, -72282]] 
 ![![349, 0, 0, 0, 0], ![189, 1, 0, 0, 0], ![226, 0, 1, 0, 0], ![213, 0, 0, 1, 0], ![107, 0, 0, 0, 1]] where
  M :=![![![7735, 93054, -200880, -11388, -72282], ![22776, 274087, -591648, -33540, -212892], ![67080, 807264, -1742561, -98784, -627024], ![197568, 2377608, -5132304, -290945, -1846752], ![124284, 1495674, -3228564, -183024, -1161731]]]
  hmulB := by decide  
  f := ![![![931, -4170, 1368, -492, 750]], ![![507, -2267, 744, -264, 402]], ![![598, -2676, 847, -312, 492]], ![![555, -2562, 936, -365, 510]], ![![305, -1356, 516, -156, 199]]]
  g := ![![![108823, 93054, -200880, -11388, -72282], ![320505, 274087, -591648, -33540, -212892], ![943970, 807264, -1742561, -98784, -627024], ![2780241, 2377608, -5132304, -290945, -1846752], ![1748959, 1495674, -3228564, -183024, -1161731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N2 : Nat.card (O ⧸ I349N2) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N2)

lemma isPrimeI349N2 : Ideal.IsPrime I349N2 := prime_ideal_of_norm_prime hp349.out _ NI349N2
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![113, -207, -73, 48, -6]] ![![-41, 229, -41, 8, -30]]
  ![![-931, 4170, -1368, 492, -750]] where
 M := ![![![-931, 4170, -1368, 492, -750]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI349N1 : IdealMulLeCertificate' Table 
  ![![-931, 4170, -1368, 492, -750]] ![![7735, 93054, -200880, -11388, -72282]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![-349, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1, I349N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
    exact isPrimeI349N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0 ⊙ MulI349N1)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-629, 6271, -1135, 208, -828]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![-629, 6271, -1135, 208, -828]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![225, 328, 56, 1, 0], ![328, 204, 316, 0, 1]] where
  M :=![![![-629, 6271, -1135, 208, -828], ![-416, 3099, -557, 105, -408], ![-210, 1426, -258, 49, -186], ![-98, 632, -101, 16, -78], ![-4, 596, -101, 19, -83]]]
  hmulB := by decide  
  f := ![![![1, -11, 17, 0, 6]], ![![0, -23, 43, 5, 12]], ![![-10, -38, 100, 9, 54]], ![![-1, -35, 68, 6, 24]], ![![-8, -58, 131, 11, 61]]]
  g := ![![![635, 303, 705, 208, -828], ![311, 147, 347, 105, -408], ![141, 66, 158, 49, -186], ![62, 32, 67, 16, -78], ![65, 32, 71, 19, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 3 2 8 [219, 209, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [282, 103, 6], [36, 249, 347], [0, 1]]
 g := ![![[255, 304, 304], [152, 335], [223, 292], [300, 152], [241, 256], [249, 221, 50], [310, 318, 1], []], ![[111, 107, 83, 238], [17, 285], [209, 265], [239, 351], [10, 25], [289, 247, 316, 20], [117, 134, 343, 297], [329, 36]], ![[161, 31, 204, 290], [185, 84], [168, 8], [24, 136], [254, 121], [202, 160, 306, 302], [233, 226, 327, 239], [341, 36]]]
 h' := ![![[282, 103, 6], [183, 350, 294], [17, 185, 138], [217, 221, 157], [139, 261, 192], [184, 100, 16], [239, 61, 129], [0, 0, 1], [0, 1]], ![[36, 249, 347], [33, 18, 117], [104, 341, 172], [300, 306, 177], [188, 2, 307], [45, 88, 348], [118, 285, 11], [60, 156, 249], [282, 103, 6]], ![[0, 1], [127, 338, 295], [333, 180, 43], [137, 179, 19], [110, 90, 207], [204, 165, 342], [311, 7, 213], [41, 197, 103], [36, 249, 347]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 37], []]
 b := ![[], [80, 1, 288], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 3
  hpos := by decide
  P := [219, 209, 35, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2531811, -1946834, -7174777, 7895633, -7687041]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2117178, -2899598, 5608427, 7895633, -7687041]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 43986977 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 11, -17, 0, -6]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![-1, 11, -17, 0, -6]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![342, 297, 1, 0, 0], ![90, 30, 0, 1, 0], ![149, 98, 0, 0, 1]] where
  M :=![![![-1, 11, -17, 0, -6], ![0, 23, -43, -5, -12], ![10, 38, -100, -9, -54], ![18, 208, -475, 26, -162], ![-8, 166, -295, -19, -53]]]
  hmulB := by decide  
  f := ![![![629, -6271, 1135, -208, 828]], ![![416, -3099, 557, -105, 408]], ![![960, -8687, 1569, -290, 1146]], ![![196, -1864, 337, -62, 246]], ![![381, -3509, 634, -117, 463]]]
  g := ![![![19, 16, -17, 0, -6], ![48, 40, -43, -5, -12], ![122, 100, -100, -9, -54], ![522, 443, -475, 26, -162], ![313, 265, -295, -19, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P1 : CertificateIrreducibleZModOfList' 353 2 2 8 [155, 273, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 352], [0, 1]]
 g := ![![[250, 41], [83], [121], [164], [15], [237, 122], [60, 46], [1]], ![[0, 312], [83], [121], [164], [15], [113, 231], [210, 307], [1]]]
 h' := ![![[80, 352], [11, 119], [121, 275], [251, 342], [322, 115], [330, 108], [231, 162], [198, 80], [0, 1]], ![[0, 1], [0, 234], [235, 78], [77, 11], [344, 238], [145, 245], [130, 191], [244, 273], [80, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [246]]
 b := ![[], [22, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N1 : CertifiedPrimeIdeal' SI353N1 353 where
  n := 2
  hpos := by decide
  P := [155, 273, 1]
  hirr := P353P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-857, -2996, 13412, -3772, 6454]
  a := ![-3, 7, 6, -2, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14759, -12764, 13412, -3772, 6454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N1 B_one_repr
lemma NI353N1 : Nat.card (O ⧸ I353N1) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N1
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![-629, 6271, -1135, 208, -828]] ![![-1, 11, -17, 0, -6]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![-353, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52469, -134349, 22828, -5165, 17100]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![52469, -134349, 22828, -5165, 17100]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![0, 0, 0, 359, 0], ![209, 259, 12, 118, 1]] where
  M :=![![![52469, -134349, 22828, -5165, 17100], ![10330, -26261, 4056, -1042, 3210], ![2084, -4594, -497, -280, 168], ![560, 852, -3922, -273, -1344], ![13282, -32550, 3188, -1440, 3377]]]
  hmulB := by decide  
  f := ![![![1, -13, 2, -3, 6]], ![![6, -29, 32, -4, -6]], ![![8, 22, -95, 52, -36]], ![![-104, 256, -146, -127, 240]], ![![-29, 56, -26, -45, 77]]]
  g := ![![![-9809, -12711, -508, -5635, 17100], ![-1840, -2389, -96, -1058, 3210], ![-92, -134, -7, -56, 168], ![784, 972, 34, 441, -1344], ![-1929, -2527, -104, -1114, 3377]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 4 2 8 [121, 316, 84, 233, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [249, 326, 184, 208], [67, 329, 320, 51], [169, 62, 214, 100], [0, 1]]
 g := ![![[262, 33, 128, 128], [232, 109, 234, 99], [157, 218, 133, 1], [333, 151, 74], [339, 220, 138], [70, 313, 184, 16], [126, 1], []], ![[104, 69, 299, 224, 221, 70], [195, 86, 91, 128, 316, 278], [135, 149, 28, 345, 178, 269], [36, 160, 346], [159, 188, 196], [205, 324, 358, 67, 244, 285], [281, 168, 241, 316, 208, 83], [15, 285, 184]], ![[82, 167, 264, 172, 234, 40], [281, 255, 238, 329, 16, 242], [118, 219, 99, 60, 334, 123], [28, 296, 205], [98, 338, 23], [226, 215, 236, 33, 60, 37], [256, 316, 161, 133, 332, 82], [199, 289, 88]], ![[169, 311, 264, 155, 170, 182], [184, 7, 304, 305, 88, 196], [89, 34, 232, 270, 232, 205], [301, 180, 225], [2, 328, 22], [55, 289, 219, 269, 0, 247], [121, 75, 295, 147, 61, 283], [148, 348, 307]]]
 h' := ![![[249, 326, 184, 208], [289, 200, 193, 152], [30, 291, 275, 278], [243, 337, 183, 1], [42, 175, 64, 206], [146, 182, 164, 79], [191, 271, 229, 355], [0, 0, 1], [0, 1]], ![[67, 329, 320, 51], [327, 144, 299, 246], [146, 186, 224, 271], [99, 92, 4, 35], [295, 264, 298, 50], [324, 51, 106, 345], [279, 243, 358, 299], [233, 345, 318, 117], [249, 326, 184, 208]], ![[169, 62, 214, 100], [32, 86, 204, 323], [71, 203, 117, 314], [253, 127, 82, 260], [236, 228, 218, 88], [310, 356, 151, 89], [176, 170, 166, 95], [155, 83, 123, 114], [67, 329, 320, 51]], ![[0, 1], [11, 288, 22, 356], [17, 38, 102, 214], [166, 162, 90, 63], [317, 51, 138, 15], [169, 129, 297, 205], [123, 34, 324, 328], [242, 290, 276, 128], [169, 62, 214, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [84, 331, 15], []]
 b := ![[], [], [68, 77, 32, 232], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 4
  hpos := by decide
  P := [121, 316, 84, 233, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56316956503, 119399970800, -32264961924, -85701003614, 138310154932]
  a := ![16, -7, -33, 16, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80677268349, -99451058932, -4713055212, -45699998010, 138310154932]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 16610312161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -13, 2, -3, 6]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![1, -13, 2, -3, 6]] 
 ![![359, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![295, 0, 1, 0, 0], ![153, 0, 0, 1, 0], ![235, 0, 0, 0, 1]] where
  M :=![![![1, -13, 2, -3, 6], ![6, -29, 32, -4, -6], ![8, 22, -95, 52, -36], ![-104, 256, -146, -127, 240], ![2, -140, 328, -130, 55]]]
  hmulB := by decide  
  f := ![![![52469, -134349, 22828, -5165, 17100]], ![![1198, -3067, 520, -118, 390]], ![![43121, -110411, 18757, -4245, 14052]], ![![22363, -57255, 9718, -2202, 7284]], ![![34383, -88035, 14952, -3385, 11203]]]
  g := ![![![-4, -13, 2, -3, 6], ![-20, -29, 32, -4, -6], ![79, 22, -95, 52, -36], ![11, 256, -146, -127, 240], ![-247, -140, 328, -130, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N1 : Nat.card (O ⧸ I359N1) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N1)

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := prime_ideal_of_norm_prime hp359.out _ NI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![52469, -134349, 22828, -5165, 17100]] ![![1, -13, 2, -3, 6]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![359, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0)


lemma PB984I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB984I7 : PrimesBelowBoundCertificateInterval O 307 359 984 where
  m := 9
  g := ![2, 2, 2, 2, 2, 3, 3, 2, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB984I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1]
    · exact ![I317N0, I317N1]
    · exact ![I331N0, I331N1]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1, I347N2]
    · exact ![I349N0, I349N1, I349N2]
    · exact ![I353N0, I353N1]
    · exact ![I359N0, I359N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
    · exact PBC317
    · exact PBC331
    · exact PBC337
    · exact PBC347
    · exact PBC349
    · exact PBC353
    · exact PBC359
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![9354951841, 311]
    · exact ![30664297, 97969]
    · exact ![10098039121, 317]
    · exact ![12003612721, 331]
    · exact ![12897917761, 337]
    · exact ![120409, 120409, 347]
    · exact ![42508549, 349, 349]
    · exact ![43986977, 124609]
    · exact ![16610312161, 359]
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
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
      exact NI349N2
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I311N1, I317N1, I331N1, I337N1, I347N2, I349N1, I349N2, I359N1]
  Il := ![[I311N1], [], [I317N1], [I331N1], [I337N1], [I347N2], [I349N1, I349N2], [], [I359N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
