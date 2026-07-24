
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}

def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 43, -13, 29, -22]] i)))

def SI541N0: IdealEqSpanCertificate' Table ![![13, 43, -13, 29, -22]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![0, 0, 541, 0, 0], ![286, 419, 111, 1, 0], ![401, 452, 442, 0, 1]] where
  M :=![![![13, 43, -13, 29, -22], ![100, 24, 279, -93, 188], ![28, 146, -155, 172, -128], ![508, 247, 1423, -548, 1180], ![292, 565, 151, 267, 41]]]
  hmulB := by decide  
  f := ![![![-3091, -153, -727, -129, 486]], ![![408, 12, 85, 17, -60]], ![![1428, 80, 335, 58, -224]], ![![-1022, -55, -249, -43, 164]], ![![-783, -38, -194, -34, 127]]]
  g := ![![![1, -4, 12, 29, -22], ![-90, -85, -134, -93, 188], ![4, -26, 69, 172, -128], ![-584, -561, -849, -548, 1180], ![-171, -240, -88, 267, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P0 : CertificateIrreducibleZModOfList' 541 3 2 9 [168, 391, 140, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [395, 329, 265], [6, 211, 276], [0, 1]]
 g := ![![[149, 533, 481], [196, 180], [350, 17, 460], [79, 292, 461], [261, 537, 188], [487, 212], [507, 418], [401, 1], []], ![[225, 410, 95, 189], [485, 20], [497, 309, 320, 161], [183, 409, 171, 408], [341, 309, 321, 49], [297, 406], [305, 214], [304, 159], [261, 436]], ![[121, 466, 410, 412], [398, 320], [126, 274, 471, 134], [203, 96, 230, 74], [301, 188, 129, 498], [102, 174], [332, 343], [483, 41], [250, 436]]]
 h' := ![![[395, 329, 265], [502, 169, 180], [169, 43, 94], [253, 311, 468], [514, 25, 193], [492, 307, 27], [349, 115, 444], [257, 472, 274], [0, 0, 1], [0, 1]], ![[6, 211, 276], [290, 167, 533], [390, 274, 392], [487, 64, 469], [533, 489, 281], [293, 231, 492], [294, 209, 270], [176, 503, 36], [190, 215, 211], [395, 329, 265]], ![[0, 1], [356, 205, 369], [242, 224, 55], [185, 166, 145], [382, 27, 67], [537, 3, 22], [522, 217, 368], [121, 107, 231], [234, 326, 329], [6, 211, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [436, 468], []]
 b := ![[], [372, 452, 331], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N0 : CertifiedPrimeIdeal' SI541N0 541 where
  n := 3
  hpos := by decide
  P := [168, 391, 140, 1]
  hirr := P541P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-168751206, -194691666, -274398156, 3938212, -192691738]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![140433100, 157582002, 156114988, 3938212, -192691738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N0 : Ideal.IsPrime I541N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N0 B_one_repr
lemma NI541N0 : Nat.card (O ⧸ I541N0) = 158340421 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N0

def I541N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 24, -84, -16, 34]] i)))

def SI541N1: IdealEqSpanCertificate' Table ![![-41, 24, -84, -16, 34]] 
 ![![541, 0, 0, 0, 0], ![160, 1, 0, 0, 0], ![323, 0, 1, 0, 0], ![198, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![-41, 24, -84, -16, 34], ![84, 223, 150, -18, -60], ![72, -132, 157, 44, -68], ![-156, -402, -270, 27, 88], ![-168, -84, -324, -34, 119]]]
  hmulB := by decide  
  f := ![![![-15413, -1416, -2004, -1868, 3926]], ![![-4556, -413, -606, -542, 1148]], ![![-9187, -852, -1175, -1128, 2358]], ![![-5634, -486, -810, -625, 1364]], ![![-1733, -168, -204, -226, 461]]]
  g := ![![![45, 24, -84, -16, 34], ![-142, 223, 150, -18, -60], ![-63, -132, 157, 44, -68], ![260, -402, -270, 27, 88], ![217, -84, -324, -34, 119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI541N1 : Nat.card (O ⧸ I541N1) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI541N1)

lemma isPrimeI541N1 : Ideal.IsPrime I541N1 := prime_ideal_of_norm_prime hp541.out _ NI541N1

def I541N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78107, 3783, 18425, 3283, -12304]] i)))

def SI541N2: IdealEqSpanCertificate' Table ![![78107, 3783, 18425, 3283, -12304]] 
 ![![541, 0, 0, 0, 0], ![270, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![423, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![78107, 3783, 18425, 3283, -12304], ![-10476, -510, -2465, -445, 1656], ![-36084, -1744, -8521, -1510, 5676], ![-41716, -2035, -9805, -1780, 6604], ![-7288, -349, -1729, -299, 1139]]]
  hmulB := by decide  
  f := ![![![1315, 1807, 2615, -23, -1320]], ![![658, 888, 1311, -9, -664]], ![![238, 332, 475, -6, -244]], ![![1009, 1414, 2014, -27, -1036]], ![![30, 51, 65, -5, -45]]]
  g := ![![![-7466, 3783, 18425, 3283, -12304], ![1005, -510, -2465, -445, 1656], ![3444, -1744, -8521, -1510, 5676], ![4008, -2035, -9805, -1780, 6604], ![691, -349, -1729, -299, 1139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI541N2 : Nat.card (O ⧸ I541N2) = 541 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI541N2)

lemma isPrimeI541N2 : Ideal.IsPrime I541N2 := prime_ideal_of_norm_prime hp541.out _ NI541N2
def MulI541N0 : IdealMulLeCertificate' Table 
  ![![13, 43, -13, 29, -22]] ![![-41, 24, -84, -16, 34]]
  ![![1315, 1807, 2615, -23, -1320]] where
 M := ![![![1315, 1807, 2615, -23, -1320]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI541N1 : IdealMulLeCertificate' Table 
  ![![1315, 1807, 2615, -23, -1320]] ![![78107, 3783, 18425, 3283, -12304]]
  ![![541, 0, 0, 0, 0]] where
 M := ![![![541, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC541 : ContainsPrimesAboveP 541 ![I541N0, I541N1, I541N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI541N0
    exact isPrimeI541N1
    exact isPrimeI541N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 541 (by decide) (𝕀 ⊙ MulI541N0 ⊙ MulI541N1)
instance hp547 : Fact (Nat.Prime 547) := {out := by norm_num}

def I547N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-331, -298, -654, -39, 267]] i)))

def SI547N0: IdealEqSpanCertificate' Table ![![-331, -298, -654, -39, 267]] 
 ![![547, 0, 0, 0, 0], ![0, 547, 0, 0, 0], ![0, 0, 547, 0, 0], ![0, 0, 0, 547, 0], ![93, 130, 311, 6, 1]] where
  M :=![![![-331, -298, -654, -39, 267], ![-140, 1510, -427, -309, 222], ![912, 322, 1797, 200, -696], ![424, -2307, 965, 592, -266], ![-710, -1563, -1345, 113, 657]]]
  hmulB := by decide  
  f := ![![![89, 4, 22, 3, -13]], ![![-12, 2, -7, 3, -2]], ![![-40, -4, -3, -6, 12]], ![![-48, 11, -35, 18, -14]], ![![-11, -1, 0, -2, 4]]]
  g := ![![![-46, -64, -153, -3, 267], ![-38, -50, -127, -3, 222], ![120, 166, 399, 8, -696], ![46, 59, 153, 4, -266], ![-113, -159, -376, -7, 657]]]
  hle1 := by decide   
  hle2 := by decide  


def P547P0 : CertificateIrreducibleZModOfList' 547 4 2 9 [114, 543, 55, 333, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [464, 5, 364, 380], [522, 246, 455, 73], [322, 295, 275, 94], [0, 1]]
 g := ![![[351, 353, 56, 16], [412, 410, 407, 521], [236, 273, 217], [463, 68, 205], [296, 68, 205], [253, 131, 106, 460], [409, 273, 395], [1], []], ![[491, 435, 294, 280, 293, 102], [157, 287, 523, 40, 14, 164], [342, 282, 344], [390, 22, 459], [540, 105, 295], [406, 417, 197, 401, 341, 343], [120, 88, 99], [513, 287, 158], [352, 334, 539]], ![[260, 373, 6, 99, 67, 346], [97, 242, 302, 405, 495, 367], [191, 113, 93], [368, 119, 519], [450, 291, 82], [353, 249, 352, 262, 515, 268], [304, 196, 477], [30, 99, 115], [306, 154, 406]], ![[43, 492, 446, 57, 130, 323], [494, 116, 283, 43, 129, 70], [434, 170, 64], [375, 189, 116], [210, 172, 372], [214, 350, 26, 512, 494, 65], [163, 515, 60], [240, 223, 502], [99, 207, 84]]]
 h' := ![![[464, 5, 364, 380], [74, 525, 421, 543], [103, 247, 534, 128], [131, 18, 174, 199], [491, 543, 322, 321], [149, 0, 225, 226], [284, 234, 276, 244], [433, 4, 492, 214], [0, 0, 1], [0, 1]], ![[522, 246, 455, 73], [324, 289, 416, 25], [198, 93, 103, 433], [389, 226, 118, 176], [514, 264, 435, 77], [458, 263, 297, 44], [436, 395, 106, 374], [21, 328, 333, 241], [128, 245, 163, 221], [464, 5, 364, 380]], ![[322, 295, 275, 94], [446, 240, 470, 64], [299, 368, 311, 242], [266, 371, 485, 164], [306, 318, 314, 197], [434, 339, 54, 58], [141, 385, 490, 373], [188, 402, 515, 515], [202, 359, 430, 425], [522, 246, 455, 73]], ![[0, 1], [398, 40, 334, 462], [538, 386, 146, 291], [519, 479, 317, 8], [313, 516, 23, 499], [133, 492, 518, 219], [407, 80, 222, 103], [374, 360, 301, 124], [502, 490, 500, 448], [322, 295, 275, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [243, 298, 56], []]
 b := ![[], [], [386, 508, 143, 254], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI547N0 : CertifiedPrimeIdeal' SI547N0 547 where
  n := 4
  hpos := by decide
  P := [114, 543, 55, 333, 1]
  hirr := P547P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1017437691938, 1234405583945, 1551356739757, 67324861039, 1063566353114]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-178965691312, -250510457625, -601860656451, -11543095535, 1063566353114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI547N0 : Ideal.IsPrime I547N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI547N0 B_one_repr
lemma NI547N0 : Nat.card (O ⧸ I547N0) = 89526025681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI547N0

def I547N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, -4, -22, -3, 13]] i)))

def SI547N1: IdealEqSpanCertificate' Table ![![-89, -4, -22, -3, 13]] 
 ![![547, 0, 0, 0, 0], ![497, 1, 0, 0, 0], ![482, 0, 1, 0, 0], ![464, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-89, -4, -22, -3, 13], ![12, -2, 7, -3, 2], ![40, 4, 3, 6, -12], ![48, -11, 35, -18, 14], ![6, 1, -7, 5, -9]]]
  hmulB := by decide  
  f := ![![![331, 298, 654, 39, -267]], ![![301, 268, 595, 36, -243]], ![![290, 262, 573, 34, -234]], ![![280, 257, 553, 32, -226]], ![![37, 35, 73, 4, -30]]]
  g := ![![![24, -4, -22, -3, 13], ![-2, -2, 7, -3, 2], ![-10, 4, 3, 6, -12], ![-7, -11, 35, -18, 14], ![2, 1, -7, 5, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI547N1 : Nat.card (O ⧸ I547N1) = 547 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI547N1)

lemma isPrimeI547N1 : Ideal.IsPrime I547N1 := prime_ideal_of_norm_prime hp547.out _ NI547N1
def MulI547N0 : IdealMulLeCertificate' Table 
  ![![-331, -298, -654, -39, 267]] ![![-89, -4, -22, -3, 13]]
  ![![547, 0, 0, 0, 0]] where
 M := ![![![-547, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC547 : ContainsPrimesAboveP 547 ![I547N0, I547N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI547N0
    exact isPrimeI547N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 547 (by decide) (𝕀 ⊙ MulI547N0)
instance hp557 : Fact (Nat.Prime 557) := {out := by norm_num}

def I557N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, -245, -235, -50, -145]] i)))

def SI557N0: IdealEqSpanCertificate' Table ![![-199, -245, -235, -50, -145]] 
 ![![557, 0, 0, 0, 0], ![0, 557, 0, 0, 0], ![1, 237, 1, 0, 0], ![84, 269, 0, 1, 0], ![232, 5, 0, 0, 1]] where
  M :=![![![-199, -245, -235, -50, -145], ![-880, -1229, -1090, -280, -690], ![-780, -1070, -1019, -210, -660], ![-5540, -7720, -6870, -1749, -4350], ![-4070, -5590, -5160, -1180, -3299]]]
  hmulB := by decide  
  f := ![![![-193, -1335, -205, 200, 65]], ![![-2140, -333, -4270, -540, 1730]], ![![-909, -138, -1814, -230, 735]], ![![-1056, -361, -2080, -229, 840]], ![![-98, -565, -120, 80, 41]]]
  g := ![![![68, 125, -235, -50, -145], ![330, 603, -1090, -280, -690], ![307, 539, -1019, -210, -660], ![2078, 3793, -6870, -1749, -4350], ![1554, 2785, -5160, -1180, -3299]]]
  hle1 := by decide   
  hle2 := by decide  


def P557P0 : CertificateIrreducibleZModOfList' 557 2 2 9 [391, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [489, 556], [0, 1]]
 g := ![![[315, 7], [389], [547, 181], [241, 7], [36], [24, 426], [529], [168], [1]], ![[396, 550], [389], [493, 376], [322, 550], [36], [20, 131], [529], [168], [1]]]
 h' := ![![[489, 556], [83, 243], [11, 226], [459, 409], [390, 243], [85, 6], [175, 312], [301, 534], [166, 489], [0, 1]], ![[0, 1], [269, 314], [239, 331], [497, 148], [19, 314], [234, 551], [125, 245], [194, 23], [334, 68], [489, 556]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [399]]
 b := ![[], [99, 478]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI557N0 : CertifiedPrimeIdeal' SI557N0 557 where
  n := 2
  hpos := by decide
  P := [391, 68, 1]
  hirr := P557P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5854, 5853, 9474, -575, 6358]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2568, -3800, 9474, -575, 6358]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI557N0 : Ideal.IsPrime I557N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI557N0 B_one_repr
lemma NI557N0 : Nat.card (O ⧸ I557N0) = 310249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI557N0

def I557N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -89, 215, -175, 236]] i)))

def SI557N1: IdealEqSpanCertificate' Table ![![-103, -89, 215, -175, 236]] 
 ![![557, 0, 0, 0, 0], ![0, 557, 0, 0, 0], ![530, 442, 1, 0, 0], ![134, 314, 0, 1, 0], ![48, 493, 0, 0, 1]] where
  M :=![![![-103, -89, 215, -175, 236], ![-56, 484, -1035, 801, -928], ![244, -502, 1463, -1004, 1252], ![-320, 2761, -5807, 4520, -5204], ![364, -395, 1867, -1131, 1581]]]
  hmulB := by decide  
  f := ![![![-2743, 95, -5499, -785, 2236]], ![![3092, 13912, 4975, -1693, -1808]], ![![-146, 11122, -1263, -2086, 684]], ![![1074, 7823, 1467, -1138, -476]], ![![2484, 12307, 3898, -1568, -1395]]]
  g := ![![![-183, -281, 215, -175, 236], ![872, 1192, -1035, 801, -928], ![-1258, -1704, 1463, -1004, 1252], ![4886, 6671, -5807, 4520, -5204], ![-1640, -2244, 1867, -1131, 1581]]]
  hle1 := by decide   
  hle2 := by decide  


def P557P1 : CertificateIrreducibleZModOfList' 557 2 2 9 [552, 449, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 556], [0, 1]]
 g := ![![[133, 248], [190], [265, 67], [211, 116], [436], [554, 372], [367], [524], [1]], ![[181, 309], [190], [260, 490], [485, 441], [436], [69, 185], [367], [524], [1]]]
 h' := ![![[108, 556], [354, 185], [211, 130], [498, 111], [177, 250], [542, 373], [269, 473], [417, 301], [5, 108], [0, 1]], ![[0, 1], [282, 372], [326, 427], [232, 446], [441, 307], [165, 184], [109, 84], [62, 256], [529, 449], [108, 556]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [463, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI557N1 : CertifiedPrimeIdeal' SI557N1 557 where
  n := 2
  hpos := by decide
  P := [552, 449, 1]
  hirr := P557P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![445268, 513510, 802734, -112509, 699939]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-796274, -1192167, 802734, -112509, 699939]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI557N1 : Ideal.IsPrime I557N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI557N1 B_one_repr
lemma NI557N1 : Nat.card (O ⧸ I557N1) = 310249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI557N1

def I557N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 5, 3, 2, 1]] i)))

def SI557N2: IdealEqSpanCertificate' Table ![![5, 5, 3, 2, 1]] 
 ![![557, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![115, 0, 1, 0, 0], ![376, 0, 0, 1, 0], ![224, 0, 0, 0, 1]] where
  M :=![![![5, 5, 3, 2, 1], ![16, 19, 26, 0, 18], ![12, 22, 9, 10, 4], ![100, 120, 158, 3, 110], ![70, 102, 80, 28, 49]]]
  hmulB := by decide  
  f := ![![![115, -637, -343, 68, 107]], ![![13, -80, -47, 8, 15]], ![![25, -129, -68, 14, 21]], ![![80, -432, -226, 47, 70]], ![![46, -260, -138, 28, 43]]]
  g := ![![![-3, 5, 3, 2, 1], ![-15, 19, 26, 0, 18], ![-13, 22, 9, 10, 4], ![-94, 120, 158, 3, 110], ![-68, 102, 80, 28, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI557N2 : Nat.card (O ⧸ I557N2) = 557 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI557N2)

lemma isPrimeI557N2 : Ideal.IsPrime I557N2 := prime_ideal_of_norm_prime hp557.out _ NI557N2
def MulI557N0 : IdealMulLeCertificate' Table 
  ![![-199, -245, -235, -50, -145]] ![![-103, -89, 215, -175, 236]]
  ![![-59903, -63674, -113380, 12515, -82869]] where
 M := ![![![-59903, -63674, -113380, 12515, -82869]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI557N1 : IdealMulLeCertificate' Table 
  ![![-59903, -63674, -113380, 12515, -82869]] ![![5, 5, 3, 2, 1]]
  ![![557, 0, 0, 0, 0]] where
 M := ![![![-7228189, -10954519, -7507803, -3536393, -4343486]]]
 hmul := by decide  
 g := ![![![![-12977, -19667, -13479, -6349, -7798]]]]
 hle2 := by decide  


def PBC557 : ContainsPrimesAboveP 557 ![I557N0, I557N1, I557N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI557N0
    exact isPrimeI557N1
    exact isPrimeI557N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 557 (by decide) (𝕀 ⊙ MulI557N0 ⊙ MulI557N1)
instance hp563 : Fact (Nat.Prime 563) := {out := by norm_num}

def I563N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89127, 4319, 21057, 3731, -14010]] i)))

def SI563N0: IdealEqSpanCertificate' Table ![![89127, 4319, 21057, 3731, -14010]] 
 ![![563, 0, 0, 0, 0], ![0, 563, 0, 0, 0], ![0, 0, 563, 0, 0], ![516, 23, 210, 1, 0], ![102, 288, 15, 0, 1]] where
  M :=![![![89127, 4319, 21057, 3731, -14010], ![-11920, -478, -2867, -415, 1828], ![-41116, -1992, -9531, -1814, 6632], ![-47384, -1697, -11459, -1500, 7212], ![-8096, -185, -1553, -401, 1607]]]
  hmulB := by decide  
  f := ![![![801, -579, 1657, 331, -682]], ![![-1860, -4534, -3331, 313, 1284]], ![![-1404, 2818, -3063, -912, 1288]], ![![140, 349, 250, -25, -96]], ![![-838, -2347, -1474, 197, 563]]]
  g := ![![![-723, 7022, -981, 3731, -14010], ![28, -919, 101, -415, 1828], ![388, -3322, 483, -1814, 6632], ![-16, -3631, 347, -1500, 7212], ![62, -806, 104, -401, 1607]]]
  hle1 := by decide   
  hle2 := by decide  


def P563P0 : CertificateIrreducibleZModOfList' 563 3 2 9 [84, 457, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [498, 535, 176], [534, 27, 387], [0, 1]]
 g := ![![[356, 542, 381], [277, 135, 297], [18, 58], [29, 314], [455, 519, 507], [247, 269, 347], [308, 415], [469, 1], []], ![[33, 450, 182, 191], [33, 469, 406, 399], [211, 166], [258, 289], [291, 73, 334, 76], [530, 388, 52, 476], [377, 192], [318, 166], [370, 11]], ![[454, 79, 337, 319], [469, 484, 122, 386], [242, 531], [533, 158], [306, 399, 205, 234], [26, 11, 124, 237], [164, 69], [200, 221], [159, 11]]]
 h' := ![![[498, 535, 176], [378, 410, 297], [455, 139, 269], [534, 228, 454], [64, 263, 434], [83, 511, 116], [222, 196, 318], [14, 86, 497], [0, 0, 1], [0, 1]], ![[534, 27, 387], [275, 86, 233], [286, 2, 199], [510, 345, 27], [15, 78, 17], [547, 23, 173], [125, 9, 294], [160, 339, 405], [169, 274, 27], [498, 535, 176]], ![[0, 1], [282, 67, 33], [7, 422, 95], [101, 553, 82], [70, 222, 112], [139, 29, 274], [245, 358, 514], [404, 138, 224], [434, 289, 535], [534, 27, 387]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [457, 416], []]
 b := ![[], [426, 70, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI563N0 : CertifiedPrimeIdeal' SI563N0 563 where
  n := 3
  hpos := by decide
  P := [84, 457, 94, 1]
  hirr := P563P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-505560010, -560350268, -862337530, 47856324, -617267452]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![67072570, 312809912, -2936330, 47856324, -617267452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI563N0 : Ideal.IsPrime I563N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI563N0 B_one_repr
lemma NI563N0 : Nat.card (O ⧸ I563N0) = 178453547 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI563N0

def I563N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, -1554, 1182, 432, -504]] i)))

def SI563N1: IdealEqSpanCertificate' Table ![![521, -1554, 1182, 432, -504]] 
 ![![563, 0, 0, 0, 0], ![155, 1, 0, 0, 0], ![430, 0, 1, 0, 0], ![369, 0, 0, 1, 0], ![552, 0, 0, 0, 1]] where
  M :=![![![521, -1554, 1182, 432, -504], ![-3252, -3943, -6174, -186, 2448], ![-288, 5040, -1021, -1008, 492], ![5508, 6798, 10446, 293, -4140], ![3348, -1716, 6864, 1254, -2815]]]
  hmulB := by decide  
  f := ![![![-24701, -31650, -28842, -7092, -17712]], ![![-7001, -8989, -8196, -2010, -5040]], ![![-19042, -24420, -22249, -5472, -13668]], ![![-17451, -22476, -20508, -5011, -12636]], ![![-25140, -32304, -29436, -7230, -18103]]]
  g := ![![![-263, -1554, 1182, 432, -504], ![3517, -3943, -6174, -186, 2448], ![-430, 5040, -1021, -1008, 492], ![-5973, 6798, 10446, 293, -4140], ![-2826, -1716, 6864, 1254, -2815]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI563N1 : Nat.card (O ⧸ I563N1) = 563 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI563N1)

lemma isPrimeI563N1 : Ideal.IsPrime I563N1 := prime_ideal_of_norm_prime hp563.out _ NI563N1

def I563N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 87, 79, 19, 50]] i)))

def SI563N2: IdealEqSpanCertificate' Table ![![63, 87, 79, 19, 50]] 
 ![![563, 0, 0, 0, 0], ![198, 1, 0, 0, 0], ![284, 0, 1, 0, 0], ![550, 0, 0, 1, 0], ![384, 0, 0, 0, 1]] where
  M :=![![![63, 87, 79, 19, 50], ![312, 428, 395, 91, 252], ![276, 382, 345, 84, 220], ![1960, 2695, 2479, 572, 1584], ![1432, 1975, 1801, 427, 1147]]]
  hmulB := by decide  
  f := ![![![29769, 1397, 7203, 1283, -4758]], ![![10462, 490, 2531, 451, -1672]], ![![14992, 704, 3627, 646, -2396]], ![![29054, 1365, 7031, 1252, -4644]], ![![20300, 953, 4913, 875, -3245]]]
  g := ![![![-123, 87, 79, 19, 50], ![-610, 428, 395, 91, 252], ![-540, 382, 345, 84, 220], ![-3834, 2695, 2479, 572, 1584], ![-2800, 1975, 1801, 427, 1147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI563N2 : Nat.card (O ⧸ I563N2) = 563 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI563N2)

lemma isPrimeI563N2 : Ideal.IsPrime I563N2 := prime_ideal_of_norm_prime hp563.out _ NI563N2
def MulI563N0 : IdealMulLeCertificate' Table 
  ![![89127, 4319, 21057, 3731, -14010]] ![![521, -1554, 1182, 432, -504]]
  ![![-29769, -1397, -7203, -1283, 4758]] where
 M := ![![![-29769, -1397, -7203, -1283, 4758]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI563N1 : IdealMulLeCertificate' Table 
  ![![-29769, -1397, -7203, -1283, 4758]] ![![63, 87, 79, 19, 50]]
  ![![563, 0, 0, 0, 0]] where
 M := ![![![-563, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC563 : ContainsPrimesAboveP 563 ![I563N0, I563N1, I563N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI563N0
    exact isPrimeI563N1
    exact isPrimeI563N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 563 (by decide) (𝕀 ⊙ MulI563N0 ⊙ MulI563N1)
instance hp569 : Fact (Nat.Prime 569) := {out := by norm_num}

def I569N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1003, 1793, 1577, 376, 1107]] i)))

def SI569N0: IdealEqSpanCertificate' Table ![![1003, 1793, 1577, 376, 1107]] 
 ![![569, 0, 0, 0, 0], ![0, 569, 0, 0, 0], ![0, 0, 569, 0, 0], ![0, 0, 0, 569, 0], ![555, 89, 408, 98, 1]] where
  M :=![![![1003, 1793, 1577, 376, 1107], ![6552, 8989, 8206, 1932, 5222], ![5932, 7972, 7335, 1720, 4616], ![41100, 56386, 51590, 12163, 32830], ![29946, 41212, 37688, 8874, 24035]]]
  hmulB := by decide  
  f := ![![![-7, -1, -9, -2, 5]], ![![4, 25, 2, 0, -6]], ![![12, -8, 27, 0, -4]], ![![-8, -30, -34, 23, -18]], ![![1, -8, 5, 2, -2]]]
  g := ![![![-1078, -170, -791, -190, 1107], ![-5082, -801, -3730, -896, 5222], ![-4492, -708, -3297, -792, 4616], ![-31950, -5036, -23450, -5633, 32830], ![-23391, -3687, -17168, -4124, 24035]]]
  hle1 := by decide   
  hle2 := by decide  


def P569P0 : CertificateIrreducibleZModOfList' 569 4 2 9 [337, 137, 228, 552, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [487, 130, 314, 279], [492, 242, 242, 406], [176, 196, 13, 453], [0, 1]]
 g := ![![[240, 111, 154, 70], [219, 402, 471], [439, 141, 125], [554, 134, 456, 498], [192, 47, 108, 568], [418, 396, 155, 121], [313, 6, 289], [1], []], ![[561, 510, 131, 341, 127, 492], [119, 511, 409], [490, 516, 320], [416, 125, 140, 74, 277, 168], [23, 208, 344, 496, 400, 453], [543, 387, 215, 2, 284, 103], [492, 303, 5], [543, 527, 132], [321, 332, 457]], ![[477, 232, 200, 357, 530, 161], [400, 220, 462], [131, 321, 383], [419, 159, 114, 161, 411, 188], [322, 117, 263, 68, 477, 230], [48, 250, 387, 422, 488, 366], [70, 64, 397], [437, 49, 121], [322, 86, 395]], ![[17, 319, 115, 40, 215, 176], [418, 128, 439], [401, 306, 281], [325, 59, 186, 14, 416, 173], [335, 371, 91, 518, 412, 211], [172, 185, 318, 373, 545, 417], [414, 410, 158], [69, 217, 226], [473, 412, 369]]]
 h' := ![![[487, 130, 314, 279], [507, 75, 53, 162], [370, 479, 304, 374], [503, 211, 357, 520], [162, 165, 309, 92], [246, 556, 315, 86], [122, 208, 17, 11], [232, 432, 341, 17], [0, 0, 1], [0, 1]], ![[492, 242, 242, 406], [124, 429, 425, 297], [484, 532, 404, 523], [349, 364, 313, 263], [260, 182, 91, 226], [67, 529, 366, 485], [519, 240, 81, 452], [449, 324, 105, 104], [398, 347, 552, 335], [487, 130, 314, 279]], ![[176, 196, 13, 453], [447, 327, 249, 39], [491, 189, 195, 529], [553, 338, 548, 39], [488, 62, 88, 306], [108, 412, 265, 398], [533, 167, 511, 461], [15, 1, 123, 484], [404, 22, 426, 11], [492, 242, 242, 406]], ![[0, 1], [291, 307, 411, 71], [257, 507, 235, 281], [145, 225, 489, 316], [339, 160, 81, 514], [62, 210, 192, 169], [147, 523, 529, 214], [187, 381, 0, 533], [169, 200, 159, 223], [176, 196, 13, 453]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [483, 335, 430], []]
 b := ![[], [], [333, 508, 367, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI569N0 : CertifiedPrimeIdeal' SI569N0 569 where
  n := 4
  hpos := by decide
  P := [337, 137, 228, 552, 1]
  hirr := P569P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2048167107, -4211431760, 13946502110, -9253763010, 11929670432]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11632546437, -1873378032, -8529629234, -2070934034, 11929670432]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI569N0 : Ideal.IsPrime I569N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI569N0 B_one_repr
lemma NI569N0 : Nat.card (O ⧸ I569N0) = 104821185121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI569N0

def I569N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 9, 2, -5]] i)))

def SI569N1: IdealEqSpanCertificate' Table ![![7, 1, 9, 2, -5]] 
 ![![569, 0, 0, 0, 0], ![352, 1, 0, 0, 0], ![516, 0, 1, 0, 0], ![178, 0, 0, 1, 0], ![500, 0, 0, 0, 1]] where
  M :=![![![7, 1, 9, 2, -5], ![-4, -25, -2, 0, 6], ![-12, 8, -27, 0, 4], ![8, 30, 34, -23, 18], ![14, 18, 22, 6, -17]]]
  hmulB := by decide  
  f := ![![![-1003, -1793, -1577, -376, -1107]], ![![-632, -1125, -990, -236, -694]], ![![-920, -1640, -1443, -344, -1012]], ![![-386, -660, -584, -139, -404]], ![![-934, -1648, -1452, -346, -1015]]]
  g := ![![![-5, 1, 9, 2, -5], ![12, -25, -2, 0, 6], ![16, 8, -27, 0, 4], ![-58, 30, 34, -23, 18], ![-18, 18, 22, 6, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI569N1 : Nat.card (O ⧸ I569N1) = 569 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI569N1)

lemma isPrimeI569N1 : Ideal.IsPrime I569N1 := prime_ideal_of_norm_prime hp569.out _ NI569N1
def MulI569N0 : IdealMulLeCertificate' Table 
  ![![1003, 1793, 1577, 376, 1107]] ![![7, 1, 9, 2, -5]]
  ![![569, 0, 0, 0, 0]] where
 M := ![![![-569, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC569 : ContainsPrimesAboveP 569 ![I569N0, I569N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI569N0
    exact isPrimeI569N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 569 (by decide) (𝕀 ⊙ MulI569N0)
instance hp571 : Fact (Nat.Prime 571) := {out := by norm_num}

def I571N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26311, -1275, -6205, -1107, 4146]] i)))

def SI571N0: IdealEqSpanCertificate' Table ![![-26311, -1275, -6205, -1107, 4146]] 
 ![![571, 0, 0, 0, 0], ![0, 571, 0, 0, 0], ![385, 512, 1, 0, 0], ![338, 46, 0, 1, 0], ![42, 233, 0, 0, 1]] where
  M :=![![![-26311, -1275, -6205, -1107, 4146], ![3528, 174, 823, 155, -564], ![12156, 584, 2879, 502, -1904], ![14048, 701, 3263, 628, -2260], ![2456, 113, 593, 93, -375]]]
  hmulB := by decide  
  f := ![![![151, 175, 299, 5, -142]], ![![76, -810, 279, 147, -244]], ![![169, -609, 450, 135, -314]], ![![94, 39, 197, 14, -104]], ![![42, -317, 136, 60, -111]]]
  g := ![![![4488, 3959, -6205, -1107, 4146], ![-599, -520, 823, 155, -564], ![-2077, -1844, 2879, 502, -1904], ![-2381, -2053, 3263, 628, -2260], ![-423, -386, 593, 93, -375]]]
  hle1 := by decide   
  hle2 := by decide  


def P571P0 : CertificateIrreducibleZModOfList' 571 2 2 9 [151, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [475, 570], [0, 1]]
 g := ![![[375, 280], [146, 270], [439], [499, 123], [119, 305], [150, 518], [536], [80], [1]], ![[332, 291], [492, 301], [439], [111, 448], [531, 266], [99, 53], [536], [80], [1]]]
 h' := ![![[475, 570], [223, 490], [476, 542], [23, 208], [303, 319], [190, 154], [542, 538], [443, 185], [420, 475], [0, 1]], ![[0, 1], [5, 81], [405, 29], [40, 363], [513, 252], [252, 417], [284, 33], [384, 386], [500, 96], [475, 570]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [83, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N0 : CertifiedPrimeIdeal' SI571N0 571 where
  n := 2
  hpos := by decide
  P := [151, 96, 1]
  hirr := P571P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![647523, 751982, 1081992, -63485, 861820]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-754217, -1315432, 1081992, -63485, 861820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI571N0 : Ideal.IsPrime I571N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI571N0 B_one_repr
lemma NI571N0 : Nat.card (O ⧸ I571N0) = 326041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI571N0

def I571N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -100, 254, -184, 224]] i)))

def SI571N1: IdealEqSpanCertificate' Table ![![25, -100, 254, -184, 224]] 
 ![![571, 0, 0, 0, 0], ![0, 571, 0, 0, 0], ![532, 463, 1, 0, 0], ![27, 481, 0, 1, 0], ![533, 303, 0, 0, 1]] where
  M :=![![![25, -100, 254, -184, 224], ![-120, 463, -1166, 846, -1024], ![160, -590, 1509, -1090, 1324], ![-672, 2608, -6562, 4769, -5772], ![192, -680, 1766, -1268, 1549]]]
  hmulB := by decide  
  f := ![![![-461, 64, -186, -44, 104]], ![![248, 281, 370, 6, -144]], ![![-228, 287, 127, -36, -20]], ![![187, 239, 302, 3, -116]], ![![-299, 209, 22, -38, 21]]]
  g := ![![![-437, -170, 254, -184, 224], ![2002, 777, -1166, 846, -1024], ![-2590, -1009, 1509, -1090, 1324], ![11275, 4371, -6562, 4769, -5772], ![-3031, -1187, 1766, -1268, 1549]]]
  hle1 := by decide   
  hle2 := by decide  


def P571P1 : CertificateIrreducibleZModOfList' 571 2 2 9 [214, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [566, 570], [0, 1]]
 g := ![![[531, 563], [322, 407], [525], [505, 191], [161, 186], [178, 473], [415], [25], [1]], ![[0, 8], [0, 164], [525], [121, 380], [373, 385], [97, 98], [415], [25], [1]]]
 h' := ![![[566, 570], [183, 265], [98, 248], [420, 518], [377, 320], [165, 140], [155, 500], [476, 302], [357, 566], [0, 1]], ![[0, 1], [0, 306], [0, 323], [114, 53], [490, 251], [36, 431], [510, 71], [108, 269], [382, 5], [566, 570]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [11, 347]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N1 : CertifiedPrimeIdeal' SI571N1 571 where
  n := 2
  hpos := by decide
  P := [214, 5, 1]
  hirr := P571P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![528, 146, 1084, -563, 1013]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1928, -942, 1084, -563, 1013]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI571N1 : Ideal.IsPrime I571N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI571N1 B_one_repr
lemma NI571N1 : Nat.card (O ⧸ I571N1) = 326041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI571N1

def I571N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -30, 68, -53, 65]] i)))

def SI571N2: IdealEqSpanCertificate' Table ![![-7, -30, 68, -53, 65]] 
 ![![571, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![496, 0, 0, 1, 0], ![254, 0, 0, 0, 1]] where
  M :=![![![-7, -30, 68, -53, 65], ![-36, 126, -335, 239, -294], ![48, -172, 425, -310, 372], ![-208, 707, -1891, 1346, -1658], ![38, -217, 479, -365, 425]]]
  hmulB := by decide  
  f := ![![![1861, 5896, 3308, -551, -1251]], ![![337, 1014, 603, -90, -229]], ![![297, 958, 527, -91, -199]], ![![1592, 5135, 2823, -488, -1066]], ![![828, 2655, 1469, -251, -555]]]
  g := ![![![11, -30, 68, -53, 65], ![-43, 126, -335, 239, -294], ![63, -172, 425, -310, 372], ![-240, 707, -1891, 1346, -1658], ![86, -217, 479, -365, 425]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI571N2 : Nat.card (O ⧸ I571N2) = 571 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI571N2)

lemma isPrimeI571N2 : Ideal.IsPrime I571N2 := prime_ideal_of_norm_prime hp571.out _ NI571N2
def MulI571N0 : IdealMulLeCertificate' Table 
  ![![-26311, -1275, -6205, -1107, 4146]] ![![25, -100, 254, -184, 224]]
  ![![42361, -4611, 26281, -10387, 8274]] where
 M := ![![![42361, -4611, 26281, -10387, 8274]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI571N1 : IdealMulLeCertificate' Table 
  ![![42361, -4611, 26281, -10387, 8274]] ![![-7, -30, 68, -53, 65]]
  ![![571, 0, 0, 0, 0]] where
 M := ![![![3605865, -15511215, 39199721, -28495184, 34623727]]]
 hmul := by decide  
 g := ![![![![6315, -27165, 68651, -49904, 60637]]]]
 hle2 := by decide  


def PBC571 : ContainsPrimesAboveP 571 ![I571N0, I571N1, I571N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI571N0
    exact isPrimeI571N1
    exact isPrimeI571N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 571 (by decide) (𝕀 ⊙ MulI571N0 ⊙ MulI571N1)
instance hp577 : Fact (Nat.Prime 577) := {out := by norm_num}

def I577N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 158, 382, 136, 240]] i)))

def SI577N0: IdealEqSpanCertificate' Table ![![293, 158, 382, 136, 240]] 
 ![![577, 0, 0, 0, 0], ![0, 577, 0, 0, 0], ![0, 0, 577, 0, 0], ![0, 0, 0, 577, 0], ![220, 544, 468, 366, 1]] where
  M :=![![![293, 158, 382, 136, 240], ![1068, 1917, 1034, 350, 1568], ![1504, 2544, 1951, 320, 972], ![10244, 13350, 13462, 2953, 7044], ![7172, 8964, 9256, 2238, 5341]]]
  hmulB := by decide  
  f := ![![![2181, 106, 514, 92, -344]], ![![-292, -15, -66, -14, 48]], ![![-1008, -48, -241, -40, 156]], ![![-1164, -62, -262, -59, 196]], ![![-1000, -52, -228, -48, 165]]]
  g := ![![![-91, -226, -194, -152, 240], ![-596, -1475, -1270, -994, 1568], ![-368, -912, -785, -616, 972], ![-2668, -6618, -5690, -4463, 7044], ![-2024, -5020, -4316, -3384, 5341]]]
  hle1 := by decide   
  hle2 := by decide  


def P577P0 : CertificateIrreducibleZModOfList' 577 4 2 9 [237, 62, 534, 216, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [268, 159, 139, 168], [154, 445, 53, 530], [516, 549, 385, 456], [0, 1]]
 g := ![![[571, 44, 88, 496], [384, 369, 568], [178, 79, 518], [455, 433, 511], [485, 127, 314], [525, 571, 200], [73, 511, 74, 496], [1], []], ![[291, 239, 338, 303, 159, 10], [162, 239, 463], [94, 423, 151], [276, 47, 131], [167, 570, 68], [375, 195, 287], [382, 561, 310, 467, 76, 358], [486, 205, 153], [378, 165, 528]], ![[477, 544, 194, 492, 429, 86], [95, 265, 283], [4, 333, 520], [512, 366, 283], [476, 361, 193], [442, 270, 145], [334, 459, 3, 504, 35, 7], [282, 279, 228], [522, 246, 478]], ![[9, 16, 341, 52, 194, 349], [546, 89, 305], [153, 354, 528], [266, 539, 53], [423, 30, 17], [321, 46, 283], [39, 143, 472, 444, 333, 386], [327, 285, 323], [349, 385, 216]]]
 h' := ![![[268, 159, 139, 168], [209, 379, 254, 361], [233, 247, 530, 72], [426, 470, 275, 234], [311, 379, 39, 348], [288, 37, 478, 499], [9, 353, 40, 237], [340, 515, 43, 361], [0, 0, 1], [0, 1]], ![[154, 445, 53, 530], [446, 526, 135, 363], [94, 379, 301, 294], [40, 220, 8, 370], [521, 194, 556, 383], [242, 165, 549, 490], [516, 413, 557, 335], [264, 326, 336, 3], [125, 180, 291, 419], [268, 159, 139, 168]], ![[516, 549, 385, 456], [124, 127, 39, 261], [504, 74, 177, 74], [426, 7, 479, 382], [394, 176, 450, 503], [445, 29, 363, 410], [461, 459, 323, 508], [269, 310, 372, 327], [400, 234, 358, 128], [154, 445, 53, 530]], ![[0, 1], [180, 122, 149, 169], [196, 454, 146, 137], [412, 457, 392, 168], [96, 405, 109, 497], [178, 346, 341, 332], [317, 506, 234, 74], [183, 3, 403, 463], [57, 163, 504, 30], [516, 549, 385, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [104, 319, 350], []]
 b := ![[], [], [76, 211, 436, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI577N0 : CertifiedPrimeIdeal' SI577N0 577 where
  n := 4
  hpos := by decide
  P := [237, 62, 534, 216, 1]
  hirr := P577P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7540707616734, 8744891762026, 12168955226218, -89912374244, 8511564643582]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3232241791978, -8009612260566, -6882570707054, -5399172568328, 8511564643582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI577N0 : Ideal.IsPrime I577N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI577N0 B_one_repr
lemma NI577N0 : Nat.card (O ⧸ I577N0) = 110841719041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI577N0

def I577N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2181, 106, 514, 92, -344]] i)))

def SI577N1: IdealEqSpanCertificate' Table ![![2181, 106, 514, 92, -344]] 
 ![![577, 0, 0, 0, 0], ![532, 1, 0, 0, 0], ![371, 0, 1, 0, 0], ![288, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![2181, 106, 514, 92, -344], ![-292, -15, -66, -14, 48], ![-1008, -48, -241, -40, 156], ![-1164, -62, -262, -59, 196], ![-204, -8, -52, -6, 29]]]
  hmulB := by decide  
  f := ![![![293, 158, 382, 136, 240]], ![![272, 149, 354, 126, 224]], ![![191, 106, 249, 88, 156]], ![![164, 102, 214, 73, 132]], ![![17, 18, 22, 6, 13]]]
  g := ![![![-465, 106, 514, 92, -344], ![62, -15, -66, -14, 48], ![215, -48, -241, -40, 156], ![250, -62, -262, -59, 196], ![43, -8, -52, -6, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI577N1 : Nat.card (O ⧸ I577N1) = 577 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI577N1)

lemma isPrimeI577N1 : Ideal.IsPrime I577N1 := prime_ideal_of_norm_prime hp577.out _ NI577N1
def MulI577N0 : IdealMulLeCertificate' Table 
  ![![293, 158, 382, 136, 240]] ![![2181, 106, 514, 92, -344]]
  ![![577, 0, 0, 0, 0]] where
 M := ![![![577, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC577 : ContainsPrimesAboveP 577 ![I577N0, I577N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI577N0
    exact isPrimeI577N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 577 (by decide) (𝕀 ⊙ MulI577N0)
instance hp587 : Fact (Nat.Prime 587) := {out := by norm_num}

def I587N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-373, 1457, -3701, 2682, -3257]] i)))

def SI587N0: IdealEqSpanCertificate' Table ![![-373, 1457, -3701, 2682, -3257]] 
 ![![587, 0, 0, 0, 0], ![0, 587, 0, 0, 0], ![0, 0, 587, 0, 0], ![447, 121, 456, 1, 0], ![51, 265, 541, 0, 1]] where
  M :=![![![-373, 1457, -3701, 2682, -3257], ![1764, -6711, 17000, -12322, 14942], ![-2300, 8634, -21947, 15886, -19280], ![9944, -37818, 95800, -69435, 84190], ![-2698, 10026, -25604, 18506, -22489]]]
  hmulB := by decide  
  f := ![![![75, 113, 47, -12, -21]], ![![160, -21, 336, 50, -138]], ![![-132, -270, -197, 18, 76]], ![![-13, -128, -49, 15, 15]], ![![-43, -248, -26, 38, 6]]]
  g := ![![![-1760, 920, 912, 2682, -3257], ![8088, -4217, -4170, -12322, 14942], ![-10426, 5444, 5391, 15886, -19280], ![45577, -23759, -23490, -69435, 84190], ![-12143, 6355, 6307, 18506, -22489]]]
  hle1 := by decide   
  hle2 := by decide  


def P587P0 : CertificateIrreducibleZModOfList' 587 3 2 9 [97, 508, 272, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [531, 0, 169], [371, 586, 418], [0, 1]]
 g := ![![[285, 120, 343], [287, 560, 254], [98, 430], [282, 34, 550], [121, 387], [317, 29], [315, 143, 222], [315, 1], []], ![[90, 425, 334, 90], [330, 483, 341, 292], [97, 229], [50, 191, 71, 70], [382, 250], [199, 363], [140, 412, 191, 234], [447, 1], [353, 385]], ![[570, 493, 27, 94], [420, 537, 397, 50], [231, 114], [390, 85, 84, 398], [276, 348], [205, 485], [565, 538, 64, 134], [], [104, 385]]]
 h' := ![![[531, 0, 169], [337, 431, 408], [520, 209, 29], [235, 34, 323], [485, 33, 186], [149, 29, 309], [556, 235, 261], [556, 134, 101], [0, 0, 1], [0, 1]], ![[371, 586, 418], [368, 74, 230], [143, 434, 72], [269, 401, 140], [340, 51, 108], [379, 151, 483], [115, 384, 125], [115, 378, 239], [6, 521, 586], [531, 0, 169]], ![[0, 1], [539, 82, 536], [338, 531, 486], [372, 152, 124], [480, 503, 293], [104, 407, 382], [493, 555, 201], [339, 75, 247], [174, 66], [371, 586, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [528, 506], []]
 b := ![[], [359, 534, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI587N0 : CertifiedPrimeIdeal' SI587N0 587 where
  n := 3
  hpos := by decide
  P := [97, 508, 272, 1]
  hirr := P587P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![167085653, 187387323, 283983638, -15979991, 206815004]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5515202, -89752998, -177710490, -15979991, 206815004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI587N0 : Ideal.IsPrime I587N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI587N0 B_one_repr
lemma NI587N0 : Nat.card (O ⧸ I587N0) = 202262003 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI587N0

def I587N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 33, 29, 7, 20]] i)))

def SI587N1: IdealEqSpanCertificate' Table ![![23, 33, 29, 7, 20]] 
 ![![587, 0, 0, 0, 0], ![187, 1, 0, 0, 0], ![310, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![23, 33, 29, 7, 20], ![120, 168, 151, 35, 96], ![108, 146, 137, 32, 84], ![752, 1031, 947, 224, 604], ![548, 755, 689, 163, 443]]]
  hmulB := by decide  
  f := ![![![-1567, -169, -215, -217, 444]], ![![-499, -53, -70, -68, 140]], ![![-826, -90, -111, -116, 236]], ![![-141, -12, -28, -13, 32]], ![![-45, -6, -4, -8, 15]]]
  g := ![![![-27, 33, 29, 7, 20], ![-139, 168, 151, 35, 96], ![-124, 146, 137, 32, 84], ![-865, 1031, 947, 224, 604], ![-631, 755, 689, 163, 443]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI587N1 : Nat.card (O ⧸ I587N1) = 587 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI587N1)

lemma isPrimeI587N1 : Ideal.IsPrime I587N1 := prime_ideal_of_norm_prime hp587.out _ NI587N1

def I587N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119, -22, 22, 9, -17]] i)))

def SI587N2: IdealEqSpanCertificate' Table ![![119, -22, 22, 9, -17]] 
 ![![587, 0, 0, 0, 0], ![531, 1, 0, 0, 0], ![111, 0, 1, 0, 0], ![401, 0, 0, 1, 0], ![525, 0, 0, 0, 1]] where
  M :=![![![119, -22, 22, 9, -17], ![-60, 0, -91, -13, 38], ![-32, 66, 31, -8, -8], ![8, -3, 133, 18, -50], ![2, -75, 31, 17, -13]]]
  hmulB := by decide  
  f := ![![![1419, 1772, 2066, 171, 1395]], ![![1295, 1620, 1881, 160, 1269]], ![![279, 348, 407, 33, 275]], ![![1041, 1317, 1489, 149, 999]], ![![1323, 1657, 1919, 166, 1294]]]
  g := ![![![25, -22, 22, 9, -17], ![-8, 0, -91, -13, 38], ![-53, 66, 31, -8, -8], ![10, -3, 133, 18, -50], ![62, -75, 31, 17, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI587N2 : Nat.card (O ⧸ I587N2) = 587 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI587N2)

lemma isPrimeI587N2 : Ideal.IsPrime I587N2 := prime_ideal_of_norm_prime hp587.out _ NI587N2
def MulI587N0 : IdealMulLeCertificate' Table 
  ![![-373, 1457, -3701, 2682, -3257]] ![![23, 33, 29, 7, 20]]
  ![![-1419, -1772, -2066, -171, -1395]] where
 M := ![![![-1419, -1772, -2066, -171, -1395]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI587N1 : IdealMulLeCertificate' Table 
  ![![-1419, -1772, -2066, -171, -1395]] ![![119, -22, 22, 9, -17]]
  ![![587, 0, 0, 0, 0]] where
 M := ![![![-587, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC587 : ContainsPrimesAboveP 587 ![I587N0, I587N1, I587N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI587N0
    exact isPrimeI587N1
    exact isPrimeI587N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 587 (by decide) (𝕀 ⊙ MulI587N0 ⊙ MulI587N1)
instance hp593 : Fact (Nat.Prime 593) := {out := by norm_num}

def I593N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 0, 0, 0, 0]] i)))

def SI593N0: IdealEqSpanCertificate' Table ![![593, 0, 0, 0, 0]] 
 ![![593, 0, 0, 0, 0], ![0, 593, 0, 0, 0], ![0, 0, 593, 0, 0], ![0, 0, 0, 593, 0], ![0, 0, 0, 0, 593]] where
  M :=![![![593, 0, 0, 0, 0], ![0, 593, 0, 0, 0], ![0, 0, 593, 0, 0], ![0, 0, 0, 593, 0], ![0, 0, 0, 0, 593]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P593P0 : CertificateIrreducibleZModOfList' 593 5 2 9 [191, 353, 317, 235, 143, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [444, 207, 381, 473, 534], [543, 269, 216, 528, 289], [509, 90, 289, 241, 269], [140, 26, 300, 537, 94], [0, 1]]
 g := ![![[541, 384, 306, 235, 301], [204, 428, 80, 522], [79, 526, 342, 315], [456, 245, 82, 225], [404, 104, 187, 3, 256], [576, 242, 229, 62], [69, 353, 52, 450, 1], [], []], ![[383, 504, 58, 3, 579, 1, 197, 277], [376, 212, 131, 305], [588, 151, 430, 97], [523, 315, 354, 162], [519, 549, 40, 103, 320, 105, 439, 279], [587, 461, 451, 510], [237, 150, 391, 201, 83, 405, 97, 142], [545, 111, 465, 157], [250, 47, 265, 516]], ![[402, 68, 79, 201, 407, 105, 241, 157], [564, 513, 511, 570], [117, 553, 9, 538], [288, 530, 216, 232], [229, 272, 185, 118, 416, 537, 260, 312], [319, 387, 231, 347], [311, 329, 153, 318, 522, 420, 407, 189], [199, 459, 119, 314], [27, 282, 492, 501]], ![[366, 555, 32, 224, 195, 336, 151, 501], [254, 459, 552, 495], [19, 264, 381, 19], [223, 328, 369, 528], [468, 322, 406, 347, 280, 271, 109, 521], [171, 365, 373, 17], [220, 281, 514, 416, 145, 116, 388, 568], [523, 546, 258, 562], [85, 507, 18, 15]], ![[286, 74, 552, 82, 193, 539, 7, 349], [160, 386, 51, 568], [13, 132, 505, 520], [222, 387, 130, 113], [313, 325, 57, 77, 149, 158, 564, 20], [419, 546, 53, 139], [391, 158, 458, 500, 63, 587, 271, 127], [320, 423, 500, 207], [209, 10, 281, 534]]]
 h' := ![![[444, 207, 381, 473, 534], [211, 111, 553, 458, 380], [464, 146, 525, 10, 119], [214, 418, 310, 433, 264], [519, 152, 190, 91, 578], [181, 366, 61, 394, 577], [460, 135, 138, 34, 282], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[543, 269, 216, 528, 289], [91, 56, 228, 480, 490], [515, 501, 325, 539, 155], [386, 164, 3, 216, 169], [282, 60, 408, 463, 92], [536, 560, 203, 357, 46], [24, 60, 244, 235, 223], [401, 573, 35, 98, 367], [543, 11, 486, 90, 549], [444, 207, 381, 473, 534]], ![[509, 90, 289, 241, 269], [240, 414, 221, 255, 177], [81, 266, 335, 104, 152], [303, 329, 76, 432, 529], [501, 233, 301, 345, 277], [8, 257, 390, 203, 392], [299, 353, 454, 166, 93], [520, 362, 420, 396, 504], [308, 436, 492, 139, 275], [543, 269, 216, 528, 289]], ![[140, 26, 300, 537, 94], [526, 357, 323, 455, 215], [553, 566, 303, 34, 552], [140, 187, 321, 263, 414], [464, 550, 458, 20, 103], [318, 400, 194, 449, 245], [369, 405, 264, 493, 69], [332, 534, 579, 151, 165], [309, 358, 440, 112, 487], [509, 90, 289, 241, 269]], ![[0, 1], [71, 248, 454, 131, 517], [338, 300, 291, 499, 208], [262, 88, 476, 435, 403], [447, 191, 422, 267, 136], [586, 196, 338, 376, 519], [352, 233, 86, 258, 519], [295, 310, 152, 541, 149], [436, 381, 360, 252, 468], [140, 26, 300, 537, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [395, 397, 9, 176], [], [], []]
 b := ![[], [375, 415, 380, 444, 204], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI593N0 : CertifiedPrimeIdeal' SI593N0 593 where
  n := 5
  hpos := by decide
  P := [191, 353, 317, 235, 143, 1]
  hirr := P593P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![610802568091812, 796219085419483, 842580804139891, 117451086027275, 557620621935932]
  a := ![21, 37, 37, -19, 92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1030021194084, 1342696602731, 1420878253187, 198062539675, 940338316924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI593N0 : Ideal.IsPrime I593N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI593N0 B_one_repr
lemma NI593N0 : Nat.card (O ⧸ I593N0) = 73328612386193 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI593N0

def PBC593 : ContainsPrimesAboveP 593 ![I593N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI593N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![593, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 593 (by decide) 𝕀



lemma PB853I11_primes (p : ℕ) :
  p ∈ Set.range ![541, 547, 557, 563, 569, 571, 577, 587, 593] ↔ Nat.Prime p ∧ 523 < p ∧ p ≤ 593 := by
  rw [← List.mem_ofFn']
  convert primes_range 523 593 (by omega)

def PB853I11 : PrimesBelowBoundCertificateInterval O 523 593 853 where
  m := 9
  g := ![3, 2, 3, 3, 2, 3, 2, 3, 1]
  P := ![541, 547, 557, 563, 569, 571, 577, 587, 593]
  hP := PB853I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I541N0, I541N1, I541N2]
    · exact ![I547N0, I547N1]
    · exact ![I557N0, I557N1, I557N2]
    · exact ![I563N0, I563N1, I563N2]
    · exact ![I569N0, I569N1]
    · exact ![I571N0, I571N1, I571N2]
    · exact ![I577N0, I577N1]
    · exact ![I587N0, I587N1, I587N2]
    · exact ![I593N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC541
    · exact PBC547
    · exact PBC557
    · exact PBC563
    · exact PBC569
    · exact PBC571
    · exact PBC577
    · exact PBC587
    · exact PBC593
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![158340421, 541, 541]
    · exact ![89526025681, 547]
    · exact ![310249, 310249, 557]
    · exact ![178453547, 563, 563]
    · exact ![104821185121, 569]
    · exact ![326041, 326041, 571]
    · exact ![110841719041, 577]
    · exact ![202262003, 587, 587]
    · exact ![73328612386193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI541N0
      exact NI541N1
      exact NI541N2
    · dsimp ; intro j
      fin_cases j
      exact NI547N0
      exact NI547N1
    · dsimp ; intro j
      fin_cases j
      exact NI557N0
      exact NI557N1
      exact NI557N2
    · dsimp ; intro j
      fin_cases j
      exact NI563N0
      exact NI563N1
      exact NI563N2
    · dsimp ; intro j
      fin_cases j
      exact NI569N0
      exact NI569N1
    · dsimp ; intro j
      fin_cases j
      exact NI571N0
      exact NI571N1
      exact NI571N2
    · dsimp ; intro j
      fin_cases j
      exact NI577N0
      exact NI577N1
    · dsimp ; intro j
      fin_cases j
      exact NI587N0
      exact NI587N1
      exact NI587N2
    · dsimp ; intro j
      fin_cases j
      exact NI593N0
  β := ![I541N1, I541N2, I547N1, I557N2, I563N1, I563N2, I569N1, I571N2, I577N1, I587N1, I587N2]
  Il := ![[I541N1, I541N2], [I547N1], [I557N2], [I563N1, I563N2], [I569N1], [I571N2], [I577N1], [I587N1, I587N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
