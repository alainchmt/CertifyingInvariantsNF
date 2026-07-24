
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp541 : Fact (Nat.Prime 541) := {out := by norm_num}

def I541N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-513, 253, 17, -94, 234]] i)))

def SI541N0: IdealEqSpanCertificate' Table ![![-513, 253, 17, -94, 234]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![0, 0, 541, 0, 0], ![482, 73, 531, 1, 0], ![166, 435, 507, 0, 1]] where
  M :=![![![-513, 253, 17, -94, 234], ![1684, -390, -46, 191, -564], ![-4130, 1357, 229, -511, 1146], ![1900, -919, -74, 334, -828], ![646, -298, -74, 80, -85]]]
  hmulB := by decide  
  f := ![![![301, -93, -63, 76, -144]], ![![-1000, 296, 198, -257, 456]], ![![3134, -999, -673, 793, -1542]], ![![3204, -1022, -689, 810, -1578]], ![![2226, -727, -491, 560, -1123]]]
  g := ![![![11, -175, -127, -94, 234], ![6, 427, 341, 191, -564], ![96, -850, -572, -511, 1146], ![-40, 619, 448, 334, -828], ![-44, 57, 1, 80, -85]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P0 : CertificateIrreducibleZModOfList' 541 3 2 9 [540, 455, 360, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [162, 518, 532], [19, 22, 9], [0, 1]]
 g := ![![[162, 291, 28], [447, 9], [285, 49, 397], [216, 25, 35], [334, 528, 31], [368, 397], [8, 453], [181, 1], []], ![[510, 353, 509, 23], [294, 130], [247, 245, 412, 366], [489, 271, 363, 140], [94, 193, 59, 34], [532, 211], [283, 187], [457, 484], [468, 81]], ![[313, 253, 2, 78], [424, 353], [474, 194, 460, 440], [376, 84, 267, 375], [243, 500, 365, 100], [162, 375], [15, 496], [239, 529], [450, 81]]]
 h' := ![![[162, 518, 532], [522, 278, 475], [285, 344, 3], [216, 317, 83], [334, 387, 24], [92, 439, 70], [309, 257, 83], [181, 419, 387], [0, 0, 1], [0, 1]], ![[19, 22, 9], [241, 167, 374], [358, 372, 216], [253, 270, 55], [275, 25, 291], [483, 158, 294], [364, 27, 54], [9, 262, 415], [203, 417, 22], [162, 518, 532]], ![[0, 1], [427, 96, 233], [57, 366, 322], [517, 495, 403], [101, 129, 226], [283, 485, 177], [11, 257, 404], [104, 401, 280], [270, 124, 518], [19, 22, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [327, 447], []]
 b := ![[], [169, 532, 230], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N0 : CertifiedPrimeIdeal' SI541N0 541 where
  n := 3
  hpos := by decide
  P := [540, 455, 360, 1]
  hirr := P541P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-63967274, -21758335, -15659354, -22561081, -28982154]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28875252, 26307648, 49275835, -22561081, -28982154]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N0 : Ideal.IsPrime I541N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N0 B_one_repr
lemma NI541N0 : Nat.card (O ⧸ I541N0) = 158340421 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N0

def I541N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301, 93, 63, -76, 144]] i)))

def SI541N1: IdealEqSpanCertificate' Table ![![-301, 93, 63, -76, 144]] 
 ![![541, 0, 0, 0, 0], ![0, 541, 0, 0, 0], ![65, 29, 1, 0, 0], ![295, 472, 0, 1, 0], ![35, 470, 0, 0, 1]] where
  M :=![![![-301, 93, 63, -76, 144], ![1000, -296, -198, 257, -456], ![-3134, 999, 673, -793, 1542], ![2872, -785, -526, 744, -1224], ![-362, 136, 92, -88, 205]]]
  hmulB := by decide  
  f := ![![![513, -253, -17, 94, -234]], ![![-1684, 390, 46, -191, 564]], ![![-21, -12, 0, 2, 0]], ![![-1193, 204, 31, -116, 366]], ![![-1431, 323, 39, -160, 475]]]
  g := ![![![24, -62, 63, -76, 144], ![-85, 182, -198, 257, -456], ![246, -682, 673, -793, 1542], ![-258, 441, -526, 744, -1224], ![23, -106, 92, -88, 205]]]
  hle1 := by decide   
  hle2 := by decide  


def P541P1 : CertificateIrreducibleZModOfList' 541 2 2 9 [376, 329, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [212, 540], [0, 1]]
 g := ![![[339, 457], [449], [33, 16], [120, 125], [510, 515], [74], [110], [41], [1]], ![[384, 84], [449], [179, 525], [111, 416], [408, 26], [74], [110], [41], [1]]]
 h' := ![![[212, 540], [111, 323], [35, 461], [324, 4], [295, 102], [12, 296], [290, 507], [448, 207], [165, 212], [0, 1]], ![[0, 1], [421, 218], [387, 80], [90, 537], [279, 439], [8, 245], [115, 34], [511, 334], [206, 329], [212, 540]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [284]]
 b := ![[], [96, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI541N1 : CertifiedPrimeIdeal' SI541N1 541 where
  n := 2
  hpos := by decide
  P := [376, 329, 1]
  hirr := P541P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5010008, 4866934, 3747843, 2243437, 7167498]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2128052, -8376057, 3747843, 2243437, 7167498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI541N1 : Ideal.IsPrime I541N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI541N1 B_one_repr
lemma NI541N1 : Nat.card (O ⧸ I541N1) = 292681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI541N1
def MulI541N0 : IdealMulLeCertificate' Table 
  ![![-513, 253, 17, -94, 234]] ![![-301, 93, 63, -76, 144]]
  ![![541, 0, 0, 0, 0]] where
 M := ![![![-541, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC541 : ContainsPrimesAboveP 541 ![I541N0, I541N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI541N0
    exact isPrimeI541N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 541 (by decide) (𝕀 ⊙ MulI541N0)
instance hp547 : Fact (Nat.Prime 547) := {out := by norm_num}

def I547N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, 136, 98, 96, 186]] i)))

def SI547N0: IdealEqSpanCertificate' Table ![![253, 136, 98, 96, 186]] 
 ![![547, 0, 0, 0, 0], ![0, 547, 0, 0, 0], ![0, 0, 547, 0, 0], ![377, 274, 531, 1, 0], ![492, 24, 197, 0, 1]] where
  M :=![![![253, 136, 98, 96, 186], ![1680, 437, 326, 576, 576], ![5760, 2506, 1839, 2130, 3456], ![13116, 4150, 3074, 4603, 5604], ![3576, 1312, 962, 1278, 1783]]]
  hmulB := by decide  
  f := ![![![175, -76, -14, 24, -42]], ![![-288, 171, 10, -60, 144]], ![![1032, -214, -19, 114, -360]], ![![977, -174, -23, 97, -306]], ![![516, -138, -19, 60, -161]]]
  g := ![![![-233, -56, -160, 96, 186], ![-912, -313, -766, 576, 576], ![-4566, -1214, -3309, 2130, 3456], ![-8189, -2544, -6481, 4603, 5604], ![-2478, -716, -1881, 1278, 1783]]]
  hle1 := by decide   
  hle2 := by decide  


def P547P0 : CertificateIrreducibleZModOfList' 547 3 2 9 [485, 16, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 542, 400], [343, 4, 147], [0, 1]]
 g := ![![[20, 303, 276], [350, 516, 174], [154, 379], [544, 423], [176, 135], [145, 158, 188], [13, 527], [489, 1], []], ![[536, 272, 332, 117], [266, 306, 126, 312], [117, 143], [106, 4], [365, 122], [360, 436, 497, 527], [516, 449], [89, 16], [231, 276]], ![[545, 531, 296, 156], [490, 107, 348, 433], [52, 383], [450, 296], [119, 505], [520, 339, 233, 101], [152, 402], [505, 25], [484, 276]]]
 h' := ![![[146, 542, 400], [367, 285, 400], [270, 374, 412], [500, 406, 356], [275, 494, 104], [238, 495, 186], [395, 412, 113], [233, 443, 66], [0, 0, 1], [0, 1]], ![[343, 4, 147], [238, 195, 183], [456, 455, 276], [163, 287, 271], [75, 358, 2], [426, 521, 183], [457, 66, 58], [373, 295, 236], [83, 469, 4], [146, 542, 400]], ![[0, 1], [137, 67, 511], [86, 265, 406], [12, 401, 467], [544, 242, 441], [332, 78, 178], [138, 69, 376], [126, 356, 245], [514, 78, 542], [343, 4, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 392], []]
 b := ![[], [503, 315, 185], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI547N0 : CertifiedPrimeIdeal' SI547N0 547 where
  n := 3
  hpos := by decide
  P := [485, 16, 58, 1]
  hirr := P547P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49208074, -19659176, -14402148, -17856701, -26847332]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36365001, 10086678, 26977021, -17856701, -26847332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI547N0 : Ideal.IsPrime I547N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI547N0 B_one_repr
lemma NI547N0 : Nat.card (O ⧸ I547N0) = 163667323 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI547N0

def I547N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, -76, -14, 24, -42]] i)))

def SI547N1: IdealEqSpanCertificate' Table ![![175, -76, -14, 24, -42]] 
 ![![547, 0, 0, 0, 0], ![0, 547, 0, 0, 0], ![277, 47, 1, 0, 0], ![311, 283, 0, 1, 0], ![511, 226, 0, 0, 1]] where
  M :=![![![175, -76, -14, 24, -42], ![-288, 171, 10, -60, 144], ![1032, -214, -19, 114, -360], ![-636, 254, 46, -83, 156], ![-240, -40, -2, -6, 61]]]
  hmulB := by decide  
  f := ![![![253, 136, 98, 96, 186]], ![![1680, 437, 326, 576, 576]], ![![283, 111, 81, 102, 150]], ![![1037, 311, 230, 361, 414]], ![![937, 310, 228, 330, 415]]]
  g := ![![![33, 6, -14, 24, -42], ![-106, -29, 10, -60, 144], ![283, 91, -19, 114, -360], ![-123, -25, 46, -83, 156], ![-53, -22, -2, -6, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P547P1 : CertificateIrreducibleZModOfList' 547 2 2 9 [475, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [539, 546], [0, 1]]
 g := ![![[243, 509], [255, 237], [131], [214], [470], [422, 509], [529], [64], [1]], ![[0, 38], [0, 310], [131], [214], [470], [179, 38], [529], [64], [1]]]
 h' := ![![[539, 546], [309, 107], [323, 519], [298, 512], [166, 211], [299, 346], [526, 440], [493, 524], [72, 539], [0, 1]], ![[0, 1], [0, 440], [0, 28], [31, 35], [119, 336], [266, 201], [288, 107], [130, 23], [136, 8], [539, 546]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [317]]
 b := ![[], [87, 432]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI547N1 : CertifiedPrimeIdeal' SI547N1 547 where
  n := 2
  hpos := by decide
  P := [475, 8, 1]
  hirr := P547P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![795371, 806765, 635851, 354396, 1218197]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1660057, -739826, 635851, 354396, 1218197]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI547N1 : Ideal.IsPrime I547N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI547N1 B_one_repr
lemma NI547N1 : Nat.card (O ⧸ I547N1) = 299209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI547N1
def MulI547N0 : IdealMulLeCertificate' Table 
  ![![253, 136, 98, 96, 186]] ![![175, -76, -14, 24, -42]]
  ![![547, 0, 0, 0, 0]] where
 M := ![![![547, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I557N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 0, 0, 0, 0]] i)))

def SI557N0: IdealEqSpanCertificate' Table ![![557, 0, 0, 0, 0]] 
 ![![557, 0, 0, 0, 0], ![0, 557, 0, 0, 0], ![0, 0, 557, 0, 0], ![0, 0, 0, 557, 0], ![0, 0, 0, 0, 557]] where
  M :=![![![557, 0, 0, 0, 0], ![0, 557, 0, 0, 0], ![0, 0, 557, 0, 0], ![0, 0, 0, 557, 0], ![0, 0, 0, 0, 557]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P557P0 : CertificateIrreducibleZModOfList' 557 5 2 9 [304, 264, 265, 470, 140, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [526, 488, 295, 44, 340], [357, 239, 250, 92, 10], [285, 81, 90, 245, 23], [363, 305, 479, 176, 184], [0, 1]]
 g := ![![[449, 11, 293, 289, 529], [240, 75, 316, 33], [237, 446, 247, 442, 49], [310, 21, 105, 426, 323], [126, 18, 346, 231], [110, 65, 254, 78, 94], [222, 192, 417, 1], [], []], ![[466, 437, 156, 468, 190, 2, 16, 224], [285, 464, 436, 250], [56, 290, 494, 103, 363, 421, 556, 78], [238, 393, 461, 486, 6, 89, 196, 191], [525, 405, 261, 131], [243, 243, 158, 494, 140, 262, 505, 5], [307, 214, 326, 127], [37, 485, 145, 182], [89, 49, 34, 301]], ![[82, 193, 442, 165, 405, 485, 556, 407], [226, 195, 366, 83], [42, 194, 37, 280, 10, 85, 260, 184], [168, 407, 520, 356, 304, 284, 437, 90], [179, 442, 7, 248], [507, 410, 431, 209, 529, 20, 385, 127], [554, 207, 285, 70], [493, 445, 141, 250], [83, 92, 94, 100]], ![[209, 224, 536, 248, 29, 15, 393, 110], [66, 479, 261, 461], [304, 450, 265, 429, 458, 293, 540, 419], [322, 321, 263, 372, 52, 130, 90, 513], [298, 329, 174, 456], [174, 457, 15, 8, 332, 176, 6, 364], [394, 276, 258, 401], [409, 398, 202, 33], [483, 485, 151, 529]], ![[207, 506, 118, 164, 475, 342, 356, 205], [522, 402, 46, 515], [452, 340, 210, 496, 502, 412, 61, 413], [527, 370, 452, 180, 294, 502, 209, 518], [37, 175, 418, 467], [225, 362, 357, 39, 339, 337, 109, 401], [145, 145, 82, 24], [492, 4, 493, 553], [392, 89, 386, 436]]]
 h' := ![![[526, 488, 295, 44, 340], [156, 520, 47, 309, 534], [362, 449, 328, 386, 67], [450, 9, 432, 115, 550], [529, 144, 151, 182, 257], [537, 142, 106, 512, 429], [466, 551, 439, 77, 180], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[357, 239, 250, 92, 10], [213, 227, 485, 480, 47], [346, 494, 430, 332, 352], [168, 357, 457, 408, 373], [185, 220, 525, 203, 542], [466, 446, 355, 163, 503], [319, 552, 506, 171, 156], [264, 244, 395, 59, 144], [84, 420, 327, 116, 521], [526, 488, 295, 44, 340]], ![[285, 81, 90, 245, 23], [158, 448, 319, 349, 327], [56, 509, 314, 363, 328], [552, 474, 71, 384, 500], [420, 68, 491, 140, 554], [352, 122, 423, 284, 372], [200, 372, 79, 438, 78], [435, 383, 525, 57, 494], [286, 454, 346, 299, 205], [357, 239, 250, 92, 10]], ![[363, 305, 479, 176, 184], [127, 213, 548, 531, 125], [498, 9, 412, 394, 254], [220, 418, 296, 201, 215], [466, 401, 496, 9, 81], [405, 65, 328, 365, 399], [46, 398, 543, 111, 60], [111, 492, 232, 377, 422], [119, 145, 445, 169, 67], [285, 81, 90, 245, 23]], ![[0, 1], [479, 263, 272, 2, 81], [133, 210, 187, 196, 113], [350, 413, 415, 6, 33], [345, 281, 8, 23, 237], [357, 339, 459, 347, 525], [72, 355, 104, 317, 83], [362, 552, 519, 64, 53], [347, 95, 552, 530, 321], [363, 305, 479, 176, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [285, 427, 474, 449], [], [], []]
 b := ![[], [459, 8, 463, 497, 518], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI557N0 : CertifiedPrimeIdeal' SI557N0 557 where
  n := 5
  hpos := by decide
  P := [304, 264, 265, 470, 140, 1]
  hirr := P557P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-871475021380658, -328574991202466, -241477496881660, -313721090543838, -448162421457630]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1564587111994, -589901240938, -433532310380, -563233555734, -804600397590]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI557N0 : Ideal.IsPrime I557N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI557N0 B_one_repr
lemma NI557N0 : Nat.card (O ⧸ I557N0) = 53613724194557 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI557N0

def PBC557 : ContainsPrimesAboveP 557 ![I557N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI557N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![557, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 557 (by decide) 𝕀

instance hp563 : Fact (Nat.Prime 563) := {out := by norm_num}

def I563N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2053, -612, -411, 525, -948]] i)))

def SI563N0: IdealEqSpanCertificate' Table ![![2053, -612, -411, 525, -948]] 
 ![![563, 0, 0, 0, 0], ![0, 563, 0, 0, 0], ![371, 344, 1, 0, 0], ![558, 15, 0, 1, 0], ![108, 560, 0, 0, 1]] where
  M :=![![![2053, -612, -411, 525, -948], ![-6534, 2041, 1374, -1656, 3150], ![21888, -6414, -4301, 5616, -9936], ![-17634, 5832, 3936, -4421, 8970], ![2886, -738, -492, 756, -1157]]]
  hmulB := by decide  
  f := ![![![-9319, 3078, 381, -1239, 3138]], ![![22626, -7801, -1020, 3042, -7434]], ![![7589, -2704, -368, 1029, -2442]], ![![-8574, 2823, 348, -1139, 2892]], ![![20730, -7174, -942, 2790, -6797]]]
  g := ![![![-64, 1179, -411, 525, -948], ![120, -3925, 1374, -1656, 3150], ![-787, 12350, -4301, 5616, -9936], ![36, -11199, 3936, -4421, 8970], ![-198, 1430, -492, 756, -1157]]]
  hle1 := by decide   
  hle2 := by decide  


def P563P0 : CertificateIrreducibleZModOfList' 563 2 2 9 [471, 392, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [171, 562], [0, 1]]
 g := ![![[265, 503], [115, 351], [271], [391], [43, 113], [471, 223], [468], [528], [1]], ![[139, 60], [458, 212], [271], [391], [224, 450], [320, 340], [468], [528], [1]]]
 h' := ![![[171, 562], [446, 429], [361, 296], [165, 432], [15, 94], [544, 537], [69, 388], [177, 144], [92, 171], [0, 1]], ![[0, 1], [52, 134], [307, 267], [284, 131], [325, 469], [39, 26], [546, 175], [29, 419], [57, 392], [171, 562]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [470]]
 b := ![[], [457, 235]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI563N0 : CertifiedPrimeIdeal' SI563N0 563 where
  n := 2
  hpos := by decide
  P := [471, 392, 1]
  hirr := P563P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61589, 28868, 31528, -31840, 54876]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![145, -72948, 31528, -31840, 54876]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI563N0 : Ideal.IsPrime I563N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI563N0 B_one_repr
lemma NI563N0 : Nat.card (O ⧸ I563N0) = 316969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI563N0

def I563N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-283, -48, 33, 15, -66]] i)))

def SI563N1: IdealEqSpanCertificate' Table ![![-283, -48, 33, 15, -66]] 
 ![![563, 0, 0, 0, 0], ![73, 1, 0, 0, 0], ![301, 0, 1, 0, 0], ![307, 0, 0, 1, 0], ![180, 0, 0, 0, 1]] where
  M :=![![![-283, -48, 33, 15, -66], ![-498, -367, -36, 48, 90], ![816, -324, -187, 30, 288], ![894, 210, -90, -55, 186], ![-150, 390, 126, -42, -223]]]
  hmulB := by decide  
  f := ![![![-93023, 28734, 19329, -23637, 44376]], ![![-11515, 3563, 2397, -2925, 5502]], ![![-51469, 15906, 10700, -13077, 24564]], ![![-49177, 15228, 10245, -12490, 23514]], ![![-29946, 9258, 6228, -7608, 14297]]]
  g := ![![![1, -48, 33, 15, -66], ![11, -367, -36, 48, 90], ![35, -324, -187, 30, 288], ![-7, 210, -90, -55, 186], ![-24, 390, 126, -42, -223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI563N1 : Nat.card (O ⧸ I563N1) = 563 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI563N1)

lemma isPrimeI563N1 : Ideal.IsPrime I563N1 := prime_ideal_of_norm_prime hp563.out _ NI563N1

def I563N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1341, 429, 290, -339, 662]] i)))

def SI563N2: IdealEqSpanCertificate' Table ![![-1341, 429, 290, -339, 662]] 
 ![![563, 0, 0, 0, 0], ![207, 1, 0, 0, 0], ![502, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![216, 0, 0, 0, 1]] where
  M :=![![![-1341, 429, 290, -339, 662], ![4618, -1308, -878, 1193, -2034], ![-13886, 4655, 3149, -3475, 7158], ![13682, -3335, -2216, 3616, -5242], ![-1444, 682, 466, -330, 1029]]]
  hmulB := by decide  
  f := ![![![-21955, 21719, 9236, -1877, -16754]], ![![-8317, 7897, 3408, -674, -6180]], ![![-19704, 19105, 8183, -1641, -14842]], ![![-4875, 4878, 2066, -423, -3748]], ![![-8208, 8532, 3566, -748, -6471]]]
  g := ![![![-595, 429, 290, -339, 662], ![1779, -1308, -878, 1193, -2034], ![-6494, 4655, 3149, -3475, 7158], ![4409, -3335, -2216, 3616, -5242], ![-988, 682, 466, -330, 1029]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI563N2 : Nat.card (O ⧸ I563N2) = 563 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI563N2)

lemma isPrimeI563N2 : Ideal.IsPrime I563N2 := prime_ideal_of_norm_prime hp563.out _ NI563N2

def I563N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![125, 17, -4, 1, -14]] i)))

def SI563N3: IdealEqSpanCertificate' Table ![![125, 17, -4, 1, -14]] 
 ![![563, 0, 0, 0, 0], ![502, 1, 0, 0, 0], ![220, 0, 1, 0, 0], ![210, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![125, 17, -4, 1, -14], ![-110, 116, 24, -25, 6], ![-2, -153, 17, 53, -150], ![-402, -51, 10, -6, 58], ![120, 0, -26, -8, 63]]]
  hmulB := by decide  
  f := ![![![-17349, 4947, 3314, -4473, 7682]], ![![-15376, 4380, 2934, -3965, 6802]], ![![-7114, 2023, 1355, -1835, 3142]], ![![-6236, 1751, 1172, -1612, 2722]], ![![-974, 272, 182, -252, 423]]]
  g := ![![![-13, 17, -4, 1, -14], ![-104, 116, 24, -25, 6], ![118, -153, 17, 53, -150], ![40, -51, 10, -6, 58], ![10, 0, -26, -8, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI563N3 : Nat.card (O ⧸ I563N3) = 563 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI563N3)

lemma isPrimeI563N3 : Ideal.IsPrime I563N3 := prime_ideal_of_norm_prime hp563.out _ NI563N3
def MulI563N0 : IdealMulLeCertificate' Table 
  ![![2053, -612, -411, 525, -948]] ![![-283, -48, 33, 15, -66]]
  ![![-49, -246, -60, 30, 108]] where
 M := ![![![-49, -246, -60, 30, 108]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI563N1 : IdealMulLeCertificate' Table 
  ![![-49, -246, -60, 30, 108]] ![![-1341, 429, 290, -339, 662]]
  ![![17349, -4947, -3314, 4473, -7682]] where
 M := ![![![17349, -4947, -3314, 4473, -7682]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI563N2 : IdealMulLeCertificate' Table 
  ![![17349, -4947, -3314, 4473, -7682]] ![![125, 17, -4, 1, -14]]
  ![![563, 0, 0, 0, 0]] where
 M := ![![![-563, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC563 : ContainsPrimesAboveP 563 ![I563N0, I563N1, I563N2, I563N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI563N0
    exact isPrimeI563N1
    exact isPrimeI563N2
    exact isPrimeI563N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 563 (by decide) (𝕀 ⊙ MulI563N0 ⊙ MulI563N1 ⊙ MulI563N2)
instance hp569 : Fact (Nat.Prime 569) := {out := by norm_num}

def I569N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 0, 0, 0, 0]] i)))

def SI569N0: IdealEqSpanCertificate' Table ![![569, 0, 0, 0, 0]] 
 ![![569, 0, 0, 0, 0], ![0, 569, 0, 0, 0], ![0, 0, 569, 0, 0], ![0, 0, 0, 569, 0], ![0, 0, 0, 0, 569]] where
  M :=![![![569, 0, 0, 0, 0], ![0, 569, 0, 0, 0], ![0, 0, 569, 0, 0], ![0, 0, 0, 569, 0], ![0, 0, 0, 0, 569]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P569P0 : CertificateIrreducibleZModOfList' 569 5 2 9 [23, 122, 266, 152, 333, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [522, 21, 413, 186, 12], [149, 121, 121, 489, 479], [22, 239, 348, 385, 319], [112, 187, 256, 78, 328], [0, 1]]
 g := ![![[101, 358, 81, 309, 537], [262, 486, 61, 113], [80, 200, 474, 197], [271, 147, 364, 313, 126], [391, 96, 456, 110, 435], [62, 399, 285, 370, 70], [40, 351, 236, 1], [], []], ![[68, 239, 213, 444, 220, 510, 128, 446], [127, 15, 247, 529], [356, 15, 545, 331], [54, 443, 299, 473, 404, 192, 363, 190], [411, 148, 390, 551, 535, 425, 170, 420], [236, 8, 184, 478, 338, 68, 326, 27], [62, 196, 361, 383], [267, 129, 485, 407], [566, 314, 325, 144]], ![[180, 146, 565, 517, 242, 94, 364, 159], [290, 99, 558, 262], [533, 265, 363, 506], [0, 378, 147, 251, 355, 94, 244, 397], [488, 35, 218, 82, 466, 487, 459, 249], [565, 282, 170, 277, 339, 176, 295, 324], [537, 544, 42, 215], [445, 43, 299, 251], [11, 122, 504, 134]], ![[162, 547, 375, 466, 74, 443, 20, 20], [197, 447, 321, 231], [449, 416, 446, 229], [177, 51, 152, 48, 44, 294, 565, 134], [273, 70, 20, 538, 338, 261, 412, 221], [149, 191, 469, 6, 431, 189, 460, 121], [142, 239, 238, 387], [66, 500, 415, 435], [156, 202, 204, 479]], ![[419, 284, 279, 314, 540, 1, 363, 1], [49, 514, 309, 1], [274, 129, 403, 196], [179, 84, 23, 124, 373, 415, 563, 69], [568, 416, 423, 525, 168, 506, 15, 450], [309, 48, 121, 489, 425, 423, 307, 249], [89, 416, 304, 35], [537, 21, 79, 165], [515, 535, 433, 43]]]
 h' := ![![[522, 21, 413, 186, 12], [340, 5, 146, 564, 295], [543, 166, 44, 250, 64], [26, 345, 321, 7, 127], [111, 32, 282, 453, 247], [281, 57, 355, 315, 343], [218, 134, 286, 333, 162], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[149, 121, 121, 489, 479], [65, 44, 275, 216, 335], [489, 139, 85, 124, 23], [43, 246, 539, 354, 539], [77, 326, 524, 191, 474], [96, 75, 124, 396, 220], [371, 565, 83, 18, 286], [122, 264, 460, 432, 530], [2, 274, 277, 150, 332], [522, 21, 413, 186, 12]], ![[22, 239, 348, 385, 319], [192, 102, 63, 296, 329], [177, 224, 383, 368, 444], [183, 268, 95, 553, 502], [324, 319, 476, 171, 489], [396, 286, 394, 163, 268], [342, 422, 382, 277, 50], [449, 318, 554, 316, 541], [326, 46, 244, 64, 113], [149, 121, 121, 489, 479]], ![[112, 187, 256, 78, 328], [54, 2, 292, 274, 157], [452, 488, 365, 75, 37], [274, 137, 304, 53, 525], [165, 5, 384, 504, 419], [76, 63, 343, 198, 550], [31, 169, 355, 22, 361], [128, 521, 313, 196, 415], [310, 494, 463, 517, 343], [22, 239, 348, 385, 319]], ![[0, 1], [208, 416, 362, 357, 22], [127, 121, 261, 321, 1], [369, 142, 448, 171, 14], [121, 456, 41, 388, 78], [68, 88, 491, 66, 326], [238, 417, 32, 488, 279], [566, 35, 380, 194, 220], [130, 324, 153, 407, 350], [112, 187, 256, 78, 328]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 353, 297, 175], [], [], []]
 b := ![[], [495, 271, 58, 63, 507], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI569N0 : CertifiedPrimeIdeal' SI569N0 569 where
  n := 5
  hpos := by decide
  P := [23, 122, 266, 152, 333, 1]
  hirr := P569P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9004375345077, 3148246181253, 2320381965860, 3203519593471, 4273762845302]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15824912733, 5532945837, 4077999940, 5630087159, 7511006758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI569N0 : Ideal.IsPrime I569N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI569N0 B_one_repr
lemma NI569N0 : Nat.card (O ⧸ I569N0) = 59643254333849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI569N0

def PBC569 : ContainsPrimesAboveP 569 ![I569N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI569N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![569, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 569 (by decide) 𝕀

instance hp571 : Fact (Nat.Prime 571) := {out := by norm_num}

def I571N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![267, 3, -47, -12, 100]] i)))

def SI571N0: IdealEqSpanCertificate' Table ![![267, 3, -47, -12, 100]] 
 ![![571, 0, 0, 0, 0], ![0, 571, 0, 0, 0], ![239, 1, 1, 0, 0], ![0, 460, 0, 1, 0], ![115, 227, 0, 0, 1]] where
  M :=![![![267, 3, -47, -12, 100], ![776, 402, 14, -53, -72], ![-682, 637, 229, -83, -318], ![-872, -91, 134, 50, -296], ![-110, -580, -136, 72, 237]]]
  hmulB := by decide  
  f := ![![![2039, -505, -337, 538, -794]], ![![-5276, 2120, 1446, -1267, 3228]], ![![885, -216, -144, 234, -340]], ![![-4268, 1721, 1174, -1024, 2620]], ![![-1679, 741, 507, -393, 1123]]]
  g := ![![![0, -30, -47, -12, 100], ![10, 72, 14, -53, -72], ![-33, 194, 229, -83, -318], ![2, 77, 134, 50, -296], ![9, -153, -136, 72, 237]]]
  hle1 := by decide   
  hle2 := by decide  


def P571P0 : CertificateIrreducibleZModOfList' 571 2 2 9 [387, 293, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [278, 570], [0, 1]]
 g := ![![[467, 481], [238, 521], [354], [152, 484], [261, 214], [180, 481], [329], [199], [1]], ![[0, 90], [42, 50], [354], [519, 87], [369, 357], [284, 90], [329], [199], [1]]]
 h' := ![![[278, 570], [396, 167], [163, 194], [560, 156], [60, 22], [2, 181], [31, 167], [239, 30], [184, 278], [0, 1]], ![[0, 1], [0, 404], [421, 377], [532, 415], [466, 549], [72, 390], [206, 404], [14, 541], [383, 293], [278, 570]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [320]]
 b := ![[], [29, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N0 : CertifiedPrimeIdeal' SI571N0 571 where
  n := 2
  hpos := by decide
  P := [387, 293, 1]
  hirr := P571P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5199, 3391, 760, 2659, 854]
  a := ![-8, -6, -11, -1, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-481, -2477, 760, 2659, 854]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI571N0 : Ideal.IsPrime I571N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI571N0 B_one_repr
lemma NI571N0 : Nat.card (O ⧸ I571N0) = 326041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI571N0

def I571N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, 0, 3, -7, 12]] i)))

def SI571N1: IdealEqSpanCertificate' Table ![![-33, 0, 3, -7, 12]] 
 ![![571, 0, 0, 0, 0], ![0, 571, 0, 0, 0], ![365, 212, 1, 0, 0], ![404, 247, 0, 1, 0], ![332, 329, 0, 0, 1]] where
  M :=![![![-33, 0, 3, -7, 12], ![82, -31, -24, 14, -42], ![-308, 78, 35, -100, 84], ![82, -104, -82, 1, -186], ![-110, -20, -4, -22, -7]]]
  hmulB := by decide  
  f := ![![![4243, -1466, -181, 577, -1434]], ![![-10318, 3567, 446, -1400, 3462]], ![![-1075, 372, 48, -145, 354]], ![![-1488, 515, 66, -201, 492]], ![![-3484, 1205, 152, -472, 1163]]]
  g := ![![![-4, -5, 3, -7, 12], ![30, 27, -24, 14, -42], ![-1, -18, 35, -100, 84], ![160, 137, -82, 1, -186], ![22, 15, -4, -22, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P571P1 : CertificateIrreducibleZModOfList' 571 2 2 9 [278, 387, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [184, 570], [0, 1]]
 g := ![![[291, 305], [554, 283], [554], [111, 467], [126, 52], [321, 36], [431], [167], [1]], ![[453, 266], [94, 288], [554], [389, 104], [558, 519], [93, 535], [431], [167], [1]]]
 h' := ![![[184, 570], [158, 154], [163, 448], [547, 211], [374, 141], [409, 223], [97, 565], [24, 370], [293, 184], [0, 1]], ![[0, 1], [515, 417], [371, 123], [543, 360], [52, 430], [329, 348], [135, 6], [155, 201], [460, 387], [184, 570]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [342]]
 b := ![[], [256, 171]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI571N1 : CertifiedPrimeIdeal' SI571N1 571 where
  n := 2
  hpos := by decide
  P := [278, 387, 1]
  hirr := P571P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33746, 24947, 25351, 12066, 48528]
  a := ![16, 10, 23, 2, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-52899, -42549, 25351, 12066, 48528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI571N1 : Ideal.IsPrime I571N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI571N1 B_one_repr
lemma NI571N1 : Nat.card (O ⧸ I571N1) = 326041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI571N1

def I571N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -19, 2, 5, -14]] i)))

def SI571N2: IdealEqSpanCertificate' Table ![![55, -19, 2, 5, -14]] 
 ![![571, 0, 0, 0, 0], ![358, 1, 0, 0, 0], ![311, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![546, 0, 0, 0, 1]] where
  M :=![![![55, -19, 2, 5, -14], ![-102, 44, -6, -3, 30], ![234, -69, 41, 9, -18], ![2, 53, -16, 40, 22], ![-76, 38, 14, -10, 45]]]
  hmulB := by decide  
  f := ![![![6073, 4511, 332, -661, -662]], ![![3796, 2836, 212, -415, -422]], ![![3251, 2434, 183, -356, -364]], ![![343, 252, 18, -37, -36]], ![![5846, 4322, 314, -634, -627]]]
  g := ![![![24, -19, 2, 5, -14], ![-53, 44, -6, -3, 30], ![38, -69, 41, 9, -18], ![-48, 53, -16, 40, 22], ![-74, 38, 14, -10, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI571N2 : Nat.card (O ⧸ I571N2) = 571 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI571N2)

lemma isPrimeI571N2 : Ideal.IsPrime I571N2 := prime_ideal_of_norm_prime hp571.out _ NI571N2
def MulI571N0 : IdealMulLeCertificate' Table 
  ![![267, 3, -47, -12, 100]] ![![-33, 0, 3, -7, 12]]
  ![![-6073, -4511, -332, 661, 662]] where
 M := ![![![-6073, -4511, -332, 661, 662]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI571N1 : IdealMulLeCertificate' Table 
  ![![-6073, -4511, -332, 661, 662]] ![![55, -19, 2, 5, -14]]
  ![![571, 0, 0, 0, 0]] where
 M := ![![![-571, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I577N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![205, 104, -9, -25, 2]] i)))

def SI577N0: IdealEqSpanCertificate' Table ![![205, 104, -9, -25, 2]] 
 ![![577, 0, 0, 0, 0], ![0, 577, 0, 0, 0], ![0, 0, 577, 0, 0], ![489, 283, 36, 1, 0], ![445, 416, 157, 0, 1]] where
  M :=![![![205, 104, -9, -25, 2], ![-34, 191, 38, -50, -150], ![-1300, -272, 3, -86, -300], ![-1302, -590, -164, -171, -322], ![318, -104, -134, -76, 57]]]
  hmulB := by decide  
  f := ![![![867, -262, -183, 225, -412]], ![![-2846, 863, 596, -736, 1350]], ![![9328, -2828, -1941, 2402, -4416]], ![![-93, 29, 19, -24, 44]], ![![1157, -350, -240, 297, -547]]]
  g := ![![![20, 11, 1, -25, 2], ![158, 133, 44, -50, -150], ![302, 258, 87, -86, -300], ![391, 315, 98, -171, -322], ![21, -4, -11, -76, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P577P0 : CertificateIrreducibleZModOfList' 577 3 2 9 [166, 423, 158, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [209, 306, 162], [210, 270, 415], [0, 1]]
 g := ![![[322, 443, 248], [252, 573], [20, 298], [434, 288], [69, 377], [96, 25], [448, 492, 198], [419, 1], []], ![[175, 36, 432, 9], [500, 277], [106, 528], [80, 368], [20, 91], [158, 131], [48, 349, 464, 283], [234, 198], [247, 279]], ![[230, 181, 458, 329], [565, 23], [442, 209], [462, 196], [88, 526], [183, 365], [330, 546, 576, 554], [538, 162], [571, 279]]]
 h' := ![![[209, 306, 162], [487, 354, 210], [270, 28, 529], [272, 272, 426], [477, 13, 169], [406, 339, 82], [65, 520, 5], [263, 313, 307], [0, 0, 1], [0, 1]], ![[210, 270, 415], [55, 565, 379], [431, 458, 231], [522, 428, 409], [115, 244, 422], [127, 121, 317], [393, 256, 194], [130, 393, 309], [371, 193, 270], [209, 306, 162]], ![[0, 1], [253, 235, 565], [99, 91, 394], [527, 454, 319], [530, 320, 563], [504, 117, 178], [85, 378, 378], [149, 448, 538], [90, 384, 306], [210, 270, 415]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [573, 163], []]
 b := ![[], [213, 454, 259], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI577N0 : CertifiedPrimeIdeal' SI577N0 577 where
  n := 3
  hpos := by decide
  P := [166, 423, 158, 1]
  hirr := P577P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![83970238, 59022361, 43881140, 33974099, 84266974]
  a := ![24, 18, 37, -5, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-93636339, -77314920, -24972446, 33974099, 84266974]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI577N0 : Ideal.IsPrime I577N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI577N0 B_one_repr
lemma NI577N0 : Nat.card (O ⧸ I577N0) = 192100033 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI577N0

def I577N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-867, 262, 183, -225, 412]] i)))

def SI577N1: IdealEqSpanCertificate' Table ![![-867, 262, 183, -225, 412]] 
 ![![577, 0, 0, 0, 0], ![0, 577, 0, 0, 0], ![53, 468, 1, 0, 0], ![20, 252, 0, 1, 0], ![341, 555, 0, 0, 1]] where
  M :=![![![-867, 262, 183, -225, 412], ![2846, -863, -596, 736, -1350], ![-9328, 2828, 1941, -2402, 4416], ![8014, -2430, -1658, 2057, -3782], ![-1214, 372, 244, -306, 567]]]
  hmulB := by decide  
  f := ![![![-205, -104, 9, 25, -2]], ![![34, -191, -38, 50, 150]], ![![11, -164, -30, 43, 122]], ![![10, -86, -16, 23, 66]], ![![-89, -245, -31, 63, 143]]]
  g := ![![![-254, -446, 183, -225, 412], ![832, 1459, -596, 736, -1350], ![-2721, -4768, 1941, -2402, 4416], ![2330, 4080, -1658, 2057, -3782], ![-349, -609, 244, -306, 567]]]
  hle1 := by decide   
  hle2 := by decide  


def P577P1 : CertificateIrreducibleZModOfList' 577 2 2 9 [331, 211, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [366, 576], [0, 1]]
 g := ![![[100, 558], [533], [44], [205], [54], [501], [184, 469], [92], [1]], ![[70, 19], [533], [44], [205], [54], [501], [469, 108], [92], [1]]]
 h' := ![![[366, 576], [531, 262], [476, 416], [302, 402], [542, 44], [554, 228], [258, 524], [60, 254], [246, 366], [0, 1]], ![[0, 1], [64, 315], [404, 161], [299, 175], [490, 533], [337, 349], [478, 53], [127, 323], [338, 211], [366, 576]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148]]
 b := ![[], [306, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI577N1 : CertifiedPrimeIdeal' SI577N1 577 where
  n := 2
  hpos := by decide
  P := [331, 211, 1]
  hirr := P577P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13135, 9590, 9289, 4603, 18200]
  a := ![11, 7, 14, 1, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11746, -27034, 9289, 4603, 18200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI577N1 : Ideal.IsPrime I577N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI577N1 B_one_repr
lemma NI577N1 : Nat.card (O ⧸ I577N1) = 332929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI577N1
def MulI577N0 : IdealMulLeCertificate' Table 
  ![![205, 104, -9, -25, 2]] ![![-867, 262, 183, -225, 412]]
  ![![577, 0, 0, 0, 0]] where
 M := ![![![-577, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I587N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4391, 783, -372, 397, -1384]] i)))

def SI587N0: IdealEqSpanCertificate' Table ![![4391, 783, -372, 397, -1384]] 
 ![![587, 0, 0, 0, 0], ![0, 587, 0, 0, 0], ![0, 0, 587, 0, 0], ![204, 137, 217, 1, 0], ![334, 177, 180, 0, 1]] where
  M :=![![![4391, 783, -372, 397, -1384], ![-10278, 3776, 2346, -2103, 2382], ![14850, -12345, -4879, 7317, -12618], ![-27246, 1953, 3984, -4908, 11222], ![10692, 804, -1284, 422, -405]]]
  hmulB := by decide  
  f := ![![![46297, -15963, -1950, 6347, -15476]], ![![-111114, 39118, 5028, -14979, 38082]], ![![274698, -93039, -10847, 38187, -89874]], ![![91434, -30710, -3499, 12792, -29614]], ![![77012, -25794, -2916, 10797, -24859]]]
  g := ![![![657, 326, 277, 397, -1384], ![-642, -221, 51, -2103, 2382], ![4662, 2076, 1156, 7317, -12618], ![-4726, -2235, -1620, -4908, 11222], ![102, 25, -34, 422, -405]]]
  hle1 := by decide   
  hle2 := by decide  


def P587P0 : CertificateIrreducibleZModOfList' 587 3 2 9 [42, 418, 330, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [448, 519, 387], [396, 67, 200], [0, 1]]
 g := ![![[185, 164, 84], [53, 414, 451], [174, 206], [515, 292, 515], [303, 579], [83, 380], [573, 359, 442], [257, 1], []], ![[225, 180, 424, 30], [236, 338, 153, 564], [276, 195], [435, 118, 268, 199], [366, 28], [233, 261], [280, 24, 471, 312], [119, 380], [67, 84]], ![[525, 151, 471, 263], [361, 411, 545, 358], [133, 343], [524, 489, 442, 111], [535, 270], [388, 490], [132, 80, 346, 557], [162, 515], [254, 84]]]
 h' := ![![[448, 519, 387], [122, 463, 200], [26, 104, 345], [89, 161, 445], [383, 397, 519], [37, 229, 414], [1, 494, 67], [359, 540, 474], [0, 0, 1], [0, 1]], ![[396, 67, 200], [447, 75, 45], [86, 510, 554], [500, 380, 550], [246, 65, 572], [535, 453, 135], [75, 111, 196], [43, 454, 68], [71, 284, 67], [448, 519, 387]], ![[0, 1], [261, 49, 342], [228, 560, 275], [231, 46, 179], [125, 125, 83], [570, 492, 38], [323, 569, 324], [465, 180, 45], [572, 303, 519], [396, 67, 200]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 295], []]
 b := ![[], [330, 3, 339], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI587N0 : CertifiedPrimeIdeal' SI587N0 587 where
  n := 3
  hpos := by decide
  P := [42, 418, 330, 1]
  hirr := P587P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-143478106, 26337501, 20406297, -44439616, 42825793]
  a := ![10, 24, 24, -50, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9167992, -2496764, 3330767, -44439616, 42825793]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI587N0 : Ideal.IsPrime I587N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI587N0 B_one_repr
lemma NI587N0 : Nat.card (O ⧸ I587N0) = 202262003 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI587N0

def I587N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46297, 15963, 1950, -6347, 15476]] i)))

def SI587N1: IdealEqSpanCertificate' Table ![![-46297, 15963, 1950, -6347, 15476]] 
 ![![587, 0, 0, 0, 0], ![0, 587, 0, 0, 0], ![276, 522, 1, 0, 0], ![202, 227, 0, 1, 0], ![344, 531, 0, 0, 1]] where
  M :=![![![-46297, 15963, 1950, -6347, 15476], ![111114, -39118, -5028, 14979, -38082], ![-274698, 93039, 10847, -38187, 89874], ![159678, -59979, -8850, 20340, -59110], ![35616, -13698, -2112, 4436, -13557]]]
  hmulB := by decide  
  f := ![![![-4391, -783, 372, -397, 1384]], ![![10278, -3776, -2346, 2103, -2382]], ![![7050, -3705, -1903, 1671, -1446]], ![![2510, -1733, -786, 685, -464]], ![![6706, -3876, -1902, 1669, -1343]]]
  g := ![![![-7881, -13252, 1950, -6347, 15476], ![19716, 33061, -5028, 14979, -38082], ![-45096, -76020, 10847, -38187, 89874], ![32074, 53373, -8850, 20340, -59110], ![7472, 12403, -2112, 4436, -13557]]]
  hle1 := by decide   
  hle2 := by decide  


def P587P1 : CertificateIrreducibleZModOfList' 587 2 2 9 [289, 262, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [325, 586], [0, 1]]
 g := ![![[7, 65], [104, 211], [195], [123, 510], [546], [114], [488, 407], [552], [1]], ![[0, 522], [0, 376], [195], [339, 77], [546], [114], [101, 180], [552], [1]]]
 h' := ![![[325, 586], [468, 69], [92, 435], [260, 37], [94, 446], [137, 528], [435, 124], [303, 355], [298, 325], [0, 1]], ![[0, 1], [0, 518], [0, 152], [545, 550], [55, 141], [333, 59], [232, 463], [39, 232], [263, 262], [325, 586]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [311]]
 b := ![[], [119, 449]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI587N1 : CertifiedPrimeIdeal' SI587N1 587 where
  n := 2
  hpos := by decide
  P := [289, 262, 1]
  hirr := P587P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4504, 6458, 5587, -5862, 8516]
  a := ![3, 8, 8, -15, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5608, -10394, 5587, -5862, 8516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI587N1 : Ideal.IsPrime I587N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI587N1 B_one_repr
lemma NI587N1 : Nat.card (O ⧸ I587N1) = 344569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI587N1
def MulI587N0 : IdealMulLeCertificate' Table 
  ![![4391, 783, -372, 397, -1384]] ![![-46297, 15963, 1950, -6347, 15476]]
  ![![587, 0, 0, 0, 0]] where
 M := ![![![-587, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC587 : ContainsPrimesAboveP 587 ![I587N0, I587N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI587N0
    exact isPrimeI587N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 587 (by decide) (𝕀 ⊙ MulI587N0)
instance hp593 : Fact (Nat.Prime 593) := {out := by norm_num}

def I593N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10137, 3019, 411, -1262, 3258]] i)))

def SI593N0: IdealEqSpanCertificate' Table ![![-10137, 3019, 411, -1262, 3258]] 
 ![![593, 0, 0, 0, 0], ![0, 593, 0, 0, 0], ![0, 0, 593, 0, 0], ![0, 0, 0, 593, 0], ![16, 154, 52, 530, 1]] where
  M :=![![![-10137, 3019, 411, -1262, 3258], ![23540, -8552, -1178, 3229, -7572], ![-54118, 20375, 2313, -7877, 19374], ![36220, -11037, -1478, 4596, -11820], ![6250, -2850, -146, 1112, -2945]]]
  hmulB := by decide  
  f := ![![![145, 53, 39, 52, 72]], ![![680, 230, 170, 241, 312]], ![![2978, 1063, 783, 1063, 1446]], ![![5784, 1999, 1474, 2054, 2712]], ![![5614, 1942, 1432, 1994, 2635]]]
  g := ![![![-105, -841, -285, -2914, 3258], ![244, 1952, 662, 6773, -7572], ![-614, -4997, -1695, -17329, 19374], ![380, 3051, 1034, 10572, -11820], ![90, 760, 258, 2634, -2945]]]
  hle1 := by decide   
  hle2 := by decide  


def P593P0 : CertificateIrreducibleZModOfList' 593 4 2 9 [334, 556, 455, 490, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [272, 232, 83, 18], [350, 508, 571, 462], [74, 445, 532, 113], [0, 1]]
 g := ![![[56, 478, 240, 113], [103, 195, 148], [175, 429, 38], [76, 241, 130], [300, 196, 446, 49], [423, 331, 17], [122, 423, 385, 528], [1], []], ![[113, 384, 434, 185, 200, 139], [89, 531, 23], [135, 147, 232], [466, 198, 445], [35, 421, 188, 86, 553, 414], [510, 484, 388], [200, 525, 458, 440, 339, 304], [141, 499, 473], [345, 187, 324]], ![[48, 13, 385, 209, 577, 244], [5, 459, 373], [484, 250, 109], [184, 465, 39], [371, 44, 136, 252, 523, 426], [517, 272, 441], [379, 386, 588, 225, 580, 176], [323, 206, 323], [63, 277, 557]], ![[265, 415, 448, 492, 140, 555], [486, 216, 123], [516, 490, 92], [242, 277, 547], [82, 38, 442, 412, 428, 169], [175, 76, 425], [514, 506, 185, 469, 354, 205], [128, 443, 563], [141, 379, 316]]]
 h' := ![![[272, 232, 83, 18], [65, 180, 78, 136], [398, 227, 51, 335], [404, 83, 70, 81], [17, 421, 65, 95], [542, 324, 371, 586], [169, 287, 153, 69], [259, 37, 138, 103], [0, 0, 1], [0, 1]], ![[350, 508, 571, 462], [240, 262, 219, 170], [113, 97, 264, 156], [214, 397, 425, 316], [133, 513, 24, 297], [499, 572, 400, 437], [184, 367, 97, 255], [68, 456, 509, 54], [264, 18, 221, 68], [272, 232, 83, 18]], ![[74, 445, 532, 113], [51, 128, 398, 542], [306, 544, 278, 465], [195, 349, 382, 508], [502, 215, 271, 558], [584, 576, 373, 394], [204, 74, 351, 21], [104, 336, 115, 514], [55, 342, 258, 491], [350, 508, 571, 462]], ![[0, 1], [286, 23, 491, 338], [543, 318, 0, 230], [575, 357, 309, 281], [501, 37, 233, 236], [331, 307, 42, 362], [65, 458, 585, 248], [341, 357, 424, 515], [485, 233, 113, 34], [74, 445, 532, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [501, 49, 163], []]
 b := ![[], [], [591, 187, 298, 214], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI593N0 : CertifiedPrimeIdeal' SI593N0 593 where
  n := 4
  hpos := by decide
  P := [334, 556, 455, 490, 1]
  hirr := P593P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![283810846012, 99186733868, 73075126578, 100929027414, 134584847808]
  a := ![16, 5, 17, 17, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3152692612, -34783945748, -11678477166, -120116425482, 134584847808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI593N0 : Ideal.IsPrime I593N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI593N0 B_one_repr
lemma NI593N0 : Nat.card (O ⧸ I593N0) = 123657019201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI593N0

def I593N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, -53, -39, -52, -72]] i)))

def SI593N1: IdealEqSpanCertificate' Table ![![-145, -53, -39, -52, -72]] 
 ![![593, 0, 0, 0, 0], ![378, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![435, 0, 0, 1, 0], ![514, 0, 0, 0, 1]] where
  M :=![![![-145, -53, -39, -52, -72], ![-680, -230, -170, -241, -312], ![-2978, -1063, -783, -1063, -1446], ![-5784, -1999, -1474, -2054, -2712], ![-1686, -592, -436, -600, -803]]]
  hmulB := by decide  
  f := ![![![10137, -3019, -411, 1262, -3258]], ![![6422, -1910, -260, 799, -2064]], ![![587, -182, -24, 75, -192]], ![![7375, -2196, -299, 918, -2370]], ![![8776, -2612, -356, 1092, -2819]]]
  g := ![![![136, -53, -39, -52, -72], ![601, -230, -170, -241, -312], ![2744, -1063, -783, -1063, -1446], ![5194, -1999, -1474, -2054, -2712], ![1532, -592, -436, -600, -803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI593N1 : Nat.card (O ⧸ I593N1) = 593 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI593N1)

lemma isPrimeI593N1 : Ideal.IsPrime I593N1 := prime_ideal_of_norm_prime hp593.out _ NI593N1
def MulI593N0 : IdealMulLeCertificate' Table 
  ![![-10137, 3019, 411, -1262, 3258]] ![![-145, -53, -39, -52, -72]]
  ![![593, 0, 0, 0, 0]] where
 M := ![![![-593, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC593 : ContainsPrimesAboveP 593 ![I593N0, I593N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI593N0
    exact isPrimeI593N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 593 (by decide) (𝕀 ⊙ MulI593N0)


lemma PB696I11_primes (p : ℕ) :
  p ∈ Set.range ![541, 547, 557, 563, 569, 571, 577, 587, 593] ↔ Nat.Prime p ∧ 523 < p ∧ p ≤ 593 := by
  rw [← List.mem_ofFn']
  convert primes_range 523 593 (by omega)

def PB696I11 : PrimesBelowBoundCertificateInterval O 523 593 696 where
  m := 9
  g := ![2, 2, 1, 4, 1, 3, 2, 2, 2]
  P := ![541, 547, 557, 563, 569, 571, 577, 587, 593]
  hP := PB696I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I541N0, I541N1]
    · exact ![I547N0, I547N1]
    · exact ![I557N0]
    · exact ![I563N0, I563N1, I563N2, I563N3]
    · exact ![I569N0]
    · exact ![I571N0, I571N1, I571N2]
    · exact ![I577N0, I577N1]
    · exact ![I587N0, I587N1]
    · exact ![I593N0, I593N1]
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
    · exact ![158340421, 292681]
    · exact ![163667323, 299209]
    · exact ![53613724194557]
    · exact ![316969, 563, 563, 563]
    · exact ![59643254333849]
    · exact ![326041, 326041, 571]
    · exact ![192100033, 332929]
    · exact ![202262003, 344569]
    · exact ![123657019201, 593]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI541N0
      exact NI541N1
    · dsimp ; intro j
      fin_cases j
      exact NI547N0
      exact NI547N1
    · dsimp ; intro j
      fin_cases j
      exact NI557N0
    · dsimp ; intro j
      fin_cases j
      exact NI563N0
      exact NI563N1
      exact NI563N2
      exact NI563N3
    · dsimp ; intro j
      fin_cases j
      exact NI569N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI593N0
      exact NI593N1
  β := ![I563N1, I563N2, I563N3, I571N2, I593N1]
  Il := ![[], [], [], [I563N1, I563N2, I563N3], [], [I571N2], [], [], [I593N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
