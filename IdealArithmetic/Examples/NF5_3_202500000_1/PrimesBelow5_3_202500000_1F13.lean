
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp647 : Fact (Nat.Prime 647) := {out := by norm_num}

def I647N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![603, -205, -29, 84, -206]] i)))

def SI647N0: IdealEqSpanCertificate' Table ![![603, -205, -29, 84, -206]] 
 ![![647, 0, 0, 0, 0], ![0, 647, 0, 0, 0], ![327, 470, 1, 0, 0], ![639, 390, 0, 1, 0], ![42, 97, 0, 0, 1]] where
  M :=![![![603, -205, -29, 84, -206], ![-1480, 510, 76, -209, 504], ![3614, -1261, -193, 523, -1254], ![-2284, 775, 128, -332, 796], ![-430, 160, 14, -58, 147]]]
  hmulB := by decide  
  f := ![![![211, 51, 45, 74, 104]], ![![980, 344, 228, 313, 444]], ![![825, 278, 190, 267, 378]], ![![811, 262, 185, 266, 376]], ![![164, 56, 38, 53, 75]]]
  g := ![![![-54, 1, -29, 84, -206], ![133, -4, 76, -209, 504], ![-332, 11, -193, 523, -1254], ![208, -11, 128, -332, 796], ![40, 3, 14, -58, 147]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P0 : CertificateIrreducibleZModOfList' 647 2 2 9 [642, 222, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [425, 646], [0, 1]]
 g := ![![[85, 388], [101, 50], [228, 36], [288], [117], [293], [225], [90, 112], [1]], ![[0, 259], [0, 597], [0, 611], [288], [117], [293], [225], [459, 535], [1]]]
 h' := ![![[425, 646], [505, 250], [493, 180], [609, 641], [254, 215], [221, 494], [467, 429], [450, 15], [5, 425], [0, 1]], ![[0, 1], [0, 397], [0, 467], [0, 6], [402, 432], [543, 153], [338, 218], [355, 632], [117, 222], [425, 646]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [263, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N0 : CertifiedPrimeIdeal' SI647N0 647 where
  n := 2
  hpos := by decide
  P := [642, 222, 1]
  hirr := P647P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42371, 25135, 15740, 17030, 28251]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26543, -25896, 15740, 17030, 28251]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI647N0 : Ideal.IsPrime I647N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N0 B_one_repr
lemma NI647N0 : Nat.card (O ⧸ I647N0) = 418609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N0

def I647N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -10, -4, 4, -2]] i)))

def SI647N1: IdealEqSpanCertificate' Table ![![11, -10, -4, 4, -2]] 
 ![![647, 0, 0, 0, 0], ![0, 647, 0, 0, 0], ![636, 627, 1, 0, 0], ![570, 503, 0, 1, 0], ![186, 404, 0, 0, 1]] where
  M :=![![![11, -10, -4, 4, -2], ![-8, 17, 6, -10, 24], ![172, 0, -19, 32, -60], ![-84, 60, 34, -21, 52], ![-12, -24, -2, 10, -3]]]
  hmulB := by decide  
  f := ![![![-435, 162, 20, -60, 146]], ![![1048, -369, -38, 146, -360]], ![![584, -197, -17, 82, -204]], ![![434, -145, -12, 61, -152]], ![![530, -184, -18, 74, -183]]]
  g := ![![![1, 2, -4, 4, -2], ![-4, -13, 6, -10, 24], ![8, 31, -19, 32, -60], ![-30, -49, 34, -21, 52], ![-6, -4, -2, 10, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P1 : CertificateIrreducibleZModOfList' 647 2 2 9 [616, 433, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [214, 646], [0, 1]]
 g := ![![[153, 632], [487, 153], [184, 454], [602], [6], [246], [578], [563, 506], [1]], ![[178, 15], [232, 494], [290, 193], [602], [6], [246], [578], [151, 141], [1]]]
 h' := ![![[214, 646], [216, 192], [528, 73], [18, 110], [267, 515], [638, 510], [58, 588], [631, 612], [31, 214], [0, 1]], ![[0, 1], [543, 455], [622, 574], [266, 537], [487, 132], [435, 137], [372, 59], [258, 35], [537, 433], [214, 646]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [495]]
 b := ![[], [368, 571]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N1 : CertifiedPrimeIdeal' SI647N1 647 where
  n := 2
  hpos := by decide
  P := [616, 433, 1]
  hirr := P647P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4985288, 4848110, 3710299, 2243333, 7092306]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7654766, -9760738, 3710299, 2243333, 7092306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI647N1 : Ideal.IsPrime I647N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N1 B_one_repr
lemma NI647N1 : Nat.card (O ⧸ I647N1) = 418609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N1

def I647N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -5, -3, -4, -6]] i)))

def SI647N2: IdealEqSpanCertificate' Table ![![-13, -5, -3, -4, -6]] 
 ![![647, 0, 0, 0, 0], ![197, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![641, 0, 0, 1, 0], ![160, 0, 0, 0, 1]] where
  M :=![![![-13, -5, -3, -4, -6], ![-56, -20, -14, -19, -24], ![-230, -85, -63, -85, -114], ![-456, -157, -118, -164, -216], ![-138, -46, -34, -48, -65]]]
  hmulB := by decide  
  f := ![![![1299, -469, -177, 290, -600]], ![![389, -141, -53, 87, -180]], ![![41, -14, -6, 9, -18]], ![![1273, -460, -173, 284, -588]], ![![322, -116, -44, 72, -149]]]
  g := ![![![7, -5, -3, -4, -6], ![31, -20, -14, -19, -24], ![139, -85, -63, -85, -114], ![265, -157, -118, -164, -216], ![78, -46, -34, -48, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI647N2 : Nat.card (O ⧸ I647N2) = 647 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI647N2)

lemma isPrimeI647N2 : Ideal.IsPrime I647N2 := prime_ideal_of_norm_prime hp647.out _ NI647N2
def MulI647N0 : IdealMulLeCertificate' Table 
  ![![603, -205, -29, 84, -206]] ![![11, -10, -4, 4, -2]]
  ![![-1299, 469, 177, -290, 600]] where
 M := ![![![-1299, 469, 177, -290, 600]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI647N1 : IdealMulLeCertificate' Table 
  ![![-1299, 469, 177, -290, 600]] ![![-13, -5, -3, -4, -6]]
  ![![647, 0, 0, 0, 0]] where
 M := ![![![-647, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC647 : ContainsPrimesAboveP 647 ![I647N0, I647N1, I647N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI647N0
    exact isPrimeI647N1
    exact isPrimeI647N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 647 (by decide) (𝕀 ⊙ MulI647N0 ⊙ MulI647N1)
instance hp653 : Fact (Nat.Prime 653) := {out := by norm_num}

def I653N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, 0, 0, 0, 0]] i)))

def SI653N0: IdealEqSpanCertificate' Table ![![653, 0, 0, 0, 0]] 
 ![![653, 0, 0, 0, 0], ![0, 653, 0, 0, 0], ![0, 0, 653, 0, 0], ![0, 0, 0, 653, 0], ![0, 0, 0, 0, 653]] where
  M :=![![![653, 0, 0, 0, 0], ![0, 653, 0, 0, 0], ![0, 0, 653, 0, 0], ![0, 0, 0, 653, 0], ![0, 0, 0, 0, 653]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P653P0 : CertificateIrreducibleZModOfList' 653 5 2 9 [158, 72, 427, 430, 179, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [572, 24, 610, 523, 293], [552, 402, 226, 86, 595], [345, 7, 400, 465, 195], [311, 219, 70, 232, 223], [0, 1]]
 g := ![![[451, 560, 404, 79, 378], [535, 296, 163, 354], [579, 13, 176, 23, 100], [227, 227, 568, 123, 23], [581, 576, 631, 233], [69, 396, 535, 59], [80, 193, 445, 44], [1], []], ![[611, 543, 601, 228, 590, 56, 306, 201], [300, 345, 387, 493], [225, 369, 421, 388, 510, 552, 417, 76], [346, 335, 314, 434, 202, 163, 393, 611], [448, 559, 85, 236], [611, 49, 159, 574], [322, 219, 49, 522], [506, 344, 255, 265, 109, 132, 455, 101], [65, 542, 299, 306]], ![[522, 95, 345, 503, 194, 314, 269, 574], [26, 611, 444, 47], [91, 177, 297, 613, 455, 607, 5, 349], [52, 268, 542, 112, 155, 47, 335, 452], [539, 558, 308, 205], [329, 306, 244, 517], [139, 423, 12, 637], [212, 447, 648, 408, 229, 458, 70, 257], [500, 179, 382, 99]], ![[27, 565, 570, 342, 531, 507, 630, 611], [439, 142, 199, 553], [602, 355, 289, 307, 65, 440, 452, 232], [419, 637, 242, 552, 384, 155, 319, 257], [262, 66], [616, 133, 484, 404], [277, 540, 178, 136], [205, 606, 526, 28, 157, 143, 516, 138], [441, 132, 213, 151]], ![[337, 457, 467, 369, 210, 118, 66, 17], [149, 120, 19, 386], [39, 631, 242, 79, 421, 445, 226, 393], [45, 386, 600, 461, 433, 527, 300, 564], [114, 471, 196, 599], [269, 40, 208, 138], [242, 463, 81, 212], [527, 637, 596, 426, 381, 46, 116, 372], [479, 552, 503, 101]]]
 h' := ![![[572, 24, 610, 523, 293], [286, 489, 593, 572, 255], [591, 451, 251, 44, 388], [49, 180, 561, 116, 643], [158, 326, 452, 471, 627], [558, 612, 556, 623, 448], [570, 211, 201, 426, 525], [495, 581, 226, 223, 474], [0, 0, 1], [0, 1]], ![[552, 402, 226, 86, 595], [209, 546, 177, 162, 268], [354, 64, 390, 640, 509], [409, 563, 357, 249, 408], [466, 372, 427, 187, 416], [217, 381, 568, 413, 256], [181, 254, 156, 498, 142], [164, 384, 647, 334, 399], [209, 481, 613, 564, 395], [572, 24, 610, 523, 293]], ![[345, 7, 400, 465, 195], [472, 85, 586, 628, 435], [3, 635, 22, 235, 312], [74, 34, 126, 164, 349], [131, 275, 607, 427, 41], [473, 334, 271, 345, 100], [614, 194, 530, 491, 155], [361, 454, 583, 101, 57], [419, 133, 294, 186, 266], [552, 402, 226, 86, 595]], ![[311, 219, 70, 232, 223], [202, 513, 456, 270, 169], [110, 340, 58, 195, 184], [135, 398, 79, 96, 580], [310, 104, 215, 456, 407], [111, 103, 555, 45], [427, 238, 587, 474, 446], [604, 456, 545, 549, 240], [372, 544, 180, 123, 197], [345, 7, 400, 465, 195]], ![[0, 1], [278, 326, 147, 327, 179], [213, 469, 585, 192, 566], [140, 131, 183, 28, 632], [223, 229, 258, 418, 468], [390, 529, 9, 533, 502], [242, 409, 485, 70, 38], [390, 84, 611, 99, 136], [143, 148, 218, 433, 448], [311, 219, 70, 232, 223]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 624, 424, 384], [], [], []]
 b := ![[], [19, 591, 587, 332, 567], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI653N0 : CertifiedPrimeIdeal' SI653N0 653 where
  n := 5
  hpos := by decide
  P := [158, 72, 427, 430, 179, 1]
  hirr := P653P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61622633552775, -21575047537896, -15900586472662, -21928815946141, -29290940944904]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-94368504675, -33039889032, -24350055854, -33581647697, -44855958568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI653N0 : Ideal.IsPrime I653N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI653N0 B_one_repr
lemma NI653N0 : Nat.card (O ⧸ I653N0) = 118731486838493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI653N0

def PBC653 : ContainsPrimesAboveP 653 ![I653N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI653N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![653, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 653 (by decide) 𝕀

instance hp659 : Fact (Nat.Prime 659) := {out := by norm_num}

def I659N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4751, 1156, 142, -548, 1572]] i)))

def SI659N0: IdealEqSpanCertificate' Table ![![-4751, 1156, 142, -548, 1572]] 
 ![![659, 0, 0, 0, 0], ![0, 659, 0, 0, 0], ![0, 0, 659, 0, 0], ![390, 313, 117, 1, 0], ![405, 135, 528, 0, 1]] where
  M :=![![![-4751, 1156, 142, -548, 1572], ![11480, -3869, -630, 1450, -3288], ![-23404, 10272, 1111, -3728, 8700], ![16740, -4380, -514, 2009, -5652], ![1716, -1878, -52, 606, -1375]]]
  hmulB := by decide  
  f := ![![![-10821, 3300, 2218, -2756, 5100]], ![![35288, -10695, -7186, 8998, -16536]], ![![-114292, 34936, 23485, -29096, 53988]], ![![-9786, 3031, 2039, -2485, 4680]], ![![-91015, 27835, 18712, -23168, 43013]]]
  g := ![![![-649, -60, -1162, -548, 1572], ![1180, -21, 2376, 1450, -3288], ![-3176, 4, -6307, -3728, 8700], ![2310, 197, 4171, 2009, -5652], ![489, -9, 994, 606, -1375]]]
  hle1 := by decide   
  hle2 := by decide  


def P659P0 : CertificateIrreducibleZModOfList' 659 3 2 9 [124, 607, 211, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 326, 365], [309, 332, 294], [0, 1]]
 g := ![![[153, 55, 402], [92, 401, 240], [450, 226], [225, 106], [304, 581, 33], [345, 209], [148, 14], [420, 448, 1], []], ![[496, 649, 103, 430], [581, 112, 507, 275], [107, 220], [459, 541], [462, 428, 186, 381], [168, 210], [182, 293], [514, 58, 397, 469], [569, 107]], ![[322, 573, 513, 113], [63, 413, 598, 412], [477, 299], [340, 166], [160, 394, 248, 565], [104, 262], [451, 445], [217, 277, 586, 636], [640, 107]]]
 h' := ![![[139, 326, 365], [454, 648, 66], [392, 206, 407], [333, 31, 415], [526, 319, 305], [378, 334, 106], [461, 648, 496], [640, 556, 452], [0, 0, 1], [0, 1]], ![[309, 332, 294], [62, 387, 104], [122, 165, 93], [139, 650, 161], [247, 489, 225], [583, 519, 260], [48, 371, 520], [520, 241, 439], [167, 190, 332], [139, 326, 365]], ![[0, 1], [51, 283, 489], [366, 288, 159], [74, 637, 83], [353, 510, 129], [160, 465, 293], [67, 299, 302], [574, 521, 427], [305, 469, 326], [309, 332, 294]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 47], []]
 b := ![[], [178, 335, 240], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI659N0 : CertifiedPrimeIdeal' SI659N0 659 where
  n := 3
  hpos := by decide
  P := [124, 607, 211, 1]
  hirr := P659P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9496586154, 4602431312, 3390817921, 3563794367, 6399558281]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6027624159, -2996670066, -5754992254, 3563794367, 6399558281]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI659N0 : Ideal.IsPrime I659N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI659N0 B_one_repr
lemma NI659N0 : Nat.card (O ⧸ I659N0) = 286191179 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI659N0

def I659N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -2, -1, 1, -2]] i)))

def SI659N1: IdealEqSpanCertificate' Table ![![5, -2, -1, 1, -2]] 
 ![![659, 0, 0, 0, 0], ![413, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![133, 0, 0, 1, 0], ![254, 0, 0, 0, 1]] where
  M :=![![![5, -2, -1, 1, -2], ![-14, 5, 2, -4, 6], ![40, -14, -9, 8, -24], ![-50, 8, 4, -13, 10], ![-2, -4, -2, 0, -3]]]
  hmulB := by decide  
  f := ![![![393, 20, -5, 21, -112]], ![![245, 13, -3, 13, -70]], ![![68, 2, -1, 4, -20]], ![![77, 4, -1, 4, -22]], ![![152, 8, -2, 8, -43]]]
  g := ![![![2, -2, -1, 1, -2], ![-5, 5, 2, -4, 6], ![18, -14, -9, 8, -24], ![-7, 8, 4, -13, 10], ![4, -4, -2, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI659N1 : Nat.card (O ⧸ I659N1) = 659 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI659N1)

lemma isPrimeI659N1 : Ideal.IsPrime I659N1 := prime_ideal_of_norm_prime hp659.out _ NI659N1

def I659N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1009, -308, -207, 257, -476]] i)))

def SI659N2: IdealEqSpanCertificate' Table ![![1009, -308, -207, 257, -476]] 
 ![![659, 0, 0, 0, 0], ![553, 1, 0, 0, 0], ![626, 0, 1, 0, 0], ![545, 0, 0, 1, 0], ![346, 0, 0, 0, 1]] where
  M :=![![![1009, -308, -207, 257, -476], ![-3294, 997, 670, -840, 1542], ![10656, -3262, -2193, 2712, -5040], ![-9178, 2752, 1848, -2345, 4258], ![1310, -410, -276, 332, -633]]]
  hmulB := by decide  
  f := ![![![-10003, 2622, 449, -1115, 2834]], ![![-8363, 2187, 375, -931, 2368]], ![![-9574, 2518, 429, -1070, 2720]], ![![-8219, 2154, 369, -916, 2328]], ![![-5244, 1374, 236, -584, 1483]]]
  g := ![![![494, -308, -207, 257, -476], ![-1593, 997, 670, -840, 1542], ![5240, -3262, -2193, 2712, -5040], ![-4375, 2752, 1848, -2345, 4258], ![666, -410, -276, 332, -633]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI659N2 : Nat.card (O ⧸ I659N2) = 659 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI659N2)

lemma isPrimeI659N2 : Ideal.IsPrime I659N2 := prime_ideal_of_norm_prime hp659.out _ NI659N2
def MulI659N0 : IdealMulLeCertificate' Table 
  ![![-4751, 1156, 142, -548, 1572]] ![![5, -2, -1, 1, -2]]
  ![![-10003, 2622, 449, -1115, 2834]] where
 M := ![![![-10003, 2622, 449, -1115, 2834]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI659N1 : IdealMulLeCertificate' Table 
  ![![-10003, 2622, 449, -1115, 2834]] ![![1009, -308, -207, 257, -476]]
  ![![659, 0, 0, 0, 0]] where
 M := ![![![659, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC659 : ContainsPrimesAboveP 659 ![I659N0, I659N1, I659N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI659N0
    exact isPrimeI659N1
    exact isPrimeI659N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 659 (by decide) (𝕀 ⊙ MulI659N0 ⊙ MulI659N1)
instance hp661 : Fact (Nat.Prime 661) := {out := by norm_num}

def I661N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, -54, -27, -1, 42]] i)))

def SI661N0: IdealEqSpanCertificate' Table ![![45, -54, -27, -1, 42]] 
 ![![661, 0, 0, 0, 0], ![0, 661, 0, 0, 0], ![0, 0, 661, 0, 0], ![175, 529, 516, 1, 0], ![320, 90, 531, 0, 1]] where
  M :=![![![45, -54, -27, -1, 42], ![334, 113, -30, -40, -6], ![-128, 318, 23, -136, -240], ![-662, -32, -40, -161, -354], ![-422, -344, -70, -4, 5]]]
  hmulB := by decide  
  f := ![![![271, -80, -61, 73, -132]], ![![-910, 273, 200, -242, 438]], ![![3020, -914, -653, 796, -1452]], ![![1697, -515, -365, 446, -816]], ![![2434, -736, -527, 642, -1171]]]
  g := ![![![-20, -5, -33, -1, 42], ![14, 33, 36, -40, -6], ![152, 142, 299, -136, -240], ![213, 177, 410, -161, -354], ![-2, 2, -1, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P661P0 : CertificateIrreducibleZModOfList' 661 3 2 9 [569, 352, 411, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [278, 564, 458], [633, 96, 203], [0, 1]]
 g := ![![[391, 448, 623], [525, 383], [221, 181, 320], [513, 366], [549, 237, 222], [491, 230], [496, 340], [14, 250, 1], []], ![[18, 125, 528, 501], [137, 383], [459, 459, 161, 430], [257, 261], [305, 604, 204, 543], [244, 451], [397, 564], [275, 396, 653, 443], [287, 227]], ![[586, 532, 364, 371], [], [358, 226, 565, 566], [390, 210], [619, 216], [511, 593], [294, 124], [657, 272, 236, 398], [542, 227]]]
 h' := ![![[278, 564, 458], [210, 341, 96], [502, 491, 387], [217, 15, 402], [272, 490, 411], [182, 282, 229], [518, 28, 363], [627, 225, 200], [0, 0, 1], [0, 1]], ![[633, 96, 203], [534, 53, 144], [102, 618, 274], [337, 202, 514], [102, 74, 137], [29, 48, 432], [452, 561, 80], [429, 375, 626], [572, 111, 96], [278, 564, 458]], ![[0, 1], [469, 267, 421], [117, 213], [171, 444, 406], [549, 97, 113], [43, 331], [565, 72, 218], [51, 61, 496], [412, 550, 564], [633, 96, 203]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [356, 364], []]
 b := ![[], [610, 560, 640], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI661N0 : CertifiedPrimeIdeal' SI661N0 661 where
  n := 3
  hpos := by decide
  P := [569, 352, 411, 1]
  hirr := P661P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-161576801, -87985804, -62215590, -62749430, -119512222]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![74226149, 66357886, 144897852, -62749430, -119512222]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI661N0 : Ideal.IsPrime I661N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI661N0 B_one_repr
lemma NI661N0 : Nat.card (O ⧸ I661N0) = 288804781 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI661N0

def I661N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-271, 80, 61, -73, 132]] i)))

def SI661N1: IdealEqSpanCertificate' Table ![![-271, 80, 61, -73, 132]] 
 ![![661, 0, 0, 0, 0], ![0, 661, 0, 0, 0], ![351, 434, 1, 0, 0], ![236, 271, 0, 1, 0], ![457, 5, 0, 0, 1]] where
  M :=![![![-271, 80, 61, -73, 132], ![910, -273, -200, 242, -438], ![-3020, 914, 653, -796, 1452], ![2638, -792, -558, 687, -1254], ![-434, 132, 84, -106, 199]]]
  hmulB := by decide  
  f := ![![![-45, 54, 27, 1, -42]], ![![-334, -113, 30, 40, 6]], ![![-243, -46, 34, 27, -18]], ![![-152, -27, 22, 17, -12]], ![![-33, 37, 19, 1, -29]]]
  g := ![![![-98, -11, 61, -73, 132], ![324, 35, -200, 242, -438], ![-1071, -112, 653, -796, 1452], ![922, 93, -558, 687, -1254], ![-145, -13, 84, -106, 199]]]
  hle1 := by decide   
  hle2 := by decide  


def P661P1 : CertificateIrreducibleZModOfList' 661 2 2 9 [390, 562, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 660], [0, 1]]
 g := ![![[15, 100], [538], [493, 20], [155], [258, 495], [202], [364], [68, 547], [1]], ![[0, 561], [538], [490, 641], [155], [349, 166], [202], [364], [19, 114], [1]]]
 h' := ![![[99, 660], [329, 651], [81, 324], [453, 431], [513, 564], [260, 627], [606, 110], [581, 365], [271, 99], [0, 1]], ![[0, 1], [0, 10], [429, 337], [157, 230], [164, 97], [199, 34], [259, 551], [361, 296], [157, 562], [99, 660]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [323]]
 b := ![[], [103, 492]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI661N1 : CertifiedPrimeIdeal' SI661N1 661 where
  n := 2
  hpos := by decide
  P := [390, 562, 1]
  hirr := P661P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59290, 31928, 36628, -36260, 62016]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-49470, -9604, 36628, -36260, 62016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI661N1 : Ideal.IsPrime I661N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI661N1 B_one_repr
lemma NI661N1 : Nat.card (O ⧸ I661N1) = 436921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI661N1
def MulI661N0 : IdealMulLeCertificate' Table 
  ![![45, -54, -27, -1, 42]] ![![-271, 80, 61, -73, 132]]
  ![![661, 0, 0, 0, 0]] where
 M := ![![![-661, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC661 : ContainsPrimesAboveP 661 ![I661N0, I661N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI661N0
    exact isPrimeI661N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 661 (by decide) (𝕀 ⊙ MulI661N0)
instance hp673 : Fact (Nat.Prime 673) := {out := by norm_num}

def I673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797, -243, -163, 204, -378]] i)))

def SI673N0: IdealEqSpanCertificate' Table ![![797, -243, -163, 204, -378]] 
 ![![673, 0, 0, 0, 0], ![0, 673, 0, 0, 0], ![425, 427, 1, 0, 0], ![220, 526, 0, 1, 0], ![293, 663, 0, 0, 1]] where
  M :=![![![797, -243, -163, 204, -378], ![-2616, 786, 532, -663, 1224], ![8466, -2587, -1735, 2157, -3978], ![-7220, 2193, 1472, -1844, 3396], ![1054, -312, -214, 266, -499]]]
  hmulB := by decide  
  f := ![![![1667, -613, -75, 234, -576]], ![![-4140, 1400, 164, -567, 1404]], ![![-1559, 496, 56, -210, 522]], ![![-2700, 897, 104, -368, 912]], ![![-3355, 1113, 129, -457, 1133]]]
  g := ![![![202, 316, -163, 204, -378], ![-656, -1024, 532, -663, 1224], ![2135, 3330, -1735, 2157, -3978], ![-1816, -2835, 1472, -1844, 3396], ![267, 419, -214, 266, -499]]]
  hle1 := by decide   
  hle2 := by decide  


def P673P0 : CertificateIrreducibleZModOfList' 673 2 2 9 [316, 515, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 672], [0, 1]]
 g := ![![[336, 590], [54], [3], [347], [235], [637, 216], [212], [280, 63], [1]], ![[9, 83], [54], [3], [347], [235], [442, 457], [212], [139, 610], [1]]]
 h' := ![![[158, 672], [46, 629], [48, 135], [550, 26], [630, 512], [608, 613], [520, 270], [356, 356], [357, 158], [0, 1]], ![[0, 1], [497, 44], [515, 538], [620, 647], [93, 161], [550, 60], [108, 403], [72, 317], [420, 515], [158, 672]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [362]]
 b := ![[], [507, 181]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI673N0 : CertifiedPrimeIdeal' SI673N0 673 where
  n := 2
  hpos := by decide
  P := [316, 515, 1]
  hirr := P673P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22246, 9861, 10250, 8469, 21324]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18492, -34115, 10250, 8469, 21324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI673N0 : Ideal.IsPrime I673N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI673N0 B_one_repr
lemma NI673N0 : Nat.card (O ⧸ I673N0) = 452929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI673N0

def I673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 15, 4, -9, 18]] i)))

def SI673N1: IdealEqSpanCertificate' Table ![![-5, 15, 4, -9, 18]] 
 ![![673, 0, 0, 0, 0], ![452, 1, 0, 0, 0], ![288, 0, 1, 0, 0], ![151, 0, 0, 1, 0], ![158, 0, 0, 0, 1]] where
  M :=![![![-5, 15, 4, -9, 18], ![126, 0, -16, 21, -54], ![-390, 109, 79, -81, 126], ![194, -105, -50, 74, -138], ![-16, -12, -2, -8, 37]]]
  hmulB := by decide  
  f := ![![![-6113, 2503, 426, -717, 2502]], ![![-4078, 1674, 286, -477, 1674]], ![![-2658, 1097, 189, -309, 1098]], ![![-1305, 560, 102, -145, 564]], ![![-1418, 588, 102, -164, 589]]]
  g := ![![![-14, 15, 4, -9, 18], ![15, 0, -16, 21, -54], ![-119, 109, 79, -81, 126], ![108, -105, -50, 74, -138], ![2, -12, -2, -8, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N1 : Nat.card (O ⧸ I673N1) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N1)

lemma isPrimeI673N1 : Ideal.IsPrime I673N1 := prime_ideal_of_norm_prime hp673.out _ NI673N1

def I673N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -6, -1, -1, 8]] i)))

def SI673N2: IdealEqSpanCertificate' Table ![![-5, -6, -1, -1, 8]] 
 ![![673, 0, 0, 0, 0], ![524, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![126, 0, 0, 1, 0], ![325, 0, 0, 0, 1]] where
  M :=![![![-5, -6, -1, -1, 8], ![62, 3, -8, 4, -6], ![-40, 68, 23, -26, 24], ![54, 2, -6, 15, -46], ![-54, -28, 0, 2, 9]]]
  hmulB := by decide  
  f := ![![![-147, -488, -227, -195, -586]], ![![-122, -381, -178, -154, -458]], ![![-20, -16, -9, -10, -20]], ![![-76, -106, -54, -53, -130]], ![![-85, -240, -113, -99, -289]]]
  g := ![![![1, -6, -1, -1, 8], ![0, 3, -8, 4, -6], ![-60, 68, 23, -26, 24], ![18, 2, -6, 15, -46], ![17, -28, 0, 2, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N2 : Nat.card (O ⧸ I673N2) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N2)

lemma isPrimeI673N2 : Ideal.IsPrime I673N2 := prime_ideal_of_norm_prime hp673.out _ NI673N2

def I673N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![717, -216, -145, 183, -334]] i)))

def SI673N3: IdealEqSpanCertificate' Table ![![717, -216, -145, 183, -334]] 
 ![![673, 0, 0, 0, 0], ![616, 1, 0, 0, 0], ![116, 0, 1, 0, 0], ![429, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![717, -216, -145, 183, -334], ![-2306, 711, 478, -586, 1098], ![7612, -2272, -1525, 1946, -3516], ![-6310, 2002, 1348, -1595, 3086], ![974, -272, -182, 252, -423]]]
  hmulB := by decide  
  f := ![![![-2717, -230, 529, 209, -1324]], ![![-2502, -217, 484, 192, -1210]], ![![-452, -52, 87, 38, -224]], ![![-1719, -144, 335, 132, -838]], ![![-120, 0, 26, 8, -63]]]
  g := ![![![122, -216, -145, 183, -334], ![-412, 711, 478, -586, 1098], ![1270, -2272, -1525, 1946, -3516], ![-1195, 2002, 1348, -1595, 3086], ![140, -272, -182, 252, -423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N3 : Nat.card (O ⧸ I673N3) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N3)

lemma isPrimeI673N3 : Ideal.IsPrime I673N3 := prime_ideal_of_norm_prime hp673.out _ NI673N3
def MulI673N0 : IdealMulLeCertificate' Table 
  ![![797, -243, -163, 204, -378]] ![![-5, 15, 4, -9, 18]]
  ![![74591, -22696, -15245, 19047, -35208]] where
 M := ![![![74591, -22696, -15245, 19047, -35208]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI673N1 : IdealMulLeCertificate' Table 
  ![![74591, -22696, -15245, 19047, -35208]] ![![-5, -6, -1, -1, 8]]
  ![![1759463, -528376, -357940, 446284, -826010]] where
 M := ![![![1759463, -528376, -357940, 446284, -826010]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI673N2 : IdealMulLeCertificate' Table 
  ![![1759463, -528376, -357940, 446284, -826010]] ![![717, -216, -145, 183, -334]]
  ![![673, 0, 0, 0, 0]] where
 M := ![![![-3865255033, 1175655624, 790097289, -984918675, 1817334204]]]
 hmul := by decide  
 g := ![![![![-5743321, 1746888, 1173993, -1463475, 2700348]]]]
 hle2 := by decide  


def PBC673 : ContainsPrimesAboveP 673 ![I673N0, I673N1, I673N2, I673N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI673N0
    exact isPrimeI673N1
    exact isPrimeI673N2
    exact isPrimeI673N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 673 (by decide) (𝕀 ⊙ MulI673N0 ⊙ MulI673N1 ⊙ MulI673N2)
instance hp677 : Fact (Nat.Prime 677) := {out := by norm_num}

def I677N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30449, -10534, -1321, 4135, -10226]] i)))

def SI677N0: IdealEqSpanCertificate' Table ![![30449, -10534, -1321, 4135, -10226]] 
 ![![677, 0, 0, 0, 0], ![0, 677, 0, 0, 0], ![0, 0, 677, 0, 0], ![9, 605, 212, 1, 0], ![286, 389, 351, 0, 1]] where
  M :=![![![30449, -10534, -1321, 4135, -10226], ![-73538, 25679, 3192, -10054, 24810], ![178372, -61974, -7675, 24332, -60324], ![-109698, 37920, 4738, -14913, 36826], ![-24666, 8478, 1030, -3362, 8385]]]
  hmulB := by decide  
  f := ![![![-23037, 7008, 4709, -5871, 10832]], ![![74914, -22785, -15314, 19088, -35226]], ![![-243632, 74090, 49793, -62080, 114528]], ![![-9345, 2839, 1907, -2382, 4384]], ![![-93046, 28295, 19015, -23710, 43735]]]
  g := ![![![4310, 2165, 4005, 4135, -10226], ![-10456, -5233, -9710, -10054, 24810], ![25424, 12826, 23645, 24332, -60324], ![-15521, -7777, -14416, -14913, 36826], ![-3534, -1801, -3293, -3362, 8385]]]
  hle1 := by decide   
  hle2 := by decide  


def P677P0 : CertificateIrreducibleZModOfList' 677 3 2 9 [350, 323, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [425, 568, 103], [218, 108, 574], [0, 1]]
 g := ![![[434, 33, 85], [285, 493], [172, 437, 663], [480, 520], [336, 410], [465, 395, 216], [560, 297], [156, 643, 1], []], ![[360, 28, 606, 34], [47, 388], [48, 369, 575, 454], [76, 361], [528, 410], [593, 494, 189, 360], [516, 540], [610, 402, 18, 394], [22, 454]], ![[643, 386, 504, 348], [490, 106], [59, 600, 2, 467], [64, 71], [], [427, 560, 622, 312], [169, 354], [321, 238, 436, 273], [228, 454]]]
 h' := ![![[425, 568, 103], [547, 579, 631], [53, 343, 164], [220, 171, 279], [659, 17, 335], [407, 41, 42], [308, 671, 427], [237, 101, 589], [0, 0, 1], [0, 1]], ![[218, 108, 574], [394, 428, 509], [443, 407, 235], [126, 108, 355], [99, 325, 19], [224, 537, 635], [405, 322, 139], [40, 134, 222], [290, 635, 108], [425, 568, 103]], ![[0, 1], [205, 347, 214], [556, 604, 278], [36, 398, 43], [210, 335, 323], [306, 99], [191, 361, 111], [187, 442, 543], [220, 42, 568], [218, 108, 574]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [247, 669], []]
 b := ![[], [652, 534, 309], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N0 : CertifiedPrimeIdeal' SI677N0 677 where
  n := 3
  hpos := by decide
  P := [350, 323, 34, 1]
  hirr := P677P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5598618, -2267037, -1661634, -2036625, -3102066]
  a := ![-8, -6, -11, -1, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1329279, 3599106, 2243616, -2036625, -3102066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI677N0 : Ideal.IsPrime I677N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI677N0 B_one_repr
lemma NI677N0 : Nat.card (O ⧸ I677N0) = 310288733 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI677N0

def I677N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -7, -6, -9, -10]] i)))

def SI677N1: IdealEqSpanCertificate' Table ![![-27, -7, -6, -9, -10]] 
 ![![677, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![428, 0, 1, 0, 0], ![293, 0, 0, 1, 0], ![494, 0, 0, 0, 1]] where
  M :=![![![-27, -7, -6, -9, -10], ![-98, -40, -28, -37, -54], ![-506, -161, -123, -175, -222], ![-910, -327, -238, -326, -442], ![-268, -96, -70, -96, -129]]]
  hmulB := by decide  
  f := ![![![-211, 373, 96, -197, 370]], ![![-28, 56, 14, -29, 54]], ![![-146, 239, 63, -127, 238]], ![![-85, 158, 40, -83, 156]], ![![-154, 272, 70, -144, 271]]]
  g := ![![![16, -7, -6, -9, -10], ![79, -40, -28, -37, -54], ![339, -161, -123, -175, -222], ![662, -327, -238, -326, -442], ![194, -96, -70, -96, -129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI677N1 : Nat.card (O ⧸ I677N1) = 677 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI677N1)

lemma isPrimeI677N1 : Ideal.IsPrime I677N1 := prime_ideal_of_norm_prime hp677.out _ NI677N1

def I677N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, -67, -8, 27, -66]] i)))

def SI677N2: IdealEqSpanCertificate' Table ![![197, -67, -8, 27, -66]] 
 ![![677, 0, 0, 0, 0], ![615, 1, 0, 0, 0], ![218, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![349, 0, 0, 0, 1]] where
  M :=![![![197, -67, -8, 27, -66], ![-474, 166, 22, -63, 162], ![1170, -397, -45, 165, -378], ![-666, 257, 40, -82, 258], ![-144, 62, 10, -18, 59]]]
  hmulB := by decide  
  f := ![![![-20003, 5993, 4066, -5073, 9402]], ![![-18075, 5415, 3674, -4584, 8496]], ![![-6752, 2025, 1373, -1713, 3174]], ![![-1034, 309, 210, -262, 486]], ![![-10351, 3101, 2104, -2625, 4865]]]
  g := ![![![96, -67, -8, 27, -66], ![-238, 166, 22, -63, 162], ![561, -397, -45, 165, -378], ![-375, 257, 40, -82, 258], ![-89, 62, 10, -18, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI677N2 : Nat.card (O ⧸ I677N2) = 677 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI677N2)

lemma isPrimeI677N2 : Ideal.IsPrime I677N2 := prime_ideal_of_norm_prime hp677.out _ NI677N2
def MulI677N0 : IdealMulLeCertificate' Table 
  ![![30449, -10534, -1321, 4135, -10226]] ![![-27, -7, -6, -9, -10]]
  ![![-143647, 50449, 6431, -19422, 49092]] where
 M := ![![![-143647, 50449, 6431, -19422, 49092]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI677N1 : IdealMulLeCertificate' Table 
  ![![-143647, 50449, 6431, -19422, 49092]] ![![197, -67, -8, 27, -66]]
  ![![677, 0, 0, 0, 0]] where
 M := ![![![-38821211, 13498026, 1683699, -5286693, 13108074]]]
 hmul := by decide  
 g := ![![![![-57343, 19938, 2487, -7809, 19362]]]]
 hle2 := by decide  


def PBC677 : ContainsPrimesAboveP 677 ![I677N0, I677N1, I677N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI677N0
    exact isPrimeI677N1
    exact isPrimeI677N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 677 (by decide) (𝕀 ⊙ MulI677N0 ⊙ MulI677N1)
instance hp683 : Fact (Nat.Prime 683) := {out := by norm_num}

def I683N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41357, -13361, -1354, 5953, -12778]] i)))

def SI683N0: IdealEqSpanCertificate' Table ![![41357, -13361, -1354, 5953, -12778]] 
 ![![683, 0, 0, 0, 0], ![0, 683, 0, 0, 0], ![0, 0, 683, 0, 0], ![389, 234, 104, 1, 0], ![539, 590, 630, 0, 1]] where
  M :=![![![41357, -13361, -1354, 5953, -12778], ![-90318, 35886, 5852, -10887, 35718], ![263970, -71339, -2627, 42387, -65322], ![-88050, 69403, 20558, 228, 74906], ![-16092, 16996, 5618, 1400, 18711]]]
  hmulB := by decide  
  f := ![![![67, -395, -100, 203, -362]], ![![-2490, 8, 314, -459, 1218]], ![![8826, -2045, -1683, 1701, -2754]], ![![523, -530, -204, 215, -204]], ![![6043, -2191, -1360, 1333, -1775]]]
  g := ![![![6754, 8979, 10878, 5953, -12778], ![-22119, -27072, -31280, -10887, 35718], ![27795, 41801, 53795, 42387, -65322], ![-59372, -64683, -69098, 228, 74906], ![-15587, -16618, -17464, 1400, 18711]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P0 : CertificateIrreducibleZModOfList' 683 3 2 9 [519, 50, 262, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [374, 574, 174], [47, 108, 509], [0, 1]]
 g := ![![[577, 262, 555], [490, 588, 476], [174, 659], [572, 472, 67], [234, 74], [83, 303, 495], [452, 604], [294, 421, 1], []], ![[445, 365, 586, 368], [360, 155, 500, 15], [578, 257], [288, 289, 30, 628], [142, 403], [543, 413, 560, 166], [178, 159], [189, 602, 501, 343], [366, 224]], ![[283, 616, 181, 228], [96, 673, 134, 324], [253, 108], [322, 574, 399, 173], [372, 663], [504, 266, 18, 509], [84, 201], [527, 198, 8, 147], [31, 224]]]
 h' := ![![[374, 574, 174], [449, 386, 171], [13, 577, 543], [237, 159, 638], [383, 591, 637], [635, 347, 542], [597, 24, 275], [406, 387, 438], [0, 0, 1], [0, 1]], ![[47, 108, 509], [133, 207, 257], [591, 144, 586], [575, 516, 267], [637, 132, 197], [104, 203, 72], [573, 331, 409], [46, 344, 581], [464, 423, 108], [374, 574, 174]], ![[0, 1], [95, 90, 255], [560, 645, 237], [535, 8, 461], [32, 643, 532], [154, 133, 69], [646, 328, 682], [97, 635, 347], [463, 260, 574], [47, 108, 509]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [630, 374], []]
 b := ![[], [300, 0, 673], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N0 : CertifiedPrimeIdeal' SI683N0 683 where
  n := 3
  hpos := by decide
  P := [519, 50, 262, 1]
  hirr := P683P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52984739, 25308730, 18860126, 19802923, 35405361]
  a := ![16, 10, 23, 2, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-39141789, -37331974, -35645712, 19802923, 35405361]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI683N0 : Ideal.IsPrime I683N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N0 B_one_repr
lemma NI683N0 : Nat.card (O ⧸ I683N0) = 318611987 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N0

def I683N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 395, 100, -203, 362]] i)))

def SI683N1: IdealEqSpanCertificate' Table ![![-67, 395, 100, -203, 362]] 
 ![![683, 0, 0, 0, 0], ![0, 683, 0, 0, 0], ![265, 370, 1, 0, 0], ![189, 339, 0, 1, 0], ![459, 172, 0, 0, 1]] where
  M :=![![![-67, 395, 100, -203, 362], ![2490, -8, -314, 459, -1218], ![-8826, 2045, 1683, -1701, 2754], ![4098, -2473, -1124, 1620, -2890], ![24, -82, -50, -202, 807]]]
  hmulB := by decide  
  f := ![![![-41357, 13361, 1354, -5953, 12778]], ![![90318, -35886, -5852, 10887, -35718]], ![![32495, -14152, -2641, 3526, -14296]], ![![33513, -14216, -2560, 3756, -14302]], ![![-5025, -83, -572, -1261, -435]]]
  g := ![![![-226, -44, 100, -203, 362], ![817, 249, -314, 459, -1218], ![-2046, -758, 1683, -1701, 2754], ![1936, 529, -1124, 1620, -2890], ![-467, -76, -50, -202, 807]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P1 : CertificateIrreducibleZModOfList' 683 2 2 9 [305, 309, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [374, 682], [0, 1]]
 g := ![![[319, 324], [551, 87], [244], [588, 378], [420], [405, 389], [507], [587, 544], [1]], ![[604, 359], [305, 596], [244], [579, 305], [420], [412, 294], [507], [509, 139], [1]]]
 h' := ![![[374, 682], [646, 18], [222, 231], [289, 314], [346, 294], [98, 127], [131, 184], [594, 481], [378, 374], [0, 1]], ![[0, 1], [548, 665], [558, 452], [249, 369], [339, 389], [469, 556], [647, 499], [176, 202], [239, 309], [374, 682]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [151, 390]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N1 : CertifiedPrimeIdeal' SI683N1 683 where
  n := 2
  hpos := by decide
  P := [305, 309, 1]
  hirr := P683P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25589, 50071, 47304, 9383, 91396]
  a := ![24, 18, 37, -5, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-82334, -53226, 47304, 9383, 91396]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI683N1 : Ideal.IsPrime I683N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N1 B_one_repr
lemma NI683N1 : Nat.card (O ⧸ I683N1) = 466489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N1
def MulI683N0 : IdealMulLeCertificate' Table 
  ![![41357, -13361, -1354, 5953, -12778]] ![![-67, 395, 100, -203, 362]]
  ![![683, 0, 0, 0, 0]] where
 M := ![![![-683, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC683 : ContainsPrimesAboveP 683 ![I683N0, I683N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI683N0
    exact isPrimeI683N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 683 (by decide) (𝕀 ⊙ MulI683N0)
instance hp691 : Fact (Nat.Prime 691) := {out := by norm_num}

def I691N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17899, -5334, -393, 2717, -5008]] i)))

def SI691N0: IdealEqSpanCertificate' Table ![![17899, -5334, -393, 2717, -5008]] 
 ![![691, 0, 0, 0, 0], ![0, 691, 0, 0, 0], ![0, 0, 691, 0, 0], ![336, 400, 40, 1, 0], ![595, 390, 60, 0, 1]] where
  M :=![![![17899, -5334, -393, 2717, -5008], ![-34630, 16001, 3210, -3470, 16302], ![123476, -25008, 2381, 22462, -20820], ![-10930, 37910, 15196, 9259, 43418], ![866, 9722, 4288, 3276, 11385]]]
  hmulB := by decide  
  f := ![![![-6609, 2080, 1367, -1719, 3170]], ![![21922, -6525, -4444, 5552, -10314]], ![![-71408, 21604, 14575, -18094, 33312]], ![![5430, -1542, -1082, 1353, -2542]], ![![469, -12, -63, 79, -193]]]
  g := ![![![3017, 1246, 277, 2717, -5008], ![-12400, -7169, -1210, -3470, 16302], ![7184, -1288, 511, 22462, -20820], ![-41904, -29810, -4284, 9259, 43418], ![-11395, -8308, -1172, 3276, 11385]]]
  hle1 := by decide   
  hle2 := by decide  


def P691P0 : CertificateIrreducibleZModOfList' 691 3 2 9 [480, 141, 305, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [374, 263, 334], [12, 427, 357], [0, 1]]
 g := ![![[624, 597, 514], [654, 605, 636], [174, 190], [452, 592], [350, 232, 30], [94, 426, 225], [309, 184], [290, 386, 1], []], ![[327, 560, 178, 309], [480, 162, 451, 41], [307, 314], [316, 489], [161, 39, 353, 183], [356, 137, 519, 105], [377, 261], [394, 160, 396, 56], [430, 305]], ![[217, 314, 299, 238], [531, 267, 238, 62], [362, 150], [263, 491], [625, 517, 11, 347], [637, 630, 61, 405], [200, 294], [23, 447, 284, 448], [407, 305]]]
 h' := ![![[374, 263, 334], [485, 366, 63], [415, 5, 456], [673, 336, 214], [604, 167, 273], [486, 610, 471], [368, 436, 15], [382, 478, 372], [0, 0, 1], [0, 1]], ![[12, 427, 357], [454, 471, 580], [168, 579, 138], [421, 108, 448], [682, 602, 290], [496, 267, 622], [300, 156, 9], [40, 479, 636], [503, 59, 427], [374, 263, 334]], ![[0, 1], [541, 545, 48], [54, 107, 97], [122, 247, 29], [633, 613, 128], [2, 505, 289], [290, 99, 667], [192, 425, 374], [337, 632, 263], [12, 427, 357]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [326, 52], []]
 b := ![[], [86, 297, 335], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI691N0 : CertifiedPrimeIdeal' SI691N0 691 where
  n := 3
  hpos := by decide
  P := [480, 141, 305, 1]
  hirr := P691P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14263039, 7237277, 5435053, 5407324, 10246241]
  a := ![11, 7, 14, 1, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11431420, -8902643, -1194837, 5407324, 10246241]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI691N0 : Ideal.IsPrime I691N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI691N0 B_one_repr
lemma NI691N0 : Nat.card (O ⧸ I691N0) = 329939371 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI691N0

def I691N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, -28, -18, 24, -46]] i)))

def SI691N1: IdealEqSpanCertificate' Table ![![87, -28, -18, 24, -46]] 
 ![![691, 0, 0, 0, 0], ![606, 1, 0, 0, 0], ![376, 0, 1, 0, 0], ![155, 0, 0, 1, 0], ![269, 0, 0, 0, 1]] where
  M :=![![![87, -28, -18, 24, -46], ![-320, 83, 62, -76, 144], ![1000, -314, -207, 254, -456], ![-820, 258, 170, -215, 404], ![128, -24, -22, 30, -63]]]
  hmulB := by decide  
  f := ![![![87157, -30280, -3762, 11888, -29386]], ![![76130, -26449, -3286, 10384, -25668]], ![![48168, -16734, -2079, 6570, -16240]], ![![19097, -6634, -824, 2605, -6438]], ![![33827, -11752, -1460, 4614, -11405]]]
  g := ![![![47, -28, -18, 24, -46], ![-146, 83, 62, -76, 144], ![510, -314, -207, 254, -456], ![-429, 258, 170, -215, 404], ![51, -24, -22, 30, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N1 : Nat.card (O ⧸ I691N1) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N1)

lemma isPrimeI691N1 : Ideal.IsPrime I691N1 := prime_ideal_of_norm_prime hp691.out _ NI691N1

def I691N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -12, -5, 7, -12]] i)))

def SI691N2: IdealEqSpanCertificate' Table ![![21, -12, -5, 7, -12]] 
 ![![691, 0, 0, 0, 0], ![655, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![588, 0, 0, 1, 0], ![399, 0, 0, 0, 1]] where
  M :=![![![21, -12, -5, 7, -12], ![-82, 21, 14, -20, 42], ![296, -74, -53, 64, -120], ![-206, 80, 44, -57, 102], ![10, -10, -4, 8, -17]]]
  hmulB := by decide  
  f := ![![![2129, 686, 527, 743, 930]], ![![2031, 655, 503, 709, 888]], ![![326, 106, 81, 114, 144]], ![![1926, 624, 478, 673, 846]], ![![1263, 408, 313, 441, 553]]]
  g := ![![![13, -12, -5, 7, -12], ![-29, 21, 14, -20, 42], ![92, -74, -53, 64, -120], ![-92, 80, 44, -57, 102], ![13, -10, -4, 8, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N2 : Nat.card (O ⧸ I691N2) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N2)

lemma isPrimeI691N2 : Ideal.IsPrime I691N2 := prime_ideal_of_norm_prime hp691.out _ NI691N2
def MulI691N0 : IdealMulLeCertificate' Table 
  ![![17899, -5334, -393, 2717, -5008]] ![![87, -28, -18, 24, -46]]
  ![![2129, 686, 527, 743, 930]] where
 M := ![![![2129, 686, 527, 743, 930]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI691N1 : IdealMulLeCertificate' Table 
  ![![2129, 686, 527, 743, 930]] ![![21, -12, -5, 7, -12]]
  ![![691, 0, 0, 0, 0]] where
 M := ![![![691, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC691 : ContainsPrimesAboveP 691 ![I691N0, I691N1, I691N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI691N0
    exact isPrimeI691N1
    exact isPrimeI691N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 691 (by decide) (𝕀 ⊙ MulI691N0 ⊙ MulI691N1)


lemma PB696I13_primes (p : ℕ) :
  p ∈ Set.range ![647, 653, 659, 661, 673, 677, 683, 691] ↔ Nat.Prime p ∧ 643 < p ∧ p ≤ 695 := by
  rw [← List.mem_ofFn']
  convert primes_range 643 695 (by omega)

def PB696I13 : PrimesBelowBoundCertificateInterval O 643 695 696 where
  m := 8
  g := ![3, 1, 3, 2, 4, 3, 2, 3]
  P := ![647, 653, 659, 661, 673, 677, 683, 691]
  hP := PB696I13_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I647N0, I647N1, I647N2]
    · exact ![I653N0]
    · exact ![I659N0, I659N1, I659N2]
    · exact ![I661N0, I661N1]
    · exact ![I673N0, I673N1, I673N2, I673N3]
    · exact ![I677N0, I677N1, I677N2]
    · exact ![I683N0, I683N1]
    · exact ![I691N0, I691N1, I691N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC647
    · exact PBC653
    · exact PBC659
    · exact PBC661
    · exact PBC673
    · exact PBC677
    · exact PBC683
    · exact PBC691
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![418609, 418609, 647]
    · exact ![118731486838493]
    · exact ![286191179, 659, 659]
    · exact ![288804781, 436921]
    · exact ![452929, 673, 673, 673]
    · exact ![310288733, 677, 677]
    · exact ![318611987, 466489]
    · exact ![329939371, 691, 691]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI647N0
      exact NI647N1
      exact NI647N2
    · dsimp ; intro j
      fin_cases j
      exact NI653N0
    · dsimp ; intro j
      fin_cases j
      exact NI659N0
      exact NI659N1
      exact NI659N2
    · dsimp ; intro j
      fin_cases j
      exact NI661N0
      exact NI661N1
    · dsimp ; intro j
      fin_cases j
      exact NI673N0
      exact NI673N1
      exact NI673N2
      exact NI673N3
    · dsimp ; intro j
      fin_cases j
      exact NI677N0
      exact NI677N1
      exact NI677N2
    · dsimp ; intro j
      fin_cases j
      exact NI683N0
      exact NI683N1
    · dsimp ; intro j
      fin_cases j
      exact NI691N0
      exact NI691N1
      exact NI691N2
  β := ![I647N2, I659N1, I659N2, I673N1, I673N2, I673N3, I677N1, I677N2, I691N1, I691N2]
  Il := ![[I647N2], [], [I659N1, I659N2], [], [I673N1, I673N2, I673N3], [I677N1, I677N2], [], [I691N1, I691N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
