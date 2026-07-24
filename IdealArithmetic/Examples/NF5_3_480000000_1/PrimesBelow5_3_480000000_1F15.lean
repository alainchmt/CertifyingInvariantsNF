
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp769 : Fact (Nat.Prime 769) := {out := by norm_num}

def I769N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8897, 3147, -5787, -1314, 1917]] i)))

def SI769N0: IdealEqSpanCertificate' Table ![![-8897, 3147, -5787, -1314, 1917]] 
 ![![769, 0, 0, 0, 0], ![0, 769, 0, 0, 0], ![127, 399, 1, 0, 0], ![81, 46, 0, 1, 0], ![62, 376, 0, 0, 1]] where
  M :=![![![-8897, 3147, -5787, -1314, 1917], ![15336, -3785, 8922, 3159, -2025], ![-8100, 5487, -6944, 255, 3726], ![7236, 3558, 771, 4390, 3258], ![10812, 10218, -1953, 9339, 8371]]]
  hmulB := by decide  
  f := ![![![18415, -56238, -94311, 396, 24003]], ![![192024, 43723, -113268, -20997, 25191]], ![![102805, 13545, -74261, -10848, 17010]], ![![13203, -3281, -16470, -1193, 3978]], ![![95318, 16873, -62895, -10230, 14230]]]
  g := ![![![928, 2148, -5787, -1314, 1917], ![-1623, -3833, 8922, 3159, -2025], ![809, 1773, -6944, 255, 3726], ![-843, -2251, 771, 4390, 3258], ![-1322, -3625, -1953, 9339, 8371]]]
  hle1 := by decide   
  hle2 := by decide  


def P769P0 : CertificateIrreducibleZModOfList' 769 2 2 9 [671, 345, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [424, 768], [0, 1]]
 g := ![![[585, 102], [226], [768], [40], [64], [475], [24], [570], [424, 1]], ![[0, 667], [226], [768], [40], [64], [475], [24], [570], [79, 768]]]
 h' := ![![[424, 768], [189, 589], [212, 42], [604, 707], [746, 136], [534, 761], [63, 86], [399, 315], [26, 697], [0, 1]], ![[0, 1], [0, 180], [333, 727], [462, 62], [735, 633], [218, 8], [384, 683], [153, 454], [258, 72], [424, 768]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [575]]
 b := ![[], [570, 672]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI769N0 : CertifiedPrimeIdeal' SI769N0 769 where
  n := 2
  hpos := by decide
  P := [671, 345, 1]
  hirr := P769P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2071, 1410, 129, 689, -424]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-57, 101, 129, 689, -424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI769N0 : Ideal.IsPrime I769N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI769N0 B_one_repr
lemma NI769N0 : Nat.card (O ⧸ I769N0) = 591361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI769N0

def I769N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175, 70, -79, -27, 26]] i)))

def SI769N1: IdealEqSpanCertificate' Table ![![-175, 70, -79, -27, 26]] 
 ![![769, 0, 0, 0, 0], ![0, 769, 0, 0, 0], ![684, 237, 1, 0, 0], ![151, 695, 0, 1, 0], ![158, 84, 0, 0, 1]] where
  M :=![![![-175, 70, -79, -27, 26], ![208, -97, 194, 51, -55], ![-220, 38, -148, -24, 49], ![92, -1, -35, 10, 16], ![-4, 35, -53, 15, 35]]]
  hmulB := by decide  
  f := ![![![-1543, -905, -301, -1563, 860]], ![![6880, 4019, 1316, 6981, -3829]], ![![728, 422, 134, 741, -404]], ![![5955, 3478, 1138, 6043, -3314]], ![![378, 220, 71, 384, -210]]]
  g := ![![![70, 46, -79, -27, 26], ![-171, -100, 194, 51, -55], ![126, 62, -148, -24, 49], ![26, 0, -35, 10, 16], ![37, -1, -53, 15, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P769P1 : CertificateIrreducibleZModOfList' 769 2 2 9 [111, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [743, 768], [0, 1]]
 g := ![![[215, 455], [722], [591], [154], [47], [648], [57], [90], [743, 1]], ![[689, 314], [722], [591], [154], [47], [648], [57], [90], [717, 768]]]
 h' := ![![[743, 768], [190, 143], [158, 549], [221, 678], [52, 326], [453, 567], [352, 87], [733, 587], [579, 565], [0, 1]], ![[0, 1], [317, 626], [495, 220], [280, 91], [35, 443], [322, 202], [397, 682], [82, 182], [500, 204], [743, 768]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [411]]
 b := ![[], [749, 590]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI769N1 : CertifiedPrimeIdeal' SI769N1 769 where
  n := 2
  hpos := by decide
  P := [111, 26, 1]
  hirr := P769P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135862, 99982, -17532, 73178, 163990]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32292, -78516, -17532, 73178, 163990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI769N1 : Ideal.IsPrime I769N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI769N1 B_one_repr
lemma NI769N1 : Nat.card (O ⧸ I769N1) = 591361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI769N1

def I769N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 16, -38, -8, 12]] i)))

def SI769N2: IdealEqSpanCertificate' Table ![![-49, 16, -38, -8, 12]] 
 ![![769, 0, 0, 0, 0], ![266, 1, 0, 0, 0], ![765, 0, 1, 0, 0], ![399, 0, 0, 1, 0], ![215, 0, 0, 0, 1]] where
  M :=![![![-49, 16, -38, -8, 12], ![96, -19, 48, 16, -12], ![-48, 34, -35, -2, 18], ![24, 14, 12, 21, 12], ![40, 46, -8, 40, 37]]]
  hmulB := by decide  
  f := ![![![-18001, -10524, -3470, -18324, 10056]], ![![-6122, -3579, -1180, -6232, 3420]], ![![-18141, -10606, -3497, -18466, 10134]], ![![-8871, -5186, -1710, -9031, 4956]], ![![-5695, -3330, -1098, -5796, 3181]]]
  g := ![![![33, 16, -38, -8, 12], ![-46, -19, 48, 16, -12], ![19, 34, -35, -2, 18], ![-31, 14, 12, 21, 12], ![-39, 46, -8, 40, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI769N2 : Nat.card (O ⧸ I769N2) = 769 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI769N2)

lemma isPrimeI769N2 : Ideal.IsPrime I769N2 := prime_ideal_of_norm_prime hp769.out _ NI769N2
def MulI769N0 : IdealMulLeCertificate' Table 
  ![![-8897, 3147, -5787, -1314, 1917]] ![![-175, 70, -79, -27, 26]]
  ![![3356135, -1079546, 2114246, 555219, -641899]] where
 M := ![![![3356135, -1079546, 2114246, 555219, -641899]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI769N1 : IdealMulLeCertificate' Table 
  ![![3356135, -1079546, 2114246, 555219, -641899]] ![![-49, 16, -38, -8, 12]]
  ![![769, 0, 0, 0, 0]] where
 M := ![![![-381921543, 124339610, -241552128, -62366669, 74196965]]]
 hmul := by decide  
 g := ![![![![-496647, 161690, -314112, -81101, 96485]]]]
 hle2 := by decide  


def PBC769 : ContainsPrimesAboveP 769 ![I769N0, I769N1, I769N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI769N0
    exact isPrimeI769N1
    exact isPrimeI769N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 769 (by decide) (𝕀 ⊙ MulI769N0 ⊙ MulI769N1)
instance hp773 : Fact (Nat.Prime 773) := {out := by norm_num}

def I773N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197, -8, -62, -9, 21]] i)))

def SI773N0: IdealEqSpanCertificate' Table ![![-197, -8, -62, -9, 21]] 
 ![![773, 0, 0, 0, 0], ![0, 773, 0, 0, 0], ![0, 0, 773, 0, 0], ![319, 389, 52, 1, 0], ![385, 424, 277, 0, 1]] where
  M :=![![![-197, -8, -62, -9, 21], ![168, -145, 2, 32, -6], ![-24, 54, -177, -35, 45], ![96, 102, 88, -18, -27], ![0, 44, -8, -17, -8]]]
  hmulB := by decide  
  f := ![![![-1, 2, 2, 3, -3]], ![![-24, -17, -2, -20, 6]], ![![24, 12, 3, 29, -27]], ![![-11, -7, 0, -7, 0]], ![![-5, -4, 1, 1, -8]]]
  g := ![![![-7, -7, -7, -9, 21], ![-10, -13, 0, 32, -6], ![-8, -7, -14, -35, 45], ![21, 24, 11, -18, -27], ![11, 13, 4, -17, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P773P0 : CertificateIrreducibleZModOfList' 773 3 2 9 [81, 149, 623, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [361, 772, 36], [562, 0, 737], [0, 1]]
 g := ![![[759, 291, 577], [223, 729], [147, 620, 1], [112, 676], [181, 47], [600, 202], [113, 62], [216, 83], [1]], ![[415, 28, 712, 517], [306, 594], [349, 162, 482, 86], [229, 327], [387, 409], [281, 303], [735, 275], [464, 663], [338, 659, 408, 276]], ![[550, 287, 417, 759], [197, 364], [538, 293, 768, 655], [321, 103], [391, 532], [633, 364], [436, 449], [49, 159], [60, 222, 342, 497]]]
 h' := ![![[361, 772, 36], [435, 138, 200], [461, 117, 746], [143, 538, 772], [375, 164, 747], [260, 446, 371], [524, 538, 277], [660, 691, 155], [692, 624, 150], [0, 1]], ![[562, 0, 737], [210, 200, 330], [148, 77, 347], [623, 643, 43], [511, 395, 493], [648, 467, 596], [620, 77, 43], [318, 228, 140], [5, 16, 47], [361, 772, 36]], ![[0, 1], [4, 435, 243], [166, 579, 453], [186, 365, 731], [282, 214, 306], [148, 633, 579], [702, 158, 453], [211, 627, 478], [116, 133, 576], [562, 0, 737]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 106], []]
 b := ![[], [27, 206, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI773N0 : CertifiedPrimeIdeal' SI773N0 773 where
  n := 3
  hpos := by decide
  P := [81, 149, 623, 1]
  hirr := P773P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![363182, 278810, -50460, 175835, 501873]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-322056, -363409, -191737, 175835, 501873]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI773N0 : Ideal.IsPrime I773N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI773N0 B_one_repr
lemma NI773N0 : Nat.card (O ⧸ I773N0) = 461889917 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI773N0

def I773N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 2, 3, -3]] i)))

def SI773N1: IdealEqSpanCertificate' Table ![![-1, 2, 2, 3, -3]] 
 ![![773, 0, 0, 0, 0], ![0, 773, 0, 0, 0], ![756, 721, 1, 0, 0], ![662, 380, 0, 1, 0], ![651, 87, 0, 0, 1]] where
  M :=![![![-1, 2, 2, 3, -3], ![-24, -17, -2, -20, 6], ![24, 12, 3, 29, -27], ![-96, -60, -16, -96, 27], ![48, 22, 20, 65, -94]]]
  hmulB := by decide  
  f := ![![![-197, -8, -62, -9, 21]], ![![168, -145, 2, 32, -6]], ![![-36, -143, -59, 21, 15]], ![![-86, -78, -52, 8, 15]], ![![-147, -23, -52, -4, 17]]]
  g := ![![![-2, -3, 2, 3, -3], ![14, 11, -2, -20, 6], ![-5, -14, 3, 29, -27], ![75, 59, -16, -96, 27], ![4, -40, 20, 65, -94]]]
  hle1 := by decide   
  hle2 := by decide  


def P773P1 : CertificateIrreducibleZModOfList' 773 2 2 9 [230, 253, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [520, 772], [0, 1]]
 g := ![![[233, 460], [655], [533, 145], [327], [104], [100], [68], [622], [520, 1]], ![[576, 313], [655], [179, 628], [327], [104], [100], [68], [622], [267, 772]]]
 h' := ![![[520, 772], [84, 211], [317, 508], [545, 193], [772, 280], [746, 710], [632, 763], [563, 29], [215, 393], [0, 1]], ![[0, 1], [38, 562], [111, 265], [415, 580], [275, 493], [452, 63], [70, 10], [183, 744], [503, 380], [520, 772]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [760]]
 b := ![[], [144, 380]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI773N1 : CertifiedPrimeIdeal' SI773N1 773 where
  n := 2
  hpos := by decide
  P := [230, 253, 1]
  hirr := P773P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12372, 9222, -5123, 529, 39212]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28450, 117, -5123, 529, 39212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI773N1 : Ideal.IsPrime I773N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI773N1 B_one_repr
lemma NI773N1 : Nat.card (O ⧸ I773N1) = 597529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI773N1
def MulI773N0 : IdealMulLeCertificate' Table 
  ![![-197, -8, -62, -9, 21]] ![![-1, 2, 2, 3, -3]]
  ![![773, 0, 0, 0, 0]] where
 M := ![![![773, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC773 : ContainsPrimesAboveP 773 ![I773N0, I773N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI773N0
    exact isPrimeI773N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 773 (by decide) (𝕀 ⊙ MulI773N0)
instance hp787 : Fact (Nat.Prime 787) := {out := by norm_num}

def I787N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![787, 0, 0, 0, 0]] i)))

def SI787N0: IdealEqSpanCertificate' Table ![![787, 0, 0, 0, 0]] 
 ![![787, 0, 0, 0, 0], ![0, 787, 0, 0, 0], ![0, 0, 787, 0, 0], ![0, 0, 0, 787, 0], ![0, 0, 0, 0, 787]] where
  M :=![![![787, 0, 0, 0, 0], ![0, 787, 0, 0, 0], ![0, 0, 787, 0, 0], ![0, 0, 0, 787, 0], ![0, 0, 0, 0, 787]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P787P0 : CertificateIrreducibleZModOfList' 787 5 2 9 [778, 71, 676, 461, 298, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [262, 407, 50, 505, 657], [372, 397, 469, 550, 744], [620, 717, 25, 200, 399], [22, 52, 243, 319, 561], [0, 1]]
 g := ![![[204, 247, 208, 589, 285], [187, 418, 547, 697, 311], [58, 52, 784, 283], [692, 90, 686, 234], [725, 782, 678, 208, 204], [380, 584, 548, 494], [605, 255, 479, 251], [489, 1], []], ![[562, 386, 694, 442, 548, 385, 138, 598], [20, 624, 567, 358, 652, 760, 517, 439], [291, 645, 689, 262], [556, 258, 403, 329], [321, 635, 128, 147, 608, 72, 496, 424], [782, 742, 84, 509], [228, 160, 701, 174], [223, 304, 676, 431], [210, 14, 361, 621, 409, 508, 729, 304]], ![[140, 723, 426, 653, 226, 603, 538, 388], [332, 214, 282, 478, 115, 81, 706, 475], [694, 388, 349, 190], [88, 309, 627, 775], [220, 464, 310, 439, 746, 457, 765, 672], [52, 781, 396, 263], [494, 698, 373, 144], [509, 767, 646, 203], [290, 237, 435, 413, 590, 689, 102, 767]], ![[19, 434, 77, 578, 444, 130, 620, 147], [682, 527, 3, 519, 430, 669, 107, 147], [155, 398, 53, 433], [644, 357, 234, 25], [621, 733, 103, 551, 607, 217, 357, 102], [463, 554, 213, 283], [355, 345, 314, 370], [655, 209, 605, 215], [183, 186, 488, 572, 559, 709, 247, 68]], ![[603, 295, 210, 404, 231, 139, 588, 287], [514, 729, 430, 377, 630, 709, 72, 579], [622, 451, 448, 370], [301, 15, 635, 381], [533, 244, 312, 358, 36, 779, 479, 265], [145, 210, 659, 107], [170, 189, 392, 703], [634, 537, 323, 326], [445, 509, 227, 743, 173, 504, 364, 540]]]
 h' := ![![[262, 407, 50, 505, 657], [109, 535, 107, 577, 203], [551, 63, 199, 123, 274], [431, 60, 548, 291, 176], [229, 683, 453, 146, 667], [506, 637, 314, 472, 178], [667, 179, 664, 431, 606], [466, 705, 692, 551, 199], [0, 0, 0, 1], [0, 1]], ![[372, 397, 469, 550, 744], [619, 391, 99, 129, 25], [562, 547, 66, 669, 69], [569, 82, 448, 664, 534], [403, 13, 522, 476, 382], [654, 217, 238, 355, 199], [485, 324, 166, 275, 751], [105, 499, 465, 708, 31], [520, 567, 281, 522, 680], [262, 407, 50, 505, 657]], ![[620, 717, 25, 200, 399], [344, 44, 364, 0, 756], [189, 177, 618, 160, 451], [387, 97, 63, 13, 42], [284, 167, 126, 585, 56], [268, 267, 492, 222, 178], [465, 716, 21, 749, 434], [219, 725, 737, 0, 12], [640, 661, 22, 423, 396], [372, 397, 469, 550, 744]], ![[22, 52, 243, 319, 561], [255, 138, 437, 552, 258], [595, 563, 609, 150, 258], [644, 638, 11, 116, 648], [688, 581, 760, 176, 782], [392, 740, 489, 1, 39], [689, 131, 60, 84, 611], [653, 660, 364, 467, 174], [76, 650, 63, 51, 256], [620, 717, 25, 200, 399]], ![[0, 1], [139, 466, 567, 316, 332], [248, 224, 82, 472, 522], [305, 697, 504, 490, 174], [269, 130, 500, 191, 474], [110, 500, 41, 524, 193], [380, 224, 663, 35, 746], [479, 559, 103, 635, 371], [487, 483, 421, 577, 242], [22, 52, 243, 319, 561]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [766, 728, 446, 742], [], [], []]
 b := ![[], [564, 169, 524, 166, 151], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI787N0 : CertifiedPrimeIdeal' SI787N0 787 where
  n := 5
  hpos := by decide
  P := [778, 71, 676, 461, 298, 1]
  hirr := P787P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![657695233411, 365340821265, 168778911904, 728968594583, -597603572961]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![835699153, 464219595, 214458592, 926262509, -759343803]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI787N0 : Ideal.IsPrime I787N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI787N0 B_one_repr
lemma NI787N0 : Nat.card (O ⧸ I787N0) = 301907333072707 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI787N0

def PBC787 : ContainsPrimesAboveP 787 ![I787N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI787N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![787, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 787 (by decide) 𝕀

instance hp797 : Fact (Nat.Prime 797) := {out := by norm_num}

def I797N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7457, 2676, -4907, -1088, 1647]] i)))

def SI797N0: IdealEqSpanCertificate' Table ![![-7457, 2676, -4907, -1088, 1647]] 
 ![![797, 0, 0, 0, 0], ![0, 797, 0, 0, 0], ![0, 0, 797, 0, 0], ![0, 0, 0, 797, 0], ![536, 652, 539, 190, 1]] where
  M :=![![![-7457, 2676, -4907, -1088, 1647], ![13176, -3041, 7528, 2803, -1617], ![-6468, 4908, -5844, 467, 3396], ![6996, 3621, 677, 4407, 3207], ![10964, 9899, -1685, 9180, 8270]]]
  hmulB := by decide  
  f := ![![![35, 21, 5, 26, -15]], ![![-120, -61, -10, -121, 63]], ![![252, 153, 60, 271, -150]], ![![-540, -324, -113, -540, 300]], ![![-32, -9, 9, -26, 11]]]
  g := ![![![-1117, -1344, -1120, -394, 1647], ![1104, 1319, 1103, 389, -1617], ![-2292, -2772, -2304, -809, 3396], ![-2148, -2619, -2168, -759, 3207], ![-5548, -6753, -5595, -1960, 8270]]]
  hle1 := by decide   
  hle2 := by decide  


def P797P0 : CertificateIrreducibleZModOfList' 797 4 2 9 [119, 465, 578, 634, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [523, 403, 147, 278], [651, 563, 644, 543], [583, 627, 6, 773], [0, 1]]
 g := ![![[9, 273, 295, 513], [363, 563, 361], [340, 48, 257, 781], [703, 290, 162, 225], [747, 791, 202, 277], [238, 540, 426], [543, 256, 115], [487, 163, 1], []], ![[700, 635, 168, 295, 556, 553], [749, 770, 248], [762, 426, 240, 303, 184, 384], [119, 693, 494, 398, 585, 640], [213, 444, 454, 564, 183, 273], [724, 316, 154], [164, 389, 430], [671, 676, 728], [377, 130, 175, 572, 617, 223]], ![[55, 307, 361, 637, 679, 593], [602, 222, 52], [323, 154, 790, 242, 151, 326], [360, 369, 742, 458, 718, 215], [117, 569, 27, 153, 87, 623], [62, 394, 273], [362, 302, 11], [439, 233, 275], [328, 744, 206, 240, 360, 53]], ![[199, 623, 483, 662, 583, 787], [176, 583, 666], [114, 277, 353, 574, 19, 728], [230, 622, 723, 410, 167, 743], [198, 21, 189, 662, 509, 313], [489, 519, 110], [132, 143, 369], [594, 411, 170], [674, 466, 269, 447, 611, 522]]]
 h' := ![![[523, 403, 147, 278], [539, 539, 694, 714], [187, 357, 485, 778], [28, 193, 186, 734], [371, 8, 616, 15], [185, 149, 776, 444], [119, 672, 193, 156], [228, 421, 453, 642], [0, 0, 0, 1], [0, 1]], ![[651, 563, 644, 543], [754, 774, 261, 327], [515, 701, 767, 103], [660, 346, 386, 15], [635, 524, 274, 679], [439, 435, 777, 557], [336, 777, 396, 494], [758, 769, 239, 216], [312, 247, 523, 512], [523, 403, 147, 278]], ![[583, 627, 6, 773], [729, 54, 294, 124], [696, 306, 289, 85], [166, 216, 21, 266], [121, 486, 242, 503], [785, 197, 580, 135], [139, 253, 281, 459], [569, 539, 711, 384], [170, 278, 357, 326], [651, 563, 644, 543]], ![[0, 1], [519, 227, 345, 429], [551, 230, 53, 628], [278, 42, 204, 579], [134, 576, 462, 397], [796, 16, 258, 458], [794, 689, 724, 485], [203, 662, 191, 352], [656, 272, 714, 755], [583, 627, 6, 773]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [393, 741, 452], []]
 b := ![[], [], [495, 49, 657, 485], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI797N0 : CertifiedPrimeIdeal' SI797N0 797 where
  n := 4
  hpos := by decide
  P := [119, 465, 578, 634, 1]
  hirr := P797P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10686506761, -6269670108, -2036169120, -10831579558, 5832910422]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3936168749, -4779582516, -3947270874, -1404121154, 5832910422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI797N0 : Ideal.IsPrime I797N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI797N0 B_one_repr
lemma NI797N0 : Nat.card (O ⧸ I797N0) = 403490473681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI797N0

def I797N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 21, 5, 26, -15]] i)))

def SI797N1: IdealEqSpanCertificate' Table ![![35, 21, 5, 26, -15]] 
 ![![797, 0, 0, 0, 0], ![226, 1, 0, 0, 0], ![763, 0, 1, 0, 0], ![541, 0, 0, 1, 0], ![656, 0, 0, 0, 1]] where
  M :=![![![35, 21, 5, 26, -15], ![-120, -61, -10, -121, 63], ![252, 153, 60, 271, -150], ![-540, -324, -113, -540, 300], ![748, 436, 143, 765, -419]]]
  hmulB := by decide  
  f := ![![![-7457, 2676, -4907, -1088, 1647]], ![![-2098, 755, -1382, -305, 465]], ![![-7147, 2568, -4705, -1041, 1581]], ![![-5053, 1821, -3330, -733, 1122]], ![![-6124, 2215, -4041, -884, 1366]]]
  g := ![![![-16, 21, 5, 26, -15], ![57, -61, -10, -121, 63], ![-161, 153, 60, 271, -150], ![319, -324, -113, -540, 300], ![-434, 436, 143, 765, -419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI797N1 : Nat.card (O ⧸ I797N1) = 797 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI797N1)

lemma isPrimeI797N1 : Ideal.IsPrime I797N1 := prime_ideal_of_norm_prime hp797.out _ NI797N1
def MulI797N0 : IdealMulLeCertificate' Table 
  ![![-7457, 2676, -4907, -1088, 1647]] ![![35, 21, 5, 26, -15]]
  ![![797, 0, 0, 0, 0]] where
 M := ![![![797, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC797 : ContainsPrimesAboveP 797 ![I797N0, I797N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI797N0
    exact isPrimeI797N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 797 (by decide) (𝕀 ⊙ MulI797N0)
instance hp809 : Fact (Nat.Prime 809) := {out := by norm_num}

def I809N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-833, 1214, -1091, 408, 895]] i)))

def SI809N0: IdealEqSpanCertificate' Table ![![-833, 1214, -1091, 408, 895]] 
 ![![809, 0, 0, 0, 0], ![0, 809, 0, 0, 0], ![0, 0, 809, 0, 0], ![0, 0, 0, 809, 0], ![376, 127, 373, 80, 1]] where
  M :=![![![-833, 1214, -1091, 408, 895], ![7160, 2143, 1612, 3675, 2119], ![8476, 7846, -1532, 7191, 6572], ![22708, 15235, -151, 16037, 13013], ![50308, 34885, -1069, 36282, 29800]]]
  hmulB := by decide  
  f := ![![![71, 43, 17, 78, -43]], ![![-344, -205, -70, -345, 191]], ![![764, 443, 140, 771, -422]], ![![-1516, -886, -293, -1550, 850]], ![![184, 106, 33, 187, -102]]]
  g := ![![![-417, -139, -414, -88, 895], ![-976, -330, -975, -205, 2119], ![-3044, -1022, -3032, -641, 6572], ![-6020, -2024, -6000, -1267, 13013], ![-13788, -4635, -13741, -2902, 29800]]]
  hle1 := by decide   
  hle2 := by decide  


def P809P0 : CertificateIrreducibleZModOfList' 809 4 2 9 [477, 339, 114, 327, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [213, 685, 301, 745], [92, 119, 382, 783], [177, 4, 126, 90], [0, 1]]
 g := ![![[661, 239, 5, 692], [179, 104, 578], [586, 337, 665], [302, 586, 741, 234], [665, 371, 490], [411, 270, 297, 698], [536, 739, 766], [27, 482, 1], []], ![[280, 87, 242, 664, 201, 79], [605, 158, 40], [35, 112, 408], [416, 44, 763, 548, 273, 90], [565, 808, 395], [58, 559, 410, 546, 292, 416], [775, 330, 705], [457, 582, 160], [625, 666, 218, 427, 197, 781]], ![[90, 621, 415, 263, 134, 298], [387, 238, 208], [589, 794, 718], [192, 334, 511, 467, 590, 76], [300, 197, 98], [312, 196, 687, 209, 344, 158], [661, 122, 790], [353, 381, 510], [305, 445, 602, 144, 699, 222]], ![[300, 783, 40, 50, 537, 687], [432, 589, 132], [606, 415, 95], [507, 98, 523, 270, 751, 804], [687, 5, 95], [249, 150, 296, 713, 490, 707], [147, 208, 46], [476, 614, 122], [410, 165, 148, 680, 720, 91]]]
 h' := ![![[213, 685, 301, 745], [555, 472, 211, 634], [669, 555, 800, 730], [757, 755, 768, 580], [283, 90, 470, 176], [540, 112, 96, 630], [152, 376, 751, 673], [65, 397, 510, 604], [0, 0, 0, 1], [0, 1]], ![[92, 119, 382, 783], [266, 57, 26, 651], [389, 111, 552, 629], [516, 101, 78, 690], [622, 257, 309, 620], [455, 108, 417, 442], [84, 338, 757, 380], [739, 562, 48, 711], [488, 428, 660, 360], [213, 685, 301, 745]], ![[177, 4, 126, 90], [764, 545, 559, 76], [464, 613, 599, 581], [158, 455, 522, 641], [657, 500, 734, 640], [654, 231, 497, 253], [392, 187, 3, 432], [370, 10, 71, 373], [565, 692, 477, 712], [92, 119, 382, 783]], ![[0, 1], [383, 544, 13, 257], [31, 339, 476, 487], [33, 307, 250, 516], [300, 771, 105, 182], [202, 358, 608, 293], [739, 717, 107, 133], [73, 649, 180, 739], [555, 498, 481, 545], [177, 4, 126, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [245, 496, 218], []]
 b := ![[], [], [805, 180, 323, 444], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI809N0 : CertifiedPrimeIdeal' SI809N0 809 where
  n := 4
  hpos := by decide
  P := [477, 339, 114, 327, 1]
  hirr := P809P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-63261486, -13789015, -60581068, -134930380, 304587624]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-141641790, -47832407, -140508980, -30286700, 304587624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI809N0 : Ideal.IsPrime I809N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI809N0 B_one_repr
lemma NI809N0 : Nat.card (O ⧸ I809N0) = 428345379361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI809N0

def I809N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 43, 17, 78, -43]] i)))

def SI809N1: IdealEqSpanCertificate' Table ![![71, 43, 17, 78, -43]] 
 ![![809, 0, 0, 0, 0], ![568, 1, 0, 0, 0], ![488, 0, 1, 0, 0], ![272, 0, 0, 1, 0], ![613, 0, 0, 0, 1]] where
  M :=![![![71, 43, 17, 78, -43], ![-344, -205, -70, -345, 191], ![764, 443, 140, 771, -422], ![-1516, -886, -293, -1550, 850], ![2156, 1262, 415, 2187, -1201]]]
  hmulB := by decide  
  f := ![![![-833, 1214, -1091, 408, 895]], ![![-576, 855, -764, 291, 631]], ![![-492, 742, -660, 255, 548]], ![![-252, 427, -367, 157, 317]], ![![-569, 963, -828, 354, 715]]]
  g := ![![![-34, 43, 17, 78, -43], ![157, -205, -70, -345, 191], ![-334, 443, 140, 771, -422], ![674, -886, -293, -1550, 850], ![-959, 1262, 415, 2187, -1201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI809N1 : Nat.card (O ⧸ I809N1) = 809 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI809N1)

lemma isPrimeI809N1 : Ideal.IsPrime I809N1 := prime_ideal_of_norm_prime hp809.out _ NI809N1
def MulI809N0 : IdealMulLeCertificate' Table 
  ![![-833, 1214, -1091, 408, 895]] ![![71, 43, 17, 78, -43]]
  ![![809, 0, 0, 0, 0]] where
 M := ![![![809, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC809 : ContainsPrimesAboveP 809 ![I809N0, I809N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI809N0
    exact isPrimeI809N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 809 (by decide) (𝕀 ⊙ MulI809N0)
instance hp811 : Fact (Nat.Prime 811) := {out := by norm_num}

def I811N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 65, 127, 5, -30]] i)))

def SI811N0: IdealEqSpanCertificate' Table ![![-37, 65, 127, 5, -30]] 
 ![![811, 0, 0, 0, 0], ![0, 811, 0, 0, 0], ![0, 0, 811, 0, 0], ![305, 775, 757, 1, 0], ![809, 127, 176, 0, 1]] where
  M :=![![![-37, 65, 127, 5, -30], ![-240, -65, 120, 39, -15], ![-60, -117, -104, 48, 51], ![324, 54, -225, 31, 105], ![268, 116, -89, 140, 130]]]
  hmulB := by decide  
  f := ![![![89, -28, 55, 17, -18]], ![![-144, 37, -90, -33, 33]], ![![132, -18, 70, 42, -33]], ![![19, 8, 0, 14, -6]], ![![95, -26, 56, 21, -20]]]
  g := ![![![28, 0, 2, 5, -30], ![0, -35, -33, 39, -15], ![-69, -54, -56, 48, 51], ![-116, -46, -52, 31, 105], ![-182, -154, -159, 140, 130]]]
  hle1 := by decide   
  hle2 := by decide  


def P811P0 : CertificateIrreducibleZModOfList' 811 3 2 9 [490, 331, 319, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [294, 349, 77], [198, 461, 734], [0, 1]]
 g := ![![[486, 121, 358], [681, 571, 464], [744, 580], [337, 365, 158], [738, 104], [459, 469, 333], [704, 728], [456, 386], [1]], ![[385, 571, 92, 254], [298, 346, 5, 693], [201, 603], [385, 378, 556, 170], [455, 271], [114, 614, 242, 214], [608, 39], [703, 692], [150, 157, 756, 751]], ![[294, 216, 507, 399], [183, 730, 413, 2], [521, 93], [430, 276, 111, 770], [787, 523], [661, 671, 262, 247], [240, 471], [492, 286], [140, 574, 110, 60]]]
 h' := ![![[294, 349, 77], [442, 366, 257], [44, 761, 274], [314, 155, 301], [320, 188, 176], [548, 52, 716], [297, 325, 244], [440, 524, 538], [321, 480, 492], [0, 1]], ![[198, 461, 734], [483, 736, 679], [265, 484, 3], [589, 380, 661], [539, 282, 725], [537, 724, 759], [336, 109, 450], [466, 629, 461], [611, 560, 197], [294, 349, 77]], ![[0, 1], [56, 520, 686], [163, 377, 534], [522, 276, 660], [227, 341, 721], [459, 35, 147], [360, 377, 117], [249, 469, 623], [646, 582, 122], [198, 461, 734]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [791, 670], []]
 b := ![[], [654, 653, 381], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI811N0 : CertifiedPrimeIdeal' SI811N0 811 where
  n := 3
  hpos := by decide
  P := [490, 331, 319, 1]
  hirr := P811P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18207, -9383, -9520, -30407, 45018]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33494, 21996, 18601, -30407, 45018]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI811N0 : Ideal.IsPrime I811N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI811N0 B_one_repr
lemma NI811N0 : Nat.card (O ⧸ I811N0) = 533411731 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI811N0

def I811N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, -28, 55, 17, -18]] i)))

def SI811N1: IdealEqSpanCertificate' Table ![![89, -28, 55, 17, -18]] 
 ![![811, 0, 0, 0, 0], ![0, 811, 0, 0, 0], ![218, 54, 1, 0, 0], ![393, 32, 0, 1, 0], ![762, 377, 0, 0, 1]] where
  M :=![![![89, -28, 55, 17, -18], ![-144, 37, -90, -33, 33], ![132, -18, 70, 42, -33], ![-60, -21, -15, -50, 30], ![100, 35, 31, 77, -41]]]
  hmulB := by decide  
  f := ![![![-37, 65, 127, 5, -30]], ![![-240, -65, 120, 39, -15]], ![![-26, 13, 42, 4, -9]], ![![-27, 29, 66, 4, -15]], ![![-146, 31, 175, 23, -35]]]
  g := ![![![-6, 4, 55, 17, -18], ![9, -8, -90, -33, 33], ![-8, 9, 70, 42, -33], ![0, -11, -15, -50, 30], ![-7, 14, 31, 77, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P811P1 : CertificateIrreducibleZModOfList' 811 2 2 9 [231, 181, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [630, 810], [0, 1]]
 g := ![![[71, 401], [345, 226], [150], [699, 156], [248], [48, 764], [445], [801], [630, 1]], ![[480, 410], [800, 585], [150], [37, 655], [248], [445, 47], [445], [801], [449, 810]]]
 h' := ![![[630, 810], [594, 83], [135, 330], [731, 31], [492, 111], [266, 516], [650, 598], [438, 88], [450, 90], [0, 1]], ![[0, 1], [169, 728], [419, 481], [797, 780], [676, 700], [135, 295], [275, 213], [730, 723], [380, 721], [630, 810]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [733]]
 b := ![[], [120, 772]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI811N1 : CertifiedPrimeIdeal' SI811N1 811 where
  n := 2
  hpos := by decide
  P := [231, 181, 1]
  hirr := P811P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-561, -1573, 1100, -2985, 1107]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![110, -472, 1100, -2985, 1107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI811N1 : Ideal.IsPrime I811N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI811N1 B_one_repr
lemma NI811N1 : Nat.card (O ⧸ I811N1) = 657721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI811N1
def MulI811N0 : IdealMulLeCertificate' Table 
  ![![-37, 65, 127, 5, -30]] ![![89, -28, 55, 17, -18]]
  ![![811, 0, 0, 0, 0]] where
 M := ![![![811, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC811 : ContainsPrimesAboveP 811 ![I811N0, I811N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI811N0
    exact isPrimeI811N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 811 (by decide) (𝕀 ⊙ MulI811N0)
instance hp821 : Fact (Nat.Prime 821) := {out := by norm_num}

def I821N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6127, -4206, 53, -4349, -3546]] i)))

def SI821N0: IdealEqSpanCertificate' Table ![![-6127, -4206, 53, -4349, -3546]] 
 ![![821, 0, 0, 0, 0], ![0, 821, 0, 0, 0], ![165, 612, 1, 0, 0], ![3, 736, 0, 1, 0], ![430, 31, 0, 0, 1]] where
  M :=![![![-6127, -4206, 53, -4349, -3546], ![-28368, -19455, 286, -20367, -16593], ![-66372, -45340, 912, -47606, -38847], ![-141204, -96317, 2123, -101066, -82536], ![-320868, -219049, 4577, -229695, -187519]]]
  hmulB := by decide  
  f := ![![![3709, 8801, -2477, 9979, -4728]], ![![-37824, -32387, -2356, -48029, 25209]], ![![-27327, -22292, -2235, -33663, 17769]], ![![-34161, -29159, -2172, -43292, 22731]], ![![890, 3609, -1315, 3797, -1735]]]
  g := ![![![1855, 3988, 53, -4349, -3546], ![8673, 18648, 286, -20367, -16593], ![20256, 43409, 912, -47606, -38847], ![42999, 92019, 2123, -101066, -82536], ![97742, 209316, 4577, -229695, -187519]]]
  hle1 := by decide   
  hle2 := by decide  


def P821P0 : CertificateIrreducibleZModOfList' 821 2 2 9 [43, 588, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [233, 820], [0, 1]]
 g := ![![[491, 611], [150], [1, 655], [203], [255, 487], [573, 361], [469], [316], [233, 1]], ![[0, 210], [150], [731, 166], [203], [428, 334], [123, 460], [469], [316], [466, 820]]]
 h' := ![![[233, 820], [325, 580], [778, 266], [182, 307], [529, 789], [812, 634], [470, 802], [344, 223], [654, 60], [0, 1]], ![[0, 1], [0, 241], [360, 555], [286, 514], [462, 32], [754, 187], [148, 19], [580, 598], [677, 761], [233, 820]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [476]]
 b := ![[], [187, 238]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI821N0 : CertifiedPrimeIdeal' SI821N0 821 where
  n := 2
  hpos := by decide
  P := [43, 588, 1]
  hirr := P821P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-648, -2894, -3089, -4942, 9308]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4237, 6378, -3089, -4942, 9308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI821N0 : Ideal.IsPrime I821N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI821N0 B_one_repr
lemma NI821N0 : Nat.card (O ⧸ I821N0) = 674041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI821N0

def I821N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5831, -13001, -12680, 1103, 3405]] i)))

def SI821N1: IdealEqSpanCertificate' Table ![![-5831, -13001, -12680, 1103, 3405]] 
 ![![821, 0, 0, 0, 0], ![0, 821, 0, 0, 0], ![662, 54, 1, 0, 0], ![376, 289, 0, 1, 0], ![550, 800, 0, 0, 1]] where
  M :=![![![-5831, -13001, -12680, 1103, 3405], ![27240, -2589, -28208, -2628, 6714], ![26856, 17615, 39, -3395, -585], ![-15960, 14977, 35114, 1003, -8742], ![-1648, 7353, 11644, -128, -2977]]]
  hmulB := by decide  
  f := ![![![4781, -1199, 2870, 1161, -1209]], ![![-9672, 445, -4720, -3884, 2274]], ![![3230, -937, 2009, 687, -831]], ![![-1232, -402, -350, -851, 252]], ![![-6210, -365, -2672, -2994, 1391]]]
  g := ![![![7431, -2888, -12680, 1103, 3405], ![19484, -3765, -28208, -2628, 6714], ![1948, 1784, 39, -3395, -585], ![-22936, 5874, 35114, 1003, -8742], ![-7338, 2189, 11644, -128, -2977]]]
  hle1 := by decide   
  hle2 := by decide  


def P821P1 : CertificateIrreducibleZModOfList' 821 2 2 9 [505, 337, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [484, 820], [0, 1]]
 g := ![![[729, 543], [387], [233, 575], [505], [27, 720], [311, 732], [590], [570], [484, 1]], ![[0, 278], [387], [214, 246], [505], [403, 101], [748, 89], [590], [570], [147, 820]]]
 h' := ![![[484, 820], [464, 474], [559, 109], [544, 619], [322, 459], [577, 174], [588, 557], [316, 296], [238, 587], [0, 1]], ![[0, 1], [0, 347], [771, 712], [475, 202], [808, 362], [230, 647], [67, 264], [726, 525], [280, 234], [484, 820]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [775]]
 b := ![[], [640, 798]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI821N1 : CertifiedPrimeIdeal' SI821N1 821 where
  n := 2
  hpos := by decide
  P := [505, 337, 1]
  hirr := P821P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1821, 318, -356, 629, 63]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41, -259, -356, 629, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI821N1 : Ideal.IsPrime I821N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI821N1 B_one_repr
lemma NI821N1 : Nat.card (O ⧸ I821N1) = 674041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI821N1

def I821N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 2, 13, -3, -6]] i)))

def SI821N2: IdealEqSpanCertificate' Table ![![-11, 2, 13, -3, -6]] 
 ![![821, 0, 0, 0, 0], ![310, 1, 0, 0, 0], ![389, 0, 1, 0, 0], ![304, 0, 0, 1, 0], ![796, 0, 0, 0, 1]] where
  M :=![![![-11, 2, 13, -3, -6], ![-48, -25, 10, -13, -15], ![-60, -50, -12, -36, -27], ![-84, -73, -19, -82, -60], ![-244, -173, -5, -181, -145]]]
  hmulB := by decide  
  f := ![![![8297, -2905, 5339, 1177, -1524]], ![![3118, -1091, 2006, 443, -573]], ![![3941, -1382, 2537, 557, -723]], ![![3076, -1072, 1977, 441, -567]], ![![8040, -2822, 5177, 1134, -1474]]]
  g := ![![![0, 2, 13, -3, -6], ![24, -25, 10, -13, -15], ![64, -50, -12, -36, -27], ![125, -73, -19, -82, -60], ![275, -173, -5, -181, -145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI821N2 : Nat.card (O ⧸ I821N2) = 821 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI821N2)

lemma isPrimeI821N2 : Ideal.IsPrime I821N2 := prime_ideal_of_norm_prime hp821.out _ NI821N2
def MulI821N0 : IdealMulLeCertificate' Table 
  ![![-6127, -4206, 53, -4349, -3546]] ![![-5831, -13001, -12680, 1103, 3405]]
  ![![-2167687, 271345, 2334865, 207193, -557124]] where
 M := ![![![-2167687, 271345, 2334865, 207193, -557124]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI821N1 : IdealMulLeCertificate' Table 
  ![![-2167687, 271345, 2334865, 207193, -557124]] ![![-11, 2, 13, -3, -6]]
  ![![821, 0, 0, 0, 0]] where
 M := ![![![-10737859, -46604886, -54635908, 2770054, 14245992]]]
 hmul := by decide  
 g := ![![![![-13079, -56766, -66548, 3374, 17352]]]]
 hle2 := by decide  


def PBC821 : ContainsPrimesAboveP 821 ![I821N0, I821N1, I821N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI821N0
    exact isPrimeI821N1
    exact isPrimeI821N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 821 (by decide) (𝕀 ⊙ MulI821N0 ⊙ MulI821N1)
instance hp823 : Fact (Nat.Prime 823) := {out := by norm_num}

def I823N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3002471, -2633706, -921770, 406046, 302724]] i)))

def SI823N0: IdealEqSpanCertificate' Table ![![-3002471, -2633706, -921770, 406046, 302724]] 
 ![![823, 0, 0, 0, 0], ![0, 823, 0, 0, 0], ![0, 0, 823, 0, 0], ![0, 0, 0, 823, 0], ![301, 812, 294, 521, 1]] where
  M :=![![![-3002471, -2633706, -921770, 406046, 302724], ![2421792, -2816667, -6079504, -130518, 1520862], ![6083448, 2038558, -2686149, -691228, 564654], ![1047720, 4864232, 5769538, -298987, -1514946], ![1172280, 1888732, 1548058, -192840, -425561]]]
  hmulB := by decide  
  f := ![![![-6161, 2186, -4010, -902, 1320]], ![![10560, -2669, 6176, 2122, -1386]], ![![-5544, 3842, -4791, 264, 2490]], ![![4680, 2260, 490, 2731, 2334]], ![![9157, 978, 3224, 3595, 1489]]]
  g := ![![![-114365, -301878, -109262, -191146, 302724], ![-553290, -1503957, -550684, -962940, 1520862], ![-199122, -554630, -204975, -358294, 564654], ![555342, 1500608, 548194, 958673, -1514946], ![157067, 422168, 153904, 269167, -425561]]]
  hle1 := by decide   
  hle2 := by decide  


def P823P0 : CertificateIrreducibleZModOfList' 823 4 2 9 [508, 324, 298, 774, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [587, 791, 24, 579], [8, 114, 488, 451], [277, 740, 311, 616], [0, 1]]
 g := ![![[318, 560, 267, 666], [302, 627, 160, 817], [603, 268, 601, 253], [716, 725, 169], [331, 147, 155, 169], [368, 163, 194, 756], [75, 336, 308], [457, 49, 1], []], ![[544, 450, 805, 326, 582, 398], [588, 1, 288, 464, 382, 722], [791, 157, 349, 386, 419, 799], [317, 558, 123], [564, 159, 579, 215, 365, 209], [670, 692, 370, 189, 451, 516], [592, 548, 235], [496, 482, 671], [365, 71, 172, 174, 692, 812]], ![[685, 565, 125, 703, 519, 538], [723, 188, 217, 644, 450, 281], [503, 50, 168, 78, 471, 769], [412, 561, 658], [111, 628, 2, 313, 708, 107], [557, 29, 130, 625, 748, 119], [708, 405, 644], [288, 782, 512], [768, 455, 411, 714, 555, 625]], ![[447, 354, 471, 572, 331, 57], [249, 210, 411, 235, 491, 794], [122, 239, 534, 452, 128, 329], [23, 717, 212], [397, 362, 560, 636, 681, 806], [698, 548, 188, 425, 249, 81], [374, 149, 338], [285, 281, 8], [448, 770, 817, 474, 732, 551]]]
 h' := ![![[587, 791, 24, 579], [485, 316, 467, 220], [655, 131, 248, 356], [557, 549, 730, 382], [567, 278, 164, 810], [700, 637, 4, 13], [543, 157, 470, 705], [753, 693, 508, 60], [0, 0, 0, 1], [0, 1]], ![[8, 114, 488, 451], [14, 628, 86, 552], [458, 244, 786, 270], [101, 282, 504, 87], [192, 402, 430, 475], [36, 184, 55, 21], [468, 220, 771, 310], [322, 664, 219, 52], [455, 611, 295, 683], [587, 791, 24, 579]], ![[277, 740, 311, 616], [4, 580, 36, 739], [754, 671, 171, 721], [587, 405, 105, 189], [29, 482, 270, 775], [285, 94, 264, 120], [135, 139, 600, 692], [526, 341, 416, 288], [470, 327, 765, 394], [8, 114, 488, 451]], ![[0, 1], [224, 122, 234, 135], [809, 600, 441, 299], [322, 410, 307, 165], [801, 484, 782, 409], [758, 731, 500, 669], [252, 307, 628, 762], [581, 771, 503, 423], [345, 708, 586, 568], [277, 740, 311, 616]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [83, 565, 804], []]
 b := ![[], [], [182, 369, 171, 188], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI823N0 : CertifiedPrimeIdeal' SI823N0 823 where
  n := 4
  hpos := by decide
  P := [508, 324, 298, 774, 1]
  hirr := P823P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18871827, -15646562, -7041900, 14923326, -4331702]
  a := ![7, -1, -26, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1561325, 4254794, 1538856, 2760316, -4331702]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI823N0 : Ideal.IsPrime I823N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI823N0 B_one_repr
lemma NI823N0 : Nat.card (O ⧸ I823N0) = 458774574241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI823N0

def I823N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6161, -2186, 4010, 902, -1320]] i)))

def SI823N1: IdealEqSpanCertificate' Table ![![6161, -2186, 4010, 902, -1320]] 
 ![![823, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![753, 0, 1, 0, 0], ![360, 0, 0, 1, 0], ![411, 0, 0, 0, 1]] where
  M :=![![![6161, -2186, 4010, 902, -1320], ![-10560, 2669, -6176, -2122, 1386], ![5544, -3842, 4791, -264, -2490], ![-4680, -2260, -490, -2731, -2334], ![-7608, -7128, 1286, -6656, -5485]]]
  hmulB := by decide  
  f := ![![![3002471, 2633706, 921770, -406046, -302724]], ![![296210, 265833, 99228, -40298, -32010]], ![![2739705, 2407220, 846633, -370670, -277662]], ![![1312080, 1146136, 396194, -177251, -130578]], ![![1497987, 1312958, 458444, -202542, -150661]]]
  g := ![![![-3179, -2186, 4010, 902, -1320], ![5608, 2669, -6176, -2122, 1386], ![-2635, -3842, 4791, -264, -2490], ![3028, -2260, -490, -2731, -2334], ![5175, -7128, 1286, -6656, -5485]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI823N1 : Nat.card (O ⧸ I823N1) = 823 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI823N1)

lemma isPrimeI823N1 : Ideal.IsPrime I823N1 := prime_ideal_of_norm_prime hp823.out _ NI823N1
def MulI823N0 : IdealMulLeCertificate' Table 
  ![![-3002471, -2633706, -921770, 406046, 302724]] ![![6161, -2186, 4010, 902, -1320]]
  ![![823, 0, 0, 0, 0]] where
 M := ![![![-823, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC823 : ContainsPrimesAboveP 823 ![I823N0, I823N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI823N0
    exact isPrimeI823N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 823 (by decide) (𝕀 ⊙ MulI823N0)
instance hp827 : Fact (Nat.Prime 827) := {out := by norm_num}

def I827N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-349, -80, -276, -23, 81]] i)))

def SI827N0: IdealEqSpanCertificate' Table ![![-349, -80, -276, -23, 81]] 
 ![![827, 0, 0, 0, 0], ![0, 827, 0, 0, 0], ![0, 0, 827, 0, 0], ![477, 483, 87, 1, 0], ![611, 177, 542, 0, 1]] where
  M :=![![![-349, -80, -276, -23, 81], ![648, -197, -114, 38, 12], ![48, 278, -235, -91, 63], ![-72, 208, 426, 12, -111], ![-72, 118, 78, -23, -16]]]
  hmulB := by decide  
  f := ![![![-23, -14, 0, -17, -9]], ![![-72, -51, 6, -46, -60]], ![![-240, -160, -5, -181, -99]], ![![-81, -55, 3, -56, -51]], ![![-191, -127, -2, -142, -85]]]
  g := ![![![-47, -4, -51, -23, 81], ![-30, -25, -12, 38, 12], ![6, 40, -32, -91, 63], ![75, 17, 72, 12, -111], ![25, 17, 13, -23, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P827P0 : CertificateIrreducibleZModOfList' 827 3 2 9 [686, 350, 222, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [817, 811, 10], [615, 15, 817], [0, 1]]
 g := ![![[258, 84, 275], [694, 815, 768], [14, 598], [222, 105, 147], [31, 773, 478], [596, 817, 195], [180, 502], [86, 491], [1]], ![[292, 371, 654, 652], [603, 53, 497, 246], [818, 289], [328, 128, 521, 118], [718, 423, 493, 234], [283, 125, 247, 443], [222, 284], [184, 311], [382, 552, 625, 173]], ![[219, 305, 822, 717], [349, 466, 520, 55], [346, 171], [232, 687, 251, 817], [465, 268, 657, 521], [776, 367, 809, 823], [192, 750], [668, 713], [251, 378, 729, 654]]]
 h' := ![![[817, 811, 10], [268, 489, 372], [810, 712, 57], [703, 244, 167], [236, 787, 180], [509, 187, 89], [715, 234, 43], [581, 802, 447], [141, 477, 605], [0, 1]], ![[615, 15, 817], [271, 247, 546], [62, 549, 532], [653, 424, 810], [736, 437, 646], [710, 404, 724], [788, 99, 504], [528, 461, 666], [761, 530, 613], [817, 811, 10]], ![[0, 1], [34, 91, 736], [289, 393, 238], [171, 159, 677], [768, 430, 1], [564, 236, 14], [78, 494, 280], [423, 391, 541], [396, 647, 436], [615, 15, 817]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119, 757], []]
 b := ![[], [803, 727, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI827N0 : CertifiedPrimeIdeal' SI827N0 827 where
  n := 3
  hpos := by decide
  P := [686, 350, 222, 1]
  hirr := P827P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19691, 4615, -9801, 7117, 13872]
  a := ![1, 0, -5, -1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14330, -7120, -9852, 7117, 13872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI827N0 : Ideal.IsPrime I827N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI827N0 B_one_repr
lemma NI827N0 : Nat.card (O ⧸ I827N0) = 565609283 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI827N0

def I827N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -14, 0, -17, -9]] i)))

def SI827N1: IdealEqSpanCertificate' Table ![![-23, -14, 0, -17, -9]] 
 ![![827, 0, 0, 0, 0], ![0, 827, 0, 0, 0], ![104, 740, 1, 0, 0], ![778, 340, 0, 1, 0], ![187, 462, 0, 0, 1]] where
  M :=![![![-23, -14, 0, -17, -9], ![-72, -51, 6, -46, -60], ![-240, -160, -5, -181, -99], ![-360, -254, 18, -238, -291], ![-1080, -728, -6, -803, -518]]]
  hmulB := by decide  
  f := ![![![-349, -80, -276, -23, 81]], ![![648, -197, -114, 38, 12]], ![![536, -186, -137, 31, 21]], ![![-62, -156, -306, -6, 81]], ![![283, -128, -126, 16, 25]]]
  g := ![![![18, 12, 0, -17, -9], ![56, 47, 6, -46, -60], ![193, 134, -5, -181, -99], ![287, 244, 18, -238, -291], ![872, 624, -6, -803, -518]]]
  hle1 := by decide   
  hle2 := by decide  


def P827P1 : CertificateIrreducibleZModOfList' 827 2 2 9 [481, 724, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 826], [0, 1]]
 g := ![![[170, 729], [455, 662], [536], [636, 48], [798, 174], [528, 421], [312], [266], [103, 1]], ![[0, 98], [0, 165], [536], [618, 779], [526, 653], [60, 406], [312], [266], [206, 826]]]
 h' := ![![[103, 826], [300, 800], [722, 547], [74, 765], [717, 606], [748, 234], [185, 633], [379, 97], [77, 204], [0, 1]], ![[0, 1], [0, 27], [0, 280], [304, 62], [283, 221], [40, 593], [51, 194], [446, 730], [414, 623], [103, 826]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [273]]
 b := ![[], [620, 550]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI827N1 : CertifiedPrimeIdeal' SI827N1 827 where
  n := 2
  hpos := by decide
  P := [481, 724, 1]
  hirr := P827P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5302, 4750, -76, 8268, 4068]
  a := ![3, 4, 0, 9, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8682, -5598, -76, 8268, 4068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI827N1 : Ideal.IsPrime I827N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI827N1 B_one_repr
lemma NI827N1 : Nat.card (O ⧸ I827N1) = 683929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI827N1
def MulI827N0 : IdealMulLeCertificate' Table 
  ![![-349, -80, -276, -23, 81]] ![![-23, -14, 0, -17, -9]]
  ![![827, 0, 0, 0, 0]] where
 M := ![![![827, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC827 : ContainsPrimesAboveP 827 ![I827N0, I827N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI827N0
    exact isPrimeI827N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 827 (by decide) (𝕀 ⊙ MulI827N0)


lemma PB1072I15_primes (p : ℕ) :
  p ∈ Set.range ![769, 773, 787, 797, 809, 811, 821, 823, 827] ↔ Nat.Prime p ∧ 761 < p ∧ p ≤ 827 := by
  rw [← List.mem_ofFn']
  convert primes_range 761 827 (by omega)

def PB1072I15 : PrimesBelowBoundCertificateInterval O 761 827 1072 where
  m := 9
  g := ![3, 2, 1, 2, 2, 2, 3, 2, 2]
  P := ![769, 773, 787, 797, 809, 811, 821, 823, 827]
  hP := PB1072I15_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I769N0, I769N1, I769N2]
    · exact ![I773N0, I773N1]
    · exact ![I787N0]
    · exact ![I797N0, I797N1]
    · exact ![I809N0, I809N1]
    · exact ![I811N0, I811N1]
    · exact ![I821N0, I821N1, I821N2]
    · exact ![I823N0, I823N1]
    · exact ![I827N0, I827N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC769
    · exact PBC773
    · exact PBC787
    · exact PBC797
    · exact PBC809
    · exact PBC811
    · exact PBC821
    · exact PBC823
    · exact PBC827
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![591361, 591361, 769]
    · exact ![461889917, 597529]
    · exact ![301907333072707]
    · exact ![403490473681, 797]
    · exact ![428345379361, 809]
    · exact ![533411731, 657721]
    · exact ![674041, 674041, 821]
    · exact ![458774574241, 823]
    · exact ![565609283, 683929]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI769N0
      exact NI769N1
      exact NI769N2
    · dsimp ; intro j
      fin_cases j
      exact NI773N0
      exact NI773N1
    · dsimp ; intro j
      fin_cases j
      exact NI787N0
    · dsimp ; intro j
      fin_cases j
      exact NI797N0
      exact NI797N1
    · dsimp ; intro j
      fin_cases j
      exact NI809N0
      exact NI809N1
    · dsimp ; intro j
      fin_cases j
      exact NI811N0
      exact NI811N1
    · dsimp ; intro j
      fin_cases j
      exact NI821N0
      exact NI821N1
      exact NI821N2
    · dsimp ; intro j
      fin_cases j
      exact NI823N0
      exact NI823N1
    · dsimp ; intro j
      fin_cases j
      exact NI827N0
      exact NI827N1
  β := ![I769N2, I797N1, I809N1, I821N2, I823N1]
  Il := ![[I769N2], [], [], [I797N1], [I809N1], [], [I821N2], [I823N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
