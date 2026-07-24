
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp769 : Fact (Nat.Prime 769) := {out := by norm_num}

def I769N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1145, -12891, 28376, 1621, 10192]] i)))

def SI769N0: IdealEqSpanCertificate' Table ![![-1145, -12891, 28376, 1621, 10192]] 
 ![![769, 0, 0, 0, 0], ![0, 769, 0, 0, 0], ![0, 0, 769, 0, 0], ![573, 132, 114, 1, 0], ![326, 67, 586, 0, 1]] where
  M :=![![![-1145, -12891, 28376, 1621, 10192], ![-3242, -38671, 83700, 4750, 30110], ![-9500, -114182, 246569, 13980, 88720], ![-27960, -336420, 726238, 41169, 261320], ![-17594, -211606, 456848, 25900, 164383]]]
  hmulB := by decide  
  f := ![![![-187, 507, -74, 13, -62]], ![![-26, 87, -12, 24, -46]], ![![-48, 206, -255, 32, 52]], ![![-151, 423, -94, 18, -46]], ![![-118, 379, -226, 32, 9]]]
  g := ![![![-5530, -1183, -7970, 1621, 10192], ![-16308, -3489, -23540, 4750, 30110], ![-48040, -10278, -69359, 13980, 88720], ![-141493, -30272, -204292, 41169, 261320], ![-89008, -19043, -128510, 25900, 164383]]]
  hle1 := by decide   
  hle2 := by decide  


def P769P0 : CertificateIrreducibleZModOfList' 769 3 2 9 [395, 285, 532, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 591, 43], [173, 177, 726], [0, 1]]
 g := ![![[177, 485, 405], [673, 729], [168, 18], [617, 43], [652, 688], [293, 469], [17, 715], [148, 32], [1]], ![[425, 362, 474, 649], [426, 588], [619, 661], [476, 688], [724, 123], [47, 282], [399, 579], [334, 543], [743, 151, 382, 300]], ![[309, 458, 248, 737], [559, 17], [613, 17], [604, 306], [20, 507], [647, 724], [407, 306], [500, 524], [144, 273, 223, 469]]]
 h' := ![![[64, 591, 43], [98, 468, 59], [468, 168, 742], [240, 336, 399], [516, 445, 245], [748, 355, 211], [582, 253, 480], [671, 381, 696], [374, 484, 237], [0, 1]], ![[173, 177, 726], [66, 422, 576], [529, 717, 138], [129, 92, 481], [546, 176, 211], [410, 584, 320], [317, 672, 483], [308, 532, 386], [188, 598, 472], [64, 591, 43]], ![[0, 1], [97, 648, 134], [150, 653, 658], [665, 341, 658], [287, 148, 313], [156, 599, 238], [201, 613, 575], [644, 625, 456], [66, 456, 60], [173, 177, 726]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175, 613], []]
 b := ![[], [506, 265, 254], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI769N0 : CertifiedPrimeIdeal' SI769N0 769 where
  n := 3
  hpos := by decide
  P := [395, 285, 532, 1]
  hirr := P769P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-895895, -1963654, 8579459, -4525093, 3919254]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1709110, 432716, -2304607, -4525093, 3919254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI769N0 : Ideal.IsPrime I769N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI769N0 B_one_repr
lemma NI769N0 : Nat.card (O ⧸ I769N0) = 454756609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI769N0

def I769N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4899, 12504, -2071, 465, -1608]] i)))

def SI769N1: IdealEqSpanCertificate' Table ![![-4899, 12504, -2071, 465, -1608]] 
 ![![769, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![169, 0, 1, 0, 0], ![668, 0, 0, 1, 0], ![492, 0, 0, 0, 1]] where
  M :=![![![-4899, 12504, -2071, 465, -1608], ![-930, 2463, -573, 215, -426], ![-430, 1204, -726, -151, 438], ![302, -2484, 4693, -1300, -30], ![-574, 1554, 319, 951, -1933]]]
  hmulB := by decide  
  f := ![![![2235089, -14121032, 2337207, -497911, 1790052]], ![![108835, -687125, 113098, -24278, 86898]], ![![491839, -3105752, 511911, -109678, 393006]], ![![1942042, -12264704, 2023569, -432962, 1552650]], ![![1430526, -9034834, 1491375, -318887, 1143995]]]
  g := ![![![472, 12504, -2071, 465, -1608], ![92, 2463, -573, 215, -426], ![-48, 1204, -726, -151, 438], ![237, -2484, 4693, -1300, -30], ![265, 1554, 319, 951, -1933]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI769N1 : Nat.card (O ⧸ I769N1) = 769 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI769N1)

lemma isPrimeI769N1 : Ideal.IsPrime I769N1 := prime_ideal_of_norm_prime hp769.out _ NI769N1

def I769N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![237, -514, -64, -32, 16]] i)))

def SI769N2: IdealEqSpanCertificate' Table ![![237, -514, -64, -32, 16]] 
 ![![769, 0, 0, 0, 0], ![618, 1, 0, 0, 0], ![269, 0, 1, 0, 0], ![631, 0, 0, 1, 0], ![626, 0, 0, 0, 1]] where
  M :=![![![237, -514, -64, -32, 16], ![64, 109, -466, -32, -160], ![64, 640, -1427, -82, -512], ![164, 1948, -4214, -239, -1516], ![160, 1080, -2626, -156, -935]]]
  hmulB := by decide  
  f := ![![![2629, -16622, 2788, -472, 2128]], ![![2114, -13367, 2242, -380, 1712]], ![![921, -5822, 981, -166, 744]], ![![2159, -13638, 2274, -379, 1740]], ![![2138, -13524, 2258, -384, 1737]]]
  g := ![![![449, -514, -64, -32, 16], ![232, 109, -466, -32, -160], ![469, 640, -1427, -82, -512], ![1339, 1948, -4214, -239, -1516], ![940, 1080, -2626, -156, -935]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI769N2 : Nat.card (O ⧸ I769N2) = 769 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI769N2)

lemma isPrimeI769N2 : Ideal.IsPrime I769N2 := prime_ideal_of_norm_prime hp769.out _ NI769N2
def MulI769N0 : IdealMulLeCertificate' Table 
  ![![-1145, -12891, 28376, 1621, 10192]] ![![-4899, 12504, -2071, 465, -1608]]
  ![![35639, -91105, 15463, -3474, 11648]] where
 M := ![![![35639, -91105, 15463, -3474, 11648]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI769N1 : IdealMulLeCertificate' Table 
  ![![35639, -91105, 15463, -3474, 11648]] ![![237, -514, -64, -32, 16]]
  ![![769, 0, 0, 0, 0]] where
 M := ![![![4899299, -12540083, 2160121, -479856, 1605672]]]
 hmul := by decide  
 g := ![![![![6371, -16307, 2809, -624, 2088]]]]
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

def I773N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![755, -2602, 421, -99, 360]] i)))

def SI773N0: IdealEqSpanCertificate' Table ![![755, -2602, 421, -99, 360]] 
 ![![773, 0, 0, 0, 0], ![0, 773, 0, 0, 0], ![0, 0, 773, 0, 0], ![654, 772, 293, 1, 0], ![489, 29, 348, 0, 1]] where
  M :=![![![755, -2602, 421, -99, 360], ![198, -883, 341, -101, 126], ![202, -508, -52, 291, -354], ![-582, 2200, -2821, 74, 1038], ![-134, -350, 1073, -961, 1021]]]
  hmulB := by decide  
  f := ![![![947, 11306, -24449, -1387, -8796]], ![![2774, 33357, -72019, -4083, -25914]], ![![8166, 98264, -212118, -12025, -76326]], ![![6698, 80500, -173821, -9855, -62544]], ![![4399, 52877, -114171, -6473, -41081]]]
  g := ![![![-143, 82, -124, -99, 360], ![6, 95, -18, -101, 126], ![-22, -278, 49, 291, -354], ![-720, -110, -499, 74, 1038], ![167, 921, -94, -961, 1021]]]
  hle1 := by decide   
  hle2 := by decide  


def P773P0 : CertificateIrreducibleZModOfList' 773 3 2 9 [304, 93, 407, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [571, 246, 109], [568, 526, 664], [0, 1]]
 g := ![![[199, 337, 133], [760, 644], [529, 190, 546], [16, 682], [306, 104], [410, 44], [314, 316], [319, 227], [1]], ![[148, 526, 441, 204], [446, 155], [599, 593, 526, 745], [492, 717], [382, 135], [569, 269], [200, 716], [472, 82], [278, 152, 243, 254]], ![[208, 116, 20, 80], [231, 187], [355, 343, 390, 7], [268, 517], [586, 484], [118, 224], [546, 95], [699, 772], [603, 194, 445, 519]]]
 h' := ![![[571, 246, 109], [338, 735, 97], [741, 596, 275], [532, 753, 701], [725, 756, 475], [80, 42, 710], [296, 343, 56], [78, 384, 33], [469, 680, 366], [0, 1]], ![[568, 526, 664], [314, 312, 500], [520, 747, 131], [358, 198, 144], [417, 639, 637], [470, 703, 41], [422, 263, 365], [131, 711, 466], [609, 191, 724], [571, 246, 109]], ![[0, 1], [480, 499, 176], [19, 203, 367], [483, 595, 701], [372, 151, 434], [111, 28, 22], [459, 167, 352], [463, 451, 274], [622, 675, 456], [568, 526, 664]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [364, 36], []]
 b := ![[], [720, 146, 489], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI773N0 : CertifiedPrimeIdeal' SI773N0 773 where
  n := 3
  hpos := by decide
  P := [304, 93, 407, 1]
  hirr := P773P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1837914, -4664505, 4379743, 1764471, -4200393]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1166709, -1610640, 1227848, 1764471, -4200393]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI773N0 : Ideal.IsPrime I773N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI773N0 B_one_repr
lemma NI773N0 : Nat.card (O ⧸ I773N0) = 461889917 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI773N0

def I773N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![947, 11306, -24449, -1387, -8796]] i)))

def SI773N1: IdealEqSpanCertificate' Table ![![947, 11306, -24449, -1387, -8796]] 
 ![![773, 0, 0, 0, 0], ![0, 773, 0, 0, 0], ![52, 480, 1, 0, 0], ![549, 6, 0, 1, 0], ![620, 18, 0, 0, 1]] where
  M :=![![![947, 11306, -24449, -1387, -8796], ![2774, 33357, -72019, -4083, -25914], ![8166, 98264, -212118, -12025, -76326], ![24050, 289420, -624745, -35416, -224802], ![15130, 182062, -393007, -22279, -141415]]]
  hmulB := by decide  
  f := ![![![755, -2602, 421, -99, 360]], ![![198, -883, 341, -101, 126]], ![![174, -724, 240, -69, 102]], ![![537, -1852, 298, -71, 258]], ![![610, -2108, 347, -83, 293]]]
  g := ![![![9686, 15412, -24449, -1387, -8796], ![28533, 45399, -72019, -4083, -25914], ![84039, 133714, -212118, -12025, -76326], ![247518, 393824, -624745, -35416, -224802], ![155705, 247742, -393007, -22279, -141415]]]
  hle1 := by decide   
  hle2 := by decide  


def P773P1 : CertificateIrreducibleZModOfList' 773 2 2 9 [550, 159, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [614, 772], [0, 1]]
 g := ![![[235, 260], [408], [755, 268], [351], [58], [14], [594], [25], [614, 1]], ![[637, 513], [408], [658, 505], [351], [58], [14], [594], [25], [455, 772]]]
 h' := ![![[614, 772], [327, 625], [624, 644], [487, 85], [610, 630], [56, 226], [418, 88], [316, 426], [101, 768], [0, 1]], ![[0, 1], [669, 148], [264, 129], [113, 688], [157, 143], [453, 547], [340, 685], [606, 347], [123, 5], [614, 772]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [461]]
 b := ![[], [739, 617]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI773N1 : CertifiedPrimeIdeal' SI773N1 773 where
  n := 2
  hpos := by decide
  P := [550, 159, 1]
  hirr := P773P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![684, -581, 163, -88, -184]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![200, -97, 163, -88, -184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI773N1 : Ideal.IsPrime I773N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI773N1 B_one_repr
lemma NI773N1 : Nat.card (O ⧸ I773N1) = 597529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI773N1
def MulI773N0 : IdealMulLeCertificate' Table 
  ![![755, -2602, 421, -99, 360]] ![![947, 11306, -24449, -1387, -8796]]
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

def I787N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 89, -206, 25, -66]] i)))

def SI787N0: IdealEqSpanCertificate' Table ![![7, 89, -206, 25, -66]] 
 ![![787, 0, 0, 0, 0], ![0, 787, 0, 0, 0], ![0, 0, 787, 0, 0], ![266, 237, 227, 1, 0], ![518, 470, 578, 0, 1]] where
  M :=![![![7, 89, -206, 25, -66], ![-50, 321, -430, -124, 18], ![248, -370, 111, -218, -708], ![436, 2644, -7396, 1963, -2724], ![-614, 3532, -5110, -166, 473]]]
  hmulB := by decide  
  f := ![![![8775, -16451, 2732, -673, 2064]], ![![1346, -827, 106, -50, 90]], ![![100, 886, -167, 26, -120]], ![![3400, -5553, 907, -235, 690]], ![![6656, -10678, 1740, -454, 1325]]]
  g := ![![![35, 32, 41, 25, -66], ![30, 27, 22, -124, 18], ![540, 488, 583, -218, -708], ![1130, 1039, 1425, 1963, -2724], ![-256, -228, -306, -166, 473]]]
  hle1 := by decide   
  hle2 := by decide  


def P787P0 : CertificateIrreducibleZModOfList' 787 3 2 9 [618, 485, 476, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [164, 567, 345], [147, 219, 442], [0, 1]]
 g := ![![[774, 379, 19], [393, 196, 227], [60, 171], [268, 393], [244, 164, 462], [375, 239], [212, 239], [55, 707], [1]], ![[568, 235, 414, 199], [10, 660, 102, 579], [99, 268], [387, 509], [258, 44, 552, 76], [191, 150], [597, 410], [408, 555], [501, 352, 129, 326]], ![[617, 589, 663, 228], [230, 390, 528, 427], [471, 696], [693, 15], [47, 631, 732, 547], [207, 23], [203, 712], [73, 728], [723, 701, 94, 461]]]
 h' := ![![[164, 567, 345], [309, 498, 448], [215, 39, 399], [189, 213, 557], [312, 304, 567], [124, 632, 72], [517, 244, 400], [80, 495, 387], [169, 302, 311], [0, 1]], ![[147, 219, 442], [776, 134, 768], [777, 259, 100], [61, 476, 292], [208, 605, 36], [427, 209, 69], [155, 695, 214], [440, 421, 540], [269, 86, 733], [164, 567, 345]], ![[0, 1], [694, 155, 358], [498, 489, 288], [343, 98, 725], [142, 665, 184], [362, 733, 646], [682, 635, 173], [729, 658, 647], [393, 399, 530], [147, 219, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [316, 585], []]
 b := ![[], [484, 95, 580], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI787N0 : CertifiedPrimeIdeal' SI787N0 787 where
  n := 3
  hpos := by decide
  P := [618, 485, 476, 1]
  hirr := P787P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8463630, -18571875, 4244080, 17356355, -20293420]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7501480, 6868970, 9903365, 17356355, -20293420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI787N0 : Ideal.IsPrime I787N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI787N0 B_one_repr
lemma NI787N0 : Nat.card (O ⧸ I787N0) = 487443403 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI787N0

def I787N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![209, -421, -461, -58, -120]] i)))

def SI787N1: IdealEqSpanCertificate' Table ![![209, -421, -461, -58, -120]] 
 ![![787, 0, 0, 0, 0], ![632, 1, 0, 0, 0], ![372, 0, 1, 0, 0], ![209, 0, 0, 1, 0], ![481, 0, 0, 0, 1]] where
  M :=![![![209, -421, -461, -58, -120], ![116, 573, -1675, -105, -588], ![210, 2258, -5034, -289, -1806], ![578, 6856, -14863, -844, -5346], ![400, 4204, -9331, -535, -3349]]]
  hmulB := by decide  
  f := ![![![-1199, 4903, -6487, 450, 1962]], ![![-964, 3927, -5179, 347, 1584]], ![![-538, 2254, -3044, 255, 858]], ![![-403, 1693, -2284, 196, 636]], ![![-801, 3099, -3900, 127, 1385]]]
  g := ![![![645, -421, -461, -58, -120], ![719, 573, -1675, -105, -588], ![1747, 2258, -5034, -289, -1806], ![5012, 6856, -14863, -844, -5346], ![3224, 4204, -9331, -535, -3349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI787N1 : Nat.card (O ⧸ I787N1) = 787 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI787N1)

lemma isPrimeI787N1 : Ideal.IsPrime I787N1 := prime_ideal_of_norm_prime hp787.out _ NI787N1

def I787N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, 458, -77, 17, -60]] i)))

def SI787N2: IdealEqSpanCertificate' Table ![![-151, 458, -77, 17, -60]] 
 ![![787, 0, 0, 0, 0], ![715, 1, 0, 0, 0], ![325, 0, 1, 0, 0], ![577, 0, 0, 1, 0], ![288, 0, 0, 0, 1]] where
  M :=![![![-151, 458, -77, 17, -60], ![-34, 123, -31, 9, -18], ![-18, 56, -12, -13, 18], ![26, -116, 179, -22, -42], ![-14, 70, -43, 53, -73]]]
  hmulB := by decide  
  f := ![![![43423, 523162, -1128973, -63993, -406248]], ![![39613, 477257, -1029912, -58378, -370602]], ![![18411, 221810, -478665, -27132, -172242]], ![![33247, 400542, -864372, -48995, -311034]], ![![16778, 202130, -436199, -24725, -156961]]]
  g := ![![![-375, 458, -77, 17, -60], ![-99, 123, -31, 9, -18], ![-43, 56, -12, -13, 18], ![63, -116, 179, -22, -42], ![-58, 70, -43, 53, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI787N2 : Nat.card (O ⧸ I787N2) = 787 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI787N2)

lemma isPrimeI787N2 : Ideal.IsPrime I787N2 := prime_ideal_of_norm_prime hp787.out _ NI787N2
def MulI787N0 : IdealMulLeCertificate' Table 
  ![![7, 89, -206, 25, -66]] ![![209, -421, -461, -58, -120]]
  ![![-43423, -523162, 1128973, 63993, 406248]] where
 M := ![![![-43423, -523162, 1128973, 63993, 406248]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI787N1 : IdealMulLeCertificate' Table 
  ![![-43423, -523162, 1128973, 63993, 406248]] ![![-151, 458, -77, 17, -60]]
  ![![787, 0, 0, 0, 0]] where
 M := ![![![-787, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC787 : ContainsPrimesAboveP 787 ![I787N0, I787N1, I787N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI787N0
    exact isPrimeI787N1
    exact isPrimeI787N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 787 (by decide) (𝕀 ⊙ MulI787N0 ⊙ MulI787N1)
instance hp797 : Fact (Nat.Prime 797) := {out := by norm_num}

def I797N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1553, -11874, 1730, -432, 1430]] i)))

def SI797N0: IdealEqSpanCertificate' Table ![![1553, -11874, 1730, -432, 1430]] 
 ![![797, 0, 0, 0, 0], ![0, 797, 0, 0, 0], ![0, 0, 797, 0, 0], ![0, 0, 0, 797, 0], ![598, 121, 213, 683, 1]] where
  M :=![![![1553, -11874, 1730, -432, 1430], ![864, -5031, -300, -266, 268], ![532, -740, -3417, -304, -1060], ![608, 4164, -11192, -689, -3944], ![396, 1978, -6912, -454, -2401]]]
  hmulB := by decide  
  f := ![![![-3, 6, 2, 0, -2]], ![![0, 5, -12, 6, -4]], ![![-12, 28, -13, -16, 28]], ![![32, -156, 232, -37, -40]], ![![22, -121, 195, -35, -29]]]
  g := ![![![-1071, -232, -380, -1226, 1430], ![-200, -47, -72, -230, 268], ![796, 160, 279, 908, -1060], ![2960, 604, 1040, 3379, -3944], ![1802, 367, 633, 2057, -2401]]]
  hle1 := by decide   
  hle2 := by decide  


def P797P0 : CertificateIrreducibleZModOfList' 797 4 2 9 [292, 592, 632, 400, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [282, 467, 670, 487], [626, 230, 346, 190], [286, 99, 578, 120], [0, 1]]
 g := ![![[70, 721, 545, 447], [721, 731, 703], [766, 179, 223, 395], [437, 63, 70, 348], [584, 43, 560, 604], [644, 630, 704], [249, 136, 628], [765, 397, 1], []], ![[709, 65, 652, 365, 94, 308], [262, 15, 315], [717, 528, 766, 265, 571, 83], [347, 665, 572, 536, 583, 188], [109, 224, 72, 257, 509, 88], [174, 491, 731], [677, 691, 519], [479, 225, 193], [87, 169, 205, 309, 384, 63]], ![[193, 377, 434, 556, 388, 124], [197, 316, 68], [415, 258, 733, 123, 753, 746], [18, 527, 789, 123, 400, 771], [125, 591, 250, 270, 708, 584], [112, 726, 647], [86, 316, 366], [182, 323, 284], [640, 69, 81, 285, 21, 18]], ![[345, 500, 775, 425, 614, 388], [101, 11, 534], [541, 210, 688, 672, 192, 434], [341, 351, 3, 659, 720, 302], [562, 112, 524, 381, 614, 546], [688, 247, 707], [29, 176, 255], [41, 85, 549], [187, 521, 400, 325, 231, 104]]]
 h' := ![![[282, 467, 670, 487], [604, 674, 324, 615], [285, 238, 198, 561], [713, 359, 191, 337], [30, 481, 198, 82], [642, 657, 612, 401], [399, 792, 234, 116], [577, 254, 98, 404], [0, 0, 0, 1], [0, 1]], ![[626, 230, 346, 190], [125, 605, 702, 457], [526, 309, 220, 223], [14, 37, 178, 10], [190, 246, 288, 178], [146, 716, 446, 49], [296, 342, 477, 368], [779, 654, 372, 461], [679, 64, 591, 139], [282, 467, 670, 487]], ![[286, 99, 578, 120], [3, 261, 659, 192], [380, 400, 454, 571], [150, 398, 760, 434], [188, 575, 359, 445], [436, 723, 451, 496], [351, 58, 80, 38], [254, 442, 251, 686], [582, 504, 610, 486], [626, 230, 346, 190]], ![[0, 1], [437, 54, 706, 330], [624, 647, 722, 239], [169, 3, 465, 16], [446, 292, 749, 92], [482, 295, 85, 648], [558, 402, 6, 275], [726, 244, 76, 43], [501, 229, 393, 171], [286, 99, 578, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [492, 405, 370], []]
 b := ![[], [], [416, 11, 6, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI797N0 : CertifiedPrimeIdeal' SI797N0 797 where
  n := 4
  hpos := by decide
  P := [292, 592, 632, 400, 1]
  hirr := P797P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27844432368, 76237178073, -57218696031, -26606736700, 60803033461]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-45656284118, -9135420164, -16321536792, -52139370879, 60803033461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI797N0 : Ideal.IsPrime I797N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI797N0 B_one_repr
lemma NI797N0 : Nat.card (O ⧸ I797N0) = 403490473681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI797N0

def I797N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 6, 2, 0, -2]] i)))

def SI797N1: IdealEqSpanCertificate' Table ![![-3, 6, 2, 0, -2]] 
 ![![797, 0, 0, 0, 0], ![682, 1, 0, 0, 0], ![324, 0, 1, 0, 0], ![598, 0, 0, 1, 0], ![379, 0, 0, 0, 1]] where
  M :=![![![-3, 6, 2, 0, -2], ![0, 5, -12, 6, -4], ![-12, 28, -13, -16, 28], ![32, -156, 232, -37, -40], ![28, -46, -16, 58, -77]]]
  hmulB := by decide  
  f := ![![![1553, -11874, 1730, -432, 1430]], ![![1330, -10167, 1480, -370, 1224]], ![![632, -4828, 699, -176, 580]], ![![1166, -8904, 1284, -325, 1068]], ![![739, -5644, 814, -206, 677]]]
  g := ![![![-5, 6, 2, 0, -2], ![-2, 5, -12, 6, -4], ![-20, 28, -13, -16, 28], ![86, -156, 232, -37, -40], ![39, -46, -16, 58, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI797N1 : Nat.card (O ⧸ I797N1) = 797 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI797N1)

lemma isPrimeI797N1 : Ideal.IsPrime I797N1 := prime_ideal_of_norm_prime hp797.out _ NI797N1
def MulI797N0 : IdealMulLeCertificate' Table 
  ![![1553, -11874, 1730, -432, 1430]] ![![-3, 6, 2, 0, -2]]
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

def I809N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 1995, -2750, -121, -1042]] i)))

def SI809N0: IdealEqSpanCertificate' Table ![![-25, 1995, -2750, -121, -1042]] 
 ![![809, 0, 0, 0, 0], ![0, 809, 0, 0, 0], ![650, 258, 1, 0, 0], ![572, 424, 0, 1, 0], ![45, 483, 0, 0, 1]] where
  M :=![![![-25, 1995, -2750, -121, -1042], ![242, 3901, -7746, -424, -2810], ![848, 10634, -22661, -1278, -8164], ![2556, 30948, -66676, -3777, -23996], ![1598, 19528, -41954, -2374, -15103]]]
  hmulB := by decide  
  f := ![![![-571, 1449, -164, 67, -248]], ![![-134, 555, -582, 198, -94]], ![![-502, 1342, -317, 116, -228]], ![![-472, 1308, -412, 151, -228]], ![![-111, 412, -360, 125, -73]]]
  g := ![![![2353, 1565, -2750, -121, -1042], ![6680, 4375, -7746, -424, -2810], ![19566, 12784, -22661, -1278, -8164], ![57580, 37608, -66676, -3777, -23996], ![36229, 23665, -41954, -2374, -15103]]]
  hle1 := by decide   
  hle2 := by decide  


def P809P0 : CertificateIrreducibleZModOfList' 809 2 2 9 [83, 371, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [438, 808], [0, 1]]
 g := ![![[716, 28], [162], [51], [662, 392], [95], [17, 468], [16], [784], [438, 1]], ![[36, 781], [162], [51], [41, 417], [95], [324, 341], [16], [784], [67, 808]]]
 h' := ![![[438, 808], [65, 297], [123, 137], [66, 745], [177, 303], [207, 293], [423, 342], [631, 805], [51, 28], [0, 1]], ![[0, 1], [711, 512], [263, 672], [349, 64], [215, 506], [719, 516], [554, 467], [497, 4], [180, 781], [438, 808]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [9, 410]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI809N0 : CertifiedPrimeIdeal' SI809N0 809 where
  n := 2
  hpos := by decide
  P := [83, 371, 1]
  hirr := P809P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7925, -26578, 27418, 2448, -14766]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22929, -1244, 27418, 2448, -14766]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI809N0 : Ideal.IsPrime I809N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI809N0 B_one_repr
lemma NI809N0 : Nat.card (O ⧸ I809N0) = 654481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI809N0

def I809N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -9, 56, -33, 24]] i)))

def SI809N1: IdealEqSpanCertificate' Table ![![-7, -9, 56, -33, 24]] 
 ![![809, 0, 0, 0, 0], ![0, 809, 0, 0, 0], ![719, 307, 1, 0, 0], ![124, 314, 0, 1, 0], ![751, 760, 0, 0, 1]] where
  M :=![![![-7, -9, 56, -33, 24], ![66, -169, 108, 74, -150], ![-148, 814, -1297, 260, 144], ![-520, -204, 2890, -2105, 1848], ![578, -2442, 3280, -300, -887]]]
  hmulB := by decide  
  f := ![![![-20477, 124441, -22262, 4271, -16314]], ![![-8542, 53321, -9572, 1824, -7002]], ![![-21445, 130860, -23423, 4489, -17160]], ![![-6456, 39782, -7130, 1363, -5220]], ![![-27037, 165631, -29662, 5679, -21725]]]
  g := ![![![-67, -31, 56, -33, 24], ![32, 71, 108, 74, -150], ![979, 257, -1297, 260, 144], ![-3962, -2016, 2890, -2105, 1848], ![-2045, -298, 3280, -300, -887]]]
  hle1 := by decide   
  hle2 := by decide  


def P809P1 : CertificateIrreducibleZModOfList' 809 2 2 9 [771, 416, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [393, 808], [0, 1]]
 g := ![![[500, 149], [36], [65], [59, 657], [32], [92, 648], [144], [215], [393, 1]], ![[0, 660], [36], [65], [189, 152], [32], [730, 161], [144], [215], [786, 808]]]
 h' := ![![[393, 808], [523, 151], [290, 803], [624, 596], [51, 150], [260, 29], [63, 535], [125, 12], [372, 777], [0, 1]], ![[0, 1], [0, 658], [359, 6], [242, 213], [753, 659], [331, 780], [787, 274], [796, 797], [740, 32], [393, 808]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [217]]
 b := ![[], [725, 513]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI809N1 : CertifiedPrimeIdeal' SI809N1 809 where
  n := 2
  hpos := by decide
  P := [771, 416, 1]
  hirr := P809P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2293, -21995, 74864, -19446, 28381]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-89904, -47551, 74864, -19446, 28381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI809N1 : Ideal.IsPrime I809N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI809N1 B_one_repr
lemma NI809N1 : Nat.card (O ⧸ I809N1) = 654481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI809N1

def I809N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-617, 1178, -196, 48, -148]] i)))

def SI809N2: IdealEqSpanCertificate' Table ![![-617, 1178, -196, 48, -148]] 
 ![![809, 0, 0, 0, 0], ![244, 1, 0, 0, 0], ![330, 0, 1, 0, 0], ![380, 0, 0, 1, 0], ![337, 0, 0, 0, 1]] where
  M :=![![![-617, 1178, -196, 48, -148], ![-96, 71, -10, 4, -8], ![-8, -56, 11, -2, 8], ![4, -44, 10, -1, 4], ![-168, 380, -66, 16, -49]]]
  hmulB := by decide  
  f := ![![![511, 6182, -13360, -760, -4796]], ![![156, 1887, -4078, -232, -1464]], ![![214, 2588, -5593, -318, -2008]], ![![256, 3100, -6698, -381, -2404]], ![![223, 2698, -5830, -332, -2093]]]
  g := ![![![-237, 1178, -196, 48, -148], ![-16, 71, -10, 4, -8], ![10, -56, 11, -2, 8], ![8, -44, 10, -1, 4], ![-75, 380, -66, 16, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI809N2 : Nat.card (O ⧸ I809N2) = 809 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI809N2)

lemma isPrimeI809N2 : Ideal.IsPrime I809N2 := prime_ideal_of_norm_prime hp809.out _ NI809N2
def MulI809N0 : IdealMulLeCertificate' Table 
  ![![-25, 1995, -2750, -121, -1042]] ![![-7, -9, 56, -33, 24]]
  ![![-511, -6182, 13360, 760, 4796]] where
 M := ![![![-511, -6182, 13360, 760, 4796]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI809N1 : IdealMulLeCertificate' Table 
  ![![-511, -6182, 13360, 760, 4796]] ![![-617, 1178, -196, 48, -148]]
  ![![809, 0, 0, 0, 0]] where
 M := ![![![-809, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC809 : ContainsPrimesAboveP 809 ![I809N0, I809N1, I809N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI809N0
    exact isPrimeI809N1
    exact isPrimeI809N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 809 (by decide) (𝕀 ⊙ MulI809N0 ⊙ MulI809N1)
instance hp811 : Fact (Nat.Prime 811) := {out := by norm_num}

def I811N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -72, 131, 7, 48]] i)))

def SI811N0: IdealEqSpanCertificate' Table ![![-5, -72, 131, 7, 48]] 
 ![![811, 0, 0, 0, 0], ![0, 811, 0, 0, 0], ![540, 527, 1, 0, 0], ![81, 173, 0, 1, 0], ![677, 157, 0, 0, 1]] where
  M :=![![![-5, -72, 131, 7, 48], ![-14, -183, 381, 21, 138], ![-42, -524, 1122, 63, 402], ![-126, -1524, 3283, 192, 1182], ![-82, -954, 2065, 117, 749]]]
  hmulB := by decide  
  f := ![![![-579, 1048, -177, 45, -132]], ![![-90, 39, -5, -3, 6]], ![![-444, 723, -121, 28, -84]], ![![-77, 113, -19, 4, -12]], ![![-501, 883, -149, 37, -109]]]
  g := ![![![-128, -96, 131, 7, 48], ![-371, -279, 381, 21, 138], ![-1089, -821, 1122, 63, 402], ![-3192, -2405, 3283, 192, 1182], ![-2012, -1513, 2065, 117, 749]]]
  hle1 := by decide   
  hle2 := by decide  


def P811P0 : CertificateIrreducibleZModOfList' 811 2 2 9 [774, 195, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [616, 810], [0, 1]]
 g := ![![[192, 321], [676, 701], [400], [716, 345], [42], [701, 569], [380], [592], [616, 1]], ![[44, 490], [229, 110], [400], [754, 466], [42], [42, 242], [380], [592], [421, 810]]]
 h' := ![![[616, 810], [682, 181], [653, 153], [540, 791], [157, 777], [796, 431], [10, 68], [575, 214], [84, 756], [0, 1]], ![[0, 1], [260, 630], [14, 658], [385, 20], [299, 34], [284, 380], [537, 743], [206, 597], [266, 55], [616, 810]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [753]]
 b := ![[], [11, 782]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI811N0 : CertifiedPrimeIdeal' SI811N0 811 where
  n := 2
  hpos := by decide
  P := [774, 195, 1]
  hirr := P811P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![774, -1779, 2180, -517, 266]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1621, -1360, 2180, -517, 266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI811N0 : Ideal.IsPrime I811N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI811N0 B_one_repr
lemma NI811N0 : Nat.card (O ⧸ I811N0) = 657721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI811N0

def I811N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81, 206, -36, 8, -26]] i)))

def SI811N1: IdealEqSpanCertificate' Table ![![-81, 206, -36, 8, -26]] 
 ![![811, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![189, 0, 1, 0, 0], ![210, 0, 0, 1, 0], ![480, 0, 0, 0, 1]] where
  M :=![![![-81, 206, -36, 8, -26], ![-16, 39, -4, 0, -4], ![0, 0, 3, 4, -8], ![-8, 40, -60, 11, 8], ![-28, 66, -8, -12, 13]]]
  hmulB := by decide  
  f := ![![![1005, -5558, -252, -288, 322]], ![![111, -611, -32, -32, 34]], ![![235, -1290, -73, -68, 70]], ![![262, -1420, -108, -77, 68]], ![![596, -3278, -176, -172, 181]]]
  g := ![![![-1, 206, -36, 8, -26], ![-1, 39, -4, 0, -4], ![3, 0, 3, 4, -8], ![2, 40, -60, 11, 8], ![-10, 66, -8, -12, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI811N1 : Nat.card (O ⧸ I811N1) = 811 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI811N1)

lemma isPrimeI811N1 : Ideal.IsPrime I811N1 := prime_ideal_of_norm_prime hp811.out _ NI811N1

def I811N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1671, 4308, -737, 165, -550]] i)))

def SI811N2: IdealEqSpanCertificate' Table ![![-1671, 4308, -737, 165, -550]] 
 ![![811, 0, 0, 0, 0], ![402, 1, 0, 0, 0], ![596, 0, 1, 0, 0], ![464, 0, 0, 1, 0], ![804, 0, 0, 0, 1]] where
  M :=![![![-1671, 4308, -737, 165, -550], ![-330, 859, -147, 33, -110], ![-66, 176, -32, 7, -22], ![-14, 36, -1, -2, -2], ![-418, 1072, -179, 41, -139]]]
  hmulB := by decide  
  f := ![![![-529, -5592, 12599, 723, 4514]], ![![-264, -2793, 6291, 361, 2254]], ![![-394, -4172, 9394, 539, 3366]], ![![-318, -3384, 7607, 436, 2726]], ![![-534, -5660, 12741, 731, 4565]]]
  g := ![![![-1145, 4308, -737, 165, -550], ![-228, 859, -147, 33, -110], ![-46, 176, -32, 7, -22], ![-14, 36, -1, -2, -2], ![-286, 1072, -179, 41, -139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI811N2 : Nat.card (O ⧸ I811N2) = 811 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI811N2)

lemma isPrimeI811N2 : Ideal.IsPrime I811N2 := prime_ideal_of_norm_prime hp811.out _ NI811N2

def I811N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 174, -182, -6, -72]] i)))

def SI811N3: IdealEqSpanCertificate' Table ![![-9, 174, -182, -6, -72]] 
 ![![811, 0, 0, 0, 0], ![604, 1, 0, 0, 0], ![134, 0, 1, 0, 0], ![164, 0, 0, 1, 0], ![578, 0, 0, 0, 1]] where
  M :=![![![-9, 174, -182, -6, -72], ![12, 267, -492, -26, -180], ![52, 680, -1431, -80, -516], ![160, 1956, -4204, -239, -1512], ![100, 1236, -2644, -150, -953]]]
  hmulB := by decide  
  f := ![![![-158099, 404438, -69138, 15514, -51624]], ![![-117784, 301307, -51508, 11558, -38460]], ![![-26130, 66844, -11427, 2564, -8532]], ![![-31972, 81788, -13980, 3137, -10440]], ![![-112726, 288368, -49296, 11062, -36809]]]
  g := ![![![-47, 174, -182, -6, -72], ![16, 267, -492, -26, -180], ![114, 680, -1431, -80, -516], ![364, 1956, -4204, -239, -1512], ![226, 1236, -2644, -150, -953]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI811N3 : Nat.card (O ⧸ I811N3) = 811 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI811N3)

lemma isPrimeI811N3 : Ideal.IsPrime I811N3 := prime_ideal_of_norm_prime hp811.out _ NI811N3
def MulI811N0 : IdealMulLeCertificate' Table 
  ![![-5, -72, 131, 7, 48]] ![![-81, 206, -36, 8, -26]]
  ![![157, -390, 57, -15, 50]] where
 M := ![![![157, -390, 57, -15, 50]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI811N1 : IdealMulLeCertificate' Table 
  ![![157, -390, 57, -15, 50]] ![![-1671, 4308, -737, 165, -550]]
  ![![-158099, 404438, -69138, 15514, -51624]] where
 M := ![![![-158099, 404438, -69138, 15514, -51624]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI811N2 : IdealMulLeCertificate' Table 
  ![![-158099, 404438, -69138, 15514, -51624]] ![![-9, 174, -182, -6, -72]]
  ![![811, 0, 0, 0, 0]] where
 M := ![![![811, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC811 : ContainsPrimesAboveP 811 ![I811N0, I811N1, I811N2, I811N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI811N0
    exact isPrimeI811N1
    exact isPrimeI811N2
    exact isPrimeI811N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 811 (by decide) (𝕀 ⊙ MulI811N0 ⊙ MulI811N1 ⊙ MulI811N2)
instance hp821 : Fact (Nat.Prime 821) := {out := by norm_num}

def I821N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![180791847, -462391498, 79065152, -17741192, 59014720]] i)))

def SI821N0: IdealEqSpanCertificate' Table ![![180791847, -462391498, 79065152, -17741192, 59014720]] 
 ![![821, 0, 0, 0, 0], ![0, 821, 0, 0, 0], ![0, 0, 821, 0, 0], ![48, 507, 533, 1, 0], ![404, 157, 122, 0, 1]] where
  M :=![![![180791847, -462391498, 79065152, -17741192, 59014720], ![35482384, -90749417, 15517406, -3481904, 11582288], ![6963808, -17810576, 3045463, -683362, 2273152], ![1366724, -3495524, 597706, -134117, 446132], ![45454864, -116254920, 19878638, -4460508, 14837539]]]
  hmulB := by decide  
  f := ![![![35, -238, 92, 16, 32]], ![![-32, -61, 98, -4, 160]], ![![8, -680, 1367, -214, 296]], ![![-12, -495, 955, -139, 292]], ![![12, -229, 266, -24, 91]]]
  g := ![![![-27782677, -892714, 2844488, -17741192, 59014720], ![-5452656, -175205, 558262, -3481904, 11582288], ![-1070144, -34386, 109565, -683362, 2273152], ![-210028, -6749, 21503, -134117, 446132], ![-6985148, -224447, 715164, -4460508, 14837539]]]
  hle1 := by decide   
  hle2 := by decide  


def P821P0 : CertificateIrreducibleZModOfList' 821 3 2 9 [653, 376, 726, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [516, 542, 541], [400, 278, 280], [0, 1]]
 g := ![![[179, 130, 438], [464, 327], [602, 305, 742], [818, 349], [34, 799, 651], [571, 410, 130], [120, 291], [238, 815], [1]], ![[149, 155, 283, 108], [224, 449], [589, 579, 246, 413], [757, 472], [154, 14, 74, 309], [217, 240, 269, 393], [467, 453], [757, 528], [593, 686, 250, 719]], ![[101, 763, 304, 807], [154, 650], [770, 117, 778, 578], [687, 660], [179, 562, 323, 722], [158, 208, 216, 643], [650, 255], [744, 5], [810, 225, 177, 102]]]
 h' := ![![[516, 542, 541], [378, 406, 139], [153, 730, 317], [721, 51, 640], [786, 161, 101], [692, 414, 662], [576, 538, 581], [65, 733, 301], [168, 445, 95], [0, 1]], ![[400, 278, 280], [395, 654, 494], [798, 223, 308], [135, 148, 261], [213, 174, 239], [230, 125, 794], [717, 394, 205], [16, 607, 767], [597, 725, 330], [516, 542, 541]], ![[0, 1], [70, 582, 188], [161, 689, 196], [496, 622, 741], [29, 486, 481], [90, 282, 186], [301, 710, 35], [44, 302, 574], [381, 472, 396], [400, 278, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [417, 240], []]
 b := ![[], [166, 749, 470], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI821N0 : CertifiedPrimeIdeal' SI821N0 821 where
  n := 3
  hpos := by decide
  P := [653, 376, 726, 1]
  hirr := P821P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14774999, -22872389, -15542986, 38337426, -39671637]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17298319, -16116322, -19012730, 38337426, -39671637]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI821N0 : Ideal.IsPrime I821N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI821N0 B_one_repr
lemma NI821N0 : Nat.card (O ⧸ I821N0) = 553387661 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI821N0

def I821N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -12, 3, -1, 2]] i)))

def SI821N1: IdealEqSpanCertificate' Table ![![3, -12, 3, -1, 2]] 
 ![![821, 0, 0, 0, 0], ![473, 1, 0, 0, 0], ![404, 0, 1, 0, 0], ![201, 0, 0, 1, 0], ![692, 0, 0, 0, 1]] where
  M :=![![![3, -12, 3, -1, 2], ![2, -7, 3, 1, -2], ![-2, 12, -22, 5, 2], ![-10, 0, 45, -36, 34], ![10, -44, 59, -7, -13]]]
  hmulB := by decide  
  f := ![![![1459, -5264, 1109, -177, 742]], ![![841, -3035, 640, -102, 428]], ![![718, -2592, 548, -87, 366]], ![![357, -1292, 278, -43, 184]], ![![1230, -4440, 939, -149, 627]]]
  g := ![![![4, -12, 3, -1, 2], ![4, -7, 3, 1, -2], ![1, 12, -22, 5, 2], ![-42, 0, 45, -36, 34], ![9, -44, 59, -7, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI821N1 : Nat.card (O ⧸ I821N1) = 821 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI821N1)

lemma isPrimeI821N1 : Ideal.IsPrime I821N1 := prime_ideal_of_norm_prime hp821.out _ NI821N1

def I821N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-98919, 252994, -43259, 9707, -32290]] i)))

def SI821N2: IdealEqSpanCertificate' Table ![![-98919, 252994, -43259, 9707, -32290]] 
 ![![821, 0, 0, 0, 0], ![636, 1, 0, 0, 0], ![257, 0, 1, 0, 0], ![748, 0, 0, 1, 0], ![668, 0, 0, 0, 1]] where
  M :=![![![-98919, 252994, -43259, 9707, -32290], ![-19414, 49655, -8495, 1907, -6338], ![-3814, 9752, -1666, 367, -1234], ![-734, 1856, -253, 68, -266], ![-24862, 63600, -10895, 2463, -8143]]]
  hmulB := by decide  
  f := ![![![-179975, 1161226, -223781, 38447, -157502]], ![![-139514, 900203, -173527, 29801, -122114]], ![![-56373, 363854, -70281, 12034, -49404]], ![![-163970, 1058340, -204441, 35002, -143706]], ![![-146450, 945156, -182447, 31269, -128295]]]
  g := ![![![-165136, 252994, -43259, 9707, -32290], ![-32411, 49655, -8495, 1907, -6338], ![-6368, 9752, -1666, 367, -1234], ![-1205, 1856, -253, 68, -266], ![-41507, 63600, -10895, 2463, -8143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI821N2 : Nat.card (O ⧸ I821N2) = 821 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI821N2)

lemma isPrimeI821N2 : Ideal.IsPrime I821N2 := prime_ideal_of_norm_prime hp821.out _ NI821N2
def MulI821N0 : IdealMulLeCertificate' Table 
  ![![180791847, -462391498, 79065152, -17741192, 59014720]] ![![3, -12, 3, -1, 2]]
  ![![227021361, -580627534, 99282543, -22277713, 74105106]] where
 M := ![![![227021361, -580627534, 99282543, -22277713, 74105106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI821N1 : IdealMulLeCertificate' Table 
  ![![227021361, -580627534, 99282543, -22277713, 74105106]] ![![-98919, 252994, -43259, 9707, -32290]]
  ![![821, 0, 0, 0, 0]] where
 M := ![![![-13389135986715, 34243922669672, -5855429739288, 1313882328764, -4370529100760]]]
 hmul := by decide  
 g := ![![![![-16308326415, 41710015432, -7132070328, 1600343884, -5323421560]]]]
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

def I823N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![188823, -1205993, 216504, -41187, 158388]] i)))

def SI823N0: IdealEqSpanCertificate' Table ![![188823, -1205993, 216504, -41187, 158388]] 
 ![![823, 0, 0, 0, 0], ![0, 823, 0, 0, 0], ![0, 0, 823, 0, 0], ![451, 435, 490, 1, 0], ![79, 496, 821, 0, 1]] where
  M :=![![![188823, -1205993, 216504, -41187, 158388], ![82374, -527103, 95938, -17898, 69654], ![35796, -232038, 46089, -7574, 31920], ![15148, -107032, 32520, -2603, 18396], ![23502, -156562, 36438, -4688, 23279]]]
  hmulB := by decide  
  f := ![![![-53, 195, -130, 103, -126]], ![![-206, 657, -630, -84, 366]], ![![168, -1838, 3699, -1194, 228]], ![![-35, -644, 1794, -692, 252]], ![![37, -1411, 3285, -1229, 437]]]
  g := ![![![7596, -75152, -133218, -41187, 158388], ![3222, -33159, -58712, -17898, 69654], ![1130, -15516, -27277, -7574, 31920], ![-321, -9841, -16762, -2603, 18396], ![363, -11742, -20387, -4688, 23279]]]
  hle1 := by decide   
  hle2 := by decide  


def P823P0 : CertificateIrreducibleZModOfList' 823 3 2 9 [114, 736, 758, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 723, 364], [787, 99, 459], [0, 1]]
 g := ![![[555, 355, 201], [627, 814, 804], [154, 778, 280], [152, 730], [730, 394, 323], [688, 459, 119], [427, 113], [354, 110], [1]], ![[647, 351, 542, 458], [107, 363, 413, 152], [154, 308, 506, 485], [443, 72], [1, 207, 309, 752], [663, 627, 785, 662], [812, 658], [615, 769], [48, 740, 257, 744]], ![[182, 233, 127, 336], [501, 377, 47, 428], [196, 299, 743, 120], [674, 359], [747, 756, 71, 128], [363, 290, 241, 473], [193, 329], [606, 632], [242, 119, 587, 79]]]
 h' := ![![[101, 723, 364], [123, 70, 791], [550, 29, 759], [311, 572, 579], [726, 595, 656], [576, 686, 745], [776, 223, 135], [622, 68, 639], [709, 87, 65], [0, 1]], ![[787, 99, 459], [529, 780, 91], [27, 315, 105], [686, 65, 523], [736, 751, 58], [535, 361, 20], [181, 122, 715], [446, 77, 775], [194, 84, 245], [101, 723, 364]], ![[0, 1], [117, 796, 764], [419, 479, 782], [740, 186, 544], [193, 300, 109], [11, 599, 58], [711, 478, 796], [696, 678, 232], [649, 652, 513], [787, 99, 459]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [655, 29], []]
 b := ![[], [100, 770, 685], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI823N0 : CertifiedPrimeIdeal' SI823N0 823 where
  n := 3
  hpos := by decide
  P := [114, 736, 758, 1]
  hirr := P823P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4430034, -14029009, 12723311, 4528548, -8750683]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1636259, 2863173, 6048658, 4528548, -8750683]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI823N0 : Ideal.IsPrime I823N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI823N0 B_one_repr
lemma NI823N0 : Nat.card (O ⧸ I823N0) = 557441767 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI823N0

def I823N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![225, -1497, 346, -45, 222]] i)))

def SI823N1: IdealEqSpanCertificate' Table ![![225, -1497, 346, -45, 222]] 
 ![![823, 0, 0, 0, 0], ![349, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![599, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![225, -1497, 346, -45, 222], ![90, -753, 366, -8, 174], ![16, -622, 789, 34, 300], ![-68, -1116, 2180, 121, 804], ![-26, -816, 1406, 66, 523]]]
  hmulB := by decide  
  f := ![![![-56746163, 145133423, -24816624, 5568529, -18523284]], ![![-24077215, 61579646, -10529614, 2362709, -7859370]], ![![-209507, 535833, -91623, 20559, -68388]], ![![-41301799, 105633071, -18062388, 4052966, -13481880]], ![![-5533366, 14152082, -2419890, 542992, -1806221]]]
  g := ![![![645, -1497, 346, -45, 222], ![307, -753, 366, -8, 174], ![207, -622, 789, 34, 300], ![299, -1116, 2180, 121, 804], ![242, -816, 1406, 66, 523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI823N1 : Nat.card (O ⧸ I823N1) = 823 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI823N1)

lemma isPrimeI823N1 : Ideal.IsPrime I823N1 := prime_ideal_of_norm_prime hp823.out _ NI823N1

def I823N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61649, 393305, -70079, 13474, -51482]] i)))

def SI823N2: IdealEqSpanCertificate' Table ![![-61649, 393305, -70079, 13474, -51482]] 
 ![![823, 0, 0, 0, 0], ![807, 1, 0, 0, 0], ![567, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![190, 0, 0, 0, 1]] where
  M :=![![![-61649, 393305, -70079, 13474, -51482], ![-26948, 171227, -29611, 5937, -22120], ![-11874, 73406, -10042, 2755, -8618], ![-5510, 28108, 4109, 1684, -706], ![-8028, 46806, -2631, 2055, -4265]]]
  hmulB := by decide  
  f := ![![![6907, -20623, 12763, -938, -2048]], ![![6775, -20206, 12464, -897, -2020]], ![![4713, -14113, 8771, -719, -1298]], ![![305, -1119, 1188, -124, -258]], ![![1702, -4906, 2803, 31, -769]]]
  g := ![![![-325879, 393305, -70079, 13474, -51482], ![-142561, 171227, -29611, 5937, -22120], ![-63149, 73406, -10042, 2755, -8618], ![-30275, 28108, 4109, 1684, -706], ![-43156, 46806, -2631, 2055, -4265]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI823N2 : Nat.card (O ⧸ I823N2) = 823 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI823N2)

lemma isPrimeI823N2 : Ideal.IsPrime I823N2 := prime_ideal_of_norm_prime hp823.out _ NI823N2
def MulI823N0 : IdealMulLeCertificate' Table 
  ![![188823, -1205993, 216504, -41187, 158388]] ![![225, -1497, 346, -45, 222]]
  ![![-63907503, 407499294, -72333156, 13982026, -53250300]] where
 M := ![![![-63907503, 407499294, -72333156, 13982026, -53250300]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI823N1 : IdealMulLeCertificate' Table 
  ![![-63907503, 407499294, -72333156, 13982026, -53250300]] ![![-61649, 393305, -70079, 13474, -51482]]
  ![![823, 0, 0, 0, 0]] where
 M := ![![![-5832120982781, 37230626741995, -6663964455211, 1273072133560, -4883189956282]]]
 hmul := by decide  
 g := ![![![![-7086416747, 45237699565, -8097162157, 1546867720, -5933402134]]]]
 hle2 := by decide  


def PBC823 : ContainsPrimesAboveP 823 ![I823N0, I823N1, I823N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI823N0
    exact isPrimeI823N1
    exact isPrimeI823N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 823 (by decide) (𝕀 ⊙ MulI823N0 ⊙ MulI823N1)
instance hp827 : Fact (Nat.Prime 827) := {out := by norm_num}

def I827N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, 364, -337, -77, 242]] i)))

def SI827N0: IdealEqSpanCertificate' Table ![![-119, 364, -337, -77, 242]] 
 ![![827, 0, 0, 0, 0], ![0, 827, 0, 0, 0], ![0, 0, 827, 0, 0], ![150, 416, 317, 1, 0], ![119, 790, 243, 0, 1]] where
  M :=![![![-119, 364, -337, -77, 242], ![154, -1241, 2311, -667, 22], ![1334, -1268, -3044, 3601, -3958], ![-7202, 24368, -26087, -2330, 13690], ![-2382, -1812, 15375, -10515, 8849]]]
  hmulB := by decide  
  f := ![![![-1321, -10528, 1987, -307, 1426]], ![![614, -7639, 1385, -251, 1010]], ![![502, -3928, 698, -133, 514]], ![![262, -7260, 1325, -233, 964]], ![![543, -9966, 1814, -323, 1321]]]
  g := ![![![-21, -192, -42, -77, 242], ![118, 313, 252, -667, 22], ![-82, 1968, -221, 3601, -3958], ![-1556, -11876, -3161, -2330, 13690], ![631, -3166, 1449, -10515, 8849]]]
  hle1 := by decide   
  hle2 := by decide  


def P827P0 : CertificateIrreducibleZModOfList' 827 3 2 9 [593, 117, 553, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [227, 643, 292], [47, 183, 535], [0, 1]]
 g := ![![[676, 525, 213], [146, 146, 300], [142, 534], [25, 574, 537], [551, 357, 82], [647, 135, 786], [822, 542], [416, 646], [1]], ![[462, 676, 823, 266], [588, 814, 269, 806], [777, 357], [107, 823, 825, 639], [735, 510, 217, 16], [448, 39, 346, 773], [461, 324], [814, 757], [51, 408, 350, 253]], ![[196, 104, 363, 392], [576, 134, 463, 583], [258, 652], [595, 569, 58, 384], [272, 696, 181, 338], [809, 725, 346, 734], [123, 361], [81, 244], [291, 208, 228, 574]]]
 h' := ![![[227, 643, 292], [257, 176, 416], [561, 395, 139], [61, 193, 594], [749, 818, 240], [57, 363, 440], [146, 736, 451], [759, 597, 37], [234, 710, 274], [0, 1]], ![[47, 183, 535], [195, 293, 162], [100, 349, 187], [72, 559, 485], [431, 183, 769], [26, 389, 441], [356, 775, 552], [244, 133, 809], [351, 19, 265], [227, 643, 292]], ![[0, 1], [780, 358, 249], [293, 83, 501], [767, 75, 575], [722, 653, 645], [477, 75, 773], [376, 143, 651], [637, 97, 808], [728, 98, 288], [47, 183, 535]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [216, 752], []]
 b := ![[], [791, 405, 224], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI827N0 : CertifiedPrimeIdeal' SI827N0 827 where
  n := 3
  hpos := by decide
  P := [593, 117, 553, 1]
  hirr := P827P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![835026, -5823459, 9497346, -882322, -193039]
  a := ![-3, 7, 6, -2, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![188821, 621189, 406411, -882322, -193039]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI827N0 : Ideal.IsPrime I827N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI827N0 B_one_repr
lemma NI827N0 : Nat.card (O ⧸ I827N0) = 565609283 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI827N0

def I827N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -7, 5, 0, 2]] i)))

def SI827N1: IdealEqSpanCertificate' Table ![![1, -7, 5, 0, 2]] 
 ![![827, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![313, 0, 1, 0, 0], ![821, 0, 0, 1, 0], ![304, 0, 0, 0, 1]] where
  M :=![![![1, -7, 5, 0, 2], ![0, -7, 11, 1, 4], ![-2, -14, 32, 1, 14], ![-2, -56, 115, 2, 34], ![0, -34, 63, 7, 17]]]
  hmulB := by decide  
  f := ![![![4969, -15223, 2639, -568, 1960]], ![![446, -1367, 237, -51, 176]], ![![1881, -5763, 999, -215, 742]], ![![4933, -15113, 2620, -564, 1946]], ![![1828, -5600, 971, -209, 721]]]
  g := ![![![-2, -7, 5, 0, 2], ![-6, -7, 11, 1, 4], ![-17, -14, 32, 1, 14], ![-53, -56, 115, 2, 34], ![-34, -34, 63, 7, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI827N1 : Nat.card (O ⧸ I827N1) = 827 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI827N1)

lemma isPrimeI827N1 : Ideal.IsPrime I827N1 := prime_ideal_of_norm_prime hp827.out _ NI827N1

def I827N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 8, -19, -17, 36]] i)))

def SI827N2: IdealEqSpanCertificate' Table ![![-3, 8, -19, -17, 36]] 
 ![![827, 0, 0, 0, 0], ![436, 1, 0, 0, 0], ![114, 0, 1, 0, 0], ![743, 0, 0, 1, 0], ![360, 0, 0, 0, 1]] where
  M :=![![![-3, 8, -19, -17, 36], ![34, -181, 281, -57, -30], ![114, 40, -622, 455, -402], ![-910, 2632, -2213, -728, 1926], ![-130, -758, 2437, -1225, 779]]]
  hmulB := by decide  
  f := ![![![-92669, 584488, -94443, 20789, -73344]], ![![-48906, 308439, -49807, 10973, -38694]], ![![-12800, 80652, -12926, 2877, -10086]], ![![-83279, 525020, -84516, 18699, -65778]], ![![-40362, 254422, -40911, 9065, -31861]]]
  g := ![![![-2, 8, -19, -17, 36], ![121, -181, 281, -57, -30], ![-169, 40, -622, 455, -402], ![-1268, 2632, -2213, -728, 1926], ![825, -758, 2437, -1225, 779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI827N2 : Nat.card (O ⧸ I827N2) = 827 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI827N2)

lemma isPrimeI827N2 : Ideal.IsPrime I827N2 := prime_ideal_of_norm_prime hp827.out _ NI827N2
def MulI827N0 : IdealMulLeCertificate' Table 
  ![![-119, 364, -337, -77, 242]] ![![1, -7, 5, 0, 2]]
  ![![709, -913, -984, 1567, -2004]] where
 M := ![![![709, -913, -984, 1567, -2004]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI827N1 : IdealMulLeCertificate' Table 
  ![![709, -913, -984, 1567, -2004]] ![![-3, 8, -19, -17, 36]]
  ![![827, 0, 0, 0, 0]] where
 M := ![![![-1310795, 5774941, -8009495, 906392, 1905408]]]
 hmul := by decide  
 g := ![![![![-1585, 6983, -9685, 1096, 2304]]]]
 hle2 := by decide  


def PBC827 : ContainsPrimesAboveP 827 ![I827N0, I827N1, I827N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI827N0
    exact isPrimeI827N1
    exact isPrimeI827N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 827 (by decide) (𝕀 ⊙ MulI827N0 ⊙ MulI827N1)


lemma PB984I15_primes (p : ℕ) :
  p ∈ Set.range ![769, 773, 787, 797, 809, 811, 821, 823, 827] ↔ Nat.Prime p ∧ 761 < p ∧ p ≤ 827 := by
  rw [← List.mem_ofFn']
  convert primes_range 761 827 (by omega)

def PB984I15 : PrimesBelowBoundCertificateInterval O 761 827 984 where
  m := 9
  g := ![3, 2, 3, 2, 3, 4, 3, 3, 3]
  P := ![769, 773, 787, 797, 809, 811, 821, 823, 827]
  hP := PB984I15_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I769N0, I769N1, I769N2]
    · exact ![I773N0, I773N1]
    · exact ![I787N0, I787N1, I787N2]
    · exact ![I797N0, I797N1]
    · exact ![I809N0, I809N1, I809N2]
    · exact ![I811N0, I811N1, I811N2, I811N3]
    · exact ![I821N0, I821N1, I821N2]
    · exact ![I823N0, I823N1, I823N2]
    · exact ![I827N0, I827N1, I827N2]
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
    · exact ![454756609, 769, 769]
    · exact ![461889917, 597529]
    · exact ![487443403, 787, 787]
    · exact ![403490473681, 797]
    · exact ![654481, 654481, 809]
    · exact ![657721, 811, 811, 811]
    · exact ![553387661, 821, 821]
    · exact ![557441767, 823, 823]
    · exact ![565609283, 827, 827]
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
      exact NI787N1
      exact NI787N2
    · dsimp ; intro j
      fin_cases j
      exact NI797N0
      exact NI797N1
    · dsimp ; intro j
      fin_cases j
      exact NI809N0
      exact NI809N1
      exact NI809N2
    · dsimp ; intro j
      fin_cases j
      exact NI811N0
      exact NI811N1
      exact NI811N2
      exact NI811N3
    · dsimp ; intro j
      fin_cases j
      exact NI821N0
      exact NI821N1
      exact NI821N2
    · dsimp ; intro j
      fin_cases j
      exact NI823N0
      exact NI823N1
      exact NI823N2
    · dsimp ; intro j
      fin_cases j
      exact NI827N0
      exact NI827N1
      exact NI827N2
  β := ![I769N1, I769N2, I787N1, I787N2, I797N1, I809N2, I811N1, I811N2, I811N3, I821N1, I821N2, I823N1, I823N2, I827N1, I827N2]
  Il := ![[I769N1, I769N2], [], [I787N1, I787N2], [I797N1], [I809N2], [I811N1, I811N2, I811N3], [I821N1, I821N2], [I823N1, I823N2], [I827N1, I827N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
