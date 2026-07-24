
import IdealArithmetic.Examples.NF5_3_675000000_2.RI5_3_675000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp769 : Fact (Nat.Prime 769) := {out := by norm_num}

def I769N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7905, -2488, -1060, 2214, 3938]] i)))

def SI769N0: IdealEqSpanCertificate' Table ![![-7905, -2488, -1060, 2214, 3938]] 
 ![![769, 0, 0, 0, 0], ![0, 769, 0, 0, 0], ![0, 0, 769, 0, 0], ![207, 463, 412, 1, 0], ![122, 767, 136, 0, 1]] where
  M :=![![![-7905, -2488, -1060, 2214, 3938], ![-22648, -7053, -2978, 6132, 10816], ![-62000, -20590, -8501, 16380, 30320], ![-6380, -2254, -814, 1049, 2120], ![-4748, -1870, -730, 1156, 2475]]]
  hmulB := by decide  
  f := ![![![1519, -152, -188, 206, 374]], ![![-2168, 1159, -190, -308, 976]], ![![-9040, -2450, 2751, -1180, -7600]], ![![-5731, -657, 1308, -761, -3382]], ![![-3526, 699, 268, -484, -313]]]
  g := ![![![-1231, -5264, -1884, 2214, 3938], ![-3396, -14489, -5202, 6132, 10816], ![-9300, -40130, -14149, 16380, 30320], ![-627, -2749, -938, 1049, 2120], ![-710, -3167, -1058, 1156, 2475]]]
  hle1 := by decide   
  hle2 := by decide  


def P769P0 : CertificateIrreducibleZModOfList' 769 3 2 9 [17, 307, 428, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [438, 353, 442], [672, 415, 327], [0, 1]]
 g := ![![[698, 223, 102], [51, 135], [700, 180], [377, 576], [335, 153], [589, 499], [578, 24], [437, 162], [1]], ![[674, 689, 208, 390], [507, 322], [178, 646], [721, 387], [289, 258], [24, 518], [572, 178], [132, 363], [115, 16, 178, 647]], ![[249, 750, 317, 276], [225, 744], [171, 124], [300, 100], [309, 475], [681, 572], [128, 344], [708, 100], [271, 682, 477, 122]]]
 h' := ![![[438, 353, 442], [152, 312, 180], [340, 54, 685], [496, 519, 552], [521, 642, 24], [8, 94, 436], [454, 151, 564], [550, 410, 454], [752, 462, 341], [0, 1]], ![[672, 415, 327], [83, 134, 360], [131, 366, 543], [9, 334, 154], [489, 279, 735], [171, 372, 247], [386, 645, 123], [486, 27, 510], [163, 483, 438], [438, 353, 442]], ![[0, 1], [645, 323, 229], [25, 349, 310], [744, 685, 63], [228, 617, 10], [162, 303, 86], [101, 742, 82], [581, 332, 574], [137, 593, 759], [672, 415, 327]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208, 164], []]
 b := ![[], [552, 103, 278], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI769N0 : CertifiedPrimeIdeal' SI769N0 769 where
  n := 3
  hpos := by decide
  P := [17, 307, 428, 1]
  hirr := P769P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5356939, -756749, 519183, -3869584, -4176624]
  a := ![-25, -8, 9, -28, -75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1711195, 6494579, 2812495, -3869584, -4176624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI769N0 : Ideal.IsPrime I769N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI769N0 B_one_repr
lemma NI769N0 : Nat.card (O ⧸ I769N0) = 454756609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI769N0

def I769N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4661, 1435, 619, -1332, -2334]] i)))

def SI769N1: IdealEqSpanCertificate' Table ![![4661, 1435, 619, -1332, -2334]] 
 ![![769, 0, 0, 0, 0], ![600, 1, 0, 0, 0], ![661, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![4661, 1435, 619, -1332, -2334], ![13344, 4090, 1765, -3806, -6648], ![37960, 11715, 5054, -10870, -19080], ![4244, 1283, 555, -1207, -2088], ![3236, 1016, 438, -936, -1663]]]
  hmulB := by decide  
  f := ![![![5933, -5233, 1525, 868, -5994]], ![![4696, -4072, 1173, 686, -4632]], ![![4777, -4462, 1349, 702, -5226]], ![![224, -221, 69, 33, -264]], ![![437, -395, 117, 64, -457]]]
  g := ![![![-1412, 1435, 619, -1332, -2334], ![-4025, 4090, 1765, -3806, -6648], ![-11526, 11715, 5054, -10870, -19080], ![-1263, 1283, 555, -1207, -2088], ![-999, 1016, 438, -936, -1663]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI769N1 : Nat.card (O ⧸ I769N1) = 769 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI769N1)

lemma isPrimeI769N1 : Ideal.IsPrime I769N1 := prime_ideal_of_norm_prime hp769.out _ NI769N1

def I769N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -5759, 2801, 86, -9235]] i)))

def SI769N2: IdealEqSpanCertificate' Table ![![9, -5759, 2801, 86, -9235]] 
 ![![769, 0, 0, 0, 0], ![663, 1, 0, 0, 0], ![299, 0, 1, 0, 0], ![454, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![9, -5759, 2801, 86, -9235], ![74224, 4865, -15166, 9884, 37972], ![-264240, 46250, 23069, -36180, -33280], ![-24960, -24268, 16116, -3001, -49090], ![-10182, 17606, -6810, -1634, 24093]]]
  hmulB := by decide  
  f := ![![![3602183, 1332601, 567885, -1132792, -2243179]], ![![3123097, 1152900, 491369, -980988, -1939985]], ![![1431293, 534041, 227464, -452212, -900249]], ![![2135670, 787162, 335522, -670261, -1324208]], ![![340473, 128845, 54833, -108410, -217708]]]
  g := ![![![4702, -5759, 2801, 86, -9235], ![-7641, 4865, -15166, 9884, 37972], ![-24669, 46250, 23069, -36180, -33280], ![21056, -24268, 16116, -3001, -49090], ![-13867, 17606, -6810, -1634, 24093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI769N2 : Nat.card (O ⧸ I769N2) = 769 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI769N2)

lemma isPrimeI769N2 : Ideal.IsPrime I769N2 := prime_ideal_of_norm_prime hp769.out _ NI769N2
def MulI769N0 : IdealMulLeCertificate' Table 
  ![![-7905, -2488, -1060, 2214, 3938]] ![![4661, 1435, 619, -1332, -2334]]
  ![![-88143093, -27095925, -11688141, 25162722, 44043568]] where
 M := ![![![-88143093, -27095925, -11688141, 25162722, 44043568]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI769N1 : IdealMulLeCertificate' Table 
  ![![-88143093, -27095925, -11688141, 25162722, 44043568]] ![![9, -5759, 2801, 86, -9235]]
  ![![769, 0, 0, 0, 0]] where
 M := ![![![2307, -3076, 0, -6152, -6921]]]
 hmul := by decide  
 g := ![![![![3, -4, 0, -8, -9]]]]
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

def I773N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-88993, 4748, 13036, -12014, -28563]] i)))

def SI773N0: IdealEqSpanCertificate' Table ![![-88993, 4748, 13036, -12014, -28563]] 
 ![![773, 0, 0, 0, 0], ![0, 773, 0, 0, 0], ![0, 0, 773, 0, 0], ![673, 676, 221, 1, 0], ![156, 459, 766, 0, 1]] where
  M :=![![![-88993, 4748, 13036, -12014, -28563], ![180448, -64390, 213, 25178, -29916], ![340040, 176775, -144662, 43010, 421800], ![-410460, 40349, 51149, -55687, -102150], ![257658, -6250, -41392, 34674, 94727]]]
  hmulB := by decide  
  f := ![![![16885, -4096, -1486, -480, 9897]], ![![-81096, 18872, 6761, 3014, -45348]], ![![374840, -89625, -32504, -11030, 217560]], ![![50769, -12644, -4659, -929, 31059]], ![![326910, -78484, -28513, -9244, 190781]]]
  g := ![![![16109, 27473, 31756, -12014, -28563], ![-15650, -4338, 22447, 25178, -29916], ![-122130, -287845, -430464, 43010, 421800], ![68567, 109407, 117212, -55687, -102150], ![-48972, -86579, -103836, 34674, 94727]]]
  hle1 := by decide   
  hle2 := by decide  


def P773P0 : CertificateIrreducibleZModOfList' 773 3 2 9 [168, 50, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [500, 18, 302], [123, 754, 471], [0, 1]]
 g := ![![[678, 722, 508], [311, 526], [495, 769, 424], [601, 623], [31, 763], [638, 184], [586, 584], [231, 83], [1]], ![[23, 726, 317, 411], [245, 596], [448, 691, 592, 702], [643, 365], [755, 328], [428, 287], [15, 557], [748, 10], [120, 156, 255, 72]], ![[242, 665, 767, 700], [253, 150], [609, 617, 435, 684], [192, 21], [178, 762], [444, 576], [666, 596], [708, 251], [549, 334, 548, 701]]]
 h' := ![![[500, 18, 302], [164, 422, 60], [324, 433, 619], [656, 351, 291], [19, 442, 520], [242, 467, 471], [711, 431, 187], [238, 582, 186], [605, 723, 623], [0, 1]], ![[123, 754, 471], [719, 663, 305], [328, 157, 736], [580, 405, 756], [622, 434, 697], [397, 246, 675], [612, 412, 610], [236, 656, 624], [427, 586, 118], [500, 18, 302]], ![[0, 1], [221, 461, 408], [601, 183, 191], [337, 17, 499], [30, 670, 329], [103, 60, 400], [232, 703, 749], [219, 308, 736], [11, 237, 32], [123, 754, 471]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [535, 192], []]
 b := ![[], [165, 351, 542], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI773N0 : CertifiedPrimeIdeal' SI773N0 773 where
  n := 3
  hpos := by decide
  P := [168, 50, 150, 1]
  hirr := P773P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2418790259, 2006526, 564521020, -3539275110, -5522047830]
  a := ![-169, -58, 56, -170, -510]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4198952653, 6374090472, 6484648070, -3539275110, -5522047830]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI773N0 : Ideal.IsPrime I773N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI773N0 B_one_repr
lemma NI773N0 : Nat.card (O ⧸ I773N0) = 461889917 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI773N0

def I773N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16885, -4096, -1486, -480, 9897]] i)))

def SI773N1: IdealEqSpanCertificate' Table ![![16885, -4096, -1486, -480, 9897]] 
 ![![773, 0, 0, 0, 0], ![0, 773, 0, 0, 0], ![463, 109, 1, 0, 0], ![287, 482, 0, 1, 0], ![452, 399, 0, 0, 1]] where
  M :=![![![16885, -4096, -1486, -480, 9897], ![-81096, 18872, 6761, 3014, -45348], ![374840, -89625, -32504, -11030, 217560], ![-137912, 32449, 11619, 5089, -77586], ![162994, -38654, -13968, -5178, 93553]]]
  hmulB := by decide  
  f := ![![![-88993, 4748, 13036, -12014, -28563]], ![![180448, -64390, 213, 25178, -29916]], ![![-27419, -6007, 7651, -3590, -20781]], ![![78945, -38335, 5039, 11167, -29391]], ![![41438, -30468, 7679, 6016, -32021]]]
  g := ![![![-4697, -4605, -1486, -480, 9897], ![21243, 20599, 6761, 3014, -45348], ![-103166, -100953, -32504, -11030, 217560], ![36340, 35278, 11619, 5089, -77586], ![-44204, -43141, -13968, -5178, 93553]]]
  hle1 := by decide   
  hle2 := by decide  


def P773P1 : CertificateIrreducibleZModOfList' 773 2 2 9 [304, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [729, 772], [0, 1]]
 g := ![![[51, 16], [692], [555, 691], [452], [121], [517], [179], [439], [729, 1]], ![[120, 757], [692], [298, 82], [452], [121], [517], [179], [439], [685, 772]]]
 h' := ![![[729, 772], [582, 769], [567, 534], [355, 73], [760, 35], [424, 762], [695, 434], [615, 233], [235, 86], [0, 1]], ![[0, 1], [758, 4], [261, 239], [235, 700], [766, 738], [135, 11], [151, 339], [412, 540], [316, 687], [729, 772]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [30, 423]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI773N1 : CertifiedPrimeIdeal' SI773N1 773 where
  n := 2
  hpos := by decide
  P := [304, 44, 1]
  hirr := P773P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4522, -480, -784, 6262, 9356]
  a := ![-14, -5, 5, -16, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7332, -8624, -784, 6262, 9356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI773N1 : Ideal.IsPrime I773N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI773N1 B_one_repr
lemma NI773N1 : Nat.card (O ⧸ I773N1) = 597529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI773N1
def MulI773N0 : IdealMulLeCertificate' Table 
  ![![-88993, 4748, 13036, -12014, -28563]] ![![16885, -4096, -1486, -480, 9897]]
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

def I787N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8919, -2740, -1182, 2546, 4457]] i)))

def SI787N0: IdealEqSpanCertificate' Table ![![-8919, -2740, -1182, 2546, 4457]] 
 ![![787, 0, 0, 0, 0], ![0, 787, 0, 0, 0], ![0, 0, 787, 0, 0], ![261, 583, 457, 1, 0], ![596, 254, 766, 0, 1]] where
  M :=![![![-8919, -2740, -1182, 2546, 4457], ![-25472, -7826, -3375, 7278, 12724], ![-72680, -22345, -9658, 20810, 36440], ![-8092, -2459, -1065, 2315, 4034], ![-6238, -1928, -834, 1798, 3153]]]
  hmulB := by decide  
  f := ![![![-27, 8, 0, -4, 11]], ![![-104, -20, 27, 6, -92]], ![![760, -55, -124, 110, 440]], ![![355, -44, -52, 67, 191]], ![![686, -54, -112, 106, 407]]]
  g := ![![![-4231, -3328, -5818, 2546, 4457], ![-12082, -9508, -16615, 7278, 12724], ![-34590, -27205, -47564, 20810, 36440], ![-3833, -3020, -5272, 2315, 4034], ![-2992, -2352, -4114, 1798, 3153]]]
  hle1 := by decide   
  hle2 := by decide  


def P787P0 : CertificateIrreducibleZModOfList' 787 3 2 9 [13, 25, 357, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [338, 716, 41], [92, 70, 746], [0, 1]]
 g := ![![[761, 562, 173], [483, 148, 395], [491, 464], [266, 263], [323, 72, 357], [290, 304], [568, 183], [74, 742], [1]], ![[747, 493, 379, 305], [640, 407, 564, 617], [38, 85], [547, 310], [189, 728, 439, 545], [24, 653], [530, 345], [175, 362], [298, 0, 3, 452]], ![[702, 278, 431, 336], [82, 698, 443, 212], [171, 402], [745, 606], [2, 604, 774, 198], [150, 267], [540, 265], [322, 253], [334, 29, 463, 335]]]
 h' := ![![[338, 716, 41], [17, 115, 685], [286, 757, 651], [130, 37, 150], [523, 431, 353], [347, 608, 688], [522, 245, 569], [781, 172, 354], [774, 762, 430], [0, 1]], ![[92, 70, 746], [489, 574, 723], [597, 403, 268], [218, 493, 212], [197, 194, 670], [581, 104, 684], [633, 264, 294], [523, 188, 352], [378, 488, 743], [338, 716, 41]], ![[0, 1], [447, 98, 166], [782, 414, 655], [128, 257, 425], [753, 162, 551], [230, 75, 202], [551, 278, 711], [445, 427, 81], [725, 324, 401], [92, 70, 746]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 538], []]
 b := ![[], [538, 418, 294], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI787N0 : CertifiedPrimeIdeal' SI787N0 787 where
  n := 3
  hpos := by decide
  P := [13, 25, 357, 1]
  hirr := P787P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-334235895, -17147465, -92784043, 568916711, 919624843]
  a := ![90, 27, -31, 89, 269]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-885537362, -718272300, -1225565884, 568916711, 919624843]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI787N0 : Ideal.IsPrime I787N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI787N0 B_one_repr
lemma NI787N0 : Nat.card (O ⧸ I787N0) = 487443403 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI787N0

def I787N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 31, 17, -92, -93]] i)))

def SI787N1: IdealEqSpanCertificate' Table ![![-79, 31, 17, -92, -93]] 
 ![![787, 0, 0, 0, 0], ![326, 1, 0, 0, 0], ![756, 0, 1, 0, 0], ![218, 0, 0, 1, 0], ![269, 0, 0, 0, 1]] where
  M :=![![![-79, 31, 17, -92, -93], ![376, -179, 122, -384, -732], ![4320, -130, -143, -1780, -1680], ![444, 104, 114, -999, -1098], ![966, -142, 6, -322, -455]]]
  hmulB := by decide  
  f := ![![![-17810611, -5475555, -2361913, 5084586, 8900289]], ![![-7442342, -2288013, -986948, 2124644, 3719070]], ![![-17293588, -5316610, -2293351, 4936988, 8641932]], ![![-4953954, -1523002, -656956, 1414257, 2475576]], ![![-6103623, -1876453, -809419, 1742468, 3050098]]]
  g := ![![![28, 31, 17, -92, -93], ![314, -179, 122, -384, -732], ![1264, -130, -143, -1780, -1680], ![500, 104, 114, -999, -1098], ![299, -142, 6, -322, -455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI787N1 : Nat.card (O ⧸ I787N1) = 787 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI787N1)

lemma isPrimeI787N1 : Ideal.IsPrime I787N1 := prime_ideal_of_norm_prime hp787.out _ NI787N1

def I787N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-893, -251, -109, 244, 400]] i)))

def SI787N2: IdealEqSpanCertificate' Table ![![-893, -251, -109, 244, 400]] 
 ![![787, 0, 0, 0, 0], ![613, 1, 0, 0, 0], ![417, 0, 1, 0, 0], ![732, 0, 0, 1, 0], ![748, 0, 0, 0, 1]] where
  M :=![![![-893, -251, -109, 244, 400], ![-2224, -794, -339, 686, 1328], ![-7880, -1905, -838, 2010, 2920], ![-420, -317, -131, 207, 580], ![-1008, -86, -44, 184, 63]]]
  hmulB := by decide  
  f := ![![![-4007, 479, -109, 1940, 2536]], ![![-3137, 373, -86, 1526, 1992]], ![![-2197, 264, -71, 1110, 1456]], ![![-3776, 451, -105, 1839, 2404]], ![![-3820, 456, -106, 1860, 2431]]]
  g := ![![![-355, -251, -109, 244, 400], ![-1105, -794, -339, 686, 1328], ![-2727, -1905, -838, 2010, 2920], ![-428, -317, -131, 207, 580], ![-142, -86, -44, 184, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI787N2 : Nat.card (O ⧸ I787N2) = 787 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI787N2)

lemma isPrimeI787N2 : Ideal.IsPrime I787N2 := prime_ideal_of_norm_prime hp787.out _ NI787N2
def MulI787N0 : IdealMulLeCertificate' Table 
  ![![-8919, -2740, -1182, 2546, 4457]] ![![-79, 31, 17, -92, -93]]
  ![![4007, -479, 109, -1940, -2536]] where
 M := ![![![4007, -479, 109, -1940, -2536]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI787N1 : IdealMulLeCertificate' Table 
  ![![4007, -479, 109, -1940, -2536]] ![![-893, -251, -109, 244, 400]]
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

def I797N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![213, -53, -15, -8, 103]] i)))

def SI797N0: IdealEqSpanCertificate' Table ![![213, -53, -15, -8, 103]] 
 ![![797, 0, 0, 0, 0], ![0, 797, 0, 0, 0], ![0, 0, 797, 0, 0], ![454, 530, 386, 1, 0], ![726, 296, 84, 0, 1]] where
  M :=![![![213, -53, -15, -8, 103], ![-856, 233, 66, 24, -508], ![4160, -1010, -323, -260, 2320], ![-1532, 344, 150, 25, -986], ![1870, -430, -162, -82, 1077]]]
  hmulB := by decide  
  f := ![![![87, 23, 9, -22, -37]], ![![208, 73, 30, -72, -116]], ![![640, 170, 101, -220, -400]], ![![498, 144, 74, -167, -292]], ![![224, 66, 30, -70, -119]]]
  g := ![![![-89, -33, -7, -8, 103], ![448, 173, 42, 24, -508], ![-1960, -690, -119, -260, 2320], ![882, 350, 92, 25, -986], ![-932, -346, -74, -82, 1077]]]
  hle1 := by decide   
  hle2 := by decide  


def P797P0 : CertificateIrreducibleZModOfList' 797 3 2 9 [518, 201, 564, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [137, 6, 441], [96, 790, 356], [0, 1]]
 g := ![![[349, 462, 348], [126, 356], [242, 326, 643], [141, 269, 670], [474, 686, 529], [659, 311], [153, 437], [530, 93], [1]], ![[580, 144, 700, 560], [208, 542], [779, 614, 190, 632], [230, 590, 667, 248], [639, 25, 495, 632], [322, 170], [400, 395], [573, 686], [602, 3, 251, 154]], ![[119, 598, 276, 461], [549, 313], [342, 36, 5, 682], [678, 755, 572, 78], [617, 133, 665, 557], [491, 155], [131, 737], [557, 484], [687, 332, 507, 643]]]
 h' := ![![[137, 6, 441], [607, 354, 82], [570, 573, 530], [286, 432, 588], [741, 350, 407], [222, 714, 23], [542, 631, 706], [160, 133, 247], [279, 596, 233], [0, 1]], ![[96, 790, 356], [145, 222, 125], [517, 417, 319], [404, 675, 695], [539, 338, 71], [564, 407, 695], [623, 240, 755], [154, 745, 337], [22, 96, 586], [137, 6, 441]], ![[0, 1], [32, 221, 590], [648, 604, 745], [426, 487, 311], [565, 109, 319], [532, 473, 79], [263, 723, 133], [261, 716, 213], [459, 105, 775], [96, 790, 356]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [588, 162], []]
 b := ![[], [511, 519, 390], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI797N0 : CertifiedPrimeIdeal' SI797N0 797 where
  n := 3
  hpos := by decide
  P := [518, 201, 564, 1]
  hirr := P797P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4830648, -1664109, 1222293, -4847290, -6352568]
  a := ![-37, -7, 14, -32, -110]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8553908, 5580627, 3018685, -4847290, -6352568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI797N0 : Ideal.IsPrime I797N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI797N0 B_one_repr
lemma NI797N0 : Nat.card (O ⧸ I797N0) = 506261573 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI797N0

def I797N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, -23, -9, 22, 37]] i)))

def SI797N1: IdealEqSpanCertificate' Table ![![-87, -23, -9, 22, 37]] 
 ![![797, 0, 0, 0, 0], ![0, 797, 0, 0, 0], ![741, 125, 1, 0, 0], ![700, 664, 0, 1, 0], ![731, 712, 0, 0, 1]] where
  M :=![![![-87, -23, -9, 22, 37], ![-208, -73, -30, 72, 116], ![-640, -170, -101, 220, 400], ![-128, -16, -6, 31, 46], ![-38, -16, -12, 26, 45]]]
  hmulB := by decide  
  f := ![![![-213, 53, 15, 8, -103]], ![![856, -233, -66, -24, 508]], ![![-69, 14, 4, 4, -19]], ![![528, -148, -42, -13, 334]], ![![567, -159, -45, -14, 358]]]
  g := ![![![-45, -50, -9, 22, 37], ![-142, -159, -30, 72, 116], ![-467, -525, -101, 220, 400], ![-64, -66, -6, 31, 46], ![-53, -60, -12, 26, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P797P1 : CertificateIrreducibleZModOfList' 797 2 2 9 [572, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [684, 796], [0, 1]]
 g := ![![[545, 294], [95], [34, 541], [782, 325], [322, 383], [367], [376], [383], [684, 1]], ![[0, 503], [95], [270, 256], [719, 472], [81, 414], [367], [376], [383], [571, 796]]]
 h' := ![![[684, 796], [240, 517], [477, 625], [610, 252], [720, 186], [207, 242], [617, 214], [761, 536], [79, 242], [0, 1]], ![[0, 1], [0, 280], [785, 172], [29, 545], [424, 611], [756, 555], [345, 583], [765, 261], [628, 555], [684, 796]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [611]]
 b := ![[], [723, 704]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI797N1 : CertifiedPrimeIdeal' SI797N1 797 where
  n := 2
  hpos := by decide
  P := [572, 113, 1]
  hirr := P797P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47136, -13338, -5314, 6390, 42972]
  a := ![28, -2, -10, 10, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-40026, -42896, -5314, 6390, 42972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI797N1 : Ideal.IsPrime I797N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI797N1 B_one_repr
lemma NI797N1 : Nat.card (O ⧸ I797N1) = 635209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI797N1
def MulI797N0 : IdealMulLeCertificate' Table 
  ![![213, -53, -15, -8, 103]] ![![-87, -23, -9, 22, 37]]
  ![![797, 0, 0, 0, 0]] where
 M := ![![![-797, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I809N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62731, -13982, -4014, 8626, 3075]] i)))

def SI809N0: IdealEqSpanCertificate' Table ![![62731, -13982, -4014, 8626, 3075]] 
 ![![809, 0, 0, 0, 0], ![0, 809, 0, 0, 0], ![0, 0, 809, 0, 0], ![115, 242, 456, 1, 0], ![757, 385, 523, 0, 1]] where
  M :=![![![62731, -13982, -4014, 8626, 3075], ![9904, 54362, -28159, 514, 91212], ![-727640, -39165, 144546, -97110, -358680], ![243148, -73251, -6283, 33709, -18666], ![-200378, 36918, 16592, -27450, -22253]]]
  hmulB := by decide  
  f := ![![![781797, 240318, 103664, -223176, -390621]], ![![2232264, 686320, 296049, -637306, -1115628]], ![![6375800, 1959575, 845304, -1819990, -3185160]], ![![4373527, 1344263, 579873, -1248467, -2185029]], ![![5916359, 1818517, 784449, -1688898, -2955908]]]
  g := ![![![-4026, -4061, -6855, 8626, 3075], ![-85410, -43494, -59291, 514, 91212], ![348530, 199695, 286794, -97110, -358680], ![12975, -1291, -6941, 33709, -18666], ![24477, 18847, 29879, -27450, -22253]]]
  hle1 := by decide   
  hle2 := by decide  


def P809P0 : CertificateIrreducibleZModOfList' 809 3 2 9 [102, 481, 430, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [360, 75, 447], [19, 733, 362], [0, 1]]
 g := ![![[282, 441, 338], [299, 679], [171, 771], [530, 94, 95], [90, 805], [106, 72, 719], [707, 723], [163, 448], [1]], ![[371, 76, 506, 495], [369, 317], [572, 222], [408, 659, 739, 680], [119, 411], [580, 477, 72, 42], [401, 795], [496, 596], [337, 713, 292, 214]], ![[61, 556, 116, 327], [568, 173], [100, 360], [592, 352, 39, 654], [657, 505], [124, 555, 7, 438], [755, 784], [333, 266], [187, 664, 559, 595]]]
 h' := ![![[360, 75, 447], [100, 806, 108], [580, 584, 413], [143, 426, 734], [181, 600, 293], [514, 664, 173], [94, 581, 106], [250, 722, 334], [707, 328, 379], [0, 1]], ![[19, 733, 362], [629, 792, 159], [513, 430, 713], [406, 704, 344], [221, 500, 805], [143, 125, 510], [658, 213, 52], [588, 800, 447], [574, 191, 507], [360, 75, 447]], ![[0, 1], [361, 20, 542], [802, 604, 492], [61, 488, 540], [84, 518, 520], [201, 20, 126], [209, 15, 651], [749, 96, 28], [729, 290, 732], [19, 733, 362]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [790, 180], []]
 b := ![[], [520, 472, 662], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI809N0 : CertifiedPrimeIdeal' SI809N0 809 where
  n := 3
  hpos := by decide
  P := [102, 481, 430, 1]
  hirr := P809P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2808634, 398863, -301859, 2660068, 3424941]
  a := ![10, 7, -2, 13, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3586399, -2425142, -3713890, 2660068, 3424941]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI809N0 : Ideal.IsPrime I809N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI809N0 B_one_repr
lemma NI809N0 : Nat.card (O ⧸ I809N0) = 529475129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI809N0

def I809N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-781797, -240318, -103664, 223176, 390621]] i)))

def SI809N1: IdealEqSpanCertificate' Table ![![-781797, -240318, -103664, 223176, 390621]] 
 ![![809, 0, 0, 0, 0], ![0, 809, 0, 0, 0], ![669, 294, 1, 0, 0], ![71, 161, 0, 1, 0], ![753, 776, 0, 0, 1]] where
  M :=![![![-781797, -240318, -103664, 223176, 390621], ![-2232264, -686320, -296049, 637306, 1115628], ![-6375800, -1959575, -845304, 1819990, 3185160], ![-704000, -216557, -93415, 201071, 352110], ![-549062, -168602, -72736, 156670, 274015]]]
  hmulB := by decide  
  f := ![![![-62731, 13982, 4014, -8626, -3075]], ![![-9904, -54362, 28159, -514, -91212]], ![![-54575, -8145, 13374, -7200, -35247]], ![![-7777, -9501, 5964, -901, -18399]], ![![-67641, -39176, 30726, -8488, -90326]]]
  g := ![![![-298410, -381726, -103664, 223176, 390621], ![-852277, -1090212, -296049, 637306, 1115628], ![-2433266, -3112661, -845304, 1819990, 3185160], ![-269004, -344082, -93415, 201071, 352110], ![-209327, -267792, -72736, 156670, 274015]]]
  hle1 := by decide   
  hle2 := by decide  


def P809P1 : CertificateIrreducibleZModOfList' 809 2 2 9 [230, 377, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [432, 808], [0, 1]]
 g := ![![[378, 707], [487], [158], [309, 729], [152], [5, 13], [322], [615], [432, 1]], ![[0, 102], [487], [158], [536, 80], [152], [767, 796], [322], [615], [55, 808]]]
 h' := ![![[432, 808], [545, 495], [387, 773], [122, 675], [421, 27], [468, 31], [114, 57], [700, 122], [147, 324], [0, 1]], ![[0, 1], [0, 314], [206, 36], [482, 134], [759, 782], [107, 778], [468, 752], [10, 687], [158, 485], [432, 808]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168]]
 b := ![[], [463, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI809N1 : CertifiedPrimeIdeal' SI809N1 809 where
  n := 2
  hpos := by decide
  P := [230, 377, 1]
  hirr := P809P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1284, -457, -403, 390, 2837]
  a := ![2, -1, -1, 1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2340, -2653, -403, 390, 2837]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI809N1 : Ideal.IsPrime I809N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI809N1 B_one_repr
lemma NI809N1 : Nat.card (O ⧸ I809N1) = 654481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI809N1
def MulI809N0 : IdealMulLeCertificate' Table 
  ![![62731, -13982, -4014, 8626, 3075]] ![![-781797, -240318, -103664, 223176, 390621]]
  ![![809, 0, 0, 0, 0]] where
 M := ![![![-809, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I811N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![189, 40, 18, -46, -60]] i)))

def SI811N0: IdealEqSpanCertificate' Table ![![189, 40, 18, -46, -60]] 
 ![![811, 0, 0, 0, 0], ![0, 811, 0, 0, 0], ![418, 494, 1, 0, 0], ![599, 212, 0, 1, 0], ![55, 796, 0, 0, 1]] where
  M :=![![![189, 40, 18, -46, -60], ![296, 173, 72, -124, -312], ![2000, 220, 109, -400, -240], ![-116, 104, 42, -37, -228], ![424, -40, -12, -44, 121]]]
  hmulB := by decide  
  f := ![![![351, 16, -66, 38, 156]], ![![-1096, 215, 96, -196, -168]], ![![-486, 138, 25, -100, -24]], ![![-25, 68, -24, -23, 72]], ![![-1053, 212, 90, -190, -155]]]
  g := ![![![29, 60, 18, -46, -60], ![76, 295, 72, -124, -312], ![258, 274, 109, -400, -240], ![21, 208, 42, -37, -228], ![31, -100, -12, -44, 121]]]
  hle1 := by decide   
  hle2 := by decide  


def P811P0 : CertificateIrreducibleZModOfList' 811 2 2 9 [413, 577, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [234, 810], [0, 1]]
 g := ![![[131, 703], [774, 371], [779], [380, 34], [605], [398, 19], [438], [36], [234, 1]], ![[0, 108], [0, 440], [779], [226, 777], [605], [789, 792], [438], [36], [468, 810]]]
 h' := ![![[234, 810], [683, 56], [575, 306], [394, 49], [502, 70], [259, 184], [468, 571], [388, 340], [678, 6], [0, 1]], ![[0, 1], [0, 755], [0, 505], [506, 762], [662, 741], [332, 627], [267, 240], [470, 471], [460, 805], [234, 810]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [246]]
 b := ![[], [207, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI811N0 : CertifiedPrimeIdeal' SI811N0 811 where
  n := 2
  hpos := by decide
  P := [413, 577, 1]
  hirr := P811P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10001, -1793, -22209, 101590, 217530]
  a := ![51, 13, -17, 50, 150]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78327, -226537, -22209, 101590, 217530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI811N0 : Ideal.IsPrime I811N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI811N0 B_one_repr
lemma NI811N0 : Nat.card (O ⧸ I811N0) = 657721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI811N0

def I811N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3379, -298, 340, -2946, -3766]] i)))

def SI811N1: IdealEqSpanCertificate' Table ![![3379, -298, 340, -2946, -3766]] 
 ![![811, 0, 0, 0, 0], ![0, 811, 0, 0, 0], ![213, 469, 1, 0, 0], ![310, 166, 0, 1, 0], ![230, 522, 0, 0, 1]] where
  M :=![![![3379, -298, 340, -2946, -3766], ![18344, -1633, 1828, -15916, -20288], ![98640, -8720, 9911, -85960, -109840], ![44316, -3944, 4422, -38483, -49072], ![18900, -1664, 1908, -16512, -21129]]]
  hmulB := by decide  
  f := ![![![601, 342, -224, 34, 650]], ![![-5064, 165, 924, -804, -2192]], ![![-2753, 181, 475, -454, -1098]], ![![-802, 166, 102, -151, -196]], ![![-3090, 202, 532, -508, -1229]]]
  g := ![![![2109, 2830, 340, -2946, -3766], ![11380, 15257, 1828, -15916, -20288], ![61527, 82551, 9911, -85960, -109840], ![27520, 36900, 4422, -38483, -49072], ![11826, 15874, 1908, -16512, -21129]]]
  hle1 := by decide   
  hle2 := by decide  


def P811P1 : CertificateIrreducibleZModOfList' 811 2 2 9 [82, 474, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [337, 810], [0, 1]]
 g := ![![[797, 703], [126, 167], [407], [301, 306], [652], [603, 176], [569], [376], [337, 1]], ![[85, 108], [446, 644], [407], [426, 505], [652], [712, 635], [569], [376], [674, 810]]]
 h' := ![![[337, 810], [211, 755], [509, 336], [459, 78], [687, 601], [25, 370], [560, 642], [342, 68], [751, 758], [0, 1]], ![[0, 1], [803, 56], [201, 475], [793, 733], [474, 210], [632, 441], [377, 169], [550, 743], [732, 53], [337, 810]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [224, 415]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI811N1 : CertifiedPrimeIdeal' SI811N1 811 where
  n := 2
  hpos := by decide
  P := [82, 474, 1]
  hirr := P811P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11370, -518, -6524, 22083, 57808]
  a := ![24, 5, -9, 21, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23108, -37956, -6524, 22083, 57808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI811N1 : Ideal.IsPrime I811N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI811N1 B_one_repr
lemma NI811N1 : Nat.card (O ⧸ I811N1) = 657721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI811N1

def I811N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-979, 302, 22, -136, 86]] i)))

def SI811N2: IdealEqSpanCertificate' Table ![![-979, 302, 22, -136, 86]] 
 ![![811, 0, 0, 0, 0], ![659, 1, 0, 0, 0], ![415, 0, 1, 0, 0], ![707, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-979, 302, 22, -136, 86], ![-1232, -919, 660, -152, -1976], ![15200, -60, -2591, 2040, 6080], ![-3432, 1496, -136, -483, 1004], ![3276, -832, -160, 452, -3]]]
  hmulB := by decide  
  f := ![![![-24625, 2662, -2114, 20224, 24638]], ![![-20153, 2175, -1734, 16568, 20198]], ![![-13485, 1450, -1161, 11080, 13510]], ![![-21825, 2350, -1882, 17957, 21906]], ![![-668, 72, -56, 540, 653]]]
  g := ![![![-141, 302, 22, -136, 86], ![579, -919, 660, -152, -1976], ![-505, -60, -2591, 2040, 6080], ![-749, 1496, -136, -483, 1004], ![368, -832, -160, 452, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI811N2 : Nat.card (O ⧸ I811N2) = 811 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI811N2)

lemma isPrimeI811N2 : Ideal.IsPrime I811N2 := prime_ideal_of_norm_prime hp811.out _ NI811N2
def MulI811N0 : IdealMulLeCertificate' Table 
  ![![189, 40, 18, -46, -60]] ![![3379, -298, 340, -2946, -3766]]
  ![![-24625, 2662, -2114, 20224, 24638]] where
 M := ![![![-24625, 2662, -2114, 20224, 24638]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI811N1 : IdealMulLeCertificate' Table 
  ![![-24625, 2662, -2114, 20224, 24638]] ![![-979, 302, 22, -136, 86]]
  ![![811, 0, 0, 0, 0]] where
 M := ![![![811, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC811 : ContainsPrimesAboveP 811 ![I811N0, I811N1, I811N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI811N0
    exact isPrimeI811N1
    exact isPrimeI811N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 811 (by decide) (𝕀 ⊙ MulI811N0 ⊙ MulI811N1)
instance hp821 : Fact (Nat.Prime 821) := {out := by norm_num}

def I821N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7142397, 2189098, 944500, -2035986, -3556136]] i)))

def SI821N0: IdealEqSpanCertificate' Table ![![7142397, 2189098, 944500, -2035986, -3556136]] 
 ![![821, 0, 0, 0, 0], ![0, 821, 0, 0, 0], ![0, 0, 821, 0, 0], ![0, 0, 0, 821, 0], ![133, 302, 223, 712, 1]] where
  M :=![![![7142397, 2189098, 944500, -2035986, -3556136], ![20305144, 6272775, 2704934, -5811216, -10207288], ![58413440, 17811310, 7687919, -16610100, -28905440], ![6327740, 1997362, 860140, -1831601, -3266300], ![5120432, 1511212, 653884, -1433020, -2435655]]]
  hmulB := by decide  
  f := ![![![25249, 982, -4832, 3374, 11840]], ![![-81224, 16303, 6074, -11144, -6872]], ![![10400, -68870, 31719, 2420, -106240]], ![![126572, -1634, -21032, 17011, 48836]], ![![86721, -13974, -8155, 11846, 12841]]]
  g := ![![![584785, 1310770, 967068, 3081526, -3556136], ![1678288, 3762331, 2775798, 8845040, -10207288], ![4753760, 10654390, 7860659, 25047580, -28905440], ![536840, 1203922, 888240, 2830419, -3266300], ![400807, 897782, 662369, 2110540, -2435655]]]
  hle1 := by decide   
  hle2 := by decide  


def P821P0 : CertificateIrreducibleZModOfList' 821 4 2 9 [60, 49, 578, 464, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [332, 213, 341, 412], [226, 338, 650, 132], [620, 269, 651, 277], [0, 1]]
 g := ![![[706, 375, 563, 7], [466, 297, 289], [353, 627, 359, 361], [428, 347, 35], [764, 707, 43, 361], [741, 7, 799, 130], [397, 713, 252], [437, 357, 1], []], ![[393, 13, 578, 776, 536, 725], [693, 5, 617], [490, 199, 385, 650, 305, 166], [305, 160, 205], [729, 290, 160, 779, 797, 172], [683, 524, 501, 45, 235, 204], [807, 219, 463], [582, 145, 294], [334, 640, 757, 333, 120, 106]], ![[537, 679, 17, 429, 190, 475], [806, 602, 94], [171, 28, 529, 739, 169, 530], [216, 683, 779], [490, 103, 461, 400, 590, 103], [77, 81, 605, 568, 252, 335], [535, 566, 169], [585, 63, 29], [360, 212, 230, 702, 444, 347]], ![[416, 795, 112, 226, 335, 772], [490, 729, 786], [744, 639, 94, 14, 768, 383], [135, 795, 28], [356, 48, 676, 130, 391, 23], [389, 411, 286, 242, 351, 664], [627, 720, 409], [429, 87, 204], [148, 587, 262, 261, 349, 706]]]
 h' := ![![[332, 213, 341, 412], [417, 125, 164, 735], [166, 244, 548, 17], [205, 256, 118, 19], [136, 58, 180, 395], [695, 572, 585, 19], [230, 277, 779, 240], [52, 680, 791, 516], [0, 0, 0, 1], [0, 1]], ![[226, 338, 650, 132], [298, 413, 441, 103], [735, 18, 356, 198], [222, 279, 573, 404], [679, 352, 156, 558], [261, 628, 204, 773], [416, 382, 685, 523], [268, 606, 151, 655], [420, 608, 510, 777], [332, 213, 341, 412]], ![[620, 269, 651, 277], [0, 684, 169, 45], [640, 202, 622, 549], [276, 444, 161, 457], [10, 630, 432, 40], [496, 730, 640, 735], [773, 66, 581, 453], [328, 436, 259, 13], [483, 759, 489, 745], [226, 338, 650, 132]], ![[0, 1], [304, 420, 47, 759], [721, 357, 116, 57], [414, 663, 790, 762], [628, 602, 53, 649], [151, 533, 213, 115], [704, 96, 418, 426], [148, 741, 441, 458], [61, 275, 643, 119], [620, 269, 651, 277]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [82, 571, 818], []]
 b := ![[], [], [396, 468, 595, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI821N0 : CertifiedPrimeIdeal' SI821N0 821 where
  n := 4
  hpos := by decide
  P := [60, 49, 578, 464, 1]
  hirr := P821P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100591232, 8782049, -10034515, 88286852, 113058300]
  a := ![6, 3, -2, 7, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18437692, -41577131, -30721115, -97940588, 113058300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI821N0 : Ideal.IsPrime I821N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI821N0 B_one_repr
lemma NI821N0 : Nat.card (O ⧸ I821N0) = 454331269681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI821N0

def I821N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25249, -982, 4832, -3374, -11840]] i)))

def SI821N1: IdealEqSpanCertificate' Table ![![-25249, -982, 4832, -3374, -11840]] 
 ![![821, 0, 0, 0, 0], ![491, 1, 0, 0, 0], ![293, 0, 1, 0, 0], ![803, 0, 0, 1, 0], ![135, 0, 0, 0, 1]] where
  M :=![![![-25249, -982, 4832, -3374, -11840], ![81224, -16303, -6074, 11144, 6872], ![-10400, 68870, -31719, -2420, 106240], ![-126572, 1634, 21032, -17011, -48836], ![68992, 5348, -14500, 9180, 36627]]]
  hmulB := by decide  
  f := ![![![-7142397, -2189098, -944500, 2035986, 3556136]], ![![-4296251, -1316833, -568154, 1224702, 2139184]], ![![-2620141, -802944, -346439, 746838, 1304328]], ![![-6993511, -2143536, -924840, 1993579, 3482148]], ![![-1180687, -361802, -156104, 336530, 587715]]]
  g := ![![![4079, -982, 4832, -3374, -11840], ![-13, -16303, -6074, 11144, 6872], ![-44983, 68870, -31719, -2420, 106240], ![16031, 1634, 21032, -17011, -48836], ![-12941, 5348, -14500, 9180, 36627]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI821N1 : Nat.card (O ⧸ I821N1) = 821 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI821N1)

lemma isPrimeI821N1 : Ideal.IsPrime I821N1 := prime_ideal_of_norm_prime hp821.out _ NI821N1
def MulI821N0 : IdealMulLeCertificate' Table 
  ![![7142397, 2189098, 944500, -2035986, -3556136]] ![![-25249, -982, 4832, -3374, -11840]]
  ![![821, 0, 0, 0, 0]] where
 M := ![![![-821, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC821 : ContainsPrimesAboveP 821 ![I821N0, I821N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI821N0
    exact isPrimeI821N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 821 (by decide) (𝕀 ⊙ MulI821N0)
instance hp823 : Fact (Nat.Prime 823) := {out := by norm_num}

def I823N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![823, 0, 0, 0, 0]] i)))

def SI823N0: IdealEqSpanCertificate' Table ![![823, 0, 0, 0, 0]] 
 ![![823, 0, 0, 0, 0], ![0, 823, 0, 0, 0], ![0, 0, 823, 0, 0], ![0, 0, 0, 823, 0], ![0, 0, 0, 0, 823]] where
  M :=![![![823, 0, 0, 0, 0], ![0, 823, 0, 0, 0], ![0, 0, 823, 0, 0], ![0, 0, 0, 823, 0], ![0, 0, 0, 0, 823]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P823P0 : CertificateIrreducibleZModOfList' 823 5 2 9 [317, 446, 149, 773, 180, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 706, 398, 575, 717], [247, 313, 745, 109, 218], [765, 9, 202, 312, 690], [451, 617, 301, 650, 21], [0, 1]]
 g := ![![[405, 624, 7, 792, 264], [251, 610, 352, 474, 282], [337, 817, 652, 22, 356], [201, 701, 773, 208], [23, 4, 662, 745, 784], [735, 555, 642, 606, 540], [442, 279, 132, 336], [643, 1], []], ![[274, 213, 162, 193, 771, 598, 723, 746], [172, 532, 360, 339, 711, 367, 109, 401], [363, 677, 253, 117, 654, 372, 287, 29], [596, 311, 144, 591], [489, 274, 376, 811, 15, 457, 197, 600], [661, 45, 133, 600, 218, 314, 428, 243], [546, 134, 810, 473], [129, 286, 354, 85], [586, 257, 157, 62, 652, 117, 60, 688]], ![[618, 658, 698, 443, 654, 634, 62, 220], [26, 82, 510, 24, 103, 53, 456, 468], [361, 373, 315, 495, 218, 334, 502, 168], [146, 745, 742, 42], [477, 237, 14, 662, 467, 473, 278, 240], [249, 89, 131, 407, 677, 585, 274, 517], [368, 372, 102, 782], [270, 505, 516, 668], [31, 596, 693, 35, 503, 42, 163, 308]], ![[673, 409, 438, 96, 185, 738, 520, 213], [286, 556, 648, 200, 380, 149, 389, 605], [607, 485, 68, 536, 473, 625, 474, 665], [339, 221, 71, 219], [539, 396, 80, 302, 213, 271, 60, 111], [139, 224, 236, 738, 564, 742, 735, 354], [138, 361, 519, 251], [581, 322, 514, 473], [821, 557, 473, 15, 26, 516, 623, 320]], ![[6, 212, 592, 9, 711, 19, 736, 630], [493, 726, 486, 235, 615, 721, 180, 123], [357, 818, 771, 324, 52, 109, 721, 303], [300, 331, 544, 332], [98, 152, 128, 156, 348, 24, 612, 517], [341, 190, 723, 371, 187, 203, 294, 359], [459, 403, 637, 97], [462, 181, 351, 35], [326, 118, 23, 30, 208, 588, 333, 208]]]
 h' := ![![[3, 706, 398, 575, 717], [264, 425, 699, 567, 330], [161, 635, 816, 62, 453], [765, 689, 39, 288, 97], [116, 808, 354, 156, 410], [737, 762, 389, 744, 795], [255, 477, 264, 732, 367], [273, 132, 38, 727, 353], [0, 0, 0, 1], [0, 1]], ![[247, 313, 745, 109, 218], [312, 807, 633, 452, 116], [54, 530, 638, 276, 47], [524, 725, 739, 97, 462], [502, 344, 41, 71, 159], [749, 546, 769, 751, 323], [592, 393, 703, 404, 294], [294, 704, 623, 165, 36], [263, 499, 754, 373, 438], [3, 706, 398, 575, 717]], ![[765, 9, 202, 312, 690], [776, 784, 420, 269, 134], [36, 793, 674, 699, 177], [554, 21, 47, 589, 801], [724, 648, 670, 790, 373], [765, 157, 820, 494, 501], [422, 90, 13, 489, 203], [414, 629, 295, 24, 157], [142, 590, 712, 522, 390], [247, 313, 745, 109, 218]], ![[451, 617, 301, 650, 21], [671, 114, 162, 486, 429], [711, 252, 296, 778, 80], [787, 12, 24, 632, 337], [577, 114, 514, 648, 515], [476, 329, 548, 237, 779], [365, 150, 289, 633, 79], [127, 593, 475, 182, 476], [573, 743, 177, 801, 36], [765, 9, 202, 312, 690]], ![[0, 1], [552, 339, 555, 695, 637], [523, 259, 45, 654, 66], [626, 199, 797, 40, 772], [540, 555, 67, 804, 189], [348, 675, 766, 243, 71], [4, 536, 377, 211, 703], [314, 411, 215, 548, 624], [158, 637, 3, 772, 782], [451, 617, 301, 650, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [298, 703, 675, 400], [], [], []]
 b := ![[], [60, 91, 32, 720, 128], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI823N0 : CertifiedPrimeIdeal' SI823N0 823 where
  n := 5
  hpos := by decide
  P := [317, 446, 149, 773, 180, 1]
  hirr := P823P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16061633280130274, -1335292975651794, 1720496910473365, -14480690681274344, -18855629127695656]
  a := ![-115, -39, 38, -140, -352]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19515957813038, -1622470201278, 2090518724755, -17595006903128, -22910849486872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI823N0 : Ideal.IsPrime I823N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI823N0 B_one_repr
lemma NI823N0 : Nat.card (O ⧸ I823N0) = 377571474600343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI823N0

def PBC823 : ContainsPrimesAboveP 823 ![I823N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI823N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![823, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 823 (by decide) 𝕀

instance hp827 : Fact (Nat.Prime 827) := {out := by norm_num}

def I827N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![391, -253, 55, 50, -231]] i)))

def SI827N0: IdealEqSpanCertificate' Table ![![391, -253, 55, 50, -231]] 
 ![![827, 0, 0, 0, 0], ![0, 827, 0, 0, 0], ![0, 0, 827, 0, 0], ![787, 431, 120, 1, 0], ![430, 703, 194, 0, 1]] where
  M :=![![![391, -253, 55, 50, -231], ![2048, 485, -584, 288, 1524], ![-11040, 940, 1433, -1640, -2640], ![432, -1058, 450, 105, -1674], ![-1134, 646, -126, -218, 731]]]
  hmulB := by decide  
  f := ![![![-5389, -1659, -715, 1536, 2691]], ![![-15384, -4737, -2040, 4376, 7668]], ![![-43840, -13540, -5821, 12440, 21840]], ![![-19513, -6014, -2589, 5549, 9729]], ![![-26168, -8067, -3472, 7438, 13043]]]
  g := ![![![73, 170, 47, 50, -231], ![-1064, -1445, -400, 288, 1524], ![2920, 3100, 859, -1640, -2640], ![771, 1367, 378, 105, -1674], ![-174, -507, -140, -218, 731]]]
  hle1 := by decide   
  hle2 := by decide  


def P827P0 : CertificateIrreducibleZModOfList' 827 3 2 9 [209, 800, 402, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [605, 690, 233], [647, 136, 594], [0, 1]]
 g := ![![[650, 622, 790], [713, 116, 675], [206, 461], [559, 667, 489], [416, 312, 628], [511, 422, 428], [652, 34], [798, 339], [1]], ![[548, 336, 177, 316], [41, 388, 250, 579], [343, 798], [424, 462, 126, 16], [338, 789, 55, 134], [261, 654, 714, 731], [327, 281], [621, 209], [701, 546, 651, 372]], ![[26, 496, 781, 89], [395, 45, 696, 691], [204, 27], [721, 748, 171, 678], [604, 706, 627, 688], [742, 502, 334, 22], [449, 81], [617, 100], [628, 71, 228, 455]]]
 h' := ![![[605, 690, 233], [670, 462, 160], [506, 767, 205], [603, 43, 561], [718, 3, 759], [711, 347, 481], [185, 649, 533], [122, 607, 193], [618, 27, 425], [0, 1]], ![[647, 136, 594], [423, 584, 394], [634, 696, 668], [445, 818, 307], [543, 104, 548], [581, 7, 715], [109, 27, 415], [247, 86, 625], [32, 732, 412], [605, 690, 233]], ![[0, 1], [469, 608, 273], [34, 191, 781], [506, 793, 786], [254, 720, 347], [760, 473, 458], [106, 151, 706], [540, 134, 9], [245, 68, 817], [647, 136, 594]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [273, 313], []]
 b := ![[], [108, 470, 311], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI827N0 : CertifiedPrimeIdeal' SI827N0 827 where
  n := 3
  hpos := by decide
  P := [209, 800, 402, 1]
  hirr := P827P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22150645, -1956274, 2414302, -19204420, -24292110]
  a := ![-32, -11, 11, -40, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![30933055, 30655988, 8488046, -19204420, -24292110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI827N0 : Ideal.IsPrime I827N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI827N0 B_one_repr
lemma NI827N0 : Nat.card (O ⧸ I827N0) = 565609283 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI827N0

def I827N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5389, 1659, 715, -1536, -2691]] i)))

def SI827N1: IdealEqSpanCertificate' Table ![![5389, 1659, 715, -1536, -2691]] 
 ![![827, 0, 0, 0, 0], ![0, 827, 0, 0, 0], ![825, 454, 1, 0, 0], ![587, 808, 0, 1, 0], ![766, 712, 0, 0, 1]] where
  M :=![![![5389, 1659, 715, -1536, -2691], ![15384, 4737, 2040, -4376, -7668], ![43840, 13540, 5821, -12440, -21840], ![4804, 1498, 638, -1335, -2358], ![3754, 1168, 500, -1058, -1867]]]
  hmulB := by decide  
  f := ![![![-391, 253, -55, -50, 231]], ![![-2048, -485, 584, -288, -1524]], ![![-1501, -15, 264, -206, -603]], ![![-2279, -293, 531, -317, -1323]], ![![-2124, -184, 452, -294, -1099]]]
  g := ![![![2876, 3427, 715, -1536, -2691], ![8192, 9763, 2040, -4376, -7668], ![23305, 27778, 5821, -12440, -21840], ![2501, 2986, 638, -1335, -2358], ![1986, 2368, 500, -1058, -1867]]]
  hle1 := by decide   
  hle2 := by decide  


def P827P1 : CertificateIrreducibleZModOfList' 827 2 2 9 [145, 250, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [577, 826], [0, 1]]
 g := ![![[458, 154], [415, 469], [705], [817, 9], [121, 219], [569, 814], [124], [563], [577, 1]], ![[0, 673], [599, 358], [705], [221, 818], [780, 608], [511, 13], [124], [563], [327, 826]]]
 h' := ![![[577, 826], [196, 669], [589, 36], [623, 626], [649, 3], [195, 410], [521, 76], [261, 557], [689, 330], [0, 1]], ![[0, 1], [0, 158], [686, 791], [426, 201], [726, 824], [243, 417], [542, 751], [774, 270], [62, 497], [577, 826]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [575]]
 b := ![[], [790, 701]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI827N1 : CertifiedPrimeIdeal' SI827N1 827 where
  n := 2
  hpos := by decide
  P := [145, 250, 1]
  hirr := P827P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21512, 5864, -5096, 35076, 52536]
  a := ![23, 12, -8, 34, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-68500, -76696, -5096, 35076, 52536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI827N1 : Ideal.IsPrime I827N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI827N1 B_one_repr
lemma NI827N1 : Nat.card (O ⧸ I827N1) = 683929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI827N1
def MulI827N0 : IdealMulLeCertificate' Table 
  ![![391, -253, 55, 50, -231]] ![![5389, 1659, 715, -1536, -2691]]
  ![![827, 0, 0, 0, 0]] where
 M := ![![![-827, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1271I15_primes (p : ℕ) :
  p ∈ Set.range ![769, 773, 787, 797, 809, 811, 821, 823, 827] ↔ Nat.Prime p ∧ 761 < p ∧ p ≤ 827 := by
  rw [← List.mem_ofFn']
  convert primes_range 761 827 (by omega)

def PB1271I15 : PrimesBelowBoundCertificateInterval O 761 827 1271 where
  m := 9
  g := ![3, 2, 3, 2, 2, 3, 2, 1, 2]
  P := ![769, 773, 787, 797, 809, 811, 821, 823, 827]
  hP := PB1271I15_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I769N0, I769N1, I769N2]
    · exact ![I773N0, I773N1]
    · exact ![I787N0, I787N1, I787N2]
    · exact ![I797N0, I797N1]
    · exact ![I809N0, I809N1]
    · exact ![I811N0, I811N1, I811N2]
    · exact ![I821N0, I821N1]
    · exact ![I823N0]
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
    · exact ![454756609, 769, 769]
    · exact ![461889917, 597529]
    · exact ![487443403, 787, 787]
    · exact ![506261573, 635209]
    · exact ![529475129, 654481]
    · exact ![657721, 657721, 811]
    · exact ![454331269681, 821]
    · exact ![377571474600343]
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
    · dsimp ; intro j
      fin_cases j
      exact NI811N0
      exact NI811N1
      exact NI811N2
    · dsimp ; intro j
      fin_cases j
      exact NI821N0
      exact NI821N1
    · dsimp ; intro j
      fin_cases j
      exact NI823N0
    · dsimp ; intro j
      fin_cases j
      exact NI827N0
      exact NI827N1
  β := ![I769N1, I769N2, I787N1, I787N2, I811N2, I821N1]
  Il := ![[I769N1, I769N2], [], [I787N1, I787N2], [], [], [I811N2], [I821N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
