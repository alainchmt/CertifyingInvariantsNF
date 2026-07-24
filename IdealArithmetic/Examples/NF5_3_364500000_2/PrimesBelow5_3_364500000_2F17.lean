
import IdealArithmetic.Examples.NF5_3_364500000_2.RI5_3_364500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp887 : Fact (Nat.Prime 887) := {out := by norm_num}

def I887N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![70631, 21569, -32554, -422, 6000]] i)))

def SI887N0: IdealEqSpanCertificate' Table ![![70631, 21569, -32554, -422, 6000]] 
 ![![887, 0, 0, 0, 0], ![0, 887, 0, 0, 0], ![0, 0, 887, 0, 0], ![0, 0, 0, 887, 0], ![409, 109, 873, 193, 1]] where
  M :=![![![70631, 21569, -32554, -422, 6000], ![-144000, -28767, 67982, -17108, -1688], ![20256, -45833, -15035, 61230, -34216], ![482592, 266412, -209486, -143345, 123304], ![-657696, -351015, 286674, 181034, -159609]]]
  hmulB := by decide  
  f := ![![![11953, 515, -3020, -346, 824]], ![![-19776, -823, 5018, 552, -1384]], ![![16608, 785, -4143, -518, 1104]], ![![-3360, 54, 1002, -3, -344]], ![![18719, 922, -4641, -603, 1223]]]
  g := ![![![-2687, -713, -5942, -1306, 6000], ![616, 175, 1738, 348, -1688], ![15800, 4153, 33659, 7514, -34216], ![-56312, -14852, -121594, -26991, 123304], ![72855, 19218, 157413, 34933, -159609]]]
  hle1 := by decide   
  hle2 := by decide  


def P887P0 : CertificateIrreducibleZModOfList' 887 4 2 9 [884, 867, 87, 729, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [771, 365, 35, 806], [399, 650, 772, 246], [762, 758, 80, 722], [0, 1]]
 g := ![![[257, 302, 401, 692], [745, 267, 345, 707], [684, 789, 862, 504], [854, 663, 387], [870, 826, 713, 381], [649, 539, 520, 857], [698, 437, 837, 42], [41, 158, 1], []], ![[96, 716, 20, 394, 519, 587], [103, 369, 669, 788, 687, 15], [431, 879, 204, 50, 235, 838], [818, 313, 288], [18, 363, 70, 657, 758, 211], [875, 861, 678, 607, 557, 349], [263, 93, 514, 438, 793, 755], [203, 738, 387], [227, 492, 377, 585, 770, 759]], ![[377, 161, 115, 850, 880, 419], [800, 258, 2, 635, 539, 360], [621, 792, 669, 803, 470, 720], [281, 254, 156], [632, 520, 359, 124, 694, 442], [275, 106, 348, 283, 533, 640], [505, 497, 827, 540, 750, 10], [423, 593, 338], [820, 814, 418, 388, 118, 415]], ![[849, 473, 624, 831, 305, 84], [576, 808, 681, 624, 866, 499], [122, 835, 764, 336, 701, 258], [777, 786, 722], [857, 776, 442, 506, 676, 447], [377, 186, 836, 682, 729, 565], [587, 79, 300, 876, 879, 397], [612, 668, 692], [0, 255, 605, 313, 720, 530]]]
 h' := ![![[771, 365, 35, 806], [461, 737, 735, 122], [278, 526, 765, 271], [728, 864, 750, 663], [836, 135, 680, 731], [173, 800, 769, 782], [320, 242, 88, 171], [123, 407, 483, 735], [0, 0, 0, 1], [0, 1]], ![[399, 650, 772, 246], [653, 809, 528, 89], [226, 362, 285, 145], [852, 658, 884, 395], [783, 596, 176, 237], [314, 826, 347, 200], [145, 652, 454, 566], [46, 863, 130, 615], [18, 170, 284, 156], [771, 365, 35, 806]], ![[762, 758, 80, 722], [557, 207, 612, 668], [331, 466, 876, 484], [367, 84, 178, 198], [630, 385, 731, 516], [410, 400, 372, 117], [594, 83, 683, 54], [711, 571, 407, 215], [267, 148, 463, 852], [399, 650, 772, 246]], ![[0, 1], [264, 21, 786, 8], [337, 420, 735, 874], [664, 168, 849, 518], [244, 658, 187, 290], [757, 635, 286, 675], [162, 797, 549, 96], [689, 820, 754, 209], [49, 569, 140, 765], [762, 758, 80, 722]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [105, 181, 216], []]
 b := ![[], [], [850, 876, 802, 302], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI887N0 : CertifiedPrimeIdeal' SI887N0 887 where
  n := 4
  hpos := by decide
  P := [884, 867, 87, 729, 1]
  hirr := P887P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2482967192, 1383905430, 326477140, -700569028, -518596520]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![241926656, 65288530, 510779300, 112050236, -518596520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI887N0 : Ideal.IsPrime I887N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI887N0 B_one_repr
lemma NI887N0 : Nat.card (O ⧸ I887N0) = 619005459361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI887N0

def I887N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11953, -515, 3020, 346, -824]] i)))

def SI887N1: IdealEqSpanCertificate' Table ![![-11953, -515, 3020, 346, -824]] 
 ![![887, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![747, 0, 0, 1, 0], ![883, 0, 0, 0, 1]] where
  M :=![![![-11953, -515, 3020, 346, -824], ![19776, 823, -5018, -552, 1384], ![-16608, -785, 4143, 518, -1104], ![3360, -54, -1002, 3, 344], ![-20256, -1159, 4896, 722, -1241]]]
  hmulB := by decide  
  f := ![![![-70631, -21569, 32554, 422, -6000]], ![![-8995, -2764, 4144, 74, -776]], ![![-3208, -921, 1485, -50, -232]], ![![-60027, -18465, 27652, 517, -5192]], ![![-69571, -21076, 32084, 216, -5793]]]
  g := ![![![446, -515, 3020, 346, -824], ![-771, 823, -5018, -552, 1384], ![559, -785, 4143, 518, -1104], ![-289, -54, -1002, 3, 344], ![534, -1159, 4896, 722, -1241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI887N1 : Nat.card (O ⧸ I887N1) = 887 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI887N1)

lemma isPrimeI887N1 : Ideal.IsPrime I887N1 := prime_ideal_of_norm_prime hp887.out _ NI887N1
def MulI887N0 : IdealMulLeCertificate' Table 
  ![![70631, 21569, -32554, -422, 6000]] ![![-11953, -515, 3020, 346, -824]]
  ![![887, 0, 0, 0, 0]] where
 M := ![![![-887, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC887 : ContainsPrimesAboveP 887 ![I887N0, I887N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI887N0
    exact isPrimeI887N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 887 (by decide) (𝕀 ⊙ MulI887N0)
instance hp907 : Fact (Nat.Prime 907) := {out := by norm_num}

def I907N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1189, 23, -324, -31, 90]] i)))

def SI907N0: IdealEqSpanCertificate' Table ![![1189, 23, -324, -31, 90]] 
 ![![907, 0, 0, 0, 0], ![0, 907, 0, 0, 0], ![170, 441, 1, 0, 0], ![311, 156, 0, 1, 0], ![430, 140, 0, 0, 1]] where
  M :=![![![1189, 23, -324, -31, 90], ![-2160, -187, 468, 72, -124], ![1488, -92, -507, -28, 144], ![-648, -236, -10, 33, 6], ![1788, -117, -616, -43, 167]]]
  hmulB := by decide  
  f := ![![![871, 287, -398, -31, 88]], ![![-2112, -557, 988, -92, -124]], ![![-862, -217, 405, -50, -44]], ![![-61, 5, 32, -28, 10]], ![![82, 47, -34, -27, 21]]]
  g := ![![![30, 149, -324, -31, 90], ![-56, -221, 468, 72, -124], ![38, 229, -507, -28, 144], ![-13, -2, -10, 33, 6], ![53, 281, -616, -43, 167]]]
  hle1 := by decide   
  hle2 := by decide  


def P907P0 : CertificateIrreducibleZModOfList' 907 2 2 9 [777, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [781, 906], [0, 1]]
 g := ![![[613, 15], [379, 353], [483], [381, 219], [832], [799], [410], [676, 816], [781, 1]], ![[537, 892], [344, 554], [483], [904, 688], [832], [799], [410], [351, 91], [655, 906]]]
 h' := ![![[781, 906], [292, 742], [159, 258], [552, 499], [898, 411], [324, 217], [518, 79], [808, 238], [853, 587], [0, 1]], ![[0, 1], [221, 165], [303, 649], [261, 408], [811, 496], [192, 690], [541, 828], [751, 669], [358, 320], [781, 906]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [285]]
 b := ![[], [361, 596]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI907N0 : CertifiedPrimeIdeal' SI907N0 907 where
  n := 2
  hpos := by decide
  P := [777, 126, 1]
  hirr := P907P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125904, 42862, -178955, 4738, 138619]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33662, 64847, -178955, 4738, 138619]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI907N0 : Ideal.IsPrime I907N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI907N0 B_one_repr
lemma NI907N0 : Nat.card (O ⧸ I907N0) = 822649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI907N0

def I907N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4853, -1562, 2234, 127, -472]] i)))

def SI907N1: IdealEqSpanCertificate' Table ![![-4853, -1562, 2234, 127, -472]] 
 ![![907, 0, 0, 0, 0], ![0, 907, 0, 0, 0], ![425, 630, 1, 0, 0], ![722, 579, 0, 1, 0], ![527, 418, 0, 0, 1]] where
  M :=![![![-4853, -1562, 2234, 127, -472], ![11328, 2827, -5266, 692, 508], ![-6096, 929, 3151, -3234, 1384], ![-22272, -13732, 9564, 8341, -6722], ![31620, 18530, -13550, -10625, 8779]]]
  hmulB := by decide  
  f := ![![![75817, 47184, 15122, -21429, -17446]], ![![418704, 239987, 67442, -109324, -85716]], ![![327491, 189471, 54127, -86281, -67954]], ![![330302, 192315, 55542, -87555, -69166]], ![![240713, 140182, 40500, -63820, -50421]]]
  g := ![![![-879, -1417, 2234, 127, -472], ![1634, 2985, -5266, 692, 508], ![287, -761, 3151, -3234, 1384], ![-7240, -8885, 9564, 8341, -6722], ![9741, 12169, -13550, -10625, 8779]]]
  hle1 := by decide   
  hle2 := by decide  


def P907P1 : CertificateIrreducibleZModOfList' 907 2 2 9 [474, 229, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [678, 906], [0, 1]]
 g := ![![[343, 365], [642, 753], [850], [672, 88], [24], [400], [755], [76, 171], [678, 1]], ![[202, 542], [535, 154], [850], [474, 819], [24], [400], [755], [825, 736], [449, 906]]]
 h' := ![![[678, 906], [444, 70], [25, 795], [736, 370], [128, 53], [361, 323], [627, 887], [256, 676], [613, 268], [0, 1]], ![[0, 1], [740, 837], [277, 112], [357, 537], [689, 854], [768, 584], [672, 20], [549, 231], [10, 639], [678, 906]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [896]]
 b := ![[], [504, 448]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI907N1 : CertifiedPrimeIdeal' SI907N1 907 where
  n := 2
  hpos := by decide
  P := [474, 229, 1]
  hirr := P907P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7744, -5804, -602, 1339, 946]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1342, -879, -602, 1339, 946]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI907N1 : Ideal.IsPrime I907N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI907N1 B_one_repr
lemma NI907N1 : Nat.card (O ⧸ I907N1) = 822649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI907N1

def I907N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3275, 1911, 554, -870, -688]] i)))

def SI907N2: IdealEqSpanCertificate' Table ![![3275, 1911, 554, -870, -688]] 
 ![![907, 0, 0, 0, 0], ![579, 1, 0, 0, 0], ![628, 0, 1, 0, 0], ![665, 0, 0, 1, 0], ![588, 0, 0, 0, 1]] where
  M :=![![![3275, 1911, 554, -870, -688], ![16512, 9657, 2810, -4396, -3480], ![41760, 24405, 7093, -11110, -8792], ![97248, 56844, 16526, -25877, -20480], ![135504, 79199, 23022, -36054, -28533]]]
  hmulB := by decide  
  f := ![![![-1663, -199, 1800, 86, -552]], ![![-1047, -120, 1146, 54, -352]], ![![-1156, -135, 1255, 58, -384]], ![![-1205, -139, 1322, 65, -408]], ![![-1068, -117, 1172, 50, -357]]]
  g := ![![![-516, 1911, 554, -870, -688], ![-2613, 9657, 2810, -4396, -3480], ![-6599, 24405, 7093, -11110, -8792], ![-15373, 56844, 16526, -25877, -20480], ![-21417, 79199, 23022, -36054, -28533]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI907N2 : Nat.card (O ⧸ I907N2) = 907 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI907N2)

lemma isPrimeI907N2 : Ideal.IsPrime I907N2 := prime_ideal_of_norm_prime hp907.out _ NI907N2
def MulI907N0 : IdealMulLeCertificate' Table 
  ![![1189, 23, -324, -31, 90]] ![![-4853, -1562, 2234, 127, -472]]
  ![![1663, 199, -1800, -86, 552]] where
 M := ![![![1663, 199, -1800, -86, 552]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI907N1 : IdealMulLeCertificate' Table 
  ![![1663, 199, -1800, -86, 552]] ![![3275, 1911, 554, -870, -688]]
  ![![907, 0, 0, 0, 0]] where
 M := ![![![-907, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC907 : ContainsPrimesAboveP 907 ![I907N0, I907N1, I907N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI907N0
    exact isPrimeI907N1
    exact isPrimeI907N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 907 (by decide) (𝕀 ⊙ MulI907N0 ⊙ MulI907N1)
instance hp911 : Fact (Nat.Prime 911) := {out := by norm_num}

def I911N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4553, -210, 1138, 128, -314]] i)))

def SI911N0: IdealEqSpanCertificate' Table ![![-4553, -210, 1138, 128, -314]] 
 ![![911, 0, 0, 0, 0], ![0, 911, 0, 0, 0], ![108, 240, 1, 0, 0], ![499, 303, 0, 1, 0], ![90, 553, 0, 0, 1]] where
  M :=![![![-4553, -210, 1138, 128, -314], ![7536, 295, -1932, -236, 512], ![-6144, -250, 1555, 116, -472], ![1896, 270, -344, -215, -24], ![-6696, 74, 1962, -44, -707]]]
  hmulB := by decide  
  f := ![![![-3463, -1834, 1510, 936, -830]], ![![19920, 9049, -8860, -3620, 3744]], ![![4788, 2146, -2133, -836, 880]], ![![4813, 2037, -2158, -699, 802]], ![![11646, 5273, -5182, -2096, 2177]]]
  g := ![![![-179, -152, 1138, 128, -314], ![316, 277, -1932, -236, 512], ![-208, -162, 1555, 116, -472], ![163, 177, -344, -215, -24], ![-146, -73, 1962, -44, -707]]]
  hle1 := by decide   
  hle2 := by decide  


def P911P0 : CertificateIrreducibleZModOfList' 911 2 2 9 [456, 542, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [369, 910], [0, 1]]
 g := ![![[173, 2], [526, 559], [650, 405], [5, 610], [746], [389], [720], [8, 245], [369, 1]], ![[0, 909], [0, 352], [691, 506], [78, 301], [746], [389], [720], [224, 666], [738, 910]]]
 h' := ![![[369, 910], [648, 176], [586, 744], [453, 607], [186, 39], [167, 657], [567, 785], [907, 202], [271, 877], [0, 1]], ![[0, 1], [0, 735], [0, 167], [330, 304], [1, 872], [274, 254], [534, 126], [743, 709], [479, 34], [369, 910]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [616]]
 b := ![[], [567, 308]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI911N0 : CertifiedPrimeIdeal' SI911N0 911 where
  n := 2
  hpos := by decide
  P := [456, 542, 1]
  hirr := P911P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99741, -38454, -11113, 39690, 29909]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23487, -28471, -11113, 39690, 29909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI911N0 : Ideal.IsPrime I911N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI911N0 B_one_repr
lemma NI911N0 : Nat.card (O ⧸ I911N0) = 829921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI911N0

def I911N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -28, -8, 4, 4]] i)))

def SI911N1: IdealEqSpanCertificate' Table ![![-41, -28, -8, 4, 4]] 
 ![![911, 0, 0, 0, 0], ![319, 1, 0, 0, 0], ![591, 0, 1, 0, 0], ![320, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![-41, -28, -8, 4, 4], ![-96, -85, -48, 16, 16], ![-192, -144, -69, 16, 32], ![-336, -248, -72, 51, 24], ![-192, -172, -136, 12, 59]]]
  hmulB := by decide  
  f := ![![![-7351, -796, 1496, 420, -268]], ![![-2567, -281, 520, 148, -92]], ![![-4791, -524, 971, 276, -172]], ![![-2608, -296, 520, 155, -88]], ![![-1052, -132, 200, 68, -29]]]
  g := ![![![13, -28, -8, 4, 4], ![53, -85, -48, 16, 16], ![85, -144, -69, 16, 32], ![112, -248, -72, 51, 24], ![136, -172, -136, 12, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI911N1 : Nat.card (O ⧸ I911N1) = 911 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI911N1)

lemma isPrimeI911N1 : Ideal.IsPrime I911N1 := prime_ideal_of_norm_prime hp911.out _ NI911N1

def I911N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 11, -4, -9, 6]] i)))

def SI911N2: IdealEqSpanCertificate' Table ![![11, 11, -4, -9, 6]] 
 ![![911, 0, 0, 0, 0], ![326, 1, 0, 0, 0], ![611, 0, 1, 0, 0], ![454, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![11, 11, -4, -9, 6], ![-144, -77, 64, 40, -36], ![432, 198, -189, -80, 80], ![-888, -360, 406, 111, -142], ![1140, 463, -504, -141, 169]]]
  hmulB := by decide  
  f := ![![![-22571, -201, 6342, 547, -1784]], ![![-8030, -67, 2260, 194, -636]], ![![-15167, -131, 4265, 367, -1200]], ![![-11230, -92, 3162, 271, -890]], ![![-949, -2, 272, 22, -77]]]
  g := ![![![3, 11, -4, -9, 6], ![-34, -77, 64, 40, -36], ![93, 198, -189, -80, 80], ![-194, -360, 406, 111, -142], ![237, 463, -504, -141, 169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI911N2 : Nat.card (O ⧸ I911N2) = 911 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI911N2)

lemma isPrimeI911N2 : Ideal.IsPrime I911N2 := prime_ideal_of_norm_prime hp911.out _ NI911N2

def I911N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 1, -8, -1, 2]] i)))

def SI911N3: IdealEqSpanCertificate' Table ![![35, 1, -8, -1, 2]] 
 ![![911, 0, 0, 0, 0], ![697, 1, 0, 0, 0], ![788, 0, 1, 0, 0], ![611, 0, 0, 1, 0], ![849, 0, 0, 0, 1]] where
  M :=![![![35, 1, -8, -1, 2], ![-48, 3, 12, 0, -4], ![48, 4, -5, -4, 0], ![24, 16, 2, -5, -6], ![84, 21, -4, -13, -3]]]
  hmulB := by decide  
  f := ![![![-1235, -955, -382, 147, 156]], ![![-949, -734, -294, 113, 120]], ![![-1076, -832, -333, 128, 136]], ![![-839, -649, -260, 100, 106]], ![![-1161, -898, -360, 138, 147]]]
  g := ![![![5, 1, -8, -1, 2], ![-9, 3, 12, 0, -4], ![4, 4, -5, -4, 0], ![-5, 16, 2, -5, -6], ![-1, 21, -4, -13, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI911N3 : Nat.card (O ⧸ I911N3) = 911 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI911N3)

lemma isPrimeI911N3 : Ideal.IsPrime I911N3 := prime_ideal_of_norm_prime hp911.out _ NI911N3
def MulI911N0 : IdealMulLeCertificate' Table 
  ![![-4553, -210, 1138, 128, -314]] ![![-41, -28, -8, 4, 4]]
  ![![5617, 3726, 1470, -604, -610]] where
 M := ![![![5617, 3726, 1470, -604, -610]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI911N1 : IdealMulLeCertificate' Table 
  ![![5617, 3726, 1470, -604, -610]] ![![11, 11, -4, -9, 6]]
  ![![1235, 955, 382, -147, -156]] where
 M := ![![![1235, 955, 382, -147, -156]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI911N2 : IdealMulLeCertificate' Table 
  ![![1235, 955, 382, -147, -156]] ![![35, 1, -8, -1, 2]]
  ![![911, 0, 0, 0, 0]] where
 M := ![![![-911, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC911 : ContainsPrimesAboveP 911 ![I911N0, I911N1, I911N2, I911N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI911N0
    exact isPrimeI911N1
    exact isPrimeI911N2
    exact isPrimeI911N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 911 (by decide) (𝕀 ⊙ MulI911N0 ⊙ MulI911N1 ⊙ MulI911N2)
instance hp919 : Fact (Nat.Prime 919) := {out := by norm_num}

def I919N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3869, 1802, -908, -286, 172]] i)))

def SI919N0: IdealEqSpanCertificate' Table ![![3869, 1802, -908, -286, 172]] 
 ![![919, 0, 0, 0, 0], ![0, 919, 0, 0, 0], ![0, 0, 919, 0, 0], ![361, 553, 145, 1, 0], ![19, 11, 332, 0, 1]] where
  M :=![![![3869, 1802, -908, -286, 172], ![-4128, 497, 4864, -440, -1144], ![13728, 6220, -1351, 288, -880], ![12624, 11068, 1740, -4651, 1148], ![2040, 970, 5900, 3530, -4519]]]
  hmulB := by decide  
  f := ![![![-29053, -1518, 7132, 954, -1868]], ![![44832, 535, -12416, -680, 3816]], ![![-45792, -5460, 8847, 2848, -1360]], ![![8333, -1145, -3279, 419, 1352]], ![![-16681, -2013, 3204, 1048, -483]]]
  g := ![![![113, 172, -18, -286, 172], ![192, 279, 488, -440, -1144], ![-80, -156, 271, 288, -880], ![1817, 2797, 321, -4651, 1148], ![-1291, -2069, 1082, 3530, -4519]]]
  hle1 := by decide   
  hle2 := by decide  


def P919P0 : CertificateIrreducibleZModOfList' 919 3 2 9 [259, 271, 852, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [699, 52], [287, 866], [0, 1]]
 g := ![![[306, 61, 569], [877, 649, 458], [110, 906, 526], [464, 367], [365, 352, 865], [667, 845], [441, 251], [137, 696, 813], [1]], ![[598, 249, 170], [543, 62, 539], [475, 587, 611], [596, 704], [157, 308, 105], [405, 747], [361, 186], [867, 390, 104], [1]], ![[232, 609, 180], [635, 208, 841], [813, 345, 701], [108, 767], [333, 259, 868], [566, 246], [796, 482], [771, 752, 2], [1]]]
 h' := ![![[699, 52], [769, 441, 830], [918, 265, 330], [393, 748, 267], [122, 53, 492], [806, 124, 142], [160, 491, 877], [358, 406, 342], [660, 648, 67], [0, 1]], ![[287, 866], [916, 692, 122], [295, 99, 890], [156, 850, 553], [81, 789, 575], [695, 639, 745], [610, 405, 388], [872, 300, 254], [194, 544, 125], [699, 52]], ![[0, 1], [536, 705, 886], [284, 555, 618], [876, 240, 99], [115, 77, 771], [838, 156, 32], [88, 23, 573], [258, 213, 323], [207, 646, 727], [287, 866]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [337], []]
 b := ![[], [238, 157, 552], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI919N0 : CertifiedPrimeIdeal' SI919N0 919 where
  n := 3
  hpos := by decide
  P := [259, 271, 852, 1]
  hirr := P919P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27674435, 11381789, -15445822, -3115201, 7105976]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1106908, 1801874, -2092411, -3115201, 7105976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI919N0 : Ideal.IsPrime I919N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI919N0 B_one_repr
lemma NI919N0 : Nat.card (O ⧸ I919N0) = 776151559 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI919N0

def I919N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29053, -1518, 7132, 954, -1868]] i)))

def SI919N1: IdealEqSpanCertificate' Table ![![-29053, -1518, 7132, 954, -1868]] 
 ![![919, 0, 0, 0, 0], ![0, 919, 0, 0, 0], ![494, 774, 1, 0, 0], ![867, 819, 0, 1, 0], ![134, 17, 0, 0, 1]] where
  M :=![![![-29053, -1518, 7132, 954, -1868], ![44832, 535, -12416, -680, 3816], ![-45792, -5460, 8847, 2848, -1360], ![-6096, -8412, -4820, 3747, 3788], ![-68040, -14270, 8340, 6930, 1159]]]
  hmulB := by decide  
  f := ![![![3869, 1802, -908, -286, 172]], ![![-4128, 497, 4864, -440, -1144]], ![![-1382, 1394, 3607, -524, -872]], ![![-15, 2155, 3480, -667, -856]], ![![490, 273, -36, -46, -1]]]
  g := ![![![-4493, -6824, 7132, 954, -1868], ![6808, 10993, -12416, -680, 3816], ![-7294, -9970, 8847, 2848, -1360], ![-1503, 641, -4820, 3747, 3788], ![-11264, -13237, 8340, 6930, 1159]]]
  hle1 := by decide   
  hle2 := by decide  


def P919P1 : CertificateIrreducibleZModOfList' 919 2 2 9 [802, 213, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [706, 918], [0, 1]]
 g := ![![[116, 863], [499, 434], [875, 468], [764], [738, 382], [704], [72], [105, 250], [706, 1]], ![[97, 56], [876, 485], [443, 451], [764], [244, 537], [704], [72], [157, 669], [493, 918]]]
 h' := ![![[706, 918], [486, 332], [366, 766], [7, 159], [879, 135], [230, 626], [441, 575], [338, 169], [811, 455], [0, 1]], ![[0, 1], [533, 587], [790, 153], [143, 760], [613, 784], [147, 293], [193, 344], [182, 750], [391, 464], [706, 918]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [488]]
 b := ![[], [254, 244]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI919N1 : CertifiedPrimeIdeal' SI919N1 919 where
  n := 2
  hpos := by decide
  P := [802, 213, 1]
  hirr := P919P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60466, 24900, -26630, -12514, 12526]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24360, 33376, -26630, -12514, 12526]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI919N1 : Ideal.IsPrime I919N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI919N1 B_one_repr
lemma NI919N1 : Nat.card (O ⧸ I919N1) = 844561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI919N1
def MulI919N0 : IdealMulLeCertificate' Table 
  ![![3869, 1802, -908, -286, 172]] ![![-29053, -1518, 7132, 954, -1868]]
  ![![919, 0, 0, 0, 0]] where
 M := ![![![919, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC919 : ContainsPrimesAboveP 919 ![I919N0, I919N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI919N0
    exact isPrimeI919N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 919 (by decide) (𝕀 ⊙ MulI919N0)
instance hp929 : Fact (Nat.Prime 929) := {out := by norm_num}

def I929N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25711, 17049, 5946, -7727, -6458]] i)))

def SI929N0: IdealEqSpanCertificate' Table ![![25711, 17049, 5946, -7727, -6458]] 
 ![![929, 0, 0, 0, 0], ![0, 929, 0, 0, 0], ![0, 0, 929, 0, 0], ![289, 655, 830, 1, 0], ![835, 420, 536, 0, 1]] where
  M :=![![![25711, 17049, 5946, -7727, -6458], ![154992, 87241, 23720, -39772, -30908], ![370896, 219578, 65197, -99912, -79544], ![877032, 512006, 148542, -233093, -184370], ![1214172, 713033, 208918, -324539, -257411]]]
  hmulB := by decide  
  f := ![![![-649, -409, 32, 111, -24]], ![![576, -131, -1136, -128, 444]], ![![-5328, -2850, 885, 640, -256]], ![![-4553, -2766, -4, 516, 78]], ![![-3407, -2076, 28, 412, 31]]]
  g := ![![![8236, 8386, 10636, -7727, -6458], ![40320, 42109, 53392, -39772, -30908], ![102976, 106642, 135229, -99912, -79544], ![239171, 248249, 314788, -233093, -184370], ![333632, 345962, 438696, -324539, -257411]]]
  hle1 := by decide   
  hle2 := by decide  


def P929P0 : CertificateIrreducibleZModOfList' 929 3 2 9 [245, 472, 836, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [455, 23, 794], [567, 905, 135], [0, 1]]
 g := ![![[529, 41, 704], [45, 476], [600, 777], [124, 800], [482, 291], [181, 495, 893], [882, 745], [61, 306, 288], [1]], ![[493, 254, 661, 657], [548, 333], [114, 740], [707, 201], [482, 489], [796, 275, 256, 622], [716, 575], [345, 3, 837, 340], [721, 458, 271, 546]], ![[607, 220, 530, 735], [848, 608], [658, 81], [681, 324], [880, 455], [167, 370, 688, 686], [615, 78], [697, 331, 764, 504], [479, 926, 794, 383]]]
 h' := ![![[455, 23, 794], [607, 500, 714], [907, 487, 194], [14, 872, 213], [517, 132, 155], [247, 859, 661], [425, 287, 86], [848, 855, 594], [684, 457, 93], [0, 1]], ![[567, 905, 135], [323, 882, 832], [454, 655, 203], [385, 346, 725], [105, 299, 756], [529, 671, 89], [650, 815, 67], [840, 917, 379], [285, 322, 174], [455, 23, 794]], ![[0, 1], [773, 476, 312], [210, 716, 532], [467, 640, 920], [709, 498, 18], [185, 328, 179], [203, 756, 776], [64, 86, 885], [227, 150, 662], [567, 905, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [816, 285], []]
 b := ![[], [655, 710, 415], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI929N0 : CertifiedPrimeIdeal' SI929N0 929 where
  n := 3
  hpos := by decide
  P := [245, 472, 836, 1]
  hirr := P929P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11706702, 3904122, -8763344, -168482, 4133971]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3650665, -1745972, -2244060, -168482, 4133971]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI929N0 : Ideal.IsPrime I929N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI929N0 B_one_repr
lemma NI929N0 : Nat.card (O ⧸ I929N0) = 801765089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI929N0

def I929N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -4, 0, -2, -2]] i)))

def SI929N1: IdealEqSpanCertificate' Table ![![-13, -4, 0, -2, -2]] 
 ![![929, 0, 0, 0, 0], ![297, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![152, 0, 0, 1, 0], ![654, 0, 0, 0, 1]] where
  M :=![![![-13, -4, 0, -2, -2], ![48, 5, -12, -16, -8], ![96, 46, 5, -44, -32], ![360, 180, 32, -115, -84], ![528, 292, 72, -166, -127]]]
  hmulB := by decide  
  f := ![![![1099, 924, -480, -654, 478]], ![![339, 289, -148, -206, 150]], ![![61, 38, -27, -22, 18]], ![![112, 124, -48, -99, 68]], ![![858, 684, -376, -470, 349]]]
  g := ![![![3, -4, 0, -2, -2], ![7, 5, -12, -16, -8], ![15, 46, 5, -44, -32], ![20, 180, 32, -115, -84], ![22, 292, 72, -166, -127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI929N1 : Nat.card (O ⧸ I929N1) = 929 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI929N1)

lemma isPrimeI929N1 : Ideal.IsPrime I929N1 := prime_ideal_of_norm_prime hp929.out _ NI929N1

def I929N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4187, 1365, -1924, -129, 418]] i)))

def SI929N2: IdealEqSpanCertificate' Table ![![4187, 1365, -1924, -129, 418]] 
 ![![929, 0, 0, 0, 0], ![830, 1, 0, 0, 0], ![209, 0, 1, 0, 0], ![176, 0, 0, 1, 0], ![794, 0, 0, 0, 1]] where
  M :=![![![4187, 1365, -1924, -129, 418], ![-10032, -2593, 4660, -504, -516], ![6192, -352, -3121, 2596, -1008], ![17112, 10972, -7294, -6901, 5450], ![-24588, -14863, 10496, 8803, -7147]]]
  hmulB := by decide  
  f := ![![![5136619, 3020679, 887098, -1374803, -1091148]], ![![4617418, 2715221, 797328, -1235782, -980788]], ![![1226635, 721119, 211665, -328207, -260452]], ![![1138720, 669050, 196194, -304515, -241586]], ![![4620802, 2716557, 797402, -1236401, -981169]]]
  g := ![![![-1115, 1365, -1924, -129, 418], ![1794, -2593, 4660, -504, -516], ![1393, -352, -3121, 2596, -1008], ![-11494, 10972, -7294, -6901, 5450], ![15332, -14863, 10496, 8803, -7147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI929N2 : Nat.card (O ⧸ I929N2) = 929 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI929N2)

lemma isPrimeI929N2 : Ideal.IsPrime I929N2 := prime_ideal_of_norm_prime hp929.out _ NI929N2
def MulI929N0 : IdealMulLeCertificate' Table 
  ![![25711, 17049, 5946, -7727, -6458]] ![![-13, -4, 0, -2, -2]]
  ![![-5136619, -3020679, -887098, 1374803, 1091148]] where
 M := ![![![-5136619, -3020679, -887098, 1374803, 1091148]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI929N1 : IdealMulLeCertificate' Table 
  ![![-5136619, -3020679, -887098, 1374803, 1091148]] ![![4187, 1365, -1924, -129, 418]]
  ![![929, 0, 0, 0, 0]] where
 M := ![![![-929, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC929 : ContainsPrimesAboveP 929 ![I929N0, I929N1, I929N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI929N0
    exact isPrimeI929N1
    exact isPrimeI929N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 929 (by decide) (𝕀 ⊙ MulI929N0 ⊙ MulI929N1)


lemma PB934I17_primes (p : ℕ) :
  p ∈ Set.range ![887, 907, 911, 919, 929] ↔ Nat.Prime p ∧ 883 < p ∧ p ≤ 933 := by
  rw [← List.mem_ofFn']
  convert primes_range 883 933 (by omega)

def PB934I17 : PrimesBelowBoundCertificateInterval O 883 933 934 where
  m := 5
  g := ![2, 3, 4, 2, 3]
  P := ![887, 907, 911, 919, 929]
  hP := PB934I17_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I887N0, I887N1]
    · exact ![I907N0, I907N1, I907N2]
    · exact ![I911N0, I911N1, I911N2, I911N3]
    · exact ![I919N0, I919N1]
    · exact ![I929N0, I929N1, I929N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC887
    · exact PBC907
    · exact PBC911
    · exact PBC919
    · exact PBC929
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![619005459361, 887]
    · exact ![822649, 822649, 907]
    · exact ![829921, 911, 911, 911]
    · exact ![776151559, 844561]
    · exact ![801765089, 929, 929]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI887N0
      exact NI887N1
    · dsimp ; intro j
      fin_cases j
      exact NI907N0
      exact NI907N1
      exact NI907N2
    · dsimp ; intro j
      fin_cases j
      exact NI911N0
      exact NI911N1
      exact NI911N2
      exact NI911N3
    · dsimp ; intro j
      fin_cases j
      exact NI919N0
      exact NI919N1
    · dsimp ; intro j
      fin_cases j
      exact NI929N0
      exact NI929N1
      exact NI929N2
  β := ![I887N1, I907N2, I911N1, I911N2, I911N3, I929N1, I929N2]
  Il := ![[I887N1], [I907N2], [I911N1, I911N2, I911N3], [], [I929N1, I929N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
