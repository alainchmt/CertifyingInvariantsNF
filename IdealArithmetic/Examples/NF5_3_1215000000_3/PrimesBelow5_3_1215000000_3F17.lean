
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp887 : Fact (Nat.Prime 887) := {out := by norm_num}

def I887N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2035, -993, -185, -194, 196]] i)))

def SI887N0: IdealEqSpanCertificate' Table ![![2035, -993, -185, -194, 196]] 
 ![![887, 0, 0, 0, 0], ![0, 887, 0, 0, 0], ![0, 0, 887, 0, 0], ![603, 694, 207, 1, 0], ![123, 442, 480, 0, 1]] where
  M :=![![![2035, -993, -185, -194, 196], ![-2352, 2240, 179, 22, -776], ![9312, -2971, -908, -1194, 88], ![648, 3723, -205, -831, -2000], ![10068, -1107, -1063, -1694, -981]]]
  hmulB := by decide  
  f := ![![![125, -3, -33, 10, 4]], ![![-48, 86, -7, -58, 40]], ![![-480, 43, 362, 66, -232]], ![![-63, 75, 56, -23, -20]], ![![-267, 66, 188, 8, -105]]]
  g := ![![![107, 53, -61, -194, 196], ![90, 372, 415, 22, -776], ![810, 887, 230, -1194, 88], ![843, 1651, 1276, -831, -2000], ![1299, 1813, 925, -1694, -981]]]
  hle1 := by decide   
  hle2 := by decide  


def P887P0 : CertificateIrreducibleZModOfList' 887 3 2 9 [450, 529, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [556, 571, 333], [311, 315, 554], [0, 1]]
 g := ![![[665, 513, 531], [452, 470, 650], [767, 315, 516], [463, 627], [844, 618, 690], [171, 485, 108], [521, 324, 228], [742, 400], [1]], ![[55, 603, 878, 822], [761, 229, 723, 231], [378, 405, 597, 642], [92, 749], [199, 125, 836, 101], [441, 333, 52, 265], [366, 372, 402, 243], [563, 152], [285, 194, 815, 227]], ![[621, 795, 694, 732], [172, 537, 654, 430], [118, 724, 298, 235], [422, 449], [582, 599, 184, 885], [456, 116, 622, 570], [36, 713, 190, 280], [460, 596], [113, 405, 30, 660]]]
 h' := ![![[556, 571, 333], [610, 793, 389], [780, 366, 142], [381, 347, 717], [723, 166, 838], [219, 548, 591], [605, 213, 229], [763, 265, 441], [437, 358, 867], [0, 1]], ![[311, 315, 554], [685, 384, 759], [820, 156, 739], [633, 647, 798], [280, 191, 815], [723, 662, 544], [44, 139, 257], [845, 360, 88], [669, 862, 265], [556, 571, 333]], ![[0, 1], [135, 597, 626], [215, 365, 6], [383, 780, 259], [817, 530, 121], [801, 564, 639], [562, 535, 401], [574, 262, 358], [883, 554, 642], [311, 315, 554]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [732, 382], []]
 b := ![[], [143, 408, 164], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI887N0 : CertifiedPrimeIdeal' SI887N0 887 where
  n := 3
  hpos := by decide
  P := [450, 529, 20, 1]
  hirr := P887P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9923568, 3405328, -1105420, -3197920, -3005830]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2602014, 4003764, 2371660, -3197920, -3005830]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI887N0 : Ideal.IsPrime I887N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI887N0 B_one_repr
lemma NI887N0 : Nat.card (O ⧸ I887N0) = 697864103 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI887N0

def I887N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6239, 3796, 546, 458, -976]] i)))

def SI887N1: IdealEqSpanCertificate' Table ![![-6239, 3796, 546, 458, -976]] 
 ![![887, 0, 0, 0, 0], ![481, 1, 0, 0, 0], ![146, 0, 1, 0, 0], ![570, 0, 0, 1, 0], ![615, 0, 0, 0, 1]] where
  M :=![![![-6239, 3796, 546, 458, -976], ![11712, -7127, -1024, -860, 1832], ![-21984, 13380, 1921, 1616, -3440], ![14784, -8996, -1294, -1089, 2316], ![-15012, 9132, 1316, 1104, -2351]]]
  hmulB := by decide  
  f := ![![![11639, 6388, 710, -1002, -1880]], ![![6337, 3477, 386, -546, -1024]], ![![1970, 1076, 117, -172, -320]], ![![7530, 4124, 454, -653, -1220]], ![![8139, 4456, 490, -706, -1319]]]
  g := ![![![-1773, 3796, 546, 458, -976], ![3329, -7127, -1024, -860, 1832], ![-6250, 13380, 1921, 1616, -3440], ![4202, -8996, -1294, -1089, 2316], ![-4265, 9132, 1316, 1104, -2351]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI887N1 : Nat.card (O ⧸ I887N1) = 887 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI887N1)

lemma isPrimeI887N1 : Ideal.IsPrime I887N1 := prime_ideal_of_norm_prime hp887.out _ NI887N1

def I887N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 349, 61, -36, -84]] i)))

def SI887N2: IdealEqSpanCertificate' Table ![![557, 349, 61, -36, -84]] 
 ![![887, 0, 0, 0, 0], ![879, 1, 0, 0, 0], ![823, 0, 1, 0, 0], ![635, 0, 0, 1, 0], ![349, 0, 0, 0, 1]] where
  M :=![![![557, 349, 61, -36, -84], ![1008, 570, 85, -46, -144], ![1728, 995, 86, -118, -184], ![600, 589, 205, -75, -164], ![1608, 819, 85, -50, -203]]]
  hmulB := by decide  
  f := ![![![-26069789, 15861767, 2281529, 1914700, -4079036]], ![![-25779477, 15685131, 2256122, 1893378, -4033612]], ![![-24292381, 14780330, 2125977, 1784158, -3800932]], ![![-18593585, 11312984, 1627240, 1365609, -2909264]], ![![-10328167, 6284016, 903882, 758554, -1616007]]]
  g := ![![![-343, 349, 61, -36, -84], ![-553, 570, 85, -46, -144], ![-907, 995, 86, -118, -184], ![-655, 589, 205, -75, -164], ![-773, 819, 85, -50, -203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI887N2 : Nat.card (O ⧸ I887N2) = 887 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI887N2)

lemma isPrimeI887N2 : Ideal.IsPrime I887N2 := prime_ideal_of_norm_prime hp887.out _ NI887N2
def MulI887N0 : IdealMulLeCertificate' Table 
  ![![2035, -993, -185, -194, 196]] ![![-6239, 3796, 546, 458, -976]]
  ![![-26069789, 15861767, 2281529, 1914700, -4079036]] where
 M := ![![![-26069789, 15861767, 2281529, 1914700, -4079036]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI887N1 : IdealMulLeCertificate' Table 
  ![![-26069789, 15861767, 2281529, 1914700, -4079036]] ![![557, 349, 61, -36, -84]]
  ![![887, 0, 0, 0, 0]] where
 M := ![![![887, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC887 : ContainsPrimesAboveP 887 ![I887N0, I887N1, I887N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI887N0
    exact isPrimeI887N1
    exact isPrimeI887N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 887 (by decide) (𝕀 ⊙ MulI887N0 ⊙ MulI887N1)
instance hp907 : Fact (Nat.Prime 907) := {out := by norm_num}

def I907N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20342, 12128, 1829, -1221, -2873]] i)))

def SI907N0: IdealEqSpanCertificate' Table ![![20342, 12128, 1829, -1221, -2873]] 
 ![![907, 0, 0, 0, 0], ![0, 907, 0, 0, 0], ![432, 551, 1, 0, 0], ![708, 792, 0, 1, 0], ![845, 421, 0, 0, 1]] where
  M :=![![![20342, 12128, 1829, -1221, -2873], ![34476, 20519, 3078, -2088, -4884], ![58608, 34758, 5159, -3612, -8352], ![32874, 19254, 2748, -2149, -4782], ![52269, 30756, 4455, -3345, -7546]]]
  hmulB := by decide  
  f := ![![![1340, -800, -89, 27, 89]], ![![-1068, 1313, -498, 0, 108]], ![![-12, 415, -343, 12, 108]], ![![114, 522, -504, 23, 162]], ![![757, -137, -316, 24, 135]]]
  g := ![![![2781, 1302, 1829, -1221, -2873], ![4752, 2243, 3078, -2088, -4884], ![8208, 3935, 5159, -3612, -8352], ![4860, 2448, 2748, -2149, -4782], ![7577, 3751, 4455, -3345, -7546]]]
  hle1 := by decide   
  hle2 := by decide  


def P907P0 : CertificateIrreducibleZModOfList' 907 2 2 9 [624, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [832, 906], [0, 1]]
 g := ![![[301, 62], [318, 281], [615], [556, 198], [356], [140], [246], [269, 383], [832, 1]], ![[186, 845], [104, 626], [615], [218, 709], [356], [140], [246], [568, 524], [757, 906]]]
 h' := ![![[832, 906], [201, 714], [400, 368], [437, 625], [365, 533], [677, 136], [779, 86], [846, 309], [543, 466], [0, 1]], ![[0, 1], [164, 193], [10, 539], [726, 282], [298, 374], [454, 771], [678, 821], [346, 598], [59, 441], [832, 906]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [329]]
 b := ![[], [500, 618]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI907N0 : CertifiedPrimeIdeal' SI907N0 907 where
  n := 2
  hpos := by decide
  P := [624, 75, 1]
  hirr := P907P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2235834, -314692, 373552, 365754, 496540]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-928490, -777136, 373552, 365754, 496540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI907N0 : Ideal.IsPrime I907N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI907N0 B_one_repr
lemma NI907N0 : Nat.card (O ⧸ I907N0) = 822649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI907N0

def I907N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2570, 1562, 249, -139, -351]] i)))

def SI907N1: IdealEqSpanCertificate' Table ![![2570, 1562, 249, -139, -351]] 
 ![![907, 0, 0, 0, 0], ![175, 1, 0, 0, 0], ![213, 0, 1, 0, 0], ![322, 0, 0, 1, 0], ![348, 0, 0, 0, 1]] where
  M :=![![![2570, 1562, 249, -139, -351], ![4212, 2607, 436, -204, -556], ![6672, 4296, 791, -240, -816], ![2790, 2140, 538, 77, -202], ![4995, 3562, 799, -3, -470]]]
  hmulB := by decide  
  f := ![![![-2905756, 1768002, 254279, 213445, -454673]], ![![-554632, 337465, 48535, 40741, -86785]], ![![-693684, 422070, 60704, 50955, -108543]], ![![-1023994, 623048, 89608, 75219, -160228]], ![![-1122597, 683042, 98237, 82461, -175656]]]
  g := ![![![-173, 1562, 249, -139, -351], ![-315, 2607, 436, -204, -556], ![-609, 4296, 791, -240, -816], ![-486, 2140, 538, 77, -202], ![-688, 3562, 799, -3, -470]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI907N1 : Nat.card (O ⧸ I907N1) = 907 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI907N1)

lemma isPrimeI907N1 : Ideal.IsPrime I907N1 := prime_ideal_of_norm_prime hp907.out _ NI907N1

def I907N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-136, -36, 15, 31, 37]] i)))

def SI907N2: IdealEqSpanCertificate' Table ![![-136, -36, 15, 31, 37]] 
 ![![907, 0, 0, 0, 0], ![234, 1, 0, 0, 0], ![571, 0, 1, 0, 0], ![194, 0, 0, 1, 0], ![786, 0, 0, 0, 1]] where
  M :=![![![-136, -36, 15, 31, 37], ![-444, -115, 50, 104, 124], ![-1488, -374, 173, 348, 416], ![-2274, -566, 272, 537, 634], ![-2757, -692, 323, 653, 776]]]
  hmulB := by decide  
  f := ![![![63770, -38820, -5611, -4681, 9995]], ![![16320, -9935, -1436, -1198, 2558]], ![![40394, -24590, -3554, -2965, 6331]], ![![13474, -8202, -1186, -989, 2112]], ![![55431, -33744, -4877, -4069, 8688]]]
  g := ![![![-39, -36, 15, 31, 37], ![-132, -115, 50, 104, 124], ![-449, -374, 173, 348, 416], ![-692, -566, 272, 537, 634], ![-840, -692, 323, 653, 776]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI907N2 : Nat.card (O ⧸ I907N2) = 907 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI907N2)

lemma isPrimeI907N2 : Ideal.IsPrime I907N2 := prime_ideal_of_norm_prime hp907.out _ NI907N2

def I907N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![172, 43, -20, -41, -49]] i)))

def SI907N3: IdealEqSpanCertificate' Table ![![172, 43, -20, -41, -49]] 
 ![![907, 0, 0, 0, 0], ![854, 1, 0, 0, 0], ![819, 0, 1, 0, 0], ![869, 0, 0, 1, 0], ![573, 0, 0, 0, 1]] where
  M :=![![![172, 43, -20, -41, -49], ![588, 144, -71, -138, -164], ![1968, 491, -236, -470, -552], ![3018, 753, -353, -719, -858], ![3705, 913, -446, -875, -1036]]]
  hmulB := by decide  
  f := ![![![8914, -2535, -366, -621, 689]], ![![8384, -2376, -343, -584, 646]], ![![8082, -2300, -332, -563, 625]], ![![8528, -2416, -349, -594, 657]], ![![5655, -1608, -232, -394, 437]]]
  g := ![![![48, 43, -20, -41, -49], ![165, 144, -71, -138, -164], ![552, 491, -236, -470, -552], ![844, 753, -353, -719, -858], ![1040, 913, -446, -875, -1036]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI907N3 : Nat.card (O ⧸ I907N3) = 907 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI907N3)

lemma isPrimeI907N3 : Ideal.IsPrime I907N3 := prime_ideal_of_norm_prime hp907.out _ NI907N3
def MulI907N0 : IdealMulLeCertificate' Table 
  ![![20342, 12128, 1829, -1221, -2873]] ![![2570, 1562, 249, -139, -351]]
  ![![97807939, 58402718, 8847280, -5826008, -13778722]] where
 M := ![![![97807939, 58402718, 8847280, -5826008, -13778722]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI907N1 : IdealMulLeCertificate' Table 
  ![![97807939, 58402718, 8847280, -5826008, -13778722]] ![![-136, -36, 15, 31, 37]]
  ![![-1161160390, -713884942, -117366957, 58710459, 155321911]] where
 M := ![![![-1161160390, -713884942, -117366957, 58710459, 155321911]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI907N2 : IdealMulLeCertificate' Table 
  ![![-1161160390, -713884942, -117366957, 58710459, 155321911]] ![![172, 43, -20, -41, -49]]
  ![![907, 0, 0, 0, 0]] where
 M := ![![![-97806258835, -24338623935, 11609276201, 23166675630, 27473476244]]]
 hmul := by decide  
 g := ![![![![-107834905, -26834205, 12799643, 25542090, 30290492]]]]
 hle2 := by decide  


def PBC907 : ContainsPrimesAboveP 907 ![I907N0, I907N1, I907N2, I907N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI907N0
    exact isPrimeI907N1
    exact isPrimeI907N2
    exact isPrimeI907N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 907 (by decide) (𝕀 ⊙ MulI907N0 ⊙ MulI907N1 ⊙ MulI907N2)
instance hp911 : Fact (Nat.Prime 911) := {out := by norm_num}

def I911N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10432, -5981, -908, 623, 1407]] i)))

def SI911N0: IdealEqSpanCertificate' Table ![![-10432, -5981, -908, 623, 1407]] 
 ![![911, 0, 0, 0, 0], ![0, 911, 0, 0, 0], ![0, 0, 911, 0, 0], ![775, 841, 588, 1, 0], ![811, 423, 200, 0, 1]] where
  M :=![![![-10432, -5981, -908, 623, 1407], ![-16884, -10556, -1599, 998, 2492], ![-29904, -16989, -2584, 1786, 3992], ![-15510, -9863, -1497, 909, 2326], ![-26151, -15031, -2286, 1557, 3528]]]
  hmulB := by decide  
  f := ![![![-50, 21, 10, -17, 5]], ![![-60, -18, 75, 30, -68]], ![![816, -83, -350, 14, 120]], ![![428, -52, -148, 22, 19]], ![![107, -8, -33, 2, -1]]]
  g := ![![![-1794, -1235, -712, 623, 1407], ![-3086, -2090, -1193, 998, 2492], ![-5106, -3521, -2032, 1786, 3992], ![-2861, -1930, -1099, 909, 2326], ![-4494, -3092, -1782, 1557, 3528]]]
  hle1 := by decide   
  hle2 := by decide  


def P911P0 : CertificateIrreducibleZModOfList' 911 3 2 9 [688, 323, 317, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [420, 324, 767], [174, 586, 144], [0, 1]]
 g := ![![[439, 201, 46], [217, 905, 557], [858, 94, 450], [260, 114, 57], [34, 469], [105, 860], [371, 80], [9, 642, 279], [1]], ![[885, 196, 588, 464], [892, 196, 454, 891], [706, 366, 238, 703], [544, 693, 493, 145], [159, 64], [579, 432], [714, 509], [234, 622, 804, 851], [892, 589, 115, 274]], ![[464, 706, 566, 760], [154, 177, 514, 723], [266, 737, 773, 38], [295, 131, 443, 561], [545, 115], [143, 634], [168, 289], [422, 666, 507, 503], [88, 102, 536, 637]]]
 h' := ![![[420, 324, 767], [108, 205, 496], [24, 30, 316], [587, 506, 818], [633, 74, 683], [155, 671, 140], [350, 106, 586], [185, 500, 371], [223, 588, 594], [0, 1]], ![[174, 586, 144], [369, 751, 590], [70, 774, 478], [370, 377, 178], [341, 656, 585], [161, 601, 903], [279, 895, 172], [48, 565, 557], [332, 502, 133], [420, 324, 767]], ![[0, 1], [622, 866, 736], [214, 107, 117], [251, 28, 826], [106, 181, 554], [252, 550, 779], [460, 821, 153], [829, 757, 894], [204, 732, 184], [174, 586, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 333], []]
 b := ![[], [64, 599, 287], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI911N0 : CertifiedPrimeIdeal' SI911N0 911 where
  n := 3
  hpos := by decide
  P := [688, 323, 317, 1]
  hirr := P911P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-355473, 703045, 291072, -520247, -233753]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![650285, 589581, 387428, -520247, -233753]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI911N0 : Ideal.IsPrime I911N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI911N0 B_one_repr
lemma NI911N0 : Nat.card (O ⧸ I911N0) = 756058031 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI911N0

def I911N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50, 21, 10, -17, 5]] i)))

def SI911N1: IdealEqSpanCertificate' Table ![![-50, 21, 10, -17, 5]] 
 ![![911, 0, 0, 0, 0], ![0, 911, 0, 0, 0], ![214, 646, 1, 0, 0], ![114, 524, 0, 1, 0], ![314, 676, 0, 0, 1]] where
  M :=![![![-50, 21, 10, -17, 5], ![-60, -18, 75, 30, -68], ![816, -83, -350, 14, 120], ![-690, 295, 147, -245, 62], ![207, -105, 102, 119, -202]]]
  hmulB := by decide  
  f := ![![![-10432, -5981, -908, 623, 1407]], ![![-16884, -10556, -1599, 998, 2492]], ![![-14456, -8909, -1350, 856, 2102]], ![![-11034, -6831, -1035, 653, 1612]], ![![-16153, -9911, -1502, 957, 2338]]]
  g := ![![![-2, -1, 10, -17, 5], ![2, -20, 75, 30, -68], ![40, 151, -350, 14, 120], ![-26, -9, 147, -245, 62], ![31, 9, 102, 119, -202]]]
  hle1 := by decide   
  hle2 := by decide  


def P911P1 : CertificateIrreducibleZModOfList' 911 2 2 9 [331, 652, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [259, 910], [0, 1]]
 g := ![![[646, 300], [886, 183], [266, 713], [623, 687], [61], [810], [441], [478, 883], [259, 1]], ![[0, 611], [0, 728], [0, 198], [0, 224], [61], [810], [441], [514, 28], [518, 910]]]
 h' := ![![[259, 910], [76, 464], [321, 857], [584, 353], [513, 399], [503, 653], [860, 666], [296, 890], [816, 247], [0, 1]], ![[0, 1], [0, 447], [0, 54], [0, 558], [0, 512], [184, 258], [264, 245], [323, 21], [108, 664], [259, 910]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [657]]
 b := ![[], [504, 784]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI911N1 : CertifiedPrimeIdeal' SI911N1 911 where
  n := 2
  hpos := by decide
  P := [331, 652, 1]
  hirr := P911P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448035, -60540, 73093, 79653, 133794]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-73745, -196994, 73093, 79653, 133794]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI911N1 : Ideal.IsPrime I911N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI911N1 B_one_repr
lemma NI911N1 : Nat.card (O ⧸ I911N1) = 829921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI911N1
def MulI911N0 : IdealMulLeCertificate' Table 
  ![![-10432, -5981, -908, 623, 1407]] ![![-50, 21, 10, -17, 5]]
  ![![911, 0, 0, 0, 0]] where
 M := ![![![911, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC911 : ContainsPrimesAboveP 911 ![I911N0, I911N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI911N0
    exact isPrimeI911N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 911 (by decide) (𝕀 ⊙ MulI911N0)
instance hp919 : Fact (Nat.Prime 919) := {out := by norm_num}

def I919N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-347, -87, 39, 80, 98]] i)))

def SI919N0: IdealEqSpanCertificate' Table ![![-347, -87, 39, 80, 98]] 
 ![![919, 0, 0, 0, 0], ![0, 919, 0, 0, 0], ![205, 227, 1, 0, 0], ![167, 530, 0, 1, 0], ![510, 864, 0, 0, 1]] where
  M :=![![![-347, -87, 39, 80, 98], ![-1176, -290, 145, 274, 320], ![-3840, -985, 442, 930, 1096], ![-5988, -1471, 697, 1401, 1700], ![-7314, -1813, 889, 1732, 2029]]]
  hmulB := by decide  
  f := ![![![-16745, 10131, 1459, 1228, -2606]], ![![31272, -19120, -2749, -2294, 4912]], ![![3925, -2424, -348, -288, 622]], ![![15035, -9212, -1324, -1103, 2366]], ![![20064, -12327, -1771, -1472, 3165]]]
  g := ![![![-78, -148, 39, 80, 98], ![-261, -495, 145, 274, 320], ![-880, -1677, 442, 930, 1096], ![-1360, -2580, 697, 1401, 1700], ![-1647, -3128, 889, 1732, 2029]]]
  hle1 := by decide   
  hle2 := by decide  


def P919P0 : CertificateIrreducibleZModOfList' 919 2 2 9 [545, 189, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [730, 918], [0, 1]]
 g := ![![[631, 452], [283, 173], [503, 42], [773], [97, 32], [556], [223], [286, 186], [730, 1]], ![[670, 467], [670, 746], [836, 877], [773], [482, 887], [556], [223], [54, 733], [541, 918]]]
 h' := ![![[730, 918], [157, 277], [646, 219], [353, 888], [437, 716], [412, 419], [713, 683], [360, 302], [77, 254], [0, 1]], ![[0, 1], [187, 642], [610, 700], [698, 31], [206, 203], [255, 500], [286, 236], [260, 617], [778, 665], [730, 918]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [553]]
 b := ![[], [627, 736]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI919N0 : CertifiedPrimeIdeal' SI919N0 919 where
  n := 2
  hpos := by decide
  P := [545, 189, 1]
  hirr := P919P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41583, -3395, 18073, 7502, -7680]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1178, -1574, 18073, 7502, -7680]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI919N0 : Ideal.IsPrime I919N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI919N0 B_one_repr
lemma NI919N0 : Nat.card (O ⧸ I919N0) = 844561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI919N0

def I919N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-755, -139, 119, 204, 232]] i)))

def SI919N1: IdealEqSpanCertificate' Table ![![-755, -139, 119, 204, 232]] 
 ![![919, 0, 0, 0, 0], ![0, 919, 0, 0, 0], ![795, 621, 1, 0, 0], ![823, 108, 0, 1, 0], ![529, 291, 0, 0, 1]] where
  M :=![![![-755, -139, 119, 204, 232], ![-2784, -608, 381, 702, 816], ![-9792, -2289, 1252, 2394, 2808], ![-15456, -3759, 1887, 3709, 4380], ![-18732, -4521, 2307, 4506, 5317]]]
  hmulB := by decide  
  f := ![![![4627, -2825, -389, -324, 704]], ![![-8448, 5266, 639, 630, -1296]], ![![-1689, 1104, 94, 144, -264]], ![![3139, -1904, -272, -215, 476]], ![![1, 34, -23, 12, -3]]]
  g := ![![![-420, -178, 119, 204, 232], ![-1431, -599, 381, 702, 816], ![-4854, -2019, 1252, 2394, 2808], ![-7492, -3102, 1887, 3709, 4380], ![-9112, -3777, 2307, 4506, 5317]]]
  hle1 := by decide   
  hle2 := by decide  


def P919P1 : CertificateIrreducibleZModOfList' 919 2 2 9 [592, 861, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 918], [0, 1]]
 g := ![![[655, 724], [458, 233], [215, 495], [208], [737, 468], [895], [865], [303, 225], [58, 1]], ![[373, 195], [187, 686], [436, 424], [208], [311, 451], [895], [865], [487, 694], [116, 918]]]
 h' := ![![[58, 918], [888, 59], [461, 243], [144, 134], [221, 813], [583, 760], [555, 401], [748, 777], [586, 15], [0, 1]], ![[0, 1], [634, 860], [770, 676], [564, 785], [506, 106], [551, 159], [838, 518], [783, 142], [537, 904], [58, 918]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [358]]
 b := ![[], [323, 179]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI919N1 : CertifiedPrimeIdeal' SI919N1 919 where
  n := 2
  hpos := by decide
  P := [592, 861, 1]
  hirr := P919P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3584, -22032, 2226, -8670, 14820]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2696, -5202, 2226, -8670, 14820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI919N1 : Ideal.IsPrime I919N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI919N1 B_one_repr
lemma NI919N1 : Nat.card (O ⧸ I919N1) = 844561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI919N1

def I919N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5012878, 3050013, 438708, 368171, -784347]] i)))

def SI919N2: IdealEqSpanCertificate' Table ![![-5012878, 3050013, 438708, 368171, -784347]] 
 ![![919, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![473, 0, 1, 0, 0], ![634, 0, 0, 1, 0], ![718, 0, 0, 0, 1]] where
  M :=![![![-5012878, 3050013, 438708, 368171, -784347], ![9412164, -5726688, -823717, -691278, 1472684], ![-17672208, 10752409, 1546604, 1297934, -2765112], ![11884590, -7230981, -1040095, -872869, 1859526], ![-12061641, 7338755, 1055588, 885863, -1887254]]]
  hmulB := by decide  
  f := ![![![27668, 2987, -4210, 1923, -1105]], ![![2152, 253, -331, 137, -77]], ![![14140, 1566, -2088, 995, -615]], ![![19358, 2013, -2985, 1365, -756]], ![![21551, 2393, -3276, 1465, -846]]]
  g := ![![![-108087, 3050013, 438708, 368171, -784347], ![202947, -5726688, -823717, -691278, 1472684], ![-381041, 10752409, 1546604, 1297934, -2765112], ![256266, -7230981, -1040095, -872869, 1859526], ![-260060, 7338755, 1055588, 885863, -1887254]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI919N2 : Nat.card (O ⧸ I919N2) = 919 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI919N2)

lemma isPrimeI919N2 : Ideal.IsPrime I919N2 := prime_ideal_of_norm_prime hp919.out _ NI919N2
def MulI919N0 : IdealMulLeCertificate' Table 
  ![![-347, -87, 39, 80, 98]] ![![-755, -139, 119, 204, 232]]
  ![![-2949911, -731920, 351434, 699812, 829482]] where
 M := ![![![-2949911, -731920, 351434, 699812, 829482]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI919N1 : IdealMulLeCertificate' Table 
  ![![-2949911, -731920, 351434, 699812, 829482]] ![![-5012878, 3050013, 438708, 368171, -784347]]
  ![![919, 0, 0, 0, 0]] where
 M := ![![![42729824, 10585961, -5094936, -10139327, -12014087]]]
 hmul := by decide  
 g := ![![![![46496, 11519, -5544, -11033, -13073]]]]
 hle2 := by decide  


def PBC919 : ContainsPrimesAboveP 919 ![I919N0, I919N1, I919N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI919N0
    exact isPrimeI919N1
    exact isPrimeI919N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 919 (by decide) (𝕀 ⊙ MulI919N0 ⊙ MulI919N1)
instance hp929 : Fact (Nat.Prime 929) := {out := by norm_num}

def I929N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211070, 126069, 19114, -12553, -29719]] i)))

def SI929N0: IdealEqSpanCertificate' Table ![![211070, 126069, 19114, -12553, -29719]] 
 ![![929, 0, 0, 0, 0], ![0, 929, 0, 0, 0], ![547, 828, 1, 0, 0], ![218, 283, 0, 1, 0], ![359, 182, 0, 0, 1]] where
  M :=![![![211070, 126069, 19114, -12553, -29719], ![356628, 213018, 32299, -21210, -50212], ![602544, 359925, 54590, -35826, -84840], ![330726, 197551, 29959, -19645, -46546], ![530067, 316663, 48034, -31509, -74618]]]
  hmulB := by decide  
  f := ![![![-1404008, 854245, 122876, 103121, -219683]], ![![2636196, -1603936, -230729, -193614, 412484]], ![![1517576, -923332, -132828, -111455, 237455]], ![![477178, -290327, -41766, -35045, 74664]], ![![-29741, 18098, 2600, 2186, -4653]]]
  g := ![![![3403, -7254, 19114, -12553, -29719], ![5747, -12260, 32299, -21210, -50212], ![9698, -20733, 54590, -35826, -84840], ![5313, -11386, 29959, -19645, -46546], ![8517, -18254, 48034, -31509, -74618]]]
  hle1 := by decide   
  hle2 := by decide  


def P929P0 : CertificateIrreducibleZModOfList' 929 2 2 9 [827, 474, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [455, 928], [0, 1]]
 g := ![![[50, 592], [761], [722], [467], [831], [440, 237], [710], [77, 671], [455, 1]], ![[0, 337], [761], [722], [467], [831], [511, 692], [710], [670, 258], [910, 928]]]
 h' := ![![[455, 928], [835, 39], [441, 804], [485, 844], [486, 112], [288, 855], [603, 548], [422, 100], [889, 889], [0, 1]], ![[0, 1], [0, 890], [235, 125], [828, 85], [351, 817], [62, 74], [42, 381], [401, 829], [340, 40], [455, 928]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [922]]
 b := ![[], [564, 461]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI929N0 : CertifiedPrimeIdeal' SI929N0 929 where
  n := 2
  hpos := by decide
  P := [827, 474, 1]
  hirr := P929P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27405, -26, 16664, 6025, -13612]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5995, -14021, 16664, 6025, -13612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI929N0 : Ideal.IsPrime I929N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI929N0 B_one_repr
lemma NI929N0 : Nat.card (O ⧸ I929N0) = 863041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI929N0

def I929N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2602, 1553, 238, -153, -369]] i)))

def SI929N1: IdealEqSpanCertificate' Table ![![2602, 1553, 238, -153, -369]] 
 ![![929, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![808, 0, 1, 0, 0], ![660, 0, 0, 1, 0], ![682, 0, 0, 0, 1]] where
  M :=![![![2602, 1553, 238, -153, -369], ![4428, 2624, 383, -262, -612], ![7344, 4461, 700, -458, -1048], ![4074, 2415, 401, -217, -610], ![6609, 3907, 548, -399, -894]]]
  hmulB := by decide  
  f := ![![![8844728, -5381391, -774060, -649611, 1383875]], ![![86852, -52843, -7601, -6379, 13589]], ![![7726288, -4700899, -676178, -567466, 1208880]], ![![6261090, -3809429, -547949, -459853, 979630]], ![![6516025, -3964539, -570260, -478577, 1019518]]]
  g := ![![![157, 1553, 238, -153, -369], ![276, 2624, 383, -262, -612], ![441, 4461, 700, -458, -1048], ![229, 2415, 401, -217, -610], ![424, 3907, 548, -399, -894]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI929N1 : Nat.card (O ⧸ I929N1) = 929 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI929N1)

lemma isPrimeI929N1 : Ideal.IsPrime I929N1 := prime_ideal_of_norm_prime hp929.out _ NI929N1

def I929N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-824, -473, -72, 49, 111]] i)))

def SI929N2: IdealEqSpanCertificate' Table ![![-824, -473, -72, 49, 111]] 
 ![![929, 0, 0, 0, 0], ![235, 1, 0, 0, 0], ![515, 0, 1, 0, 0], ![684, 0, 0, 1, 0], ![775, 0, 0, 0, 1]] where
  M :=![![![-824, -473, -72, 49, 111], ![-1332, -834, -127, 78, 196], ![-2352, -1341, -206, 138, 312], ![-1206, -775, -121, 67, 178], ![-2043, -1183, -184, 117, 272]]]
  hmulB := by decide  
  f := ![![![-4606, 1263, 1310, -917, 67]], ![![-1166, 317, 335, -229, 13]], ![![-2506, 696, 702, -509, 49]], ![![-3462, 949, 985, -689, 50]], ![![-3821, 1042, 1094, -754, 47]]]
  g := ![![![30, -473, -72, 49, 111], ![59, -834, -127, 78, 196], ![89, -1341, -206, 138, 312], ![64, -775, -121, 67, 178], ![86, -1183, -184, 117, 272]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI929N2 : Nat.card (O ⧸ I929N2) = 929 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI929N2)

lemma isPrimeI929N2 : Ideal.IsPrime I929N2 := prime_ideal_of_norm_prime hp929.out _ NI929N2

def I929N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 262, 40, -26, -62]] i)))

def SI929N3: IdealEqSpanCertificate' Table ![![439, 262, 40, -26, -62]] 
 ![![929, 0, 0, 0, 0], ![784, 1, 0, 0, 0], ![342, 0, 1, 0, 0], ![249, 0, 0, 1, 0], ![800, 0, 0, 0, 1]] where
  M :=![![![439, 262, 40, -26, -62], ![744, 443, 66, -44, -104], ![1248, 750, 115, -76, -176], ![684, 410, 66, -39, -100], ![1110, 658, 96, -66, -153]]]
  hmulB := by decide  
  f := ![![![-61, -646, 16, 146, 350]], ![![-56, -545, 14, 124, 296]], ![![-30, -242, 7, 56, 132]], ![![-33, -176, 6, 43, 98]], ![![-70, -562, 16, 130, 307]]]
  g := ![![![-175, 262, 40, -26, -62], ![-296, 443, 66, -44, -104], ![-502, 750, 115, -76, -176], ![-273, 410, 66, -39, -100], ![-440, 658, 96, -66, -153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI929N3 : Nat.card (O ⧸ I929N3) = 929 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI929N3)

lemma isPrimeI929N3 : Ideal.IsPrime I929N3 := prime_ideal_of_norm_prime hp929.out _ NI929N3
def MulI929N0 : IdealMulLeCertificate' Table 
  ![![211070, 126069, 19114, -12553, -29719]] ![![2602, 1553, 238, -153, -369]]
  ![![1000257095, 597436692, 90579122, -59496118, -140844414]] where
 M := ![![![1000257095, 597436692, 90579122, -59496118, -140844414]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI929N1 : IdealMulLeCertificate' Table 
  ![![1000257095, 597436692, 90579122, -59496118, -140844414]] ![![-824, -473, -72, 49, 111]]
  ![![-1473542158858, -880121976453, -133437867402, 87647542123, 207486825629]] where
 M := ![![![-1473542158858, -880121976453, -133437867402, 87647542123, 207486825629]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI929N2 : IdealMulLeCertificate' Table 
  ![![-1473542158858, -880121976453, -133437867402, 87647542123, 207486825629]] ![![439, 262, 40, -26, -62]]
  ![![929, 0, 0, 0, 0]] where
 M := ![![![-1177964921477068, -703578658206663, -106671618510946, 70066356382481, 165867125529523]]]
 hmul := by decide  
 g := ![![![![-1267992380492, -757350547047, -114824131874, 75421266289, 178543730387]]]]
 hle2 := by decide  


def PBC929 : ContainsPrimesAboveP 929 ![I929N0, I929N1, I929N2, I929N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI929N0
    exact isPrimeI929N1
    exact isPrimeI929N2
    exact isPrimeI929N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 929 (by decide) (𝕀 ⊙ MulI929N0 ⊙ MulI929N1 ⊙ MulI929N2)
instance hp937 : Fact (Nat.Prime 937) := {out := by norm_num}

def I937N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5141, 1217, -645, -1266, -1490]] i)))

def SI937N0: IdealEqSpanCertificate' Table ![![5141, 1217, -645, -1266, -1490]] 
 ![![937, 0, 0, 0, 0], ![0, 937, 0, 0, 0], ![0, 0, 937, 0, 0], ![0, 0, 0, 937, 0], ![294, 723, 928, 392, 1]] where
  M :=![![![5141, 1217, -645, -1266, -1490], ![17880, 4272, -2211, -4270, -5064], ![60768, 14875, -7444, -14550, -17080], ![93540, 23261, -11067, -22389, -26568], ![114558, 28079, -13833, -27160, -32195]]]
  hmulB := by decide  
  f := ![![![-247, 149, 21, 18, -38]], ![![456, -282, -39, -34, 72]], ![![-864, 523, 74, 66, -136]], ![![588, -355, -57, -45, 96]], ![![-336, 199, 26, 26, -51]]]
  g := ![![![473, 1151, 1475, 622, -1490], ![1608, 3912, 5013, 2114, -5064], ![5424, 13195, 16908, 7130, -17080], ![8436, 20525, 26301, 11091, -26568], ![10224, 24872, 31871, 13440, -32195]]]
  hle1 := by decide   
  hle2 := by decide  


def P937P0 : CertificateIrreducibleZModOfList' 937 4 2 9 [884, 703, 137, 795, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [548, 857, 779, 839], [213, 268, 263, 764], [318, 748, 832, 271], [0, 1]]
 g := ![![[470, 571, 239, 477], [300, 430, 300], [12, 371, 81], [240, 904, 266, 861], [776, 621, 70], [715, 797, 891, 786], [121, 611, 835], [496, 350, 142, 1], []], ![[455, 664, 451, 827, 485, 174], [323, 546, 499], [139, 9, 4], [384, 664, 634, 527, 126, 876], [826, 526, 612], [823, 891, 536, 131, 25, 455], [840, 796, 863], [898, 713, 782, 856, 880, 322], [51, 690, 234, 268, 318, 493]], ![[913, 683, 825, 908, 874, 764], [186, 429, 744], [878, 55, 416], [582, 815, 493, 184, 433, 187], [825, 847, 509], [16, 687, 74, 51, 814, 252], [555, 16, 422], [422, 568, 32, 257, 914, 601], [592, 160, 741, 163, 620, 145]], ![[848, 542, 562, 831, 218, 272], [930, 518, 911], [786, 838, 108], [815, 36, 63, 749, 169, 100], [650, 359, 277], [504, 844, 871, 35, 89, 715], [219, 14, 410], [798, 709, 813, 138, 644, 323], [842, 73, 417, 60, 265, 631]]]
 h' := ![![[548, 857, 779, 839], [629, 83, 339, 872], [687, 540, 709, 187], [539, 509, 683, 9], [654, 884, 916, 406], [415, 893, 146, 658], [684, 868, 754, 387], [52, 623, 860, 480], [0, 0, 0, 1], [0, 1]], ![[213, 268, 263, 764], [227, 207, 768, 896], [781, 19, 228, 865], [61, 682, 374, 935], [490, 551, 523, 659], [667, 91, 773, 669], [505, 490, 646, 854], [906, 246, 509, 556], [237, 860, 375, 85], [548, 857, 779, 839]], ![[318, 748, 832, 271], [430, 480, 720, 936], [702, 752, 488, 41], [9, 803, 753, 443], [156, 873, 450, 345], [242, 60, 420, 833], [464, 710, 19, 608], [875, 51, 729, 135], [771, 102, 563, 17], [213, 268, 263, 764]], ![[0, 1], [572, 167, 47, 107], [484, 563, 449, 781], [422, 817, 64, 487], [865, 503, 922, 464], [412, 830, 535, 651], [332, 743, 455, 25], [229, 17, 713, 703], [179, 912, 936, 834], [318, 748, 832, 271]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [922, 579, 535], []]
 b := ![[], [], [335, 935, 7, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI937N0 : CertifiedPrimeIdeal' SI937N0 937 where
  n := 4
  hpos := by decide
  P := [884, 703, 137, 795, 1]
  hirr := P937P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43893349, 6051844, -35633275, -14297613, 27761135]
  a := ![-1, -4, -2, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8663693, -21414353, -27532515, -11629309, 27761135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI937N0 : Ideal.IsPrime I937N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI937N0 B_one_repr
lemma NI937N0 : Nat.card (O ⧸ I937N0) = 770829564961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI937N0

def I937N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![247, -149, -21, -18, 38]] i)))

def SI937N1: IdealEqSpanCertificate' Table ![![247, -149, -21, -18, 38]] 
 ![![937, 0, 0, 0, 0], ![306, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![362, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![247, -149, -21, -18, 38], ![-456, 282, 39, 34, -72], ![864, -523, -74, -66, 136], ![-588, 355, 57, 45, -96], ![606, -359, -57, -44, 95]]]
  hmulB := by decide  
  f := ![![![-5141, -1217, 645, 1266, 1490]], ![![-1698, -402, 213, 418, 492]], ![![-416, -99, 52, 102, 120]], ![![-2086, -495, 261, 513, 604]], ![![-435, -104, 54, 106, 125]]]
  g := ![![![55, -149, -21, -18, 38], ![-104, 282, 39, 34, -72], ![194, -523, -74, -66, 136], ![-132, 355, 57, 45, -96], ![133, -359, -57, -44, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI937N1 : Nat.card (O ⧸ I937N1) = 937 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI937N1)

lemma isPrimeI937N1 : Ideal.IsPrime I937N1 := prime_ideal_of_norm_prime hp937.out _ NI937N1
def MulI937N0 : IdealMulLeCertificate' Table 
  ![![5141, 1217, -645, -1266, -1490]] ![![247, -149, -21, -18, 38]]
  ![![937, 0, 0, 0, 0]] where
 M := ![![![-937, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC937 : ContainsPrimesAboveP 937 ![I937N0, I937N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI937N0
    exact isPrimeI937N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 937 (by decide) (𝕀 ⊙ MulI937N0)
instance hp941 : Fact (Nat.Prime 941) := {out := by norm_num}

def I941N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![162031, -98589, -14179, -11900, 25352]] i)))

def SI941N0: IdealEqSpanCertificate' Table ![![162031, -98589, -14179, -11900, 25352]] 
 ![![941, 0, 0, 0, 0], ![0, 941, 0, 0, 0], ![0, 0, 941, 0, 0], ![772, 50, 720, 1, 0], ![616, 487, 528, 0, 1]] where
  M :=![![![162031, -98589, -14179, -11900, 25352], ![-304224, 185104, 26619, 22346, -47600], ![571200, -347551, -49988, -41962, 89384], ![-384192, 233727, 33645, 28223, -60124], ![389916, -237223, -34143, -28634, 61015]]]
  hmulB := by decide  
  f := ![![![-253, -133, -13, 28, 48]], ![![-576, -246, 3, 70, 112]], ![![-1344, -531, 62, 230, 280]], ![![-1268, -529, 37, 203, 260]], ![![-1220, -513, 28, 184, 247]]]
  g := ![![![-6661, -12593, -5135, -11900, 25352], ![12504, 23644, 9639, 22346, -47600], ![-23480, -44399, -18100, -41962, 89384], ![15796, 29865, 12177, 28223, -60124], ![-16036, -30308, -12363, -28634, 61015]]]
  hle1 := by decide   
  hle2 := by decide  


def P941P0 : CertificateIrreducibleZModOfList' 941 3 2 9 [732, 366, 495, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [221, 34, 506], [225, 906, 435], [0, 1]]
 g := ![![[834, 843, 805], [895, 189], [148, 442, 33], [496, 563, 194], [357, 372], [868, 681, 9], [686, 428], [143, 52, 365], [1]], ![[499, 388, 41, 15], [376, 134], [9, 597, 925, 442], [525, 899, 79, 50], [669, 462], [939, 911, 280, 603], [275, 887], [858, 300, 692, 241], [168, 725, 438, 159]], ![[217, 808, 500, 141], [122, 459], [845, 505, 783, 286], [762, 827, 387, 379], [641, 14], [914, 117, 369, 765], [317, 30], [609, 545, 304, 432], [465, 866, 251, 782]]]
 h' := ![![[221, 34, 506], [322, 151, 294], [820, 761, 182], [154, 836, 534], [212, 549, 843], [740, 492, 833], [153, 856, 3], [716, 329, 37], [209, 575, 446], [0, 1]], ![[225, 906, 435], [642, 890, 246], [535, 842, 414], [705, 436, 637], [818, 6, 806], [301, 312, 544], [110, 389, 171], [6, 813, 504], [886, 770, 568], [221, 34, 506]], ![[0, 1], [854, 841, 401], [827, 279, 345], [514, 610, 711], [8, 386, 233], [531, 137, 505], [707, 637, 767], [18, 740, 400], [82, 537, 868], [225, 906, 435]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [281, 524], []]
 b := ![[], [402, 694, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI941N0 : CertifiedPrimeIdeal' SI941N0 941 where
  n := 3
  hpos := by decide
  P := [732, 366, 495, 1]
  hirr := P941P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55483284, -16670867, 9534447, 15813166, 13111888]
  a := ![3, -11, -14, -1, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21615484, -7643803, -19446357, 15813166, 13111888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI941N0 : Ideal.IsPrime I941N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI941N0 B_one_repr
lemma NI941N0 : Nat.card (O ⧸ I941N0) = 833237621 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI941N0

def I941N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, 133, 13, -28, -48]] i)))

def SI941N1: IdealEqSpanCertificate' Table ![![253, 133, 13, -28, -48]] 
 ![![941, 0, 0, 0, 0], ![0, 941, 0, 0, 0], ![473, 442, 1, 0, 0], ![859, 419, 0, 1, 0], ![798, 245, 0, 0, 1]] where
  M :=![![![253, 133, 13, -28, -48], ![576, 246, -3, -70, -112], ![1344, 531, -62, -230, -280], ![1392, 493, -63, -307, -404], ![2028, 635, -159, -366, -475]]]
  hmulB := by decide  
  f := ![![![-162031, 98589, 14179, 11900, -25352]], ![![304224, -185104, -26619, -22346, 47600]], ![![60845, -37020, -5323, -4470, 9520]], ![![-12041, 7328, 1055, 883, -1884]], ![![-58614, 35665, 5130, 4304, -9171]]]
  g := ![![![60, 19, 13, -28, -48], ![161, 62, -3, -70, -112], ![480, 205, -62, -230, -280], ![656, 272, -63, -307, -404], ![819, 362, -159, -366, -475]]]
  hle1 := by decide   
  hle2 := by decide  


def P941P1 : CertificateIrreducibleZModOfList' 941 2 2 9 [651, 898, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 940], [0, 1]]
 g := ![![[250, 438], [409], [406, 864], [206, 133], [30], [448, 778], [70], [598, 179], [43, 1]], ![[264, 503], [409], [859, 77], [279, 808], [30], [26, 163], [70], [767, 762], [86, 940]]]
 h' := ![![[43, 940], [95, 863], [115, 721], [457, 176], [311, 622], [62, 541], [494, 479], [276, 171], [237, 257], [0, 1]], ![[0, 1], [505, 78], [65, 220], [497, 765], [709, 319], [741, 400], [389, 462], [101, 770], [937, 684], [43, 940]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [344]]
 b := ![[], [66, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI941N1 : CertifiedPrimeIdeal' SI941N1 941 where
  n := 2
  hpos := by decide
  P := [651, 898, 1]
  hirr := P941P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15925, -7480, -1283, 785, 19028]
  a := ![1, -6, -8, -2, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16225, -4709, -1283, 785, 19028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI941N1 : Ideal.IsPrime I941N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI941N1 B_one_repr
lemma NI941N1 : Nat.card (O ⧸ I941N1) = 885481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI941N1
def MulI941N0 : IdealMulLeCertificate' Table 
  ![![162031, -98589, -14179, -11900, 25352]] ![![253, 133, 13, -28, -48]]
  ![![941, 0, 0, 0, 0]] where
 M := ![![![-941, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC941 : ContainsPrimesAboveP 941 ![I941N0, I941N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI941N0
    exact isPrimeI941N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 941 (by decide) (𝕀 ⊙ MulI941N0)
instance hp947 : Fact (Nat.Prime 947) := {out := by norm_num}

def I947N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![947, 0, 0, 0, 0]] i)))

def SI947N0: IdealEqSpanCertificate' Table ![![947, 0, 0, 0, 0]] 
 ![![947, 0, 0, 0, 0], ![0, 947, 0, 0, 0], ![0, 0, 947, 0, 0], ![0, 0, 0, 947, 0], ![0, 0, 0, 0, 947]] where
  M :=![![![947, 0, 0, 0, 0], ![0, 947, 0, 0, 0], ![0, 0, 947, 0, 0], ![0, 0, 0, 947, 0], ![0, 0, 0, 0, 947]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P947P0 : CertificateIrreducibleZModOfList' 947 5 2 9 [489, 120, 735, 810, 922, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [390, 214, 111, 65, 602], [655, 323, 770, 13, 255], [380, 851, 219, 856, 366], [494, 505, 794, 13, 671], [0, 1]]
 g := ![![[708, 692, 100, 460, 81], [686, 43, 716, 449, 769], [694, 75, 6, 908], [766, 118, 874, 237], [722, 715, 73, 813, 818], [226, 344, 854, 32, 161], [110, 146, 425, 734], [762, 25, 1], []], ![[640, 232, 576, 783, 152, 594, 774, 397], [542, 114, 321, 47, 213, 708, 344, 598], [271, 688, 69, 923], [205, 629, 325, 505], [129, 76, 632, 678, 887, 280, 97, 813], [108, 15, 228, 543, 760, 70, 786, 840], [877, 339, 802, 363], [514, 879, 485, 906, 907, 608, 819, 208], [612, 804, 212, 681, 343, 120, 789, 189]], ![[365, 747, 259, 397, 232, 809, 503, 123], [534, 321, 774, 559, 654, 194, 259, 329], [33, 652, 280, 427], [668, 658, 251, 3], [575, 745, 649, 900, 778, 643, 499, 355], [782, 540, 743, 762, 230, 53, 424, 249], [788, 551, 663, 250], [733, 942, 406, 436, 734, 711, 281, 124], [598, 657, 398, 932, 599, 627, 186, 352]], ![[22, 585, 754, 97, 783, 219, 425, 124], [5, 839, 140, 904, 536, 506, 407, 215], [116, 314, 723, 890], [6, 913, 581, 427], [611, 42, 68, 855, 262, 342, 895, 27], [358, 664, 726, 610, 748, 5, 122, 555], [159, 765, 464, 740], [290, 262, 315, 889, 746, 66, 823, 877], [374, 414, 612, 494, 740, 925, 346, 759]], ![[220, 433, 271, 473, 767, 718, 615, 356], [254, 12, 36, 251, 732, 336, 234, 427], [551, 224, 164, 942], [336, 340, 528, 942], [19, 20, 522, 453, 876, 745, 40, 366], [375, 508, 412, 724, 621, 545, 737, 421], [101, 582, 0, 914], [728, 96, 118, 606, 498, 404, 381, 253], [405, 70, 314, 50, 573, 608, 82, 718]]]
 h' := ![![[390, 214, 111, 65, 602], [731, 535, 415, 597, 9], [788, 527, 649, 929, 732], [63, 385, 221, 757, 603], [173, 75, 304, 631, 474], [285, 309, 308, 354, 415], [181, 885, 668, 869, 663], [500, 505, 853, 669, 906], [0, 0, 0, 1], [0, 1]], ![[655, 323, 770, 13, 255], [715, 944, 54, 117, 27], [728, 467, 476, 820, 841], [573, 29, 489, 24, 665], [121, 731, 700, 285, 427], [751, 82, 42, 298, 448], [186, 414, 179, 801, 908], [525, 732, 323, 127, 687], [798, 464, 633, 456, 570], [390, 214, 111, 65, 602]], ![[380, 851, 219, 856, 366], [904, 99, 459, 776, 205], [530, 146, 888, 924, 160], [66, 739, 22, 530, 84], [368, 44, 34, 885, 579], [211, 29, 903, 220, 51], [175, 928, 828, 792, 232], [770, 716, 668, 721, 555], [690, 720, 910, 855, 299], [655, 323, 770, 13, 255]], ![[494, 505, 794, 13, 671], [210, 650, 632, 867, 58], [715, 618, 731, 23, 250], [654, 59, 806, 516, 872], [606, 319, 42, 808, 84], [917, 162, 929, 32, 863], [670, 382, 424, 176, 516], [86, 807, 202, 394, 578], [811, 146, 797, 946, 848], [380, 851, 219, 856, 366]], ![[0, 1], [868, 613, 334, 484, 648], [33, 136, 97, 145, 858], [90, 682, 356, 67, 617], [766, 725, 814, 232, 330], [786, 365, 659, 43, 117], [190, 232, 742, 203, 522], [243, 81, 795, 930, 115], [562, 564, 501, 583, 177], [494, 505, 794, 13, 671]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [855, 784, 328, 453], [], [], []]
 b := ![[], [584, 23, 107, 852, 306], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI947N0 : CertifiedPrimeIdeal' SI947N0 947 where
  n := 5
  hpos := by decide
  P := [489, 120, 735, 810, 922, 1]
  hirr := P947P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7873711231, 403914440, 1950176040, -53969530, 679889180]
  a := ![4, 2, 2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8314373, 426520, 2059320, -56990, 717940]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI947N0 : Ideal.IsPrime I947N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI947N0 B_one_repr
lemma NI947N0 : Nat.card (O ⧸ I947N0) = 761640264209507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI947N0

def PBC947 : ContainsPrimesAboveP 947 ![I947N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI947N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![947, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 947 (by decide) 𝕀

instance hp953 : Fact (Nat.Prime 953) := {out := by norm_num}

def I953N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![201841, -122828, -17662, -14820, 31590]] i)))

def SI953N0: IdealEqSpanCertificate' Table ![![201841, -122828, -17662, -14820, 31590]] 
 ![![953, 0, 0, 0, 0], ![0, 953, 0, 0, 0], ![0, 0, 953, 0, 0], ![484, 302, 243, 1, 0], ![280, 179, 570, 0, 1]] where
  M :=![![![201841, -122828, -17662, -14820, 31590], ![-379080, 230589, 33172, 27856, -59280], ![711360, -433044, -62243, -52216, 111424], ![-479004, 291084, 41956, 35253, -74792], ![485286, -295648, -42476, -35562, 76145]]]
  hmulB := by decide  
  f := ![![![45341, 27076, 4102, -2696, -6382]], ![![76584, 45757, 6940, -4560, -10784]], ![![129408, 77300, 11741, -7688, -18240]], ![![80368, 48006, 7283, -4779, -11320]], ![![105226, 62855, 9542, -6254, -14827]]]
  g := ![![![-1543, -1366, -15134, -14820, 31590], ![2872, 2549, 28388, 27856, -59280], ![-5472, -4836, -53395, -52216, 111424], ![3568, 3182, 35789, 35253, -74792], ![-3802, -3343, -36520, -35562, 76145]]]
  hle1 := by decide   
  hle2 := by decide  


def P953P0 : CertificateIrreducibleZModOfList' 953 3 2 9 [278, 145, 909, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [920, 685, 229], [77, 267, 724], [0, 1]]
 g := ![![[792, 474, 701], [707, 284], [47, 401], [594, 549, 50], [203, 851, 114], [26, 202, 127], [737, 489], [612, 949, 30], [1]], ![[762, 330, 588, 935], [741, 607], [662, 221], [681, 857, 205, 757], [431, 263, 926, 639], [835, 70, 947, 67], [704, 296], [566, 649, 876, 259], [480, 258, 916, 236]], ![[166, 742, 222, 946], [175, 235], [136, 855], [290, 350, 818, 371], [749, 669, 886, 420], [710, 940, 102, 104], [779, 727], [619, 557, 793, 128], [386, 382, 912, 717]]]
 h' := ![![[920, 685, 229], [853, 823, 520], [829, 779, 64], [690, 415, 391], [746, 398, 399], [396, 96, 837], [421, 743, 689], [451, 139, 676], [675, 808, 44], [0, 1]], ![[77, 267, 724], [833, 454, 428], [909, 116, 114], [560, 270, 255], [231, 441, 404], [462, 211, 542], [449, 855, 547], [744, 576, 757], [257, 924, 462], [920, 685, 229]], ![[0, 1], [44, 629, 5], [278, 58, 775], [331, 268, 307], [803, 114, 150], [406, 646, 527], [707, 308, 670], [148, 238, 473], [427, 174, 447], [77, 267, 724]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [650, 278], []]
 b := ![[], [884, 389, 777], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI953N0 : CertifiedPrimeIdeal' SI953N0 953 where
  n := 3
  hpos := by decide
  P := [278, 145, 909, 1]
  hirr := P953P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![894436573, 466293453, -9014373, -410332535, -391855886]
  a := ![7, 23, 45, -23, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![324464881, 204122689, 338992284, -410332535, -391855886]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI953N0 : Ideal.IsPrime I953N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI953N0 B_one_repr
lemma NI953N0 : Nat.card (O ⧸ I953N0) = 865523177 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI953N0

def I953N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8419, -5092, -760, -610, 1318]] i)))

def SI953N1: IdealEqSpanCertificate' Table ![![8419, -5092, -760, -610, 1318]] 
 ![![953, 0, 0, 0, 0], ![110, 1, 0, 0, 0], ![289, 0, 1, 0, 0], ![251, 0, 0, 1, 0], ![417, 0, 0, 0, 1]] where
  M :=![![![8419, -5092, -760, -610, 1318], ![-15816, 9587, 1400, 1116, -2440], ![29280, -17972, -2405, -2080, 4464], ![-18876, 11916, 1322, 1501, -2940], ![19506, -12088, -1564, -1570, 3123]]]
  hmulB := by decide  
  f := ![![![-345624097, -206435572, -31298348, 20557962, 48666666]], ![![-40506454, -24193837, -3668104, 2409352, 5703636]], ![![-105846953, -63220640, -9585081, 6295850, 14904106]], ![![-91598455, -54710248, -8294794, 5448339, 12897802]], ![![-152144235, -90873244, -13777580, 9049644, 21423137]]]
  g := ![![![411, -5092, -760, -610, 1318], ![-774, 9587, 1400, 1116, -2440], ![1429, -17972, -2405, -2080, 4464], ![-905, 11916, 1322, 1501, -2940], ![937, -12088, -1564, -1570, 3123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI953N1 : Nat.card (O ⧸ I953N1) = 953 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI953N1)

lemma isPrimeI953N1 : Ideal.IsPrime I953N1 := prime_ideal_of_norm_prime hp953.out _ NI953N1

def I953N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-158, 89, 14, 13, -21]] i)))

def SI953N2: IdealEqSpanCertificate' Table ![![-158, 89, 14, 13, -21]] 
 ![![953, 0, 0, 0, 0], ![357, 1, 0, 0, 0], ![253, 0, 1, 0, 0], ![405, 0, 0, 1, 0], ![760, 0, 0, 0, 1]] where
  M :=![![![-158, 89, 14, 13, -21], ![252, -178, -21, -14, 52], ![-624, 297, 58, 62, -56], ![210, -253, -15, 9, 98], ![-543, 175, 54, 69, -6]]]
  hmulB := by decide  
  f := ![![![-22288, -13239, -1936, 1331, 3079]], ![![-8388, -4983, -729, 501, 1159]], ![![-5984, -3554, -520, 357, 827]], ![![-9510, -5648, -825, 568, 1313]], ![![-17831, -10593, -1550, 1065, 2464]]]
  g := ![![![-26, 89, 14, 13, -21], ![37, -178, -21, -14, 52], ![-109, 297, 58, 62, -56], ![17, -253, -15, 9, 98], ![-105, 175, 54, 69, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI953N2 : Nat.card (O ⧸ I953N2) = 953 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI953N2)

lemma isPrimeI953N2 : Ideal.IsPrime I953N2 := prime_ideal_of_norm_prime hp953.out _ NI953N2
def MulI953N0 : IdealMulLeCertificate' Table 
  ![![201841, -122828, -17662, -14820, 31590]] ![![8419, -5092, -760, -610, 1318]]
  ![![4020740527, -2446359984, -351880050, -295303218, 629109960]] where
 M := ![![![4020740527, -2446359984, -351880050, -295303218, 629109960]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI953N1 : IdealMulLeCertificate' Table 
  ![![4020740527, -2446359984, -351880050, -295303218, 629109960]] ![![-158, 89, 14, 13, -21]]
  ![![953, 0, 0, 0, 0]] where
 M := ![![![-1435806952094, 873595566359, 125656370252, 105452961805, -224655362559]]]
 hmul := by decide  
 g := ![![![![-1506617998, 916679503, 131853484, 110653685, -235734903]]]]
 hle2 := by decide  


def PBC953 : ContainsPrimesAboveP 953 ![I953N0, I953N1, I953N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI953N0
    exact isPrimeI953N1
    exact isPrimeI953N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 953 (by decide) (𝕀 ⊙ MulI953N0 ⊙ MulI953N1)


lemma PB1705I17_primes (p : ℕ) :
  p ∈ Set.range ![887, 907, 911, 919, 929, 937, 941, 947, 953] ↔ Nat.Prime p ∧ 883 < p ∧ p ≤ 953 := by
  rw [← List.mem_ofFn']
  convert primes_range 883 953 (by omega)

def PB1705I17 : PrimesBelowBoundCertificateInterval O 883 953 1705 where
  m := 9
  g := ![3, 4, 2, 3, 4, 2, 2, 1, 3]
  P := ![887, 907, 911, 919, 929, 937, 941, 947, 953]
  hP := PB1705I17_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I887N0, I887N1, I887N2]
    · exact ![I907N0, I907N1, I907N2, I907N3]
    · exact ![I911N0, I911N1]
    · exact ![I919N0, I919N1, I919N2]
    · exact ![I929N0, I929N1, I929N2, I929N3]
    · exact ![I937N0, I937N1]
    · exact ![I941N0, I941N1]
    · exact ![I947N0]
    · exact ![I953N0, I953N1, I953N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC887
    · exact PBC907
    · exact PBC911
    · exact PBC919
    · exact PBC929
    · exact PBC937
    · exact PBC941
    · exact PBC947
    · exact PBC953
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![697864103, 887, 887]
    · exact ![822649, 907, 907, 907]
    · exact ![756058031, 829921]
    · exact ![844561, 844561, 919]
    · exact ![863041, 929, 929, 929]
    · exact ![770829564961, 937]
    · exact ![833237621, 885481]
    · exact ![761640264209507]
    · exact ![865523177, 953, 953]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI887N0
      exact NI887N1
      exact NI887N2
    · dsimp ; intro j
      fin_cases j
      exact NI907N0
      exact NI907N1
      exact NI907N2
      exact NI907N3
    · dsimp ; intro j
      fin_cases j
      exact NI911N0
      exact NI911N1
    · dsimp ; intro j
      fin_cases j
      exact NI919N0
      exact NI919N1
      exact NI919N2
    · dsimp ; intro j
      fin_cases j
      exact NI929N0
      exact NI929N1
      exact NI929N2
      exact NI929N3
    · dsimp ; intro j
      fin_cases j
      exact NI937N0
      exact NI937N1
    · dsimp ; intro j
      fin_cases j
      exact NI941N0
      exact NI941N1
    · dsimp ; intro j
      fin_cases j
      exact NI947N0
    · dsimp ; intro j
      fin_cases j
      exact NI953N0
      exact NI953N1
      exact NI953N2
  β := ![I887N1, I887N2, I907N1, I907N2, I907N3, I919N2, I929N1, I929N2, I929N3, I937N1, I953N1, I953N2]
  Il := ![[I887N1, I887N2], [I907N1, I907N2, I907N3], [], [I919N2], [I929N1, I929N2, I929N3], [I937N1], [], [], [I953N1, I953N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
