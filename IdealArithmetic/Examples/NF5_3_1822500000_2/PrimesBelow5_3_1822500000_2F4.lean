
import IdealArithmetic.Examples.NF5_3_1822500000_2.RI5_3_1822500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8405, -34956, 11383, 18489, 56166]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-8405, -34956, 11383, 18489, 56166]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![68, 12, 48, 1, 0], ![2, 15, 91, 0, 1]] where
  M :=![![![-8405, -34956, 11383, 18489, 56166], ![-16776, -70163, 22923, 37177, 112962], ![-34344, -141186, 45632, 74381, 225866], ![-65352, -281994, 93709, 150826, 458898], ![41952, 177414, -58308, -94316, -286725]]]
  hmulB := by decide  
  f := ![![![12103, 2076, 1635, 2735, 8854]], ![![-15576, -1943, -1911, -3279, -10570]], ![![17592, 858, 1800, 3259, 10418]], ![![9332, 1026, 1107, 1918, 6174]], ![![8822, 327, 875, 1600, 5107]]]
  g := ![![![-8777, -7002, -38135, 18489, 56166], ![-17648, -14081, -76695, 37177, 112962], ![-35312, -28164, -153366, 74381, 225866], ![-71588, -57168, -311501, 150826, 458898], ![44770, 35733, 194655, -94316, -286725]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [139, 140, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 149, 40], [118, 7, 117], [0, 1]]
 g := ![![[110, 79, 109], [79, 90], [70, 146, 57], [27, 156, 36], [7, 20, 19], [57, 1], []], ![[156, 119, 29, 76], [144, 90], [56, 26, 91, 145], [148, 112, 51, 3], [153, 77, 89, 9], [2, 49], [128, 30]], ![[134, 59, 152, 9], [132, 46], [79, 76, 35, 27], [136, 141, 117, 109], [150, 16, 35, 71], [77, 64], [51, 30]]]
 h' := ![![[96, 149, 40], [25, 139, 57], [4, 118, 103], [15, 146, 34], [126, 156, 6], [84, 45, 126], [0, 0, 1], [0, 1]], ![[118, 7, 117], [90, 51, 150], [139, 20, 103], [23, 16, 112], [70, 23, 2], [63, 112, 13], [59, 81, 7], [96, 149, 40]], ![[0, 1], [20, 124, 107], [129, 19, 108], [3, 152, 11], [41, 135, 149], [121, 0, 18], [84, 76, 149], [118, 7, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152, 144], []]
 b := ![[], [125, 64, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [139, 140, 100, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3207927905, -398140853, -4185925181, -3132174388, -9098504181]
  a := ![-180, -61, -183, -126, -395]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1452082413, 1106149774, 6204600802, -3132174388, -9098504181]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 50, -23, -39, -120]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-37, 50, -23, -39, -120]] 
 ![![157, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![132, 0, 1, 0, 0], ![125, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![-37, 50, -23, -39, -120], ![72, 107, -37, -53, -162], ![72, 258, -36, -95, -274], ![-264, 258, -375, -402, -1310], ![72, -228, 158, 200, 633]]]
  hmulB := by decide  
  f := ![![![-36121, 1606, -61611, -46677, -129704]], ![![-2729, 121, -4654, -3526, -9798]], ![![-41196, 1830, -70264, -53233, -147922]], ![![-103025, 4568, -175700, -133115, -369898]], ![![6529, -286, 11127, 8431, 23429]]]
  g := ![![![112, 50, -23, -39, -120], ![156, 107, -37, -53, -162], ![243, 258, -36, -95, -274], ![1318, 258, -375, -402, -1310], ![-619, -228, 158, 200, 633]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5303, 2264, 3131, 2187, 7888]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![5303, 2264, 3131, 2187, 7888]] 
 ![![157, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![137, 0, 0, 0, 1]] where
  M :=![![![5303, 2264, 3131, 2187, 7888], ![-31848, -13201, -19509, -13727, -48854], ![184152, 78390, 108370, 75805, 273834], ![-1114056, -461034, -686027, -482724, -1714510], ![310344, 127938, 192196, 135344, 479717]]]
  hmulB := by decide  
  f := ![![![5853899, 2176528, 1102247, 1710789, 5610576]], ![![3804640, 1418959, 717545, 1113341, 3651438]], ![![762511, 270578, 140141, 218564, 716170]], ![![4116436, 1558550, 782539, 1212292, 3977078]], ![![5110903, 1896386, 961313, 1492363, 4894057]]]
  g := ![![![-10304, 2264, 3131, 2187, 7888], ![63427, -13201, -19509, -13727, -48854], ![-357448, 78390, 108370, 75805, 273834], ![2225349, -461034, -686027, -482724, -1714510], ![-622189, 127938, 192196, 135344, 479717]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-8405, -34956, 11383, 18489, 56166]] ![![-37, 50, -23, -39, -120]]
  ![![-2223415, -9259414, 3017752, 4899700, 14885018]] where
 M := ![![![-2223415, -9259414, 3017752, 4899700, 14885018]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-2223415, -9259414, 3017752, 4899700, 14885018]] ![![5303, 2264, 3131, 2187, 7888]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-236043377, -807564982, 228607229, 397151125, 1195748110]]]
 hmul := by decide  
 g := ![![![![-1503461, -5143726, 1456097, 2529625, 7616230]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10387, -955, 18772, 14273, 39362]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![10387, -955, 18772, 14273, 39362]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![18, 56, 87, 61, 1]] where
  M :=![![![10387, -955, 18772, 14273, 39362], ![82968, -1319, 135648, 102630, 287034], ![500544, -37218, 888889, 674604, 1863840], ![3839328, -83520, 6340554, 4797649, 13395432], ![-1312056, 34287, -2180214, -1650147, -4603151]]]
  hmulB := by decide  
  f := ![![![-4199, 6031, 1226, 1285, 4576]], ![![-17304, -14543, -5412, -7740, -25770]], ![![61200, 28866, 13147, 19908, 65580]], ![![-140544, -51228, -26190, -40733, -133536]], ![![-26202, -8077, -4491, -7106, -23225]]]
  g := ![![![-4283, -13529, -20894, -14643, 39362], ![-31188, -98621, -152370, -106788, 287034], ![-202752, -640566, -989357, -693372, 1863840], ![-1455696, -4602624, -7110810, -4983581, 13395432], ![500274, 1581661, 2443521, 1712528, -4603151]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [21, 97, 68, 124, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 31, 102, 130], [38, 108, 72, 79], [88, 23, 152, 117], [0, 1]]
 g := ![![[74, 132, 98, 134], [13, 106, 83, 15], [11, 110, 43], [89, 65, 121], [32, 19, 33], [39, 1], []], ![[45, 159, 139, 3, 149, 112], [57, 71, 97, 118, 145, 11], [45, 51, 156], [134, 4, 146], [21, 138, 81], [83, 60, 53, 113, 56, 67], [3, 42, 111]], ![[103, 109, 4, 119, 139, 89], [89, 1, 153, 90, 21, 20], [15, 55, 55], [36, 11, 90], [95, 112, 140], [130, 151, 121, 56, 23, 116], [52, 6, 47]], ![[140, 118, 140, 106, 106, 42], [1, 144, 102, 141, 121, 107], [51, 34, 41], [124, 81, 97], [113, 55, 56], [81, 37, 66, 160, 47, 31], [25, 80, 160]]]
 h' := ![![[76, 31, 102, 130], [53, 81, 133, 42], [109, 3, 156, 129], [103, 162, 21, 83], [159, 34, 93, 152], [159, 108, 22, 149], [0, 0, 1], [0, 1]], ![[38, 108, 72, 79], [67, 61, 132, 131], [130, 116, 132, 124], [89, 55, 16, 112], [135, 7, 76, 132], [24, 69, 131, 9], [8, 116, 76, 27], [76, 31, 102, 130]], ![[88, 23, 152, 117], [142, 126, 80, 117], [44, 138, 145, 36], [14, 5, 28, 50], [97, 115, 143, 116], [138, 138, 139, 125], [26, 104, 132, 35], [38, 108, 72, 79]], ![[0, 1], [134, 58, 144, 36], [20, 69, 56, 37], [73, 104, 98, 81], [45, 7, 14, 89], [25, 11, 34, 43], [47, 106, 117, 101], [88, 23, 152, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [162, 88, 113], []]
 b := ![[], [], [155, 118, 11, 143], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [21, 97, 68, 124, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125286449420523, 17484181947233, 158886097441874, 118704530290295, 346689075032862]
  a := ![309, 41, 314, 215, 678]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37516054608411, -119000638158853, -184067873806240, -129014288630149, 346689075032862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4199, 6031, 1226, 1285, 4576]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-4199, 6031, 1226, 1285, 4576]] 
 ![![163, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![102, 0, 0, 1, 0], ![118, 0, 0, 0, 1]] where
  M :=![![![-4199, 6031, 1226, 1285, 4576], ![-17304, -14543, -5412, -7740, -25770], ![61200, 28866, 13147, 19908, 65580], ![-140544, -51228, -26190, -40733, -133536], ![22464, 2865, 2772, 4749, 15313]]]
  hmulB := by decide  
  f := ![![![10387, -955, 18772, 14273, 39362]], ![![2357, -178, 4172, 3169, 8764]], ![![11801, -1031, 21231, 16135, 44518]], ![![30054, -1110, 50646, 38365, 106812]], ![![-530, -481, 214, 209, 255]]]
  g := ![![![-6246, 6031, 1226, 1285, 4576], ![30529, -14543, -5412, -7740, -25770], ![-75743, 28866, 13147, 19908, 65580], ![152424, -51228, -26190, -40733, -133536], ![-16759, 2865, 2772, 4749, 15313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![10387, -955, 18772, 14273, 39362]] ![![-4199, 6031, 1226, 1285, 4576]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5197, 178, -416, -820, -2588]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-5197, 178, -416, -820, -2588]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![98, 21, 69, 1, 0], ![26, 60, 104, 0, 1]] where
  M :=![![![-5197, 178, -416, -820, -2588], ![3072, -1585, -158, -8, -160], ![3264, 4320, 1511, 2002, 6736], ![-17520, -9312, -4462, -6165, -20484], ![6240, 1230, 1002, 1496, 4891]]]
  hmulB := by decide  
  f := ![![![253, 994, -300, -508, -1548]], ![![576, 1993, -486, -932, -2864]], ![![1632, 3984, -171, -1262, -4056]], ![![934, 2527, -277, -927, -2924]], ![![1246, 3322, -334, -1196, -3781]]]
  g := ![![![853, 1034, 1948, -820, -2588], ![48, 49, 102, -8, -160], ![-2204, -2646, -5013, 2002, 6736], ![6702, 8079, 15277, -6165, -20484], ![-1602, -1938, -3658, 1496, 4891]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [55, 156, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 161, 108], [61, 5, 59], [0, 1]]
 g := ![![[163, 51, 162], [3, 34, 18], [66, 152, 147], [1, 11], [80, 56], [148, 114, 1], []], ![[39, 71, 156, 16], [106, 44, 56, 24], [25, 51, 160, 137], [9, 132], [51, 36], [141, 15, 60, 28], [82, 141]], ![[105, 52, 116, 26], [89, 147, 41, 105], [88, 144, 83, 15], [60, 32], [144, 11], [151, 162, 37, 120], [131, 141]]]
 h' := ![![[53, 161, 108], [2, 99, 117], [44, 124, 39], [57, 99, 100], [121, 56, 41], [43, 34, 35], [0, 0, 1], [0, 1]], ![[61, 5, 59], [119, 110, 88], [63, 103, 60], [33, 2, 3], [148, 62, 74], [92, 38, 6], [136, 26, 5], [53, 161, 108]], ![[0, 1], [48, 125, 129], [155, 107, 68], [46, 66, 64], [138, 49, 52], [83, 95, 126], [23, 141, 161], [61, 5, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 7], []]
 b := ![[], [105, 94, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [55, 156, 53, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-315089, 16064, -540574, -410576, -1139036]
  a := ![-5, -4, -5, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![416385, 460960, 875742, -410576, -1139036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, -3, -3, -10]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-5, 0, -3, -3, -10]] 
 ![![167, 0, 0, 0, 0], ![131, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![104, 0, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![-5, 0, -3, -3, -10], ![24, 13, 11, 7, 26], ![-120, -42, -74, -55, -194], ![696, 306, 405, 280, 1010], ![-192, -90, -110, -74, -269]]]
  hmulB := by decide  
  f := ![![![1013, 264, 155, 253, 826]], ![![785, 205, 120, 196, 640]], ![![256, 66, 38, 63, 206]], ![![608, 162, 87, 148, 486]], ![![855, 222, 133, 215, 701]]]
  g := ![![![11, 0, -3, -3, -10], ![-39, 13, 11, 7, 26], ![248, -42, -74, -55, -194], ![-1360, 306, 405, 280, 1010], ![369, -90, -110, -74, -269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143, -62, -85, -59, -212]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-143, -62, -85, -59, -212]] 
 ![![167, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![135, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-143, -62, -85, -59, -212], ![840, 349, 507, 357, 1278], ![-4968, -2094, -2984, -2091, -7494], ![29304, 12294, 17625, 12370, 44322], ![-8136, -3408, -4896, -3438, -12317]]]
  hmulB := by decide  
  f := ![![![5015, 226, 509, 925, 2956]], ![![3998, 185, 407, 739, 2362]], ![![2408, 94, 240, 439, 1402]], ![![4095, 216, 420, 763, 2442]], ![![274, 8, 28, 50, 159]]]
  g := ![![![150, -62, -85, -59, -212], ![-883, 349, 507, 357, 1278], ![5219, -2094, -2984, -2091, -7494], ![-30786, 12294, 17625, 12370, 44322], ![8548, -3408, -4896, -3438, -12317]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-5197, 178, -416, -820, -2588]] ![![-5, 0, -3, -3, -10]]
  ![![6353, 1786, 913, 1629, 5274]] where
 M := ![![![6353, 1786, 913, 1629, 5274]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![6353, 1786, 913, 1629, 5274]] ![![-143, -62, -85, -59, -212]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![882929, 370740, 530726, 372410, 1334330]]]
 hmul := by decide  
 g := ![![![![5287, 2220, 3178, 2230, 7990]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 2, 12, 24, 76]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![139, 2, 12, 24, 76]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![97, 21, 1, 0, 0], ![39, 2, 0, 1, 0], ![22, 119, 0, 0, 1]] where
  M :=![![![139, 2, 12, 24, 76], ![-96, 31, 6, -4, -8], ![-96, -120, -77, -66, -232], ![816, 408, 398, 335, 1172], ![-288, -90, -110, -96, -333]]]
  hmulB := by decide  
  f := ![![![-25, -58, 0, 16, 52]], ![![-96, -109, -86, -32, -72]], ![![-29, -47, -15, 2, 12]], ![![-27, -16, -34, -21, -56]], ![![-62, -81, -48, -12, -21]]]
  g := ![![![-21, -54, 12, 24, 76], ![-2, 5, 6, -4, -8], ![87, 169, -77, -66, -232], ![-443, -856, 398, 335, 1172], ![124, 243, -110, -96, -333]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [60, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 172], [0, 1]]
 g := ![![[85, 124], [133], [133, 138], [27, 158], [31], [77, 142], [1]], ![[0, 49], [133], [97, 35], [61, 15], [31], [55, 31], [1]]]
 h' := ![![[90, 172], [116, 41], [151, 47], [110, 22], [49, 37], [51, 107], [113, 90], [0, 1]], ![[0, 1], [0, 132], [56, 126], [14, 151], [92, 136], [166, 66], [82, 83], [90, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [105, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [60, 83, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2534898, 611286, 2614499, 1926839, 5879354]
  a := ![319, 126, 324, 221, 700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2633318, -4380289, 2614499, 1926839, 5879354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![695, 2884, -934, -1520, -4616]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![695, 2884, -934, -1520, -4616]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![142, 92, 1, 0, 0], ![84, 155, 0, 1, 0], ![150, 51, 0, 0, 1]] where
  M :=![![![695, 2884, -934, -1520, -4616], ![1344, 5759, -1908, -3078, -9360], ![3024, 11712, -3655, -6048, -18324], ![4320, 22788, -8340, -12871, -39384], ![-3168, -14496, 4974, 7890, 24047]]]
  hmulB := by decide  
  f := ![![![-6053, 268, -10270, -7784, -21632]], ![![-41280, 1819, -70428, -53358, -148272]], ![![-28558, 1260, -48675, -36880, -102484]], ![![-51156, 2257, -87240, -66097, -183672]], ![![-13542, 597, -23058, -17472, -48553]]]
  g := ![![![5511, 3236, -934, -1520, -4616], ![11184, 6565, -1908, -3078, -9360], ![21842, 12832, -3655, -6048, -18324], ![47268, 27709, -8340, -12871, -39384], ![-28782, -16887, 4974, 7890, 24047]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [104, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 172], [0, 1]]
 g := ![![[1, 109], [78], [57, 151], [89, 116], [25], [162, 90], [1]], ![[83, 64], [78], [96, 22], [135, 57], [25], [144, 83], [1]]]
 h' := ![![[69, 172], [59, 121], [127, 123], [86, 155], [159, 17], [106, 5], [69, 69], [0, 1]], ![[0, 1], [104, 52], [137, 50], [55, 18], [121, 156], [105, 168], [159, 104], [69, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [64, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [104, 104, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3800017, 973878, 3761785, 2768280, 8526504]
  a := ![-391, -131, -396, -270, -858]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11802801, -6988702, 3761785, 2768280, 8526504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 552, -177, -293, -890]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![-5, 552, -177, -293, -890]] 
 ![![173, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![96, 0, 0, 1, 0], ![160, 0, 0, 0, 1]] where
  M :=![![![-5, 552, -177, -293, -890], ![264, 973, -367, -587, -1794], ![792, 2322, -616, -1013, -3046], ![168, 3894, -1569, -2530, -7754], ![-432, -2646, 902, 1466, 4463]]]
  hmulB := by decide  
  f := ![![![1511, -696, 4075, 3133, 8246]], ![![684, -227, 1635, 1253, 3338]], ![![795, -282, 1943, 1490, 3960]], ![![7800, 54, 12353, 9330, 26218]], ![![-896, -750, 352, 324, 323]]]
  g := ![![![828, 552, -177, -293, -890], ![1719, 973, -367, -587, -1794], ![2696, 2322, -616, -1013, -3046], ![7525, 3894, -1569, -2530, -7754], ![-4198, -2646, 902, 1466, 4463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![139, 2, 12, 24, 76]] ![![695, 2884, -934, -1520, -4616]]
  ![![-1507, -1846, 362, 724, 2124]] where
 M := ![![![-1507, -1846, 362, 724, 2124]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![-1507, -1846, 362, 724, 2124]] ![![-5, 552, -177, -293, -890]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-989041, -4588306, 1501121, 2440511, 7415818]]]
 hmul := by decide  
 g := ![![![![-5717, -26522, 8677, 14107, 42866]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1559, -6523, 2132, 3457, 10504]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-1559, -6523, 2132, 3457, 10504]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![31, 0, 1, 0, 0], ![0, 31, 0, 1, 0], ![116, 13, 0, 0, 1]] where
  M :=![![![-1559, -6523, 2132, 3457, 10504], ![-3192, -13127, 4246, 6918, 21006], ![-6048, -26214, 8749, 14050, 42744], ![-14256, -53544, 16324, 27345, 82700], ![8400, 33375, -10568, -17389, -52723]]]
  hmulB := by decide  
  f := ![![![-16237, -1945, -1970, -3391, -10926]], ![![18072, 713, 1810, 3296, 10522]], ![![-2897, -323, -345, -597, -1922]], ![![3144, 73, 302, 557, 1774]], ![![-9148, -1194, -1136, -1943, -6267]]]
  g := ![![![-7185, -1398, 2132, 3457, 10504], ![-14366, -2797, 4246, 6918, 21006], ![-29249, -5684, 8749, 14050, 42744], ![-56500, -11041, 16324, 27345, 82700], ![36044, 7027, -10568, -17389, -52723]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [147, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 178], [0, 1]]
 g := ![![[44, 151], [71, 85], [126], [87], [94, 39], [34, 39], [1]], ![[0, 28], [0, 94], [126], [87], [53, 140], [172, 140], [1]]]
 h' := ![![[155, 178], [124, 35], [123, 117], [71, 157], [144, 83], [14, 24], [32, 155], [0, 1]], ![[0, 1], [0, 144], [0, 62], [62, 22], [121, 96], [154, 155], [71, 24], [155, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [2, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [147, 24, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1844163, 719520, 1250708, 887172, 3052244]
  a := ![216, 72, 220, 140, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2184291, -371296, 1250708, 887172, 3052244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2795, 1175, 1678, 1177, 4220]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![2795, 1175, 1678, 1177, 4220]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![168, 94, 1, 0, 0], ![139, 103, 0, 1, 0], ![116, 28, 0, 0, 1]] where
  M :=![![![2795, 1175, 1678, 1177, 4220], ![-16536, -6937, -9964, -6992, -25034], ![97392, 40962, 58429, 40980, 146964], ![-576576, -241764, -347670, -243995, -873360], ![160176, 67137, 96648, 67833, 242743]]]
  hmulB := by decide  
  f := ![![![12385, 3149, 1972, 3177, 10346]], ![![-19560, -4481, -2888, -4714, -15334]], ![![1512, 632, 357, 544, 1780]], ![![-1855, -168, -158, -292, -940]], ![![4948, 1333, 822, 1315, 4285]]]
  g := ![![![-5208, -2212, 1678, 1177, 4220], ![30912, 13133, -9964, -6992, -25034], ![-181356, -77024, 58429, 40980, 146964], ![1078531, 458239, -347670, -243995, -873360], ![-299797, -127382, 96648, 67833, 242743]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [165, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 178], [0, 1]]
 g := ![![[87, 64], [], [80], [29], [88, 110], [0, 151], [1]], ![[174, 115], [], [80], [29], [176, 69], [85, 28], [1]]]
 h' := ![![[144, 178], [0, 171], [23], [131, 120], [158, 71], [0, 162], [14, 144], [0, 1]], ![[0, 1], [101, 8], [23], [48, 59], [0, 108], [58, 17], [165, 35], [144, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [133, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [165, 35, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![63113, 23418, 45541, 32349, 109332]
  a := ![41, 10, 42, 27, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-138362, -59501, 45541, 32349, 109332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![288503, 103386, 53292, 83030, 272114]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![288503, 103386, 53292, 83030, 272114]] 
 ![![179, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![114, 0, 1, 0, 0], ![155, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![288503, 103386, 53292, 83030, 272114], ![-552576, -167803, -94046, -149032, -486960], ![956736, 253296, 152941, 245714, 800944], ![-1531248, -354624, -231294, -376463, -1224388], ![9432, -23562, -5414, -6200, -21623]]]
  hmulB := by decide  
  f := ![![![-412139, -178110, -245200, -170350, -612002]], ![![-182173, -78949, -108266, -75142, -270030]], ![![-342498, -147156, -204215, -142166, -510468]], ![![115357, 43866, 71814, 51911, 184482]], ![![-315320, -134526, -188526, -131564, -472071]]]
  g := ![![![-274935, 103386, 53292, 83030, 272114], ![483177, -167803, -94046, -149032, -486960], ![-783072, 253296, 152941, 245714, 800944], ![1180347, -354624, -231294, -376463, -1224388], ![29722, -23562, -5414, -6200, -21623]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-1559, -6523, 2132, 3457, 10504]] ![![2795, 1175, 1678, 1177, 4220]]
  ![![412139, 178110, 245200, 170350, 612002]] where
 M := ![![![412139, 178110, 245200, 170350, 612002]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![412139, 178110, 245200, 170350, 612002]] ![![288503, 103386, 53292, 83030, 272114]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3103, -4002, -785, -799, -2866]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![3103, -4002, -785, -799, -2866]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![130, 3, 1, 0, 0], ![153, 121, 0, 1, 0], ![159, 139, 0, 0, 1]] where
  M :=![![![3103, -4002, -785, -799, -2866], ![11256, 9721, 3589, 5121, 17058], ![-40680, -19362, -8780, -13289, -43782], ![93960, 34422, 17527, 27282, 89438], ![-15216, -1956, -1874, -3220, -10381]]]
  hmulB := by decide  
  f := ![![![-30341, -126438, 41235, 66927, 203318]], ![![-60888, -253955, 82919, 134497, 408566]], ![![-23474, -97839, 31915, 51794, 157344]], ![![-67689, -282311, 92171, 149510, 454174]], ![![-72567, -302543, 98730, 160190, 486627]]]
  g := ![![![3774, 2726, -785, -799, -2866], ![-21829, -16529, 3589, 5121, 17058], ![55775, 42545, -8780, -13289, -43782], ![-113698, -87023, 17527, 27282, 89438], ![13103, 10145, -1874, -3220, -10381]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [146, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 180], [0, 1]]
 g := ![![[69, 33], [142], [144, 15], [177], [64, 169], [128, 43], [1]], ![[124, 148], [142], [169, 166], [177], [44, 12], [79, 138], [1]]]
 h' := ![![[62, 180], [143, 157], [153, 93], [140, 14], [68, 143], [136, 168], [35, 62], [0, 1]], ![[0, 1], [103, 24], [127, 88], [103, 167], [65, 38], [54, 13], [78, 119], [62, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [179]]
 b := ![[], [31, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [146, 119, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5451542, 1452933, 5291741, 3881256, 12022412]
  a := ![453, 153, 463, 312, 994]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17612544, -11907014, 5291741, 3881256, 12022412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3107, -127, 5290, 4005, 11128]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![3107, -127, 5290, 4005, 11128]] 
 ![![181, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![3107, -127, 5290, 4005, 11128], ![21288, -925, 36294, 27492, 76390], ![146064, -6414, 249021, 188654, 524236], ![1001424, -44364, 1707900, 1293945, 3595532], ![-345552, 15279, -589298, -446459, -1240593]]]
  hmulB := by decide  
  f := ![![![47231, -85571, -18500, -20321, -71558]], ![![24368, -40479, -8570, -9270, -32762]], ![![5397, -20655, -5003, -5921, -20498]], ![![12677, 607, 1296, 2346, 7498]], ![![9270, -20067, -4500, -5071, -17751]]]
  g := ![![![-3798, -127, 5290, 4005, 11128], ![-26042, -925, 36294, 27492, 76390], ![-178673, -6414, 249021, 188654, 524236], ![-1225263, -44364, 1707900, 1293945, 3595532], ![422777, 15279, -589298, -446459, -1240593]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-259, -128, -55, -83, -274]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-259, -128, -55, -83, -274]] 
 ![![181, 0, 0, 0, 0], ![131, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-259, -128, -55, -83, -274], ![600, 215, 115, 179, 586], ![-1176, -378, -196, -311, -1018], ![2040, 522, 333, 542, 1762], ![-96, 30, -10, -22, -67]]]
  hmulB := by decide  
  f := ![![![-6103, 272, -10419, -7893, -21930]], ![![-4649, 207, -7936, -6012, -16704]], ![![-2734, 122, -4666, -3535, -9822]], ![![-13301, 586, -22678, -17181, -47744]], ![![2785, -122, 4745, 3595, 9991]]]
  g := ![![![178, -128, -55, -83, -274], ![-338, 215, 115, 179, 586], ![589, -378, -196, -311, -1018], ![-924, 522, 333, 542, 1762], ![-1, 30, -10, -22, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2

def I181N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 153, -50, -81, -246]] i)))

def SI181N3: IdealEqSpanCertificate' Table ![![37, 153, -50, -81, -246]] 
 ![![181, 0, 0, 0, 0], ![140, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![37, 153, -50, -81, -246], ![72, 307, -102, -164, -498], ![144, 618, -211, -334, -1012], ![240, 1236, -488, -719, -2172], ![-168, -777, 282, 433, 1311]]]
  hmulB := by decide  
  f := ![![![-2183, -1083, -480, -727, -2396]], ![![-1660, -827, -366, -554, -1826]], ![![-1611, -789, -351, -533, -1756]], ![![-392, -216, -96, -139, -460]], ![![-1064, -525, -232, -353, -1163]]]
  g := ![![![55, 153, -50, -81, -246], ![114, 307, -102, -164, -498], ![239, 618, -211, -334, -1012], ![608, 1236, -488, -719, -2172], ![-334, -777, 282, 433, 1311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N3 : Nat.card (O ⧸ I181N3) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N3)

lemma isPrimeI181N3 : Ideal.IsPrime I181N3 := prime_ideal_of_norm_prime hp181.out _ NI181N3
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![3103, -4002, -785, -799, -2866]] ![![3107, -127, 5290, 4005, 11128]]
  ![![461, -19, 765, 580, 1614]] where
 M := ![![![461, -19, 765, 580, 1614]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![461, -19, 765, 580, 1614]] ![![-259, -128, -55, -83, -274]]
  ![![-2183, -1083, -480, -727, -2396]] where
 M := ![![![-2183, -1083, -480, -727, -2396]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N2 : IdealMulLeCertificate' Table 
  ![![-2183, -1083, -480, -727, -2396]] ![![37, 153, -50, -81, -246]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2, I181N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
    exact isPrimeI181N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1 ⊙ MulI181N2)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10207, 58299, -19615, -31894, -97040]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![10207, 58299, -19615, -31894, -97040]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![184, 60, 27, 143, 1]] where
  M :=![![![10207, 58299, -19615, -31894, -97040], ![32592, 118111, -38043, -61675, -187252], ![53448, 237660, -77368, -125761, -382050], ![114408, 473634, -155743, -252618, -767738], ![-69000, -298113, 97790, 158767, 482473]]]
  hmulB := by decide  
  f := ![![![-679, -279, -423, -298, -1054]], ![![3840, 1655, 2209, 1541, 5616]], ![![-23832, -9720, -15020, -10597, -37322]], ![![132744, 57738, 75105, 52282, 191774]], ![![96376, 42021, 54287, 37768, 138779]]]
  g := ![![![93537, 30789, 13615, 72486, -97040], ![180560, 59441, 26271, 139871, -187252], ![368328, 121260, 53602, 285379, -382050], ![740200, 243654, 107713, 573476, -767738], ![-465152, -153123, -67691, -360392, 482473]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [74, 44, 16, 33, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 142, 167, 33], [115, 6, 135, 43], [171, 42, 80, 115], [0, 1]]
 g := ![![[74, 159, 75, 23], [50, 76, 32, 135], [100, 7, 176, 144], [3, 30, 27, 85], [140, 68, 60, 172], [158, 1], []], ![[50, 26, 70, 77, 16, 122], [139, 175, 35, 121, 54, 82], [84, 141, 55, 33, 169, 44], [130, 35, 32, 133, 26, 61], [108, 176, 12, 68, 125, 141], [175, 178, 6, 70, 91, 114], [104, 106, 134]], ![[107, 138, 25, 133, 167, 121], [100, 77, 107, 117, 139, 68], [146, 149, 47, 104, 109, 48], [68, 48, 62, 182, 105, 34], [125, 134, 10, 102, 14, 134], [70, 42, 32, 180, 166, 5], [99, 62, 130]], ![[3, 14, 104, 174, 24, 43], [93, 150, 145, 120, 130, 60], [63, 146, 117, 182, 47, 86], [155, 10, 179, 36, 157, 129], [18, 185, 132, 171, 114, 134], [175, 94, 186, 37, 79, 107], [85, 74, 46]]]
 h' := ![![[63, 142, 167, 33], [120, 116, 117, 126], [49, 54, 82, 138], [160, 146, 113, 179], [145, 39, 145, 127], [150, 41, 102, 118], [0, 0, 1], [0, 1]], ![[115, 6, 135, 43], [165, 138, 188, 97], [182, 37, 52, 132], [12, 118, 12, 175], [91, 50, 188, 5], [2, 70, 48, 109], [93, 124, 132, 70], [63, 142, 167, 33]], ![[171, 42, 80, 115], [151, 107, 9, 16], [183, 83, 159, 76], [170, 153, 169, 157], [141, 50, 98, 65], [56, 77, 100, 143], [169, 76, 155, 3], [115, 6, 135, 43]], ![[0, 1], [77, 21, 68, 143], [87, 17, 89, 36], [53, 156, 88, 62], [180, 52, 142, 185], [109, 3, 132, 12], [31, 182, 94, 118], [171, 42, 80, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [97, 80, 58], []]
 b := ![[], [], [107, 28, 6, 163], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [74, 44, 16, 33, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48249700492374, 5873697449370, 63233292923608, 47325904419106, 137363477994450]
  a := ![247, 84, 250, 171, 542]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-132076598170086, -43120078440930, -19086809491762, -102595033763284, 137363477994450]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![679, 279, 423, 298, 1054]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![679, 279, 423, 298, 1054]] 
 ![![191, 0, 0, 0, 0], ![185, 1, 0, 0, 0], ![155, 0, 1, 0, 0], ![166, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![679, 279, 423, 298, 1054], ![-3840, -1655, -2209, -1541, -5616], ![23832, 9720, 15020, 10597, 37322], ![-132744, -57738, -75105, -52282, -191774], ![36576, 16047, 20366, 14147, 52223]]]
  hmulB := by decide  
  f := ![![![-10207, -58299, 19615, 31894, 97040]], ![![-10057, -57086, 19198, 31215, 94972]], ![![-8563, -48555, 16323, 26541, 80750]], ![![-9470, -53148, 17863, 29042, 88358]], ![![-5624, -32625, 10990, 17871, 54377]]]
  g := ![![![-1487, 279, 423, 298, 1054], ![8008, -1655, -2209, -1541, -5616], ![-52574, 9720, 15020, 10597, 37322], ![274071, -57738, -75105, -52282, -191774], ![-74797, 16047, 20366, 14147, 52223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![10207, 58299, -19615, -31894, -97040]] ![![679, 279, 423, 298, 1054]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269389, 101106, 50975, 79041, 259262]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![269389, 101106, 50975, 79041, 259262]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![25, 71, 1, 0, 0], ![155, 2, 0, 1, 0], ![102, 1, 0, 0, 1]] where
  M :=![![![269389, 101106, 50975, 79041, 259262], ![-531336, -166985, -91927, -145167, -474622], ![938904, 256254, 152130, 243675, 794714], ![-1528536, -365322, -233893, -379544, -1235050], ![22512, -20472, -3422, -2964, -11095]]]
  hmulB := by decide  
  f := ![![![9301, 4518, 5311, 3519, 12766]], ![![-53016, -21137, -32213, -22995, -82298]], ![![-16643, -6487, -10162, -7305, -26126]], ![![-2689, -634, -1780, -1421, -5032]], ![![7302, 3391, 4221, 2853, 10327]]]
  g := ![![![-205705, -20391, 50975, 79041, 259262], ![376576, 36916, -91927, -145167, -474622], ![-630543, -61280, 152130, 243675, 794714], ![979913, 94483, -233893, -379544, -1235050], ![8804, 1241, -3422, -2964, -11095]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [59, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 192], [0, 1]]
 g := ![![[21, 36], [169], [170], [144], [21], [126], [112, 1]], ![[0, 157], [169], [170], [144], [21], [126], [31, 192]]]
 h' := ![![[112, 192], [93, 187], [75, 180], [164, 39], [174, 12], [86, 139], [147, 133], [0, 1]], ![[0, 1], [0, 6], [163, 13], [93, 154], [167, 181], [21, 54], [182, 60], [112, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [15, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [59, 81, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1253847, 217036, 1496591, 1113205, 3290332]
  a := ![232, 80, 235, 164, 509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2820319, -578019, 1496591, 1113205, 3290332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8267, -1942, -1257, -2043, -6646]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-8267, -1942, -1257, -2043, -6646]] 
 ![![193, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![128, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-8267, -1942, -1257, -2043, -6646], ![12408, 2515, 1777, 2929, 9506], ![-17256, -2850, -2306, -3869, -12518], ![21864, 2550, 2627, 4532, 14598], ![2784, 1008, 522, 812, 2661]]]
  hmulB := by decide  
  f := ![![![23149, 9646, 14111, 9915, 35346]], ![![8779, 3653, 5364, 3770, 13428]], ![![19544, 8138, 11926, 8381, 29866]], ![![-10167, -4452, -5676, -3945, -14548]], ![![12698, 5360, 7574, 5308, 19077]]]
  g := ![![![4546, -1942, -1257, -2043, -6646], ![-6382, 2515, 1777, 2929, 9506], ![8195, -2850, -2306, -3869, -12518], ![-9202, 2550, 2627, 4532, 14598], ![-1926, 1008, 522, 812, 2661]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 99, 63, 102, 332]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![409, 99, 63, 102, 332]] 
 ![![193, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![176, 0, 0, 0, 1]] where
  M :=![![![409, 99, 63, 102, 332], ![-624, -131, -91, -149, -484], ![888, 156, 124, 203, 658], ![-1176, -162, -159, -254, -826], ![-120, -45, -20, -35, -113]]]
  hmulB := by decide  
  f := ![![![-1535, -6393, 2089, 3386, 10286]], ![![-684, -2849, 931, 1509, 4584]], ![![-707, -2949, 965, 1563, 4748]], ![![-71, -303, 104, 164, 496]], ![![-1360, -5661, 1848, 2997, 9105]]]
  g := ![![![-372, 99, 63, 102, 332], ![536, -131, -91, -149, -484], ![-719, 156, 124, 203, 658], ![889, -162, -159, -254, -826], ![131, -45, -20, -35, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2

def I193N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 81, -21, -34, -102]] i)))

def SI193N3: IdealEqSpanCertificate' Table ![![47, 81, -21, -34, -102]] 
 ![![193, 0, 0, 0, 0], ![152, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![173, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![47, 81, -21, -34, -102], ![0, 149, -55, -89, -272], ![120, 312, -92, -153, -462], ![72, 606, -231, -350, -1074], ![-96, -387, 132, 207, 631]]]
  hmulB := by decide  
  f := ![![![1271, -75, 2229, 1682, 4668]], ![![1048, -61, 1835, 1385, 3844]], ![![688, -36, 1192, 901, 2502]], ![![3331, -165, 5736, 4340, 12054]], ![![-183, 0, -285, -219, -611]]]
  g := ![![![19, 81, -21, -34, -102], ![101, 149, -55, -89, -272], ![127, 312, -92, -153, -462], ![388, 606, -231, -350, -1074], ![-204, -387, 132, 207, 631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N3 : Nat.card (O ⧸ I193N3) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N3)

lemma isPrimeI193N3 : Ideal.IsPrime I193N3 := prime_ideal_of_norm_prime hp193.out _ NI193N3
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![269389, 101106, 50975, 79041, 259262]] ![![-8267, -1942, -1257, -2043, -6646]]
  ![![597797617, 48740048, 66470510, 117290028, 376385992]] where
 M := ![![![597797617, 48740048, 66470510, 117290028, 376385992]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![597797617, 48740048, 66470510, 117290028, 376385992]] ![![409, 99, 63, 102, 332]]
  ![![90011856313, 27228063179, 15291414451, 24241426480, 79203040968]] where
 M := ![![![90011856313, 27228063179, 15291414451, 24241426480, 79203040968]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N2 : IdealMulLeCertificate' Table 
  ![![90011856313, 27228063179, 15291414451, 24241426480, 79203040968]] ![![47, 81, -21, -34, -102]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![207417754463, 157590676000, 60429303986, 87243063800, 289950806312]]]
 hmul := by decide  
 g := ![![![![1074703391, 816532000, 313105202, 452036600, 1502335784]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2, I193N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
    exact isPrimeI193N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1 ⊙ MulI193N2)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 242, -65, -107, -322]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![77, 242, -65, -107, -322]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![108, 5, 1, 0, 0], ![51, 83, 0, 1, 0], ![147, 175, 0, 0, 1]] where
  M :=![![![77, 242, -65, -107, -322], ![24, 407, -163, -263, -806], ![408, 966, -254, -417, -1254], ![72, 1686, -633, -1040, -3186], ![-240, -1128, 366, 600, 1825]]]
  hmulB := by decide  
  f := ![![![937, 398, 571, 399, 1430]], ![![-5592, -2357, -3365, -2359, -8458]], ![![540, 229, 329, 230, 824]], ![![-3105, -1307, -1865, -1308, -4690]], ![![-3993, -1681, -2398, -1682, -6031]]]
  g := ![![![304, 334, -65, -107, -322], ![759, 833, -163, -263, -806], ![1185, 1301, -254, -417, -1254], ![2994, 3293, -633, -1040, -3186], ![-1719, -1889, 366, 600, 1825]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [121, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [181, 196], [0, 1]]
 g := ![![[62, 127], [41], [28, 64], [134], [142], [101], [181, 1]], ![[0, 70], [41], [186, 133], [134], [142], [101], [165, 196]]]
 h' := ![![[181, 196], [106, 179], [158, 108], [115, 8], [61, 79], [164, 39], [163, 135], [0, 1]], ![[0, 1], [0, 18], [6, 89], [184, 189], [176, 118], [131, 158], [170, 62], [181, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [159]]
 b := ![[], [45, 178]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [121, 16, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3818490, 1090038, 3534561, 2583460, 8099640]
  a := ![-359, -113, -376, -246, -788]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8631054, -8367751, 3534561, 2583460, 8099640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1307, -5398, 1758, 2854, 8670]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-1307, -5398, 1758, 2854, 8670]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![154, 49, 1, 0, 0], ![137, 117, 0, 1, 0], ![131, 31, 0, 0, 1]] where
  M :=![![![-1307, -5398, 1758, 2854, 8670], ![-2592, -10841, 3534, 5738, 17432], ![-5232, -21768, 7097, 11522, 35004], ![-10512, -43740, 14246, 23133, 70276], ![6600, 27450, -8944, -14522, -44117]]]
  hmulB := by decide  
  f := ![![![113, 62, 58, 46, 166]], ![![-672, -277, -398, -298, -1032]], ![![-62, -13, -45, -32, -104]], ![![-427, -163, -266, -195, -670]], ![![-1, 9, -4, -2, -3]]]
  g := ![![![-9131, -3524, 1758, 2854, 8670], ![-18358, -7085, 3534, 5738, 17432], ![-36864, -14227, 7097, 11522, 35004], ![-74009, -28563, 14246, 23133, 70276], ![46461, 17931, -8944, -14522, -44117]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [83, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 196], [0, 1]]
 g := ![![[68, 19], [54], [146, 61], [28], [40], [136], [69, 1]], ![[0, 178], [54], [21, 136], [28], [40], [136], [138, 196]]]
 h' := ![![[69, 196], [6, 77], [96, 60], [34, 88], [83, 15], [137, 146], [183, 147], [0, 1]], ![[0, 1], [0, 120], [99, 137], [196, 109], [133, 182], [164, 51], [82, 50], [69, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [121, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [83, 128, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1216112, 277844, 1283130, 949081, 2879497]
  a := ![-221, -70, -227, -154, -485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3571696, -1334530, 1283130, 949081, 2879497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1661, 72, -2825, -2141, -5950]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-1661, 72, -2825, -2141, -5950]] 
 ![![197, 0, 0, 0, 0], ![143, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![-1661, 72, -2825, -2141, -5950], ![-11352, 505, -19371, -14675, -40778], ![-77928, 3450, -132876, -100673, -279750], ![-534456, 23670, -911429, -690526, -1918834], ![184416, -8166, 314482, 238262, 662083]]]
  hmulB := by decide  
  f := ![![![28679, 117480, -38173, -61979, -188262]], ![![21101, 86473, -28100, -45624, -138584]], ![![6261, 25662, -8339, -13540, -41128]], ![![20944, 85926, -27931, -45346, -137742]], ![![17471, 71514, -23233, -37723, -114583]]]
  g := ![![![5752, 72, -2825, -2141, -5950], ![39416, 505, -19371, -14675, -40778], ![270412, 3450, -132876, -100673, -279750], ![1854783, 23670, -911429, -690526, -1918834], ![-639983, -8166, 314482, 238262, 662083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![77, 242, -65, -107, -322]] ![![-1307, -5398, 1758, 2854, 8670]]
  ![![-1388239, -5782968, 1884935, 3060277, 9297016]] where
 M := ![![![-1388239, -5782968, 1884935, 3060277, 9297016]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-1388239, -5782968, 1884935, 3060277, 9297016]] ![![-1661, 72, -2825, -2141, -5950]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![1379, -2364, 5122, 4334, 12214]]]
 hmul := by decide  
 g := ![![![![7, -12, 26, 22, 62]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)


lemma PB2088I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB2088I4 : PrimesBelowBoundCertificateInterval O 151 197 2088 where
  m := 9
  g := ![3, 2, 3, 3, 3, 4, 2, 4, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB2088I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1, I181N2, I181N3]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2, I193N3]
    · exact ![I197N0, I197N1, I197N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3869893, 157, 157]
    · exact ![705911761, 163]
    · exact ![4657463, 167, 167]
    · exact ![29929, 29929, 173]
    · exact ![32041, 32041, 179]
    · exact ![32761, 181, 181, 181]
    · exact ![1330863361, 191]
    · exact ![37249, 193, 193, 193]
    · exact ![38809, 38809, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
      exact NI181N3
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
      exact NI193N3
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I157N1, I157N2, I163N1, I167N1, I167N2, I173N2, I179N2, I181N1, I181N2, I181N3, I191N1, I193N1, I193N2, I193N3, I197N2]
  Il := ![[I157N1, I157N2], [I163N1], [I167N1, I167N2], [I173N2], [I179N2], [I181N1, I181N2, I181N3], [I191N1], [I193N1, I193N2, I193N3], [I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
