
import IdealArithmetic.Examples.NF5_1_25312500_2.RI5_1_25312500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9263, 3236, 8131, -1535, -2606]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-9263, 3236, 8131, -1535, -2606]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 9, 149, 18, 1]] where
  M :=![![![-9263, 3236, 8131, -1535, -2606], ![32656, -17835, -22507, 14727, -464], ![-17898, 19754, 2816, -22507, 15191], ![-73790, 25306, 65199, -11560, -21436], ![191854, -95686, -140956, 73330, 10947]]]
  hmulB := by decide  
  f := ![![![10115, -5462, 273, -225, 1357]], ![![-13522, 7319, -341, 321, -1807]], ![![15786, -8558, 432, -341, 2128]], ![![-14520, 7808, -353, 364, -1923]], ![![12574, -6825, 351, -264, 1700]]]
  g := ![![![-59, 170, 2525, 289, -2606], ![208, -87, 297, 147, -464], ![-114, -745, -14399, -1885, 15191], ![-470, 1390, 20759, 2384, -21436], ![1222, -1237, -11287, -788, 10947]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [13, 51, 129, 46, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 90, 61, 20], [76, 79, 70, 99], [59, 144, 26, 38], [0, 1]]
 g := ![![[26, 33, 84, 148], [138, 79, 156], [129, 61, 89, 64], [114, 126, 23, 17], [154, 131, 97, 75], [1], []], ![[105, 35, 36, 41, 50, 7], [23, 145, 17], [16, 1, 124, 122, 78, 50], [100, 72, 89, 24, 19, 142], [149, 113, 22, 68, 74, 5], [42, 52, 126], [23, 54, 86]], ![[113, 148, 97, 36, 95, 138], [122, 36, 11], [33, 145, 81, 46, 116, 71], [54, 89, 37, 66, 130, 93], [133, 42, 150, 145, 14, 37], [65, 5, 10], [142, 102, 67]], ![[92, 24, 40, 136, 75, 32], [55, 83, 35], [61, 95, 11, 4, 61, 107], [124, 43, 100, 121, 0, 112], [29, 72, 71, 79, 109, 15], [17, 76, 132], [62, 79, 31]]]
 h' := ![![[133, 90, 61, 20], [78, 90, 30, 73], [50, 58, 9, 28], [88, 35, 62, 8], [39, 32, 51, 71], [144, 106, 28, 111], [0, 0, 1], [0, 1]], ![[76, 79, 70, 99], [5, 81, 53, 89], [33, 88, 1, 71], [111, 29, 25, 148], [145, 39, 96, 66], [38, 155, 142, 79], [120, 85, 60, 122], [133, 90, 61, 20]], ![[59, 144, 26, 38], [116, 144, 57, 142], [17, 44, 41, 110], [139, 143, 133, 122], [154, 24, 155, 14], [122, 91, 7, 17], [5, 143, 26, 18], [76, 79, 70, 99]], ![[0, 1], [73, 156, 17, 10], [72, 124, 106, 105], [13, 107, 94, 36], [35, 62, 12, 6], [129, 119, 137, 107], [6, 86, 70, 17], [59, 144, 26, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [55, 112, 38], []]
 b := ![[], [], [3, 71, 115, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [13, 51, 129, 46, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3359471713, -807530707, -3363950513, -25881823, 1546291889]
  a := ![-16, 11, 7, -17, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![21397909, -93784444, -1488926382, -177446725, 1546291889]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10115, -5462, 273, -225, 1357]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![10115, -5462, 273, -225, 1357]] 
 ![![157, 0, 0, 0, 0], ![122, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![106, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![10115, -5462, 273, -225, 1357], ![-13522, 7319, -341, 321, -1807], ![15786, -8558, 432, -341, 2128], ![-14520, 7808, -353, 364, -1923], ![5062, -2798, 162, -80, 705]]]
  hmulB := by decide  
  f := ![![![-9263, 3236, 8131, -1535, -2606]], ![![-6990, 2401, 6175, -1099, -2028]], ![![-2061, 806, 1727, -466, -451]], ![![-6724, 2346, 5905, -1110, -1896]], ![![-2200, 586, 2106, -100, -893]]]
  g := ![![![3902, -5462, 273, -225, 1357], ![-5251, 7319, -341, 321, -1807], ![6104, -8558, 432, -341, 2128], ![-5621, 7808, -353, 364, -1923], ![1966, -2798, 162, -80, 705]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-9263, 3236, 8131, -1535, -2606]] ![![10115, -5462, 273, -225, 1357]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1673, -904, 44, -38, 224]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![1673, -904, 44, -38, 224]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![101, 49, 1, 0, 0], ![155, 143, 0, 1, 0], ![150, 79, 0, 0, 1]] where
  M :=![![![1673, -904, 44, -38, 224], ![-2234, 1211, -60, 50, -300], ![2612, -1412, 71, -60, 350], ![-2392, 1296, -64, 55, -322], ![848, -456, 20, -20, 115]]]
  hmulB := by decide  
  f := ![![![-5, -8, 20, 30, 12]], ![![-70, -39, 60, 70, 48]], ![![-25, -17, 31, 40, 22]], ![![-67, -43, 72, 91, 54]], ![![-40, -27, 48, 62, 35]]]
  g := ![![![-187, -94, 44, -38, 224], ![252, 127, -60, 50, -300], ![-293, -147, 71, -60, 350], ![269, 135, -64, 55, -322], ![-94, -47, 20, -20, 115]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [145, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 162], [0, 1]]
 g := ![![[132, 9], [93, 136], [9], [34], [39], [60, 34], [1]], ![[0, 154], [0, 27], [9], [34], [39], [159, 129], [1]]]
 h' := ![![[94, 162], [44, 3], [68, 138], [118, 160], [22, 94], [102, 56], [18, 94], [0, 1]], ![[0, 1], [0, 160], [0, 25], [162, 3], [56, 69], [150, 107], [52, 69], [94, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [87, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [145, 69, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2514583, 565580, 1806722, -356044, -125961]
  a := ![-121, 61, 62, -122, -243]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-680445, -166249, 1806722, -356044, -125961]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159, 56, 139, -27, -44]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-159, 56, 139, -27, -44]] 
 ![![163, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-159, 56, 139, -27, -44], ![552, -303, -379, 251, -10], ![-290, 330, 36, -379, 261], ![-1266, 438, 1115, -204, -362], ![3254, -1630, -2384, 1254, 175]]]
  hmulB := by decide  
  f := ![![![-5171, -3750, 1155, 2217, 1349]], ![![-760, -565, 169, 327, 201]], ![![-2359, -1712, 521, 1006, 613]], ![![-1976, -1452, 431, 840, 515]], ![![-1801, -1316, 389, 761, 466]]]
  g := ![![![-46, 56, 139, -27, -44], ![125, -303, -379, 251, -10], ![-11, 330, 36, -379, 261], ![-369, 438, 1115, -204, -362], ![787, -1630, -2384, 1254, 175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -6, -1, 3, -1]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![9, -6, -1, 3, -1]] 
 ![![163, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![106, 0, 0, 0, 1]] where
  M :=![![![9, -6, -1, 3, -1], ![12, -1, -19, 1, 7], ![-50, 22, 46, -19, -6], ![20, -20, -11, 26, -15], ![74, -10, -78, -12, 45]]]
  hmulB := by decide  
  f := ![![![1005, 960, 95, -161, -168]], ![![423, 405, 42, -66, -70]], ![![26, 26, 6, -1, -3]], ![![401, 386, 46, -57, -64]], ![![648, 622, 70, -96, -105]]]
  g := ![![![2, -6, -1, 3, -1], ![-4, -1, -19, 1, 7], ![1, 22, 46, -19, -6], ![8, -20, -11, 26, -15], ![-18, -10, -78, -12, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2

def I163N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1619, -840, 38, -46, 207]] i)))

def SI163N3: IdealEqSpanCertificate' Table ![![1619, -840, 38, -46, 207]] 
 ![![163, 0, 0, 0, 0], ![140, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![1619, -840, 38, -46, 207], ![-2078, 1201, -62, 30, -299], ![2518, -1322, 67, -62, 329], ![-2232, 1284, -56, 43, -315], ![836, -404, 30, -18, 105]]]
  hmulB := by decide  
  f := ![![![-2395, 1668, 1308, -1600, 573]], ![![-2094, 1437, 1164, -1368, 469]], ![![-915, 682, 457, -676, 286]], ![![-858, 596, 470, -571, 203]], ![![-826, 480, 542, -414, 55]]]
  g := ![![![665, -840, 38, -46, 207], ![-934, 1201, -62, 30, -299], ![1039, -1322, 67, -62, 329], ![-1008, 1284, -56, 43, -315], ![312, -404, 30, -18, 105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N3 : Nat.card (O ⧸ I163N3) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N3)

lemma isPrimeI163N3 : Ideal.IsPrime I163N3 := prime_ideal_of_norm_prime hp163.out _ NI163N3
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![1673, -904, 44, -38, 224]] ![![-159, 56, 139, -27, -44]]
  ![![-771, 356, 361, -103, -132]] where
 M := ![![![-771, 356, 361, -103, -132]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-771, 356, 361, -103, -132]] ![![9, -6, -1, 3, -1]]
  ![![-32545, 15592, 22042, -9910, -3298]] where
 M := ![![![-32545, 15592, 22042, -9910, -3298]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N2 : IdealMulLeCertificate' Table 
  ![![-32545, 15592, 22042, -9910, -3298]] ![![1619, -840, 38, -46, 207]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-10226783, 5532220, -270580, 231460, -1371645]]]
 hmul := by decide  
 g := ![![![![-62741, 33940, -1660, 1420, -8415]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2, I163N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
    exact isPrimeI163N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1 ⊙ MulI163N2)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189, -316, -391, -301, -108]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-189, -316, -391, -301, -108]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![127, 139, 33, 60, 1]] where
  M :=![![![-189, -316, -391, -301, -108], ![388, -29, -1105, -1083, -494], ![1182, 794, -900, -1105, -589], ![2822, 1942, -1919, -2396, -1298], ![3210, 2414, -1688, -2310, -1291]]]
  hmulB := by decide  
  f := ![![![-93, 50, -3, 3, -13]], ![![130, -69, -1, -3, 19]], ![![-162, 86, 8, -1, -22]], ![![144, -80, -1, 4, 15]], ![![57, -31, -2, 1, 7]]]
  g := ![![![81, 88, 19, 37, -108], ![378, 411, 91, 171, -494], ![455, 495, 111, 205, -589], ![1004, 1092, 245, 452, -1298], ![1001, 1089, 245, 450, -1291]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [154, 93, 95, 66, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 25, 69, 103], [148, 37, 113, 134], [45, 104, 152, 97], [0, 1]]
 g := ![![[70, 5, 121, 130], [88, 124, 11, 19], [46, 39, 99, 150], [57, 132, 57], [143, 162, 48], [101, 1], []], ![[67, 11, 128, 100, 162, 17], [140, 35, 20, 18, 114, 134], [41, 151, 21, 79, 57, 149], [163, 75, 61], [101, 141, 133], [165, 83, 53, 3, 26, 34], [26, 56, 88]], ![[68, 30, 56, 16, 133, 143], [76, 48, 28, 54, 101, 82], [129, 83, 123, 39], [10, 22, 124], [84, 3, 27], [162, 145, 112, 46, 154, 39], [19, 160, 87]], ![[70, 21, 47, 12, 143, 122], [110, 55, 163, 128, 87, 77], [148, 53, 157, 4, 64, 152], [130, 75, 21], [137, 10, 32], [65, 141, 61, 31, 128, 3], [96, 8, 57]]]
 h' := ![![[75, 25, 69, 103], [142, 165, 109, 56], [97, 18, 95, 55], [68, 66, 102, 22], [50, 115, 70, 97], [144, 139, 165, 86], [0, 0, 1], [0, 1]], ![[148, 37, 113, 134], [12, 13, 109, 128], [98, 150, 5, 58], [140, 104, 108, 151], [5, 26, 156, 140], [23, 56, 119, 48], [118, 56, 99, 6], [75, 25, 69, 103]], ![[45, 104, 152, 97], [3, 136, 17, 21], [33, 153, 163, 47], [162, 20, 101], [115, 45, 63, 142], [5, 47, 142, 148], [107, 76, 58, 101], [148, 37, 113, 134]], ![[0, 1], [87, 20, 99, 129], [73, 13, 71, 7], [53, 144, 23, 161], [130, 148, 45, 122], [112, 92, 75, 52], [100, 35, 9, 60], [45, 104, 152, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [48, 110, 140], []]
 b := ![[], [], [55, 9, 16, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [154, 93, 95, 66, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1209096262, -246547784, -1226687626, -56287695, 589478139]
  a := ![-12, 8, 6, -13, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-441045673, -492119815, -123829139, -212125605, 589478139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, 50, -3, 3, -13]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-93, 50, -3, 3, -13]] 
 ![![167, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![160, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![-93, 50, -3, 3, -13], ![130, -69, -1, -3, 19], ![-162, 86, 8, -1, -22], ![144, -80, -1, 4, 15], ![-34, 26, -18, -4, 5]]]
  hmulB := by decide  
  f := ![![![-189, -316, -391, -301, -108]], ![![-52, -91, -119, -93, -34]], ![![-174, -298, -380, -295, -107]], ![![-8, -30, -63, -54, -22]], ![![-60, -118, -174, -140, -53]]]
  g := ![![![-7, 50, -3, 3, -13], ![14, -69, -1, -3, 19], ![-24, 86, 8, -1, -22], ![18, -80, -1, 4, 15], ![8, 26, -18, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-189, -316, -391, -301, -108]] ![![-93, 50, -3, 3, -13]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![221, 482, -739, -765, 897]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![221, 482, -739, -765, 897]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![88, 134, 58, 68, 1]] where
  M :=![![![221, 482, -739, -765, 897], ![-10474, 4001, 8879, -2243, -2427], ![20690, -10982, -14586, 8879, 184], ![1224, 4160, -5437, -6446, 7217], ![-47986, 15530, 43274, -6176, -15325]]]
  hmulB := by decide  
  f := ![![![-69, -12, 135, 137, 64]], ![![-368, -225, 353, 407, 210]], ![![-486, -354, 262, 353, 197]], ![![-1070, -814, 543, 750, 426]], ![![-910, -624, 646, 802, 431]]]
  g := ![![![-455, -692, -305, -357, 897], ![1174, 1903, 865, 941, -2427], ![26, -206, -146, -21, 184], ![-3664, -5566, -2451, -2874, 7217], ![7518, 11960, 5388, 5988, -15325]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [130, 156, 162, 169, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 68, 127, 30], [110, 110, 91, 63], [79, 167, 128, 80], [0, 1]]
 g := ![![[48, 160, 7, 95], [124, 85, 16], [77, 71, 23, 139], [155, 96, 41, 35], [16, 155, 37], [4, 1], []], ![[81, 123, 117, 109, 45, 65], [97, 23, 121], [133, 79, 54, 165, 82, 72], [156, 127, 51, 10, 128, 42], [71, 51, 172], [163, 90, 167, 120, 90, 114], [80, 148, 35]], ![[131, 38, 108, 146, 96, 145], [153, 77, 121], [12, 35, 2, 64, 53, 20], [117, 136, 40, 132, 141, 153], [120, 42, 121], [158, 89, 22, 28, 116, 12], [92, 8, 163]], ![[156, 140, 38, 155, 114, 58], [172, 135, 151], [28, 76, 37, 171, 57, 69], [69, 10, 15, 29, 98, 107], [78, 45, 34], [101, 172, 66, 14, 116, 108], [91, 62, 172]]]
 h' := ![![[161, 68, 127, 30], [26, 34, 13, 152], [24, 14, 154, 4], [91, 25, 102, 100], [170, 141, 166, 143], [172, 111, 61, 27], [0, 0, 1], [0, 1]], ![[110, 110, 91, 63], [6, 125, 0, 66], [81, 24, 76, 162], [152, 22, 152, 146], [137, 31, 107, 167], [168, 112, 124, 93], [124, 37, 76, 65], [161, 68, 127, 30]], ![[79, 167, 128, 80], [5, 30, 27, 62], [0, 89, 105, 162], [60, 32, 85, 96], [79, 90, 0, 105], [121, 96, 90, 11], [140, 158, 141, 85], [110, 110, 91, 63]], ![[0, 1], [8, 157, 133, 66], [140, 46, 11, 18], [19, 94, 7, 4], [102, 84, 73, 104], [143, 27, 71, 42], [120, 151, 128, 23], [79, 167, 128, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [86, 16, 162], []]
 b := ![[], [], [139, 113, 11, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [130, 156, 162, 169, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![513913364546, -142966392098, -516572024160, 11561453548, 235225038468]
  a := ![51, -28, -25, 50, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-116681445206, -183023823970, -81847539048, -92391567412, 235225038468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, 12, -135, -137, -64]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![69, 12, -135, -137, -64]] 
 ![![173, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![124, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![69, 12, -135, -137, -64], ![368, 225, -353, -407, -210], ![486, 354, -262, -353, -197], ![1070, 814, -543, -750, -426], ![1098, 862, -456, -678, -397]]]
  hmulB := by decide  
  f := ![![![-221, -482, 739, 765, -897]], ![![12, -129, 111, 181, -183]], ![![-278, -282, 614, 497, -644]], ![![-85, -194, 292, 307, -358]], ![![225, -204, -75, 217, -124]]]
  g := ![![![158, 12, -135, -137, -64], ![399, 225, -353, -407, -210], ![284, 354, -262, -353, -197], ![582, 814, -543, -750, -426], ![477, 862, -456, -678, -397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![221, 482, -739, -765, 897]] ![![69, 12, -135, -137, -64]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0, 0, 0]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![0, 0, 0, 0, 179]] where
  M :=![![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![0, 0, 0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 5 2 7 [46, 19, 4, 162, 78, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 135, 173, 126, 44], [137, 39, 130, 6, 128], [157, 168, 8, 91, 130], [110, 15, 47, 135, 56], [0, 1]]
 g := ![![[135, 77, 173, 155, 15], [110, 94, 91, 117, 67], [93, 112, 122, 13], [65, 55, 81, 116], [175, 117, 99, 10, 177], [1], []], ![[173, 56, 16, 105, 111, 163, 140, 10], [47, 27, 101, 38, 7, 140, 119, 96], [22, 146, 1, 4], [70, 168, 30, 88], [147, 114, 105, 112, 164, 122, 49, 96], [116, 79, 45, 129, 164, 144, 38, 148], [4, 60, 58, 146]], ![[135, 49, 103, 83, 102, 65, 63, 18], [86, 154, 31, 44, 42, 106, 99, 92], [14, 61, 161, 4], [103, 173, 12, 47], [10, 111, 10, 4, 4, 137, 5, 130], [35, 34, 82, 64, 108, 7, 98, 178], [144, 137, 33, 95]], ![[11, 63, 101, 11, 14, 120, 108, 152], [69, 140, 49, 143, 3, 52, 81, 6], [52, 110], [131, 133, 92, 81], [163, 177, 157, 43, 107, 31, 175, 114], [75, 21, 131, 92, 144, 172, 121, 164], [84, 25, 167, 74]], ![[81, 87, 17, 174, 145, 109, 84, 36], [15, 99, 156, 126, 120, 83, 90, 126], [139, 63, 24, 171], [78, 58, 67, 14], [71, 87, 133, 67, 18, 7, 88, 125], [107, 146, 123, 5, 30, 74, 19, 15], [1, 74, 169, 93]]]
 h' := ![![[55, 135, 173, 126, 44], [131, 107, 32, 64, 146], [16, 0, 116, 137, 109], [78, 135, 100, 32, 152], [5, 32, 178, 0, 37], [133, 160, 175, 17, 101], [0, 0, 1], [0, 1]], ![[137, 39, 130, 6, 128], [14, 45, 99, 133, 74], [129, 156, 44, 55, 92], [70, 116, 150, 123, 2], [28, 4, 121, 170, 154], [131, 96, 56, 165, 87], [156, 21, 137, 133, 82], [55, 135, 173, 126, 44]], ![[157, 168, 8, 91, 130], [35, 26, 108, 13, 157], [19, 62, 75, 41, 110], [22, 177, 165, 163, 2], [74, 44, 99, 152, 91], [171, 33, 109, 173, 146], [152, 37, 45, 95, 72], [137, 39, 130, 6, 128]], ![[110, 15, 47, 135, 56], [144, 36, 8, 44, 136], [163, 86, 127, 43, 135], [7, 29, 62, 162], [22, 1, 53, 18, 9], [94, 2, 87, 4, 140], [21, 65, 47, 58, 72], [157, 168, 8, 91, 130]], ![[0, 1], [150, 144, 111, 104, 24], [39, 54, 175, 82, 91], [139, 80, 60, 57, 23], [133, 98, 86, 18, 67], [27, 67, 110, 178, 63], [61, 56, 128, 72, 132], [110, 15, 47, 135, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 60, 76, 115], [], [], []]
 b := ![[], [14, 69, 174, 112, 34], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 5
  hpos := by decide
  P := [46, 19, 4, 162, 78, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2037502747606, -831585739452, -1677219357197, 509173761029, 398193896532]
  a := ![-12, 9, 7, -10, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11382696914, -4645730388, -9369940543, 2844546151, 2224546908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 183765996899 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4473, 2416, -118, 102, -599]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-4473, 2416, -118, 102, -599]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![49, 127, 1, 0, 0], ![137, 131, 0, 1, 0], ![29, 83, 0, 0, 1]] where
  M :=![![![-4473, 2416, -118, 102, -599], ![5974, -3239, 158, -134, 803], ![-6990, 3778, -185, 158, -937], ![6400, -3468, 168, -145, 859], ![-2260, 1220, -62, 50, -303]]]
  hmulB := by decide  
  f := ![![![55, -36, -48, 20, 1]], ![![-38, 49, -16, -76, 39]], ![![-13, 25, -23, -48, 27]], ![![17, 7, -50, -39, 29]], ![![-11, 19, -14, -34, 19]]]
  g := ![![![26, 297, -118, 102, -599], ![-37, -400, 158, -134, 803], ![42, 466, -185, 158, -937], ![-38, -426, 168, -145, 859], ![15, 153, -62, 50, -303]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [157, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 180], [0, 1]]
 g := ![![[150, 44], [165], [85, 13], [125], [23, 147], [90, 38], [1]], ![[175, 137], [165], [6, 168], [125], [160, 34], [54, 143], [1]]]
 h' := ![![[161, 180], [26, 166], [49, 76], [4, 111], [9, 135], [169, 50], [24, 161], [0, 1]], ![[0, 1], [145, 15], [158, 105], [137, 70], [24, 46], [74, 131], [62, 20], [161, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [89, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [157, 20, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2763, -3772, -48, 2364, 3092]
  a := ![-16, 10, 4, -26, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2287, -3116, -48, 2364, 3092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -28, -11, -3, 1]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-25, -28, -11, -3, 1]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![109, 139, 1, 0, 0], ![108, 58, 0, 1, 0], ![50, 46, 0, 0, 1]] where
  M :=![![![-25, -28, -11, -3, 1], ![-24, -37, -37, -25, -7], ![16, 12, -28, -37, -18], ![66, 30, -73, -76, -41], ![98, 62, -74, -84, -39]]]
  hmulB := by decide  
  f := ![![![1717, -930, 43, -37, 230]], ![![-2294, 1241, -63, 49, -304]], ![![-713, 385, -22, 15, -93]], ![![276, -150, 5, -6, 38]], ![![-104, 56, -4, 2, -13]]]
  g := ![![![8, 9, -11, -3, 1], ![39, 38, -37, -25, -7], ![44, 38, -28, -37, -18], ![101, 91, -73, -76, -41], ![106, 94, -74, -84, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [2, 177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 180], [0, 1]]
 g := ![![[179, 1], [5], [146, 117], [80], [76, 108], [48, 16], [1]], ![[2, 180], [5], [71, 64], [80], [146, 73], [112, 165], [1]]]
 h' := ![![[4, 180], [3, 180], [70, 27], [138, 29], [29, 73], [85, 164], [179, 4], [0, 1]], ![[0, 1], [180, 1], [178, 154], [73, 152], [140, 108], [17, 17], [14, 177], [4, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [91, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [2, 177, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6682, 4258, 7275, -1065, -4183]
  a := ![1, 9, 7, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2627, -4159, 7275, -1065, -4183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -4, -7, 3, 1]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![9, -4, -7, 3, 1]] 
 ![![181, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![118, 0, 0, 0, 1]] where
  M :=![![![9, -4, -7, 3, 1], ![-14, 11, 7, -11, 5], ![-20, 0, 24, 7, -16], ![74, -34, -57, 24, 9], ![-110, 70, 66, -64, 17]]]
  hmulB := by decide  
  f := ![![![-17, 358, -5, -51, -82]], ![![3, 27, 0, -4, -6]], ![![-10, 180, -2, -25, -41]], ![![2, 20, 1, -2, -4]], ![![-12, 234, -2, -32, -53]]]
  g := ![![![3, -4, -7, 3, 1], ![-7, 11, 7, -11, 5], ![-2, 0, 24, 7, -16], ![24, -34, -57, 24, 9], ![-46, 70, 66, -64, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-4473, 2416, -118, 102, -599]] ![![-25, -28, -11, -3, 1]]
  ![![-17, 358, -5, -51, -82]] where
 M := ![![![-17, 358, -5, -51, -82]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-17, 358, -5, -51, -82]] ![![9, -4, -7, 3, 1]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7945, 4320, 5496, -3554, 82]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-7945, 4320, 5496, -3554, 82]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![63, 84, 161, 1, 0], ![125, 83, 169, 0, 1]] where
  M :=![![![-7945, 4320, 5496, -3554, 82], ![1122, -5403, 3800, 7438, -7190], ![41008, -12248, -37963, 3800, 14628], ![-65184, 35104, 45416, -28667, 164], ![44680, -45664, -10504, 50912, -32467]]]
  hmulB := by decide  
  f := ![![![2921, -2208, 136, 74, 558]], ![![-5370, 1619, -88, 346, -410]], ![![4864, -3224, 67, -88, 756]], ![![2673, -2724, 61, 103, 638]], ![![3889, -3601, 109, 120, 857]]]
  g := ![![![1077, 1550, 2952, -3554, 82], ![2258, -175, 112, 7438, -7190], ![-10612, -8092, -16345, 3800, 14628], ![9007, 12720, 24257, -28667, 164], ![4689, -8521, -14243, 50912, -32467]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [96, 101, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 187, 66], [31, 3, 125], [0, 1]]
 g := ![![[176, 72, 48], [107, 50, 3], [77, 119, 36], [45, 42, 97], [37, 81, 79], [92, 134, 1], []], ![[144, 186, 60, 159], [7, 53, 56, 190], [25, 80, 170, 74], [182, 154, 118, 7], [81, 10, 144, 131], [100, 34, 26, 21], [53, 154]], ![[88, 162, 144, 4], [12, 157, 49, 107], [92, 5, 129, 18], [131, 126, 64, 102], [172, 2, 7, 43], [91, 183, 179, 90], [185, 154]]]
 h' := ![![[103, 187, 66], [42, 57, 95], [57, 71, 167], [73, 26, 185], [77, 153, 80], [145, 0, 35], [0, 0, 1], [0, 1]], ![[31, 3, 125], [1, 34, 36], [162, 68, 30], [185, 175, 170], [71, 61, 24], [88, 187, 105], [173, 49, 3], [103, 187, 66]], ![[0, 1], [181, 100, 60], [132, 52, 185], [61, 181, 27], [1, 168, 87], [78, 4, 51], [9, 142, 187], [31, 3, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 160], []]
 b := ![[], [58, 117, 177], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [96, 101, 57, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4771, 1086, 935, -1208, 7656]
  a := ![-3, 0, 1, -4, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4637, -2790, -5751, -1208, 7656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 8, 17, -5, -4]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-21, 8, 17, -5, -4]] 
 ![![191, 0, 0, 0, 0], ![114, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![178, 0, 0, 0, 1]] where
  M :=![![![-21, 8, 17, -5, -4], ![52, -33, -33, 29, -6], ![2, 22, -24, -33, 35], ![-166, 66, 137, -40, -34], ![338, -186, -232, 154, -7]]]
  hmulB := by decide  
  f := ![![![7827, -4330, 189, -181, 1063]], ![![4616, -2555, 111, -107, 627]], ![![5392, -2982, 130, -125, 732]], ![![2646, -1464, 63, -62, 359]], ![![7316, -4046, 176, -170, 993]]]
  g := ![![![-11, 8, 17, -5, -4], ![38, -33, -33, 29, -6], ![-18, 22, -24, -33, 35], ![-88, 66, 137, -40, -34], ![224, -186, -232, 154, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -28, 57, 49, -62]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-25, -28, 57, 49, -62]] 
 ![![191, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![97, 0, 1, 0, 0], ![158, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![-25, -28, 57, 49, -62], ![726, -283, -609, 163, 160], ![-1386, 746, 966, -609, 3], ![-154, -250, 425, 414, -498], ![3362, -1122, -3000, 482, 1023]]]
  hmulB := by decide  
  f := ![![![6871, -718, -399, -1107, -9]], ![![4921, -475, -292, -804, -18]], ![![3543, -372, -203, -568, -3]], ![![5678, -548, -333, -924, -19]], ![![1976, -190, -112, -318, -5]]]
  g := ![![![-32, -28, 57, 49, -62], ![336, -283, -609, 163, 160], ![-530, 746, 966, -609, 3], ![-239, -250, 425, 414, -498], ![1658, -1122, -3000, 482, 1023]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-7945, 4320, 5496, -3554, 82]] ![![-21, 8, 17, -5, -4]]
  ![![1020157, -335024, -915451, 138425, 318482]] where
 M := ![![![1020157, -335024, -915451, 138425, 318482]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![1020157, -335024, -915451, 138425, 318482]] ![![-25, -28, 57, 49, -62]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![2049502771, -1008622104, -1518762476, 763704714, 137271509]]]
 hmul := by decide  
 g := ![![![![10730381, -5280744, -7951636, 3998454, 718699]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19487, 22376, -12200, -16854, -10488]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![19487, 22376, -12200, -16854, -10488]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![158, 123, 179, 115, 1]] where
  M :=![![![19487, 22376, -12200, -16854, -10488], ![75826, 49941, -26952, -41254, -23220], ![44084, 48796, -15987, -26952, -18034], ![118912, 88056, -30716, -55139, -33318], ![92376, 82848, -21876, -42916, -28187]]]
  hmulB := by decide  
  f := ![![![4015, -1640, -3296, 1010, 772]], ![![-10006, 6205, 6192, -5582, 1248]], ![![-932, -4060, 5005, 6192, -6830]], ![![32272, -13032, -26636, 7901, 6430]], ![![14940, -8733, -9753, 7565, -1067]]]
  g := ![![![8687, 6800, 9664, 6162, -10488], ![19402, 15057, 21396, 13622, -23220], ![14992, 11746, 16643, 10606, -18034], ![27892, 21690, 30742, 19567, -33318], ![23554, 18393, 26029, 16573, -28187]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [47, 187, 143, 89, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 72, 19, 179], [106, 177, 41, 73], [173, 136, 133, 134], [0, 1]]
 g := ![![[53, 132, 154, 169], [123, 164, 179], [95, 192, 145], [130, 51, 63], [11, 116, 6], [58, 104, 1], []], ![[109, 107, 4, 130, 58, 181], [33, 99, 118], [189, 149, 54], [78, 81, 8], [132, 103, 28], [79, 38, 12], [95, 133, 150, 62, 49, 151]], ![[39, 112, 6, 112, 160, 53], [38, 125, 172], [119, 187, 7], [131, 104, 75], [0, 161, 4], [169, 82, 185], [24, 82, 122, 152, 182, 122]], ![[9, 151, 0, 42, 26, 175], [51, 161, 185], [49, 182, 151], [126, 84, 184], [136, 52, 166], [133, 43, 170], [97, 136, 42, 32, 178, 166]]]
 h' := ![![[18, 72, 19, 179], [174, 118, 191, 13], [92, 156, 96, 117], [73, 133, 166, 97], [59, 41, 20, 16], [169, 92, 3, 44], [0, 0, 0, 1], [0, 1]], ![[106, 177, 41, 73], [192, 90, 47, 40], [44, 67, 66, 73], [186, 155, 77, 61], [68, 108, 40, 104], [17, 162, 191, 75], [16, 34, 68, 28], [18, 72, 19, 179]], ![[173, 136, 133, 134], [89, 187, 69, 111], [36, 140, 150, 128], [15, 113, 88, 134], [162, 97, 66, 123], [82, 155, 81, 2], [43, 64, 121, 125], [106, 177, 41, 73]], ![[0, 1], [144, 184, 79, 29], [15, 23, 74, 68], [52, 178, 55, 94], [143, 140, 67, 143], [121, 170, 111, 72], [179, 95, 4, 39], [173, 136, 133, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 171, 77], []]
 b := ![[], [], [128, 129, 1, 147], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [47, 187, 143, 89, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![828671227, 459762786, -1616222584, -1062854444, 1564759332]
  a := ![12, -6, -3, 8, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1276701053, -994847850, -1459627684, -937876568, 1564759332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4015, -1640, -3296, 1010, 772]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![4015, -1640, -3296, 1010, 772]] 
 ![![193, 0, 0, 0, 0], ![157, 1, 0, 0, 0], ![142, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![149, 0, 0, 0, 1]] where
  M :=![![![4015, -1640, -3296, 1010, 772], ![-10006, 6205, 6192, -5582, 1248], ![-932, -4060, 5005, 6192, -6830], ![32272, -13032, -26636, 7901, 6430], ![-64664, 35856, 44068, -29932, 1709]]]
  hmulB := by decide  
  f := ![![![19487, 22376, -12200, -16854, -10488]], ![![16245, 18461, -10064, -13924, -8652]], ![![14566, 16716, -9059, -12540, -7810]], ![![1020, 920, -412, -635, -390]], ![![15523, 17704, -9532, -13234, -8243]]]
  g := ![![![3163, -1640, -3296, 1010, 772], ![-10503, 6205, 6192, -5582, 1248], ![4760, -4060, 5005, 6192, -6830], ![25238, -13032, -26636, 7901, 6430], ![-62625, 35856, 44068, -29932, 1709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![19487, 22376, -12200, -16854, -10488]] ![![4015, -1640, -3296, 1010, 772]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42101, 21684, -1466, 768, -5565]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-42101, 21684, -1466, 768, -5565]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![156, 152, 47, 1, 0], ![100, 2, 63, 0, 1]] where
  M :=![![![-42101, 21684, -1466, 768, -5565], ![54952, -30849, 314, -2164, 7101], ![-63906, 35502, -2759, 314, -9265], ![61676, -30760, -668, -3911, 6647], ![-17836, 13508, -2614, -2134, -4225]]]
  hmulB := by decide  
  f := ![![![-3261, 3080, 1008, -3350, 1991]], ![![-22252, 6143, 21080, -1334, -8691]], ![![64454, -29690, -49701, 21080, 7357]], ![![-4518, 226, 5255, 1207, -3294]], ![![18310, -7808, -14717, 5082, 3028]]]
  g := ![![![2003, -426, 1589, 768, -5565], ![-1612, 1441, -1753, -2164, 7101], ![4130, 32, 2874, 314, -9265], ![36, 2794, -1196, -3911, 6647], ![3744, 1758, 1847, -2134, -4225]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [126, 136, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 54, 152], [45, 142, 45], [0, 1]]
 g := ![![[114, 153, 107], [60, 65], [70, 43, 154], [185, 107], [31, 114], [36, 101], [1]], ![[48, 76, 31, 185], [136, 92], [34, 137, 6, 75], [179, 22], [44, 33], [61, 137], [128, 167, 58, 86]], ![[85, 94, 186, 67], [81, 70], [112, 91, 115, 184], [193, 6], [69, 104], [141, 196], [165, 167, 171, 111]]]
 h' := ![![[17, 54, 152], [178, 78, 86], [45, 130, 159], [117, 69, 101], [141, 124, 86], [111, 102, 36], [71, 61, 62], [0, 1]], ![[45, 142, 45], [31, 180, 34], [15, 129, 180], [48, 159, 8], [185, 103, 131], [193, 123, 128], [14, 94, 149], [17, 54, 152]], ![[0, 1], [108, 136, 77], [55, 135, 55], [195, 166, 88], [171, 167, 177], [0, 169, 33], [6, 42, 183], [45, 142, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 148], []]
 b := ![[], [142, 15, 139], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [126, 136, 135, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30902, -1183610, 280942, 1216876, -595883]
  a := ![9, -6, -5, 8, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-660982, -938868, -98333, 1216876, -595883]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3261, -3080, -1008, 3350, -1991]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![3261, -3080, -1008, 3350, -1991]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![122, 52, 1, 0, 0], ![120, 68, 0, 1, 0], ![17, 168, 0, 0, 1]] where
  M :=![![![3261, -3080, -1008, 3350, -1991], ![22252, -6143, -21080, 1334, 8691], ![-64454, 29690, 49701, -21080, -7357], ![28364, -25736, -9774, 27613, -15739], ![82928, -12008, -88954, -10782, 48693]]]
  hmulB := by decide  
  f := ![![![42101, -21684, 1466, -768, 5565]], ![![-54952, 30849, -314, 2164, -7101]], ![![11892, -5466, 839, 94, 1619]], ![![6364, -2404, 788, 299, 905]], ![![-43139, 24368, -128, 1790, -5554]]]
  g := ![![![-1228, 792, -1008, 3350, -1991], ![11605, -2339, -21080, 1334, 8691], ![-17631, 582, 49701, -21080, -7357], ![-9265, 6340, -9774, 27613, -15739], ![57875, -14384, -88954, -10782, 48693]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [45, 188, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 196], [0, 1]]
 g := ![![[118, 154], [1], [34, 163], [4], [187], [114], [9, 1]], ![[125, 43], [1], [122, 34], [4], [187], [114], [18, 196]]]
 h' := ![![[9, 196], [101, 101], [46, 1], [23, 153], [20, 195], [113, 37], [186, 36], [0, 1]], ![[0, 1], [25, 96], [55, 196], [21, 44], [2, 2], [52, 160], [116, 161], [9, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [179, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [45, 188, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![673, -168, 46, 1107, 517]
  a := ![4, 0, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-744, -836, 46, 1107, 517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-42101, 21684, -1466, 768, -5565]] ![![3261, -3080, -1008, 3350, -1991]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![-197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)


lemma PB314I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB314I4 : PrimesBelowBoundCertificateInterval O 151 197 314 where
  m := 9
  g := ![2, 4, 2, 2, 1, 3, 3, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB314I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2, I163N3]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1]
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
    · exact ![607573201, 157]
    · exact ![26569, 163, 163, 163]
    · exact ![777796321, 167]
    · exact ![895745041, 173]
    · exact ![183765996899]
    · exact ![32761, 32761, 181]
    · exact ![6967871, 191, 191]
    · exact ![1387488001, 193]
    · exact ![7645373, 38809]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
      exact NI163N3
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I163N1, I163N2, I163N3, I167N1, I173N1, I181N2, I191N1, I191N2, I193N1]
  Il := ![[I157N1], [I163N1, I163N2, I163N3], [I167N1], [I173N1], [], [I181N2], [I191N1, I191N2], [I193N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
