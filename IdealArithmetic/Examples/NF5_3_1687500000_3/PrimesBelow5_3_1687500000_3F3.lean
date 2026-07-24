
import IdealArithmetic.Examples.NF5_3_1687500000_3.RI5_3_1687500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -7, 1, -2, 2]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![3, -7, 1, -2, 2]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![2, 31, 1, 0, 0], ![76, 56, 0, 1, 0], ![23, 37, 0, 0, 1]] where
  M :=![![![3, -7, 1, -2, 2], ![-44, -2, 37, 46, -92], ![92, 177, -232, -110, 276], ![472, -317, -131, -539, 836], ![192, -82, -92, -228, 365]]]
  hmulB := by decide  
  f := ![![![58593, -34403, -9541, -14586, 31630]], ![![19988, -11750, -3259, -4982, 10804]], ![![6950, -4085, -1133, -1732, 3756]], ![![51996, -30537, -8469, -12947, 28076]], ![![19225, -11293, -3132, -4788, 10383]]]
  g := ![![![1, 0, 1, -2, 2], ![-14, -3, 37, 46, -92], ![24, 31, -232, -110, 276], ![210, 28, -131, -539, 836], ![87, 19, -92, -228, 365]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [65, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 106], [0, 1]]
 g := ![![[41, 36], [76, 34], [61], [91, 87], [48], [10, 1]], ![[80, 71], [95, 73], [61], [105, 20], [48], [20, 106]]]
 h' := ![![[10, 106], [89, 101], [38, 81], [77, 32], [47, 27], [99, 35], [0, 1]], ![[0, 1], [29, 6], [99, 26], [76, 75], [103, 80], [21, 72], [10, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [20, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [65, 97, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![294122, -300723, -635, -310683, 463411]
  a := ![-189, -11, 173, 177, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![123821, -271, -635, -310683, 463411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 10, 2, 3, -7]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-16, 10, 2, 3, -7]] 
 ![![107, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![103, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![-16, 10, 2, 3, -7], ![-14, -1, 12, 10, -22], ![-20, 40, -17, 20, -20], ![227, 12, -206, -242, 471], ![96, 8, -88, -96, 191]]]
  hmulB := by decide  
  f := ![![![1086, -560, -426, -799, 1901]], ![![62, -37, -24, -44, 104]], ![![1194, -640, -467, -871, 2069]], ![![261, -178, -100, -179, 420]], ![![1162, -632, -454, -845, 2006]]]
  g := ![![![4, 10, 2, 3, -7], ![8, -1, 12, 10, -22], ![33, 40, -17, 20, -20], ![-220, 12, -206, -242, 471], ![-85, 8, -88, -96, 191]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14859, 16504, 5426, 8430, -18878]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-14859, 16504, 5426, 8430, -18878]] 
 ![![107, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![105, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-14859, 16504, 5426, 8430, -18878], ![-23500, 26305, 8660, 13456, -30140], ![-37648, 42212, 13901, 21600, -48384], ![-18490, 20766, 6840, 10629, -23810], ![-18216, 20518, 6762, 10508, -23541]]]
  hmulB := by decide  
  f := ![![![-6117, 4352, 2350, 4150, -9694]], ![![-526, 377, 200, 356, -832]], ![![-4649, 3308, 1787, 3150, -7366]], ![![-6925, 4886, 2690, 4715, -11000]], ![![-2583, 1822, 1004, 1758, -4103]]]
  g := ![![![-7115, 16504, 5426, 8430, -18878], ![-11350, 26305, 8660, 13456, -30140], ![-18217, 42212, 13901, 21600, -48384], ![-8963, 20766, 6840, 10629, -23810], ![-8859, 20518, 6762, 10508, -23541]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2

def I107N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-444, 498, 164, 255, -571]] i)))

def SI107N3: IdealEqSpanCertificate' Table ![![-444, 498, 164, 255, -571]] 
 ![![107, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![106, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-444, 498, 164, 255, -571], ![-710, 801, 260, 406, -910], ![-1148, 1272, 437, 660, -1484], ![-625, 646, 250, 390, -845], ![-584, 630, 226, 348, -769]]]
  hmulB := by decide  
  f := ![![![-106854, 62712, 17380, 26565, -57599]], ![![-68246, 40053, 11100, 16966, -36786]], ![![-83996, 49296, 13661, 20880, -45272]], ![![-105697, 62032, 17190, 26274, -56967]], ![![520, -306, -86, -132, 287]]]
  g := ![![![-702, 498, 164, 255, -571], ![-1122, 801, 260, 406, -910], ![-1816, 1272, 437, 660, -1484], ![-999, 646, 250, 390, -845], ![-928, 630, 226, 348, -769]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N3 : Nat.card (O ⧸ I107N3) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N3)

lemma isPrimeI107N3 : Ideal.IsPrime I107N3 := prime_ideal_of_norm_prime hp107.out _ NI107N3
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![3, -7, 1, -2, 2]] ![![-16, 10, 2, 3, -7]]
  ![![-232, 69, 141, 251, -447]] where
 M := ![![![-232, 69, 141, 251, -447]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-232, 69, 141, 251, -447]] ![![-14859, 16504, 5426, 8430, -18878]]
  ![![18982, -21271, -7025, -10893, 24409]] where
 M := ![![![18982, -21271, -7025, -10893, 24409]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N2 : IdealMulLeCertificate' Table 
  ![![18982, -21271, -7025, -10893, 24409]] ![![-444, 498, 164, 255, -571]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![7292371, -8180043, -2694153, -4186054, 9377052]]]
 hmul := by decide  
 g := ![![![![68153, -76449, -25179, -39122, 87636]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2, I107N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
    exact isPrimeI107N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1 ⊙ MulI107N2)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7349, 525, 5909, 7910, -14924]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-7349, 525, 5909, 7910, -14924]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![7, 22, 51, 19, 1]] where
  M :=![![![-7349, 525, 5909, 7910, -14924], ![33740, 29304, -54257, -35950, 83300], ![156100, -175717, 15254, -169914, 240300], ![-1182064, -219039, 1210043, 1268809, -2541952], ![-447704, -123112, 492646, 480096, -981473]]]
  hmulB := by decide  
  f := ![![![-5473, 4351, 1321, 2034, -4492]], ![![-4412, 4408, 1389, 2138, -4756]], ![![-5324, 6009, 1878, 2866, -6372]], ![![-1328, 2125, 585, 837, -1824]], ![![-3967, 4365, 1350, 2055, -4561]]]
  g := ![![![891, 3017, 7037, 2674, -14924], ![-5040, -16544, -39473, -14850, 83300], ![-14000, -50113, -112294, -43446, 240300], ![152400, 511045, 1200455, 454733, -2541952], ![58923, 196966, 463741, 175487, -981473]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [25, 30, 49, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 62, 29, 55], [45, 32, 3, 49], [10, 14, 77, 5], [0, 1]]
 g := ![![[59, 105, 79, 20], [96, 97, 9], [104, 9, 6, 74], [16, 59, 3, 34], [69, 106, 1], []], ![[85, 61, 108, 3, 42, 96], [66, 24, 106], [51, 38, 92, 42, 40, 47], [73, 3, 64, 35, 97, 14], [24, 28, 29], [31, 53, 55, 66, 35, 41]], ![[100, 105, 67, 38, 73, 22], [88, 74, 5], [6, 96, 67, 2, 107, 73], [21, 49, 11, 37, 71, 97], [96, 14, 26], [64, 104, 30, 10, 22, 38]], ![[72, 69, 12, 65, 11, 12], [37, 23, 97], [41, 85, 77, 79, 91, 81], [92, 55, 88, 14, 21, 87], [76, 92, 22], [41, 13, 90, 80, 59, 16]]]
 h' := ![![[51, 62, 29, 55], [36, 86, 86, 42], [16, 22, 52, 106], [36, 41, 41, 40], [19, 76, 63, 19], [0, 0, 0, 1], [0, 1]], ![[45, 32, 3, 49], [19, 3, 15, 65], [90, 107, 64, 18], [41, 7, 42, 51], [32, 102, 106, 79], [95, 78, 65, 47], [51, 62, 29, 55]], ![[10, 14, 77, 5], [25, 58, 46, 43], [63, 88, 67, 21], [11, 60, 97, 34], [95, 75, 30, 83], [36, 2, 20, 35], [45, 32, 3, 49]], ![[0, 1], [92, 71, 71, 68], [6, 1, 35, 73], [88, 1, 38, 93], [33, 74, 19, 37], [84, 29, 24, 26], [10, 14, 77, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [75, 34, 34], []]
 b := ![[], [], [94, 2, 29, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [25, 30, 49, 3, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8764289171390, -339409085034086, 282712528071412, -13238322767194, -140143138242314]
  a := ![171, -54, -156, -226, 350]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9080424374932, 25171926204558, 68165253013114, 24307167925108, -140143138242314]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5473, 4351, 1321, 2034, -4492]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-5473, 4351, 1321, 2034, -4492]] 
 ![![109, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![101, 0, 0, 0, 1]] where
  M :=![![![-5473, 4351, 1321, 2034, -4492], ![-4412, 4408, 1389, 2138, -4756], ![-5324, 6009, 1878, 2866, -6372], ![-1328, 2125, 585, 837, -1824], ![-272, 1518, 452, 652, -1445]]]
  hmulB := by decide  
  f := ![![![-7349, 525, 5909, 7910, -14924]], ![![-4410, 606, 3297, 4750, -8820]], ![![1095, -1588, 411, -1196, 1520]], ![![-11384, -1971, 11535, 12221, -24416]], ![![-10917, -643, 9995, 11734, -22833]]]
  g := ![![![1108, 4351, 1321, 2034, -4492], ![1315, 4408, 1389, 2138, -4756], ![1700, 6009, 1878, 2866, -6372], ![225, 2125, 585, 837, -1824], ![293, 1518, 452, 652, -1445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-7349, 525, 5909, 7910, -14924]] ![![-5473, 4351, 1321, 2034, -4492]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80, 44, 60, 55, -129]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-80, 44, 60, 55, -129]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![68, 16, 11, 1, 0], ![41, 24, 27, 0, 1]] where
  M :=![![![-80, 44, 60, 55, -129], ![-270, 219, 92, 242, -430], ![1564, 736, -1909, -1756, 3612], ![-621, -3844, 3862, 582, -3053], ![40, -1394, 1194, -100, -547]]]
  hmulB := by decide  
  f := ![![![10218, -5990, -1652, -2521, 5461]], ![![3338, -1937, -508, -762, 1634]], ![![676, -328, 3, 52, -172]], ![![6667, -3898, -1061, -1612, 3483]], ![![4526, -2632, -697, -1049, 2254]]]
  g := ![![![13, 20, 26, 55, -129], ![8, 59, 80, 242, -430], ![-240, -512, -709, -1756, 3612], ![752, 532, 707, 582, -3053], ![259, 118, 151, -100, -547]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [12, 12, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 30, 48], [7, 82, 65], [0, 1]]
 g := ![![[24, 84, 98], [26, 52], [73, 28], [105, 31], [25, 38, 87], [1]], ![[100, 66, 58, 58], [36, 4], [49, 81], [39, 50], [56, 78, 52, 48], [44, 92, 9, 78]], ![[90, 39, 37, 39], [12, 99], [35, 87], [29, 63], [72, 102, 45, 101], [97, 51, 85, 35]]]
 h' := ![![[51, 30, 48], [14, 30, 95], [10, 37, 39], [35, 13, 49], [39, 66, 12], [101, 101, 58], [0, 1]], ![[7, 82, 65], [72, 105, 77], [39, 64, 2], [47, 87, 9], [17, 24, 84], [26, 17, 112], [51, 30, 48]], ![[0, 1], [110, 91, 54], [64, 12, 72], [22, 13, 55], [12, 23, 17], [83, 108, 56], [7, 82, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 49], []]
 b := ![[], [77, 97, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [12, 12, 55, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1831683, 50862538, -44995298, -1680971, 27596307]
  a := ![-62, -6, 57, 55, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8985052, -5173038, -6828362, -1680971, 27596307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, -28, -8, -12, 26]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![49, -28, -8, -12, 26]] 
 ![![113, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![49, -28, -8, -12, 26], ![16, -9, -2, -4, 8], ![-8, -2, 11, 12, -24], ![4, 30, -30, -11, 32], ![-24, 26, -6, 4, -5]]]
  hmulB := by decide  
  f := ![![![-639, 520, 244, 420, -974]], ![![-152, 123, 58, 100, -232]], ![![-626, 506, 239, 412, -956]], ![![-109, 82, 42, 73, -170]], ![![-382, 306, 146, 252, -585]]]
  g := ![![![1, -28, -8, -12, 26], ![0, -9, -2, -4, 8], ![2, -2, 11, 12, -24], ![5, 30, -30, -11, 32], ![2, 26, -6, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1046, 698, 316, 545, -1259]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-1046, 698, 316, 545, -1259]] 
 ![![113, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-1046, 698, 316, 545, -1259], ![-2290, 1619, 846, 1494, -3490], ![-7052, 5034, 2683, 4752, -11116], ![-10223, 7316, 3916, 6940, -16239], ![-7776, 5584, 3012, 5344, -12511]]]
  hmulB := by decide  
  f := ![![![380, -20, -336, -383, 763]], ![![218, -25, -182, -219, 431]], ![![16, 42, -57, -9, 49]], ![![613, 146, -668, -644, 1327]], ![![236, 68, -268, -247, 516]]]
  g := ![![![-511, 698, 316, 545, -1259], ![-1207, 1619, 846, 1494, -3490], ![-3763, 5034, 2683, 4752, -11116], ![-5472, 7316, 3916, 6940, -16239], ![-4181, 5584, 3012, 5344, -12511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-80, 44, 60, 55, -129]] ![![49, -28, -8, -12, 26]]
  ![![-380, 20, 336, 383, -763]] where
 M := ![![![-380, 20, 336, 383, -763]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-380, 20, 336, 383, -763]] ![![-1046, 698, 316, 545, -1259]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12470, 14338, 4740, 7367, -16513]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-12470, 14338, 4740, 7367, -16513]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![8, 89, 71, 42, 1]] where
  M :=![![![-12470, 14338, 4740, 7367, -16513], ![-20846, 23517, 7746, 12034, -26958], ![-33732, 37926, 12477, 19376, -43396], ![-16641, 18688, 6124, 9504, -21273], ![-16768, 18688, 6124, 9504, -21273]]]
  hmulB := by decide  
  f := ![![![0, 0, 0, 1, -1]], ![![22, 3, -22, -22, 46]], ![![-4, -90, 79, 8, -52]], ![![-363, 70, 252, 398, -719]], ![![-108, -25, 113, 122, -237]]]
  g := ![![![942, 11685, 9269, 5519, -16513], ![1534, 19077, 15132, 9010, -26958], ![2468, 30710, 24359, 14504, -43396], ![1209, 15055, 11941, 7110, -21273], ![1208, 15055, 11941, 7110, -21273]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [19, 112, 100, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 110, 116, 17], [72, 110, 101, 45], [74, 33, 37, 65], [0, 1]]
 g := ![![[56, 67, 6, 68], [41, 58, 80, 124], [76, 57, 37, 121], [22, 22, 99, 13], [95, 106, 98, 1], []], ![[116, 80, 88, 90, 4, 79], [46, 54, 72, 47, 90, 44], [19, 119, 36, 108, 1, 115], [20, 41, 53, 83, 54, 15], [63, 104, 95, 104, 81, 21], [36, 116, 71, 113, 5, 87]], ![[28, 123, 25, 74, 96, 10], [11, 42, 118, 100, 112, 78], [75, 54, 43, 3, 92, 78], [17, 102, 119, 82, 96, 114], [94, 125, 34, 74, 99, 86], [89, 68, 7, 102, 29, 66]], ![[68, 30, 12, 78], [19, 107, 93, 12, 30, 12], [15, 72, 8, 30, 71, 80], [115, 35, 49, 2, 29, 27], [112, 94, 50, 56, 126, 66], [56, 124, 8, 38, 9, 51]]]
 h' := ![![[79, 110, 116, 17], [110, 71, 17, 103], [80, 29, 109, 39], [90, 6, 115, 11], [100, 46, 7, 34], [0, 0, 0, 1], [0, 1]], ![[72, 110, 101, 45], [113, 71, 36, 114], [17, 26, 112, 5], [32, 112, 109, 70], [111, 105, 85, 15], [103, 85, 47, 51], [79, 110, 116, 17]], ![[74, 33, 37, 65], [107, 105, 15, 37], [92, 66, 93, 51], [67, 107, 21, 76], [123, 78, 4, 30], [82, 73, 71, 8], [72, 110, 101, 45]], ![[0, 1], [102, 7, 59], [63, 6, 67, 32], [53, 29, 9, 97], [24, 25, 31, 48], [46, 96, 9, 67], [74, 33, 37, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [122, 30, 65], []]
 b := ![[], [], [86, 39, 88, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [19, 112, 100, 29, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54760555862195, -16414354776992, 61405630181404, 58744687177062, -120693845774908]
  a := ![295, 33, -270, -263, 604]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7171576459347, 84451479678660, 67958021103936, 40377056769474, -120693845774908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 0, 0, -1, 1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![0, 0, 0, -1, 1]] 
 ![![127, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![0, 0, 0, -1, 1], ![-22, -3, 22, 22, -46], ![4, 90, -79, -8, 52], ![363, -70, -252, -398, 719], ![144, -8, -116, -160, 295]]]
  hmulB := by decide  
  f := ![![![12470, -14338, -4740, -7367, 16513]], ![![3208, -3685, -1218, -1893, 4243]], ![![5666, -6508, -2151, -3343, 7493]], ![![2193, -2518, -832, -1293, 2898]], ![![2194, -2518, -832, -1293, 2898]]]
  g := ![![![0, 0, 0, -1, 1], ![-5, -3, 22, 22, -46], ![5, 90, -79, -8, 52], ![76, -70, -252, -398, 719], ![31, -8, -116, -160, 295]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-12470, 14338, 4740, 7367, -16513]] ![![0, 0, 0, -1, 1]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [111, 9, 45, 75, 121, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 28, 68, 18, 97], [17, 90, 123, 71, 27], [61, 100, 69, 16, 108], [45, 43, 2, 26, 30], [0, 1]]
 g := ![![[14, 118, 7, 122, 58], [38, 95, 65, 125, 100], [130, 114, 124, 63], [71, 29, 109, 12], [110, 25, 10, 1], [], []], ![[113, 35, 85, 61, 124, 20, 112, 66], [0, 90, 26, 75, 21, 65, 97, 29], [73, 129, 14, 36], [88, 24, 40, 25], [59, 17, 115, 59], [6, 13, 82, 105], [1, 46, 118, 108]], ![[107, 102, 40, 124, 125, 25, 57, 113], [76, 72, 75, 58, 8, 119, 80, 75], [83, 14, 45, 53], [89, 76, 46, 58], [13, 88, 64, 94], [89, 65, 44, 114], [10, 128, 120, 74]], ![[66, 118, 94, 99, 53, 27, 94, 112], [80, 16, 101, 102, 89, 1, 37, 80], [72, 65, 39, 113], [69, 46, 37, 75], [66, 127, 64, 28], [11, 29, 113, 114], [96, 65, 100, 5]], ![[30, 9, 27, 68, 119, 28, 59, 116], [48, 92, 21, 118, 9, 122, 66, 72], [85, 7, 115, 28], [101, 58, 3, 45], [14, 94, 126, 38], [11, 17, 95, 105], [90, 120, 80, 114]]]
 h' := ![![[18, 28, 68, 18, 97], [105, 120, 6, 55, 53], [38, 15, 87, 120, 10], [53, 70, 111, 85, 71], [104, 34, 3, 118, 76], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[17, 90, 123, 71, 27], [106, 4, 64, 115, 107], [64, 32, 4, 76, 93], [62, 83, 89, 124, 6], [108, 74, 1, 110, 5], [32, 129, 100, 52, 37], [82, 85, 24, 3, 57], [18, 28, 68, 18, 97]], ![[61, 100, 69, 16, 108], [130, 120, 60, 63, 49], [38, 94, 91, 25, 42], [122, 78, 52, 83, 61], [62, 129, 91, 79, 53], [123, 111, 46, 128, 15], [96, 28, 111, 104, 30], [17, 90, 123, 71, 27]], ![[45, 43, 2, 26, 30], [14, 6, 110, 4, 67], [57, 47, 0, 65, 126], [53, 129, 67, 13, 84], [101, 112, 35, 75, 59], [22, 0, 89, 42, 91], [8, 60, 55, 111, 101], [61, 100, 69, 16, 108]], ![[0, 1], [104, 12, 22, 25, 117], [12, 74, 80, 107, 122], [88, 33, 74, 88, 40], [66, 44, 1, 11, 69], [110, 22, 27, 40, 118], [26, 89, 71, 44, 74], [45, 43, 2, 26, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 8, 12, 79], [], [], []]
 b := ![[], [36, 89, 112, 120, 37], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [111, 9, 45, 75, 121, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3557837602297485620, -609711155691265847, 3599655898430634510, 3819492114231769108, -7627795320934791286]
  a := ![-421, -19, 386, 404, -862]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27159065666393020, -4654283631231037, 27478289300997210, 29156428352914268, -58227445197975506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 38579489651 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6407380, -7187412, -2367072, -3678099, 8239053]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![6407380, -7187412, -2367072, -3678099, 8239053]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![81, 125, 1, 0, 0], ![75, 106, 0, 1, 0], ![79, 93, 0, 0, 1]] where
  M :=![![![6407380, -7187412, -2367072, -3678099, 8239053], ![10300902, -11554943, -3805452, -5913138, 13245606], ![16560324, -18576432, -6117863, -9506292, 21294372], ![8161137, -9154776, -3014958, -4684802, 10494081], ![8089608, -9074514, -2988534, -4643748, 10402123]]]
  hmulB := by decide  
  f := ![![![74, 78, -72, 165, -177]], ![![3390, 509, -3348, -3558, 7110]], ![![3084, 407, -2963, -3093, 6225]], ![![2247, 610, -2418, -2213, 4626]], ![![2164, 441, -2202, -2127, 4378]]]
  g := ![![![-1291150, -639831, -2367072, -3678099, 8239053], ![-2075730, -1028629, -3805452, -5913138, 13245606], ![-3337053, -1653673, -6117863, -9506292, 21294372], ![-1644522, -814931, -3014958, -4684802, 10494081], ![-1630115, -807795, -2988534, -4643748, 10402123]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [136, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 136], [0, 1]]
 g := ![![[15, 136], [76], [76], [93, 128], [126], [88], [1]], ![[0, 1], [76], [76], [95, 9], [126], [88], [1]]]
 h' := ![![[15, 136], [7, 100], [94, 79], [93, 79], [101, 111], [89, 117], [1, 15], [0, 1]], ![[0, 1], [0, 37], [46, 58], [45, 58], [122, 26], [63, 20], [89, 122], [15, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [91, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [136, 122, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-659648, -850924, 1297588, 700640, -1758872]
  a := ![210, 0, -192, -220, 430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-141324, -538264, 1297588, 700640, -1758872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 18, -36, -27, 59]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![24, 18, -36, -27, 59]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![86, 93, 1, 0, 0], ![111, 103, 0, 1, 0], ![106, 74, 0, 0, 1]] where
  M :=![![![24, 18, -36, -27, 59], ![46, -125, 68, -54, 38], ![-1508, -32, 1335, 1612, -3124], ![2589, 3150, -4930, -2762, 6817], ![744, 1274, -1730, -796, 2133]]]
  hmulB := by decide  
  f := ![![![23198, -26444, -8732, -13571, 30413]], ![![38278, -43089, -14196, -22058, 49414]], ![![40998, -46357, -15285, -23752, 53216]], ![![47797, -54071, -17830, -27707, 62078]], ![![38848, -43984, -14506, -22542, 50507]]]
  g := ![![![-1, 13, -36, -27, 59], ![-28, -27, 68, -54, 38], ![262, -431, 1335, 1612, -3124], ![77, 1764, -4930, -2762, 6817], ![86, 630, -1730, -796, 2133]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [100, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 136], [0, 1]]
 g := ![![[43, 37], [115], [50], [39, 99], [18], [69], [1]], ![[0, 100], [115], [50], [135, 38], [18], [69], [1]]]
 h' := ![![[84, 136], [19, 96], [55, 65], [73, 119], [116, 109], [86, 93], [37, 84], [0, 1]], ![[0, 1], [0, 41], [35, 72], [68, 18], [93, 28], [89, 44], [106, 53], [84, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [49, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [100, 53, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141915, -47380, 162886, 158363, -317437]
  a := ![-29, 11, 29, 41, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14014, -58517, 162886, 158363, -317437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-907, 532, 148, 226, -490]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-907, 532, 148, 226, -490]] 
 ![![137, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![100, 0, 0, 1, 0], ![75, 0, 0, 0, 1]] where
  M :=![![![-907, 532, 148, 226, -490], ![-308, 183, 48, 76, -164], ![-88, 56, 7, 8, -24], ![82, -112, 52, 25, -54], ![448, -288, -48, -96, 207]]]
  hmulB := by decide  
  f := ![![![-42135, 47316, 15564, 24174, -54142]], ![![-17716, 19895, 6544, 10164, -22764]], ![![-5401, 6068, 1995, 3098, -6938]], ![![-31134, 34968, 11500, 17861, -40002]], ![![-23445, 26332, 8660, 13450, -30123]]]
  g := ![![![-137, 532, 148, 226, -490], ![-48, 183, 48, 76, -164], ![-17, 56, 7, 8, -24], ![52, -112, 52, 25, -54], ![83, -288, -48, -96, 207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![6407380, -7187412, -2367072, -3678099, 8239053]] ![![24, 18, -36, -27, 59]]
  ![![-42135, 47316, 15564, 24174, -54142]] where
 M := ![![![-42135, 47316, 15564, 24174, -54142]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-42135, 47316, 15564, 24174, -54142]] ![![-907, 532, 148, 226, -490]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59366, -33214, -8994, -13701, 29561]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![59366, -33214, -8994, -13701, 29561]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![39, 21, 123, 41, 1]] where
  M :=![![![59366, -33214, -8994, -13701, 29561], ![15778, -6591, -1412, -2046, 4154], ![-2852, 6120, 2585, 4244, -9796], ![-16725, 12304, 4274, 6892, -15505], ![-38672, 25068, 7668, 12008, -26507]]]
  hmulB := by decide  
  f := ![![![36, -20, -14, -39, 65]], ![![-338, -121, 396, 362, -754]], ![![124, 1536, -1421, -116, 972]], ![![7453, -1190, -5430, -8030, 14829]], ![![2289, 983, -2821, -2451, 5183]]]
  g := ![![![-7867, -4705, -26223, -8818, 29561], ![-1052, -675, -3686, -1240, 4154], ![2728, 1524, 8687, 2920, -9796], ![4230, 2431, 13751, 4623, -15505], ![7159, 4185, 23511, 7905, -26507]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [70, 85, 90, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 5, 19, 20], [13, 84, 101, 18], [1, 49, 19, 101], [0, 1]]
 g := ![![[86, 75, 81, 117], [9, 54, 3, 106], [103, 43, 80], [12, 128, 91, 120], [69, 13, 7], [1], []], ![[100, 0, 8, 79, 25, 136], [19, 94, 73, 121, 48, 30], [125, 75, 54], [32, 42, 81, 42, 115, 136], [24, 6, 131], [112, 103, 64], [87, 2, 122]], ![[102, 59, 102, 132, 84, 15], [66, 75, 101, 55, 79, 130], [23, 65, 51], [47, 69, 32, 3, 96, 15], [16, 88, 67], [3, 109, 96], [12, 78, 46]], ![[75, 109, 5, 115, 70, 8], [117, 67, 113, 13, 31, 92], [83, 0, 136], [116, 62, 122, 35, 71, 3], [83, 104, 31], [5, 18, 44], [115, 48, 54]]]
 h' := ![![[96, 5, 19, 20], [65, 39, 13, 16], [54, 128, 39, 84], [133, 63, 0, 48], [70, 121, 66, 26], [69, 54, 49, 110], [0, 0, 1], [0, 1]], ![[13, 84, 101, 18], [12, 1, 30, 37], [114, 16, 37, 40], [61, 120, 60, 38], [71, 73, 31, 37], [120, 76, 92, 100], [68, 97, 60, 131], [96, 5, 19, 20]], ![[1, 49, 19, 101], [2, 115, 13, 118], [39, 101, 117, 25], [113, 28, 28, 107], [91, 16, 51, 21], [88, 106, 43, 22], [24, 13, 3, 42], [13, 84, 101, 18]], ![[0, 1], [78, 123, 83, 107], [117, 33, 85, 129], [28, 67, 51, 85], [124, 68, 130, 55], [97, 42, 94, 46], [13, 29, 75, 105], [1, 49, 19, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [34, 130, 5], []]
 b := ![[], [], [95, 75, 130, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [70, 85, 90, 29, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![970007980951, 478418917585, -1248450673022, -1037746667927, 2225149131106]
  a := ![83, -1, -76, -85, 170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-617343943397, -332731747019, -1977998516540, -663804755707, 2225149131106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36, -20, -14, -39, 65]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![36, -20, -14, -39, 65]] 
 ![![139, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![36, -20, -14, -39, 65], ![-338, -121, 396, 362, -754], ![124, 1536, -1421, -116, 972], ![7453, -1190, -5430, -8030, 14829], ![3040, -180, -2476, -3272, 6191]]]
  hmulB := by decide  
  f := ![![![59366, -33214, -8994, -13701, 29561]], ![![20614, -11517, -3116, -4746, 10238]], ![![25178, -14054, -3799, -5785, 12477]], ![![37891, -21178, -5728, -8723, 18816]], ![![5274, -2926, -786, -1195, 2574]]]
  g := ![![![32, -20, -14, -39, 65], ![-290, -121, 396, 362, -754], ![57, 1536, -1421, -116, 972], ![6524, -1190, -5430, -8030, 14829], ![2651, -180, -2476, -3272, 6191]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![59366, -33214, -8994, -13701, 29561]] ![![36, -20, -14, -39, 65]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -3, 3, 1, -3]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-2, -3, 3, 1, -3]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![35, 24, 1, 0, 0], ![27, 28, 0, 1, 0], ![144, 84, 0, 0, 1]] where
  M :=![![![-2, -3, 3, 1, -3], ![-18, 6, 9, 20, -34], ![160, 65, -196, -170, 360], ![39, -371, 283, -46, -93], ![48, -138, 76, -52, 33]]]
  hmulB := by decide  
  f := ![![![-180, 57, 23, 41, -93]], ![![-138, 18, 39, 80, -194]], ![![-68, 18, 13, 25, -59]], ![![-65, 18, 14, 27, -64]], ![![-256, 68, 46, 88, -207]]]
  g := ![![![2, 1, 3, 1, -3], ![27, 14, 9, 20, -34], ![-270, -139, -196, -170, 360], ![32, 13, 283, -46, -93], ![-40, -22, 76, -52, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [71, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 148], [0, 1]]
 g := ![![[30, 113], [68], [13, 112], [107], [93, 113], [148], [1]], ![[124, 36], [68], [2, 37], [107], [38, 36], [148], [1]]]
 h' := ![![[105, 148], [36, 115], [120, 98], [125, 74], [102, 133], [46, 34], [78, 105], [0, 1]], ![[0, 1], [42, 34], [129, 51], [147, 75], [61, 16], [40, 115], [77, 44], [105, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [31, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [71, 44, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54192, -562776, 432686, -57716, -153132]
  a := ![213, 9, -193, -208, 436]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![57178, 23704, 432686, -57716, -153132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89639, -52572, -14516, -22160, 48014]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![89639, -52572, -14516, -22160, 48014]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![118, 116, 1, 0, 0], ![10, 111, 0, 1, 0], ![90, 69, 0, 0, 1]] where
  M :=![![![89639, -52572, -14516, -22160, 48014], ![29560, -17211, -4570, -6884, 14800], ![6872, -3578, -335, -180, -24], ![-18800, 11706, 4210, 6923, -15620], ![-50344, 30070, 9086, 14268, -31411]]]
  hmulB := by decide  
  f := ![![![371, -128, -248, -360, 686]], ![![-1400, -1283, 2250, 1556, -3520]], ![![-830, -1050, 1541, 964, -2244]], ![![-690, -923, 1340, 783, -1880]], ![![-298, -645, 760, 368, -943]]]
  g := ![![![-15417, 5222, -14516, -22160, 48014], ![-4660, 1717, -4570, -6884, 14800], ![338, 382, -335, -180, -24], ![5510, -1123, 4210, 6923, -15620], ![10482, -2955, 9086, 14268, -31411]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [126, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 148], [0, 1]]
 g := ![![[22, 85], [129], [38, 64], [63], [29, 24], [54], [1]], ![[120, 64], [129], [89, 85], [63], [104, 125], [54], [1]]]
 h' := ![![[59, 148], [89, 95], [129, 24], [83, 8], [71, 19], [132, 89], [23, 59], [0, 1]], ![[0, 1], [32, 54], [55, 125], [108, 141], [0, 130], [19, 60], [77, 90], [59, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [30, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [126, 90, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![414318, -643209, 187400, -436044, 549119]
  a := ![253, 13, -232, -241, 518]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-448048, -79664, 187400, -436044, 549119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52, -55, -21, -31, 69]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![52, -55, -21, -31, 69]] 
 ![![149, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![52, -55, -21, -31, 69], ![78, -100, -19, -44, 94], ![32, -123, 18, 30, -24], ![351, 117, -433, -344, 763], ![160, 10, -176, -140, 319]]]
  hmulB := by decide  
  f := ![![![115110, -67539, -18689, -28551, 61887]], ![![7212, -4231, -1170, -1787, 3873]], ![![52608, -30865, -8538, -13042, 28268]], ![![47759, -28019, -7749, -11836, 25653]], ![![38212, -22418, -6200, -9470, 20525]]]
  g := ![![![3, -55, -21, -31, 69], ![2, -100, -19, -44, 94], ![-5, -123, 18, 30, -24], ![80, 117, -433, -344, 763], ![32, 10, -176, -140, 319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-2, -3, 3, 1, -3]] ![![89639, -52572, -14516, -22160, 48014]]
  ![![-115110, 67539, 18689, 28551, -61887]] where
 M := ![![![-115110, 67539, 18689, 28551, -61887]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-115110, 67539, 18689, 28551, -61887]] ![![52, -55, -21, -31, 69]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![860, -884, 12, -935, 1363]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![860, -884, 12, -935, 1363]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![139, 149, 1, 0, 0], ![139, 68, 0, 1, 0], ![13, 127, 0, 0, 1]] where
  M :=![![![860, -884, 12, -935, 1363], ![-12010, -2361, 12410, 12890, -25890], ![23580, 52070, -64941, -24760, 72940], ![215445, -80730, -117340, -232646, 407065], ![91808, -22452, -60224, -99000, 179033]]]
  hmulB := by decide  
  f := ![![![270038, -159146, -44512, -68225, 148187]], ![![98290, -59111, -17550, -27390, 60130]], ![![345912, -205053, -58379, -89975, 196073]], ![![292767, -173102, -48908, -75201, 163648]], ![![105156, -62993, -18502, -28785, 63076]]]
  g := ![![![738, -743, 12, -935, 1363], ![-21140, 3709, 12410, 12890, -25890], ![76449, 14229, -64941, -24760, 72940], ![288554, -122347, -117340, -232646, 407065], ![131765, -46717, -60224, -99000, 179033]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [89, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 150], [0, 1]]
 g := ![![[138, 86], [11, 138], [8, 11], [81], [63, 5], [34], [1]], ![[131, 65], [70, 13], [51, 140], [81], [110, 146], [34], [1]]]
 h' := ![![[100, 150], [78, 29], [43, 17], [137, 39], [131, 9], [63, 96], [62, 100], [0, 1]], ![[0, 1], [109, 122], [82, 134], [111, 112], [125, 142], [150, 55], [96, 51], [100, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [146, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [89, 51, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81487, -5105, -67167, -82244, 163718]
  a := ![67, 8, -61, -58, 137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![123982, -34416, -67167, -82244, 163718]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3776, 3827, 1237, 1919, -4285]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-3776, 3827, 1237, 1919, -4285]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![58, 139, 1, 0, 0], ![46, 33, 0, 1, 0], ![47, 145, 0, 0, 1]] where
  M :=![![![-3776, 3827, 1237, 1919, -4285], ![-5102, 5584, 1831, 2844, -6366], ![-7872, 8783, 2890, 4490, -10056], ![-3719, 4235, 1397, 2172, -4867], ![-3408, 4034, 1340, 2084, -4675]]]
  hmulB := by decide  
  f := ![![![98, -83, -29, -59, 147]], ![![462, -196, -281, -344, 806]], ![![474, -221, -273, -348, 816]], ![![123, -81, -54, -80, 197]], ![![476, -223, -274, -347, 818]]]
  g := ![![![249, 2582, 1237, 1919, -4285], ![378, 3843, 1831, 2844, -6366], ![600, 6073, 2890, 4490, -10056], ![292, 2941, 1397, 2172, -4867], ![283, 2827, 1340, 2084, -4675]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [59, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 150], [0, 1]]
 g := ![![[59, 64], [132, 36], [126, 91], [38], [104, 139], [64], [1]], ![[0, 87], [146, 115], [2, 60], [38], [49, 12], [64], [1]]]
 h' := ![![[143, 150], [64, 8], [116, 145], [28, 53], [55, 76], [7, 130], [92, 143], [0, 1]], ![[0, 1], [0, 143], [13, 6], [57, 98], [51, 75], [24, 21], [5, 8], [143, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144]]
 b := ![[], [137, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [59, 8, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40624, -1042130, 923713, 41052, -573108]
  a := ![-287, -5, 258, 282, -588]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-189194, -315843, 923713, 41052, -573108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3843, -2831, -1609, -2876, 6756]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![3843, -2831, -1609, -2876, 6756]] 
 ![![151, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![3843, -2831, -1609, -2876, 6756], ![14328, -10274, -5519, -9786, 22904], ![47068, -33667, -17988, -31870, 74564], ![69206, -49475, -26403, -46771, 109418], ![53928, -38520, -20518, -36336, 84995]]]
  hmulB := by decide  
  f := ![![![505, -1023, 121, -204, 392]], ![![42, -96, 13, -10, 24]], ![![482, -691, -54, -274, 548]], ![![4, -313, 249, 9, -146]], ![![140, -350, 100, -68, 83]]]
  g := ![![![-79, -2831, -1609, -2876, 6756], ![-150, -10274, -5519, -9786, 22904], ![-450, -33667, -17988, -31870, 74564], ![-648, -49475, -26403, -46771, 109418], ![-488, -38520, -20518, -36336, 84995]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![860, -884, 12, -935, 1363]] ![![-3776, 3827, 1237, 1919, -4285]]
  ![![505, -1023, 121, -204, 392]] where
 M := ![![![505, -1023, 121, -204, 392]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![505, -1023, 121, -204, 392]] ![![3843, -2831, -1609, -2876, 6756]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB2009I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB2009I3 : PrimesBelowBoundCertificateInterval O 103 151 2009 where
  m := 9
  g := ![4, 2, 3, 2, 1, 3, 2, 3, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB2009I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2, I107N3]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![11449, 107, 107, 107]
    · exact ![141158161, 109]
    · exact ![1442897, 113, 113]
    · exact ![260144641, 127]
    · exact ![38579489651]
    · exact ![18769, 18769, 137]
    · exact ![373301041, 139]
    · exact ![22201, 22201, 149]
    · exact ![22801, 22801, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
      exact NI107N3
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I107N1, I107N2, I107N3, I109N1, I113N1, I113N2, I127N1, I137N2, I139N1, I149N2, I151N2]
  Il := ![[I107N1, I107N2, I107N3], [I109N1], [I113N1, I113N2], [I127N1], [], [I137N2], [I139N1], [I149N2], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
