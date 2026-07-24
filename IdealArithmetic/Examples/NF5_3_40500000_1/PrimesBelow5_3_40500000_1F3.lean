
import IdealArithmetic.Examples.NF5_3_40500000_1.RI5_3_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, -5, -13, -4, 29]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![8, -5, -13, -4, 29]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![58, 78, 1, 0, 0], ![92, 37, 0, 1, 0], ![98, 3, 0, 0, 1]] where
  M :=![![![8, -5, -13, -4, 29], ![-89, -20, -3, 2, 11], ![-83, -59, -72, -20, 173], ![-248, -91, -51, -3, 120], ![-51, -33, -39, -10, 92]]]
  hmulB := by decide  
  f := ![![![30, 1, 15, 4, -43]], ![![159, 46, 27, 2, -109]], ![![137, 35, 30, 4, -109]], ![![93, 19, 26, 5, -87]], ![![36, 3, 16, 4, -47]]]
  g := ![![![-16, 10, -13, -4, 29], ![-11, 1, -3, 2, 11], ![-103, 54, -72, -20, 173], ![-82, 34, -51, -3, 120], ![-55, 29, -39, -10, 92]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [66, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 106], [0, 1]]
 g := ![![[45, 33], [88, 9], [25], [66, 101], [61], [26, 1]], ![[47, 74], [1, 98], [25], [17, 6], [61], [52, 106]]]
 h' := ![![[26, 106], [77, 51], [60, 104], [31, 5], [56, 23], [103, 75], [0, 1]], ![[0, 1], [12, 56], [89, 3], [54, 102], [12, 84], [20, 32], [26, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [92, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [66, 81, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-186612, -44696, -68436, -6466, 208440]
  a := ![77, -62, 79, 36, -264]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-149996, 45862, -68436, -6466, 208440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-98, -30, -32, -6, 89]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-98, -30, -32, -6, 89]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![72, 77, 1, 0, 0], ![10, 68, 0, 1, 0], ![100, 68, 0, 0, 1]] where
  M :=![![![-98, -30, -32, -6, 89], ![-361, -107, -118, -22, 335], ![-1367, -386, -447, -82, 1289], ![-2468, -660, -808, -149, 2376], ![-937, -254, -306, -56, 896]]]
  hmulB := by decide  
  f := ![![![-132, 10, 30, 8, -55]], ![![163, -69, 0, 4, -1]], ![![28, -41, 19, 8, -36]], ![![88, -44, 4, 3, -6]], ![![-21, -34, 28, 10, -52]]]
  g := ![![![-62, -30, -32, -6, 89], ![-235, -115, -118, -22, 335], ![-909, -449, -447, -82, 1289], ![-1686, -840, -808, -149, 2376], ![-635, -316, -306, -56, 896]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [13, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 106], [0, 1]]
 g := ![![[70, 33], [68, 29], [102], [82, 101], [89], [53, 1]], ![[0, 74], [0, 78], [102], [85, 6], [89], [106, 106]]]
 h' := ![![[53, 106], [79, 51], [81, 55], [4, 40], [89, 84], [60, 14], [0, 1]], ![[0, 1], [0, 56], [0, 52], [91, 67], [47, 23], [53, 93], [53, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [15, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [13, 54, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6725163, -1320796, -2263402, -296538, 7345524]
  a := ![379, -328, 378, 160, -1299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5377077, -2863270, -2263402, -296538, 7345524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 2, -16, -6, 34]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![37, 2, -16, -6, 34]] 
 ![![107, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![37, 2, -16, -6, 34], ![-86, -11, 24, 10, -50], ![110, -2, -61, -22, 130], ![-128, -26, 22, 11, -48], ![48, -2, -28, -10, 59]]]
  hmulB := by decide  
  f := ![![![-77, -70, 76, 30, -158]], ![![-39, -37, 40, 16, -84]], ![![-44, -34, 39, 14, -78]], ![![-25, -36, 38, 17, -86]], ![![-16, -14, 16, 6, -33]]]
  g := ![![![3, 2, -16, -6, 34], ![-1, -11, 24, 10, -50], ![16, -2, -61, -22, 130], ![7, -26, 22, 11, -48], ![8, -2, -28, -10, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![8, -5, -13, -4, 29]] ![![-98, -30, -32, -6, 89]]
  ![![1491, 587, 503, 100, -1240]] where
 M := ![![![1491, 587, 503, 100, -1240]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![1491, 587, 503, 100, -1240]] ![![37, 2, -16, -6, 34]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-12305, -4601, -3531, -642, 8774]]]
 hmul := by decide  
 g := ![![![![-115, -43, -33, -6, 82]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![726, -33, -421, -148, 917]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![726, -33, -421, -148, 917]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![67, 101, 73, 50, 1]] where
  M :=![![![726, -33, -421, -148, 917], ![-2513, -406, 353, 194, -685], ![709, -711, -1946, -652, 4517], ![-5472, -1743, -159, 239, 504], ![89, -445, -967, -298, 2222]]]
  hmulB := by decide  
  f := ![![![-1044, -229, -339, -60, 1063]], ![![-4475, -980, -1455, -258, 4561]], ![![-19193, -4207, -6232, -1104, 19543]], ![![-38892, -8523, -12639, -2239, 39624]], ![![-35615, -7805, -11571, -2050, 36279]]]
  g := ![![![-557, -850, -618, -422, 917], ![398, 631, 462, 316, -685], ![-2770, -4192, -3043, -2078, 4517], ![-360, -483, -339, -229, 504], ![-1365, -2063, -1497, -1022, 2222]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [99, 56, 15, 53, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 10, 12, 82], [32, 84, 94, 84], [2, 14, 3, 52], [0, 1]]
 g := ![![[24, 17, 85, 4], [54, 89, 35], [59, 74, 2, 97], [45, 31, 42, 80], [69, 56, 1], []], ![[66, 108, 1, 43, 101, 84], [58, 64, 4], [96, 9, 106, 84, 80, 61], [106, 36, 35, 18, 92, 49], [49, 47, 16], [73, 9, 10, 99, 44, 46]], ![[23, 66, 46, 45, 48, 21], [86, 0, 106], [102, 9, 36, 55, 21, 82], [76, 64, 75, 83, 42, 89], [61, 66, 104], [89, 77, 58, 59, 49, 71]], ![[83, 63, 5, 47, 64, 13], [34, 15, 64], [70, 84, 76, 32, 0, 44], [18, 38, 28, 6, 104, 62], [45, 37, 83], [79, 41, 43, 46, 26, 107]]]
 h' := ![![[22, 10, 12, 82], [58, 21, 47, 2], [45, 30, 28, 97], [14, 67, 30, 73], [36, 75, 90, 25], [0, 0, 0, 1], [0, 1]], ![[32, 84, 94, 84], [81, 93, 16, 106], [68, 96, 69, 2], [106, 59, 87, 74], [74, 91, 17, 14], [42, 58, 71, 4], [22, 10, 12, 82]], ![[2, 14, 3, 52], [72, 25, 9, 55], [56, 15, 41, 18], [93, 42, 79, 36], [49, 12, 87, 52], [86, 82, 24, 39], [32, 84, 94, 84]], ![[0, 1], [28, 79, 37, 55], [48, 77, 80, 101], [1, 50, 22, 35], [40, 40, 24, 18], [35, 78, 14, 65], [2, 14, 3, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [48, 2, 47], []]
 b := ![[], [], [107, 24, 89, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [99, 56, 15, 53, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23212895547, -4940531347, -7792952381, -1401297446, 24285311189]
  a := ![40, -33, 41, 18, -137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15140630690, -22548229004, -16335969442, -11152906944, 24285311189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1044, 229, 339, 60, -1063]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![1044, 229, 339, 60, -1063]] 
 ![![109, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![1044, 229, 339, 60, -1063], ![4475, 980, 1455, 258, -4561], ![19193, 4207, 6232, 1104, -19543], ![38892, 8523, 12639, 2239, -39624], ![14423, 3161, 4685, 830, -14690]]]
  hmulB := by decide  
  f := ![![![-726, 33, 421, 148, -917]], ![![-643, 34, 383, 134, -835]], ![![-193, 15, 126, 44, -277]], ![![-456, 39, 295, 101, -644]], ![![-527, 28, 314, 110, -685]]]
  g := ![![![441, 229, 339, 60, -1063], ![1894, 980, 1455, 258, -4561], ![8110, 4207, 6232, 1104, -19543], ![16448, 8523, 12639, 2239, -39624], ![6097, 3161, 4685, 830, -14690]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![726, -33, -421, -148, 917]] ![![1044, 229, 339, 60, -1063]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, -3, 0, 2]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![3, 1, -3, 0, 2]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![24, 95, 110, 1, 0], ![58, 57, 55, 0, 1]] where
  M :=![![![3, 1, -3, 0, 2], ![-10, 2, -3, -6, 14], ![14, -65, 64, 36, -190], ![228, 141, -111, -59, 192], ![38, -7, 17, 8, -65]]]
  hmulB := by decide  
  f := ![![![-21, -3, 5, 2, -10]], ![![22, -4, -13, -4, 26]], ![![-74, -9, 4, 2, -10]], ![![-58, -13, -6, -1, 10]], ![![-36, -8, -2, 0, 3]]]
  g := ![![![-1, -1, -1, 0, 2], ![-6, -2, -1, -6, 14], ![90, 65, 58, 36, -190], ![-84, -46, -37, -59, 192], ![32, 26, 24, 8, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [9, 104, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 87, 71], [88, 25, 42], [0, 1]]
 g := ![![[39, 103, 98], [85, 52], [30, 83], [42, 53], [24, 96, 13], [1]], ![[76, 56, 100, 58], [71, 99], [86, 28], [16, 72], [64, 13, 81, 107], [54, 32, 31, 40]], ![[77, 68, 50, 17], [24, 72], [68, 14], [38, 9], [63, 110, 98, 17], [30, 96, 101, 73]]]
 h' := ![![[101, 87, 71], [18, 0, 95], [61, 80, 74], [61, 87, 99], [10, 111, 36], [104, 9, 76], [0, 1]], ![[88, 25, 42], [24, 60, 2], [18, 84, 72], [1, 7, 64], [22, 45, 80], [46, 40, 53], [101, 87, 71]], ![[0, 1], [19, 53, 16], [3, 62, 80], [84, 19, 63], [58, 70, 110], [38, 64, 97], [88, 25, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 57], []]
 b := ![[], [96, 32, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [9, 104, 37, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9384225143, -2016567360, -2758279738, -470896368, 9061574012]
  a := ![-240, 198, -243, -111, 823]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4634106239, -4192841868, -3976515486, -470896368, 9061574012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3396, -745, -1105, -196, 3463]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-3396, -745, -1105, -196, 3463]] 
 ![![113, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![-3396, -745, -1105, -196, 3463], ![-14571, -3194, -4731, -838, 14833], ![-62433, -13687, -20290, -3596, 63607], ![-126560, -27739, -41115, -7285, 128904], ![-46921, -10285, -15247, -2702, 47800]]]
  hmulB := by decide  
  f := ![![![378, 999, -931, -516, 2293]], ![![113, 363, -334, -190, 836]], ![![199, 172, -187, -76, 386]], ![![-242, -36, 78, -3, -67]], ![![353, 868, -814, -446, 1991]]]
  g := ![![![-2555, -745, -1105, -196, 3463], ![-10943, -3194, -4731, -838, 14833], ![-46929, -13687, -20290, -3596, 63607], ![-95105, -27739, -41115, -7285, 128904], ![-35267, -10285, -15247, -2702, 47800]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44, 10, -16, 0, 15]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![44, 10, -16, 0, 15]] 
 ![![113, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![44, 10, -16, 0, 15], ![-75, 43, -20, -32, 105], ![-77, -342, 313, 184, -801], ![752, 708, -740, -315, 1560], ![45, -50, 38, 34, -130]]]
  hmulB := by decide  
  f := ![![![68698, 15062, 22330, 3958, -69999]], ![![47595, 10435, 15470, 2742, -48495]], ![![48259, 10580, 15685, 2780, -49170]], ![![70678, 15494, 22970, 4071, -72009]], ![![65545, 14370, 21304, 3776, -66784]]]
  g := ![![![-10, 10, -16, 0, 15], ![-83, 43, -20, -32, 105], ![592, -342, 313, 184, -801], ![-1135, 708, -740, -315, 1560], ![97, -50, 38, 34, -130]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![3, 1, -3, 0, 2]] ![![-3396, -745, -1105, -196, 3463]]
  ![![68698, 15062, 22330, 3958, -69999]] where
 M := ![![![68698, 15062, 22330, 3958, -69999]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![68698, 15062, 22330, 3958, -69999]] ![![44, 10, -16, 0, 15]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-128, -10, 70, 26, -163]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-128, -10, 70, 26, -163]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![60, 92, 118, 91, 1]] where
  M :=![![![-128, -10, 70, 26, -163], ![451, 65, -74, -42, 107], ![53, 22, 481, 146, -1267], ![1920, 404, 220, -9, -984], ![261, 70, 272, 72, -764]]]
  hmulB := by decide  
  f := ![![![-6, -2, 0, 0, 1]], ![![-5, -5, -4, 0, 7]], ![![-35, -2, -19, -8, 49]], ![![-64, -44, 12, 9, -24]], ![![-85, -38, -12, -1, 34]]]
  g := ![![![76, 118, 152, 117, -163], ![-47, -77, -100, -77, 107], ![599, 918, 1181, 909, -1267], ![480, 716, 916, 705, -984], ![363, 554, 712, 548, -764]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [84, 7, 110, 54, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 64, 57, 34], [111, 115, 4, 22], [108, 74, 66, 71], [0, 1]]
 g := ![![[35, 45, 38, 61], [56, 39, 73, 11], [61, 113, 111, 1], [67, 66, 80, 72], [78, 12, 73, 1], []], ![[84, 11, 41, 97, 79, 64], [103, 1, 52, 114, 114, 44], [123, 41, 18, 69, 20, 62], [3, 82, 116, 83, 43, 37], [86, 93, 46, 122, 89, 107], [63, 115, 126, 81, 72, 61]], ![[20, 118, 98, 33, 101, 81], [103, 117, 44, 16, 33, 52], [41, 63, 75, 65, 23, 60], [103, 76, 45, 16, 14, 103], [64, 44, 69, 105, 83, 69], [27, 26, 103, 87, 30, 107]], ![[89, 38, 89, 39, 83, 44], [45, 89, 67, 87, 113, 17], [20, 35, 56, 63, 8, 37], [19, 81, 2, 61, 107, 17], [88, 109, 120, 18, 7, 36], [77, 107, 42, 37, 72, 25]]]
 h' := ![![[108, 64, 57, 34], [122, 46, 52, 76], [83, 63, 118, 97], [87, 120, 108, 126], [52, 97, 63, 96], [0, 0, 0, 1], [0, 1]], ![[111, 115, 4, 22], [81, 53, 109, 37], [110, 36, 6, 87], [68, 78, 113, 81], [80, 13, 22, 77], [41, 29, 59, 72], [108, 64, 57, 34]], ![[108, 74, 66, 71], [38, 118, 50, 104], [87, 53, 13, 52], [94, 23, 94, 96], [124, 123, 111, 99], [113, 95, 104, 63], [111, 115, 4, 22]], ![[0, 1], [26, 37, 43, 37], [38, 102, 117, 18], [18, 33, 66, 78], [28, 21, 58, 109], [8, 3, 91, 118], [108, 74, 66, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [90, 3, 100], []]
 b := ![[], [], [20, 23, 36, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [84, 7, 110, 54, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1259415913805, -235707045631, -469996662679, -96169992804, 1431743284921]
  a := ![135, -105, 140, 70, -463]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-686330811095, -1039024324869, -1333981923491, -1026652038745, 1431743284921]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -2, 0, 0, 1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-6, -2, 0, 0, 1]] 
 ![![127, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-6, -2, 0, 0, 1], ![-5, -5, -4, 0, 7], ![-35, -2, -19, -8, 49], ![-64, -44, 12, 9, -24], ![-21, -6, -6, -2, 16]]]
  hmulB := by decide  
  f := ![![![-128, -10, 70, 26, -163]], ![![-67, -5, 38, 14, -89]], ![![-53, -4, 33, 12, -78]], ![![0, 2, 10, 3, -27]], ![![-5, 0, 6, 2, -15]]]
  g := ![![![1, -2, 0, 0, 1], ![4, -5, -4, 0, 7], ![7, -2, -19, -8, 49], ![19, -44, 12, 9, -24], ![5, -6, -6, -2, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-128, -10, 70, 26, -163]] ![![-6, -2, 0, 0, 1]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -5, 15, 6, -48]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![27, -5, 15, 6, -48]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![102, 91, 59, 1, 0], ![4, 107, 48, 0, 1]] where
  M :=![![![27, -5, 15, 6, -48], ![156, 60, 1, -12, -48], ![408, -23, 336, 86, -912], ![1600, 359, 255, 41, -1104], ![436, 55, 187, 42, -569]]]
  hmulB := by decide  
  f := ![![![-563, -51, 205, 80, -432]], ![![1040, 90, -387, -150, 816]], ![![-1980, -181, 708, 276, -1488]], ![![-598, -58, 206, 81, -432]], ![![100, 5, -48, -18, 103]]]
  g := ![![![-3, 35, 15, 6, -48], ![12, 48, 23, -12, -48], ![-36, 685, 298, 86, -912], ![14, 876, 388, 41, -1104], ![-12, 436, 191, 42, -569]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [119, 22, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 52, 13], [9, 78, 118], [0, 1]]
 g := ![![[10, 55, 15], [122, 58, 100], [105, 9], [25, 74], [87, 62], [129, 1], []], ![[48, 24, 47, 61], [42, 81, 119, 34], [4, 61], [80, 81], [119, 48], [74, 58], [97, 38]], ![[70, 47, 2, 23], [112, 64, 66, 116], [26, 60], [75, 62], [82, 80], [11, 84], [123, 38]]]
 h' := ![![[120, 52, 13], [23, 100, 43], [75, 26, 10], [115, 45, 128], [48, 72, 104], [107, 56, 113], [0, 0, 1], [0, 1]], ![[9, 78, 118], [75, 51, 69], [63, 118, 70], [88, 64, 89], [62, 28, 9], [72, 129, 110], [106, 60, 78], [120, 52, 13]], ![[0, 1], [16, 111, 19], [28, 118, 51], [41, 22, 45], [53, 31, 18], [95, 77, 39], [116, 71, 52], [9, 78, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 25], []]
 b := ![[], [64, 15, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [119, 22, 2, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76819713, -94574704, 92542812, 43665612, -204927552]
  a := ![-84, 56, -86, -62, 288]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28328259, 136329028, 56128200, 43665612, -204927552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 23, -19, -12, 50]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![7, 23, -19, -12, 50]] 
 ![![131, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![103, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![7, 23, -19, -12, 50], ![-82, -94, 103, 46, -226], ![486, 301, -332, -116, 626], ![-712, -201, 343, 51, -480], ![104, 87, -83, -36, 173]]]
  hmulB := by decide  
  f := ![![![-61763, -13535, -20089, -3562, 62978]], ![![-20882, -4576, -6791, -1204, 21290]], ![![-57233, -12542, -18613, -3300, 58352]], ![![-25124, -5505, -8165, -1447, 25600]], ![![-10761, -2358, -3498, -620, 10967]]]
  g := ![![![6, 23, -19, -12, 50], ![-43, -94, 103, 46, -226], ![144, 301, -332, -116, 626], ![-187, -201, 343, 51, -480], ![32, 87, -83, -36, 173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -3, -1, 0, 5]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-10, -3, -1, 0, 5]] 
 ![![131, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![98, 0, 0, 0, 1]] where
  M :=![![![-10, -3, -1, 0, 5], ![-25, -6, -13, -2, 35], ![-147, -25, -46, -12, 149], ![-276, -85, -65, -3, 216], ![-105, -23, -31, -6, 100]]]
  hmulB := by decide  
  f := ![![![-1520, -153, 523, 208, -1099]], ![![-1187, -120, 407, 162, -855]], ![![-705, -72, 241, 96, -506]], ![![-1464, -149, 499, 199, -1048]], ![![-1157, -117, 397, 158, -834]]]
  g := ![![![-1, -3, -1, 0, 5], ![-14, -6, -13, -2, 35], ![-61, -25, -46, -12, 149], ![-65, -85, -65, -3, 216], ![-38, -23, -31, -6, 100]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![27, -5, 15, 6, -48]] ![![7, 23, -19, -12, 50]]
  ![![-1375, 224, 34, -260, 686]] where
 M := ![![![-1375, 224, 34, -260, 686]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-1375, 224, 34, -260, 686]] ![![-10, -3, -1, 0, 5]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![2882, 8253, -7467, -4192, 18471]]]
 hmul := by decide  
 g := ![![![![22, 63, -57, -32, 141]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0, 0, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] where
  M :=![![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 5 2 7 [100, 28, 77, 68, 49, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 21, 62, 63, 42], [106, 65, 133, 126, 103], [16, 19, 9, 41, 97], [47, 31, 70, 44, 32], [0, 1]]
 g := ![![[120, 113, 41, 31, 126], [35, 12, 68, 121], [134, 4, 136, 36], [117, 2, 71, 125, 129], [45, 4, 88, 1], [], []], ![[81, 27, 58, 63, 121, 135, 13, 5], [8, 7, 136, 63], [79, 56, 2, 120], [115, 51, 39, 126, 36, 2, 95, 55], [114, 102, 44, 98], [78, 16, 19, 38], [74, 100, 97, 120]], ![[18, 13, 90, 30, 37, 63, 118, 37], [0, 78, 43, 68], [135, 47, 57, 2], [44, 23, 41, 115, 134, 74, 9, 77], [39, 47, 134, 129], [12, 20, 111, 25], [50, 12, 0, 60]], ![[72, 105, 135, 71, 0, 122, 11, 127], [130, 71, 132, 25], [22, 29, 127, 73], [30, 84, 99, 17, 86, 5, 104, 82], [78, 31, 97, 9], [50, 72, 106, 130], [49, 119, 109, 93]], ![[35, 49, 13, 31, 33, 120, 132, 65], [130, 38, 29, 118], [47, 127, 102, 112], [52, 73, 117, 65, 84, 33, 133, 76], [27, 28, 47, 50], [120, 19, 11, 14], [33, 75, 42, 65]]]
 h' := ![![[56, 21, 62, 63, 42], [61, 19, 10, 1, 20], [37, 76, 79, 92, 11], [82, 116, 14, 70, 131], [21, 121, 90, 96, 35], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[106, 65, 133, 126, 103], [87, 109, 83, 27, 6], [32, 14, 80, 136, 101], [64, 59, 84, 132, 42], [136, 11, 80, 108, 56], [24, 88, 123, 32, 80], [120, 7, 10, 22, 77], [56, 21, 62, 63, 42]], ![[16, 19, 9, 41, 97], [38, 136, 61, 107, 55], [77, 80, 73, 95, 43], [98, 94, 128, 71, 31], [98, 69, 107, 95, 50], [5, 134, 124, 102, 35], [71, 83, 13, 113, 132], [106, 65, 133, 126, 103]], ![[47, 31, 70, 44, 32], [16, 72, 102, 97, 69], [136, 74, 89, 122, 5], [12, 24, 71, 134, 22], [90, 12, 60, 127, 118], [128, 132, 120, 44, 3], [14, 77, 43, 97, 104], [16, 19, 9, 41, 97]], ![[0, 1], [76, 75, 18, 42, 124], [91, 30, 90, 103, 114], [63, 118, 114, 4, 48], [25, 61, 74, 122, 15], [81, 57, 44, 96, 18], [5, 107, 70, 42, 98], [47, 31, 70, 44, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 0, 71, 41], [], [], []]
 b := ![[], [62, 46, 0, 71, 61], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 5
  hpos := by decide
  P := [100, 28, 77, 68, 49, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-388957312554674, -84345983008076, -125661981200804, -21988734663053, 396293517113419]
  a := ![-12, 22, -8, 15, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2839104471202, -615664109548, -917240738692, -160501712869, 2892653409587]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 48261724457 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀

instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0, 0, 0]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]] where
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [54, 69, 89, 121, 76, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 65, 118, 63, 134], [48, 115, 124, 70, 58], [62, 119, 55, 82, 136], [69, 117, 120, 63, 89], [0, 1]]
 g := ![![[136, 134, 20, 122, 13], [62, 81, 37, 14, 120], [104, 57, 8, 11], [50, 113, 46, 44, 54], [80, 95, 63, 1], [], []], ![[83, 7, 106, 134, 45, 84, 79, 87], [13, 135, 125, 79, 1, 50, 61, 90], [68, 86, 44, 45], [43, 61, 93, 46, 50, 41, 105, 128], [68, 12, 25, 38], [42, 106, 0, 13], [25, 85, 111, 25]], ![[80, 97, 81, 61, 1, 68, 46, 102], [32, 86, 8, 114, 131, 114, 4, 2], [26, 87, 135, 1], [128, 128, 116, 65, 60, 119, 18, 92], [28, 126, 15, 131], [102, 94, 63, 31], [118, 22, 15, 28]], ![[17, 16, 81, 44, 47, 17, 30, 122], [90, 120, 5, 88, 65, 124, 8, 54], [85, 85, 114, 116], [48, 75, 126, 66, 128, 42, 119, 4], [13, 61, 43, 44], [60, 102, 2, 77], [94, 22, 75, 9]], ![[37, 104, 117, 105, 58, 83, 133, 31], [130, 13, 135, 126, 116, 49, 117, 1], [71, 50, 27, 83], [62, 113, 103, 137, 93, 131, 112, 112], [31, 128, 16, 29], [7, 120, 24, 121], [104, 64, 107, 137]]]
 h' := ![![[23, 65, 118, 63, 134], [127, 103, 60, 61, 41], [89, 56, 66, 42, 26], [80, 21, 88, 33, 17], [128, 53, 20, 121, 101], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[48, 115, 124, 70, 58], [8, 131, 89, 33, 109], [7, 44, 87, 47, 11], [64, 95, 25, 79, 36], [138, 108, 111, 75, 126], [125, 4, 75, 88, 90], [13, 11, 17, 29, 41], [23, 65, 118, 63, 134]], ![[62, 119, 55, 82, 136], [135, 118, 45, 122, 23], [16, 126, 1, 78, 118], [126, 109, 1, 103, 138], [5, 67, 90, 74, 39], [31, 68, 80, 127, 100], [102, 42, 67, 55, 46], [48, 115, 124, 70, 58]], ![[69, 117, 120, 63, 89], [87, 14, 79, 82, 57], [77, 76, 2, 131, 128], [48, 4, 117, 109, 106], [64, 132, 99, 102, 36], [40, 94, 6, 105, 34], [19, 132, 97, 95, 63], [62, 119, 55, 82, 136]], ![[0, 1], [70, 51, 5, 119, 48], [50, 115, 122, 119, 134], [39, 49, 47, 93, 120], [71, 57, 97, 45, 115], [63, 112, 117, 97, 53], [118, 93, 96, 99, 128], [69, 117, 120, 63, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119, 86, 28, 73], [], [], []]
 b := ![[], [47, 102, 105, 126, 98], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [54, 69, 89, 121, 76, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11148986087, 11426304014, -11852040720, -5158892704, 25339092153]
  a := ![-12, 6, -13, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![80208533, 82203626, -85266480, -37114336, 182295627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 51888844699 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4128, -910, -1342, -238, 4201]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-4128, -910, -1342, -238, 4201]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![105, 81, 26, 1, 0], ![72, 135, 126, 0, 1]] where
  M :=![![![-4128, -910, -1342, -238, 4201], ![-17673, -3887, -5742, -1018, 17983], ![-75663, -16630, -24583, -4358, 77017], ![-153200, -33640, -49776, -8821, 155976], ![-56815, -12478, -18460, -3272, 57844]]]
  hmulB := by decide  
  f := ![![![54, -18, -4, 0, 7]], ![![-35, 57, -32, -8, 49]], ![![-133, -106, 79, -8, -41]], ![![-3, -1, -6, -5, 22]], ![![-118, -47, 36, -14, 13]]]
  g := ![![![-1890, -3683, -3520, -238, 4201], ![-8091, -15766, -15068, -1018, 17983], ![-34653, -67523, -64533, -4358, 77017], ![-70183, -136751, -130694, -8821, 155976], ![-26027, -50714, -48468, -3272, 57844]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [7, 129, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 41, 99], [136, 107, 50], [0, 1]]
 g := ![![[90, 52, 4], [76, 123], [99, 43, 33], [74, 64], [43, 136, 36], [102, 1], []], ![[29, 40, 53, 70], [71, 54], [1, 36, 146, 84], [50, 127], [78, 28, 117, 58], [75, 125], [133, 116]], ![[65, 66, 47, 41], [31, 61], [134, 79, 70, 51], [101, 145], [107, 103, 6, 117], [10, 42], [33, 116]]]
 h' := ![![[115, 41, 99], [86, 60, 2], [52, 10, 47], [87, 139, 114], [146, 124, 141], [31, 96, 143], [0, 0, 1], [0, 1]], ![[136, 107, 50], [135, 133, 45], [6, 36, 59], [2, 8, 33], [90, 88, 96], [36, 40, 71], [76, 103, 107], [115, 41, 99]], ![[0, 1], [76, 105, 102], [137, 103, 43], [3, 2, 2], [73, 86, 61], [49, 13, 84], [87, 46, 41], [136, 107, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 100], []]
 b := ![[], [135, 24, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [7, 129, 47, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-833592510, -217259541, -178717889, -18038930, 647106729]
  a := ![-125, 97, -125, -66, 429]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-305578452, -577956474, -545269487, -18038930, 647106729]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54, 18, 4, 0, -7]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-54, 18, 4, 0, -7]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![139, 97, 1, 0, 0], ![38, 59, 0, 1, 0], ![2, 138, 0, 0, 1]] where
  M :=![![![-54, 18, 4, 0, -7], ![35, -57, 32, 8, -49], ![133, 106, -79, 8, 41], ![-176, 120, -64, -111, 360], ![-13, 46, -18, -2, 16]]]
  hmulB := by decide  
  f := ![![![4128, 910, 1342, 238, -4201]], ![![17673, 3887, 5742, 1018, -17983]], ![![15864, 3491, 5155, 914, -16143]], ![![9079, 1997, 2950, 523, -9239]], ![![16805, 3696, 5460, 968, -17100]]]
  g := ![![![-4, 4, 4, 0, -7], ![-31, 21, 32, 8, -49], ![72, 11, -79, 8, 41], ![82, -247, -64, -111, 360], ![17, -2, -18, -2, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [86, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 148], [0, 1]]
 g := ![![[8, 26], [30], [4, 5], [1], [143, 107], [120], [1]], ![[0, 123], [30], [140, 144], [1], [133, 42], [120], [1]]]
 h' := ![![[57, 148], [132, 131], [103, 103], [56, 68], [69, 148], [56, 16], [63, 57], [0, 1]], ![[0, 1], [0, 18], [14, 46], [58, 81], [12, 1], [74, 133], [34, 92], [57, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [35, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [86, 92, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-186673, -31120, -91601, -14187, 268990]
  a := ![-86, 68, -89, -43, 295]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![84208, -184090, -91601, -14187, 268990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-4128, -910, -1342, -238, 4201]] ![![-54, 18, 4, 0, -7]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, -21, -81, -26, 180]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![61, -21, -81, -26, 180]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![95, 21, 1, 0, 0], ![135, 54, 0, 1, 0], ![24, 148, 0, 0, 1]] where
  M :=![![![61, -21, -81, -26, 180], ![-536, -126, 9, 20, 12], ![-340, -295, -450, -122, 1044], ![-1488, -481, -281, -33, 720], ![-248, -169, -237, -62, 553]]]
  hmulB := by decide  
  f := ![![![-673, -151, -207, -36, 660]], ![![-2796, -616, -931, -162, 2892]], ![![-893, -198, -286, -50, 900]], ![![-1765, -392, -570, -99, 1788]], ![![-2908, -641, -965, -168, 3001]]]
  g := ![![![46, -156, -81, -26, 180], ![-29, -21, 9, 20, 12], ![224, -919, -450, -122, 1044], ![82, -658, -281, -33, 720], ![115, -488, -237, -62, 553]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [138, 144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 150], [0, 1]]
 g := ![![[47, 58], [15, 138], [92, 29], [55], [144, 50], [49], [1]], ![[0, 93], [75, 13], [144, 122], [55], [41, 101], [49], [1]]]
 h' := ![![[7, 150], [44, 80], [139, 134], [87, 28], [60, 31], [51, 72], [13, 7], [0, 1]], ![[0, 1], [0, 71], [20, 17], [132, 123], [126, 120], [102, 79], [62, 144], [7, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [21, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [138, 144, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70912, -6614, -25376, -4599, 86272]
  a := ![-22, 22, -22, -3, 76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5895, -79428, -25376, -4599, 86272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11425, -2503, -3713, -658, 11642]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-11425, -2503, -3713, -658, 11642]] 
 ![![151, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![92, 0, 0, 1, 0], ![120, 0, 0, 0, 1]] where
  M :=![![![-11425, -2503, -3713, -658, 11642], ![-48998, -10734, -15917, -2820, 49910], ![-210070, -46025, -68254, -12094, 214010], ![-425868, -93307, -138359, -24515, 433824], ![-157896, -34595, -51301, -9090, 160853]]]
  hmulB := by decide  
  f := ![![![-3055, -957, 1425, 224, -1982]], ![![-1776, -578, 847, 142, -1202]], ![![-1108, -227, 416, 16, -446]], ![![-2092, -855, 1145, 263, -1816]], ![![-2456, -747, 1127, 168, -1543]]]
  g := ![![![-6107, -2503, -3713, -658, 11642], ![-26180, -10734, -15917, -2820, 49910], ![-112256, -46025, -68254, -12094, 214010], ![-227552, -93307, -138359, -24515, 433824], ![-84372, -34595, -51301, -9090, 160853]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 1, -5, -2, 10]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![15, 1, -5, -2, 10]] 
 ![![151, 0, 0, 0, 0], ![92, 1, 0, 0, 0], ![143, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![98, 0, 0, 0, 1]] where
  M :=![![![15, 1, -5, -2, 10], ![-22, -2, 11, 4, -26], ![74, 7, -10, -6, 10], ![28, 5, 33, 9, -96], ![44, 5, -1, -2, -7]]]
  hmulB := by decide  
  f := ![![![-31, -61, 37, 24, -94]], ![![-18, -36, 21, 14, -54]], ![![-37, -62, 39, 24, -96]], ![![4, -7, 1, 3, -8]], ![![-22, -41, 25, 16, -63]]]
  g := ![![![-2, 1, -5, -2, 10], ![7, -2, 11, 4, -26], ![0, 7, -10, -6, 10], ![27, 5, 33, 9, -96], ![3, 5, -1, -2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2

def I151N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-496, -45, 179, 70, -377]] i)))

def SI151N3: IdealEqSpanCertificate' Table ![![-496, -45, 179, 70, -377]] 
 ![![151, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![99, 0, 0, 0, 1]] where
  M :=![![![-496, -45, 179, 70, -377], ![905, 76, -341, -132, 721], ![-1757, -167, 614, 242, -1289], ![1076, 77, -439, -167, 936], ![-793, -77, 273, 108, -572]]]
  hmulB := by decide  
  f := ![![![250, 141, -201, -58, 371]], ![![157, 91, -130, -38, 242]], ![![29, 7, -18, -2, 27]], ![![144, 101, -139, -45, 272]], ![![165, 92, -134, -38, 247]]]
  g := ![![![216, -45, 179, 70, -377], ![-408, 76, -341, -132, 721], ![745, -167, 614, 242, -1289], ![-519, 77, -439, -167, 936], ![332, -77, 273, 108, -572]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N3 : Nat.card (O ⧸ I151N3) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N3)

lemma isPrimeI151N3 : Ideal.IsPrime I151N3 := prime_ideal_of_norm_prime hp151.out _ NI151N3
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![61, -21, -81, -26, 180]] ![![-11425, -2503, -3713, -658, 11642]]
  ![![-1009, -362, -508, -114, 1358]] where
 M := ![![![-1009, -362, -508, -114, 1358]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-1009, -362, -508, -114, 1358]] ![![15, 1, -5, -2, 10]]
  ![![11797, 2379, 1023, -124, -4320]] where
 M := ![![![11797, 2379, 1023, -124, -4320]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N2 : IdealMulLeCertificate' Table 
  ![![11797, 2379, 1023, -124, -4320]] ![![-496, -45, 179, 70, -377]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-2203392, -197810, 803622, 313476, -1695881]]]
 hmul := by decide  
 g := ![![![![-14592, -1310, 5322, 2076, -11231]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2, I151N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
    exact isPrimeI151N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1 ⊙ MulI151N2)


lemma PB312I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB312I3 : PrimesBelowBoundCertificateInterval O 103 151 312 where
  m := 9
  g := ![3, 2, 3, 2, 3, 1, 1, 2, 4]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB312I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0]
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2, I151N3]
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
    · exact ![11449, 11449, 107]
    · exact ![141158161, 109]
    · exact ![1442897, 113, 113]
    · exact ![260144641, 127]
    · exact ![2248091, 131, 131]
    · exact ![48261724457]
    · exact ![51888844699]
    · exact ![3307949, 22201]
    · exact ![22801, 151, 151, 151]
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
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
      exact NI151N3
  β := ![I107N2, I109N1, I113N1, I113N2, I127N1, I131N1, I131N2, I151N1, I151N2, I151N3]
  Il := ![[I107N2], [I109N1], [I113N1, I113N2], [I127N1], [I131N1, I131N2], [], [], [], [I151N1, I151N2, I151N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
