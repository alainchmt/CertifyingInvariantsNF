
import IdealArithmetic.Examples.NF5_1_7500000_1.RI5_1_7500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1351, 2143, -1114, 567, -741]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![1351, 2143, -1114, 567, -741]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![40, 70, 123, 1, 0], ![104, 28, 56, 0, 1]] where
  M :=![![![1351, 2143, -1114, 567, -741], ![-2964, -2727, 1576, -746, 1134], ![4536, 3148, -1981, 884, -1492], ![-1502, -343, 344, -116, 317], ![2902, 1629, -1104, 469, -862]]]
  hmulB := by decide  
  f := ![![![51, 31, -22, -49, 17]], ![![68, 97, 80, -78, -98]], ![![-392, -244, 175, 356, -156]], ![![-266, -143, 165, 234, -159]], ![![-90, -47, 60, 77, -60]]]
  g := ![![![355, -107, -187, 567, -741], ![-580, 113, 190, -746, 1134], ![792, -108, -173, 884, -1492], ![-190, -7, -20, -116, 317], ![470, -45, -67, 469, -862]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [42, 120, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 116, 10], [67, 40, 147], [0, 1]]
 g := ![![[10, 92, 101], [69, 12], [82, 83, 17], [18, 57, 117], [58, 37, 144], [118, 1], []], ![[59, 17, 65, 111], [101, 39], [91, 0, 125, 143], [63, 31, 1, 19], [151, 74, 99, 117], [146, 30], [147, 100]], ![[138, 102, 15, 109], [144, 101], [105, 110, 4, 35], [106, 54, 22, 90], [85, 108, 30, 108], [50, 111], [10, 100]]]
 h' := ![![[51, 116, 10], [28, 95, 27], [10, 75, 13], [29, 123, 86], [76, 35, 66], [68, 85, 145], [0, 0, 1], [0, 1]], ![[67, 40, 147], [90, 11, 146], [90, 114, 14], [150, 124, 117], [130, 106, 7], [22, 117, 56], [38, 40, 40], [51, 116, 10]], ![[0, 1], [76, 51, 141], [156, 125, 130], [87, 67, 111], [150, 16, 84], [110, 112, 113], [144, 117, 116], [67, 40, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 149], []]
 b := ![[], [5, 134, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [42, 120, 39, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112482, 111051, 31511, -112828, -46888]
  a := ![0, -2, 2, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![60522, 59375, 105319, -112828, -46888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121, -243, -97, -52, -52]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-121, -243, -97, -52, -52]] 
 ![![157, 0, 0, 0, 0], ![111, 1, 0, 0, 0], ![82, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![145, 0, 0, 0, 1]] where
  M :=![![![-121, -243, -97, -52, -52], ![-208, -426, -191, -90, -104], ![-416, -815, -336, -174, -180], ![-256, -523, -225, -111, -122], ![-452, -892, -374, -190, -201]]]
  hmulB := by decide  
  f := ![![![331, 263, -5, -292, -40]], ![![233, 187, 0, -206, -32]], ![![158, 125, -2, -138, -20]], ![![55, 36, -16, -47, 10]], ![![331, 263, -7, -294, -37]]]
  g := ![![![278, -243, -97, -52, -52], ![510, -426, -191, -90, -104], ![943, -815, -336, -174, -180], ![616, -523, -225, -111, -122], ![1039, -892, -374, -190, -201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 13, 7, 2, 8]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-47, 13, 7, 2, 8]] 
 ![![157, 0, 0, 0, 0], ![114, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![146, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![-47, 13, 7, 2, 8], ![32, -8, 11, -2, 4], ![16, 59, -6, 14, -4], ![-24, 1, 17, -1, 12], ![32, 50, -2, 12, -3]]]
  hmulB := by decide  
  f := ![![![205, 219, 83, -210, -112]], ![![146, 158, 63, -150, -84]], ![![35, 38, 15, -36, -20]], ![![202, 207, 65, -205, -92]], ![![143, 151, 55, -146, -75]]]
  g := ![![![-18, 13, 7, 2, 8], ![3, -8, 11, -2, 4], ![-52, 59, -6, 14, -4], ![-11, 1, 17, -1, 12], ![-45, 50, -2, 12, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![1351, 2143, -1114, 567, -741]] ![![-121, -243, -97, -52, -52]]
  ![![43989, 31130, -16497, 8567, -12837]] where
 M := ![![![43989, 31130, -16497, 8567, -12837]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![43989, 31130, -16497, 8567, -12837]] ![![-47, 13, 7, 2, 8]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-1951667, -1283789, 920648, -367851, 683735]]]
 hmul := by decide  
 g := ![![![![-12431, -8177, 5864, -2343, 4355]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, 351, 59, -374, -104]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![379, 351, 59, -374, -104]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![131, 116, 29, 1, 0], ![113, 139, 113, 0, 1]] where
  M :=![![![379, 351, 59, -374, -104], ![-416, 22, 725, 326, -748], ![-2992, -2683, -304, 2946, 652], ![1512, -355, -3177, -1119, 3320], ![5144, 4466, 230, -5024, -793]]]
  hmulB := by decide  
  f := ![![![-2247, -829, 665, -254, 560]], ![![2240, 658, -575, 210, -508]], ![![-2032, -367, 448, -134, 420]], ![![-575, -265, 206, -79, 164]], ![![-1061, -268, 282, -90, 247]]]
  g := ![![![375, 357, 139, -374, -104], ![254, 406, 465, 326, -748], ![-2838, -2669, -978, 2946, 652], ![-1393, -2037, -2122, -1119, 3320], ![4619, 4279, 1445, -5024, -793]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [35, 34, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 54, 73], [57, 108, 90], [0, 1]]
 g := ![![[149, 133, 10], [145, 31, 60], [76, 93], [149, 81], [45, 118], [70, 58, 1], []], ![[82, 158, 59, 101], [84, 127, 107, 63], [83, 56], [161, 41], [76, 54], [7, 86, 144, 123], [94, 113]], ![[22, 22, 75, 69], [52, 77, 140, 97], [12, 77], [74, 131], [159, 77], [51, 117, 19, 10], [77, 113]]]
 h' := ![![[1, 54, 73], [141, 147, 70], [91, 156, 95], [44, 7, 16], [80, 135, 154], [158, 154, 97], [0, 0, 1], [0, 1]], ![[57, 108, 90], [51, 16, 35], [100, 141, 132], [76, 160, 120], [150, 98, 81], [107, 128, 39], [134, 129, 108], [1, 54, 73]], ![[0, 1], [30, 0, 58], [162, 29, 99], [16, 159, 27], [18, 93, 91], [82, 44, 27], [65, 34, 54], [57, 108, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 62], []]
 b := ![[], [134, 83, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [35, 34, 105, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16857879, -10619125, 8270169, 12448566, -7523678]
  a := ![3, -65, -1, -66, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4892297, -2508353, 3051763, 12448566, -7523678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2247, 829, -665, 254, -560]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![2247, 829, -665, 254, -560]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![41, 105, 1, 0, 0], ![48, 132, 0, 1, 0], ![4, 74, 0, 0, 1]] where
  M :=![![![2247, 829, -665, 254, -560], ![-2240, -658, 575, -210, 508], ![2032, 367, -448, 134, -420], ![280, 281, -171, 77, -120], ![776, -2, -122, 16, -133]]]
  hmulB := by decide  
  f := ![![![-379, -351, -59, 374, 104]], ![![416, -22, -725, -326, 748]], ![![191, -86, -480, -134, 504]], ![![216, -119, -585, -147, 616]], ![![148, -46, -332, -108, 347]]]
  g := ![![![120, 482, -665, 254, -560], ![-109, -435, 575, -210, 508], ![96, 373, -448, 134, -420], ![25, 104, -171, 77, -120], ![34, 126, -122, 16, -133]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [47, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 162], [0, 1]]
 g := ![![[149, 111], [136, 74], [65], [38], [58], [141, 36], [1]], ![[0, 52], [91, 89], [65], [38], [58], [31, 127], [1]]]
 h' := ![![[6, 162], [128, 33], [24, 143], [54, 126], [84, 110], [56, 59], [116, 6], [0, 1]], ![[0, 1], [0, 130], [67, 20], [158, 37], [92, 53], [84, 104], [152, 157], [6, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [45, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [47, 157, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-147, -830, 245, -343, -551]
  a := ![1, -4, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![52, 365, 245, -343, -551]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![379, 351, 59, -374, -104]] ![![2247, 829, -665, 254, -560]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 45, -13, 6, -4]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![61, 45, -13, 6, -4]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![110, 114, 45, 82, 1]] where
  M :=![![![61, 45, -13, 6, -4], ![-16, 32, 39, -18, 12], ![48, 71, 50, 54, -36], ![-64, -39, -11, 95, 48], ![120, 94, -42, -32, 77]]]
  hmulB := by decide  
  f := ![![![-13, -7, 5, -2, 4]], ![![16, 8, -5, 2, -4]], ![![-16, -5, 6, -2, 4]], ![![0, -1, 1, 1, 0]], ![![-2, -1, 2, 0, 1]]]
  g := ![![![3, 3, 1, 2, -4], ![-8, -8, -3, -6, 12], ![24, 25, 10, 18, -36], ![-32, -33, -13, -23, 48], ![-50, -52, -21, -38, 77]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [71, 20, 140, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 34, 74, 83], [42, 118, 89, 56], [149, 14, 4, 28], [0, 1]]
 g := ![![[165, 141, 9, 76], [81, 154, 108, 7], [127, 139, 6, 11], [114], [56, 91, 116], [166, 1], []], ![[111, 124, 166, 6, 31, 145], [153, 7, 4, 8, 65, 163], [69, 86, 29, 64, 31, 20], [7, 111, 18], [106, 49, 4], [107, 162, 25, 44, 102, 68], [12, 51, 42]], ![[72, 9, 166, 30, 30, 1], [36, 139, 9, 143, 7, 162], [156, 2, 135, 90, 154, 32], [9, 19, 128], [148, 120, 49], [92, 73, 6, 73, 59, 7], [113, 152, 130]], ![[115, 43, 109, 72, 166, 137], [136, 110, 36, 5, 97, 114], [92, 51, 41, 104, 87, 57], [102, 37, 50], [101, 71, 28], [50, 66, 18, 46, 83, 16], [150, 108, 116]]]
 h' := ![![[142, 34, 74, 83], [94, 139, 11, 57], [1, 111, 5, 95], [50, 88, 100, 41], [63, 40, 75], [71, 116, 120, 28], [0, 0, 1], [0, 1]], ![[42, 118, 89, 56], [155, 139, 62, 82], [134, 80, 153, 141], [136, 148, 88, 36], [74, 115, 69, 128], [98, 7, 55, 2], [107, 117, 124, 71], [142, 34, 74, 83]], ![[149, 14, 4, 28], [13, 93, 32, 62], [151, 61, 24, 94], [73, 16, 69, 116], [85, 14, 138, 104], [78, 33, 143, 160], [87, 33, 157, 45], [42, 118, 89, 56]], ![[0, 1], [1, 130, 62, 133], [86, 82, 152, 4], [32, 82, 77, 141], [107, 165, 52, 102], [40, 11, 16, 144], [28, 17, 52, 51], [149, 14, 4, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 73, 61], []]
 b := ![[], [], [15, 86, 29, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [71, 20, 140, 1, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21715447, 90407660, 190700317, 22184853, -184059933]
  a := ![1, 18, -3, 17, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![121107049, 126187066, 50738906, 90509577, -184059933]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 7, -5, 2, -4]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![13, 7, -5, 2, -4]] 
 ![![167, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![158, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![13, 7, -5, 2, -4], ![-16, -8, 5, -2, 4], ![16, 5, -6, 2, -4], ![0, 1, -1, -1, 0], ![8, 2, -2, 0, -3]]]
  hmulB := by decide  
  f := ![![![-61, -45, 13, -6, 4]], ![![-1, -1, 0, 0, 0]], ![![-58, -43, 12, -6, 4]], ![![-4, -3, 1, -1, 0]], ![![-23, -17, 5, -2, 1]]]
  g := ![![![6, 7, -5, 2, -4], ![-6, -8, 5, -2, 4], ![7, 5, -6, 2, -4], ![1, 1, -1, -1, 0], ![3, 2, -2, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![61, 45, -13, 6, -4]] ![![13, 7, -5, 2, -4]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB171I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 170 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 170 (by omega)

def PB171I4 : PrimesBelowBoundCertificateInterval O 151 170 171 where
  m := 3
  g := ![3, 2, 2]
  P := ![157, 163, 167]
  hP := PB171I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3869893, 157, 157]
    · exact ![4330747, 26569]
    · exact ![777796321, 167]
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
  β := ![I157N1, I157N2, I167N1]
  Il := ![[I157N1, I157N2], [], [I167N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
