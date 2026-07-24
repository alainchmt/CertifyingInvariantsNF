
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-209, -316, 743, 1473, -667]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-209, -316, 743, 1473, -667]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![106, 149, 146, 83, 1]] where
  M :=![![![-209, -316, 743, 1473, -667], ![-4002, -10214, 3108, 12045, 1473], ![8838, 18093, -18827, -44001, 12045], ![7626, 22539, 2319, -10961, -13356], ![-48420, -107004, 82011, 210321, -38984]]]
  hmulB := by decide  
  f := ![![![-2165, -1490, 595, -153, 217]], ![![1302, 1090, -420, 123, -153]], ![![-918, -993, 319, -135, 123]], ![![582, 651, -225, 85, -84]], ![![-770, -549, 180, -67, 71]]]
  g := ![![![449, 631, 625, 362, -667], ![-1020, -1463, -1350, -702, 1473], ![-8076, -11316, -11321, -6648, 12045], ![9066, 12819, 12435, 6991, -13356], ![26012, 36316, 36775, 21949, -38984]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [134, 126, 68, 115, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 132, 1, 55], [61, 83, 102, 147], [54, 98, 54, 112], [0, 1]]
 g := ![![[147, 29, 88, 148], [95, 148, 93], [14, 78, 106, 4], [56, 34, 33, 154], [47, 107, 81, 37], [1], []], ![[31, 50, 133, 134, 89, 70], [139, 66, 39], [22, 150, 6, 119, 149, 45], [91, 49, 107, 6, 18, 129], [92, 21, 88, 105, 121, 102], [85, 105, 27], [98, 147, 42]], ![[55, 76, 134, 76, 41, 127], [146, 13, 110], [63, 43, 67, 63, 99, 76], [70, 131, 107, 16, 54, 25], [49, 15, 24, 8, 63, 127], [124, 57, 27], [34, 119, 100]], ![[67, 60, 39, 66, 103, 142], [146, 107, 122], [100, 61, 45, 61, 92, 77], [21, 64, 78, 103, 46, 22], [89, 124, 110, 51, 36, 20], [108, 89, 108], [67, 120, 141]]]
 h' := ![![[84, 132, 1, 55], [51, 134, 128, 84], [8, 112, 61, 67], [32, 16, 94, 155], [139, 51, 113, 132], [23, 31, 89, 42], [0, 0, 1], [0, 1]], ![[61, 83, 102, 147], [99, 51, 147, 12], [55, 16, 101, 143], [111, 73, 114, 30], [5, 155, 18, 15], [82, 116, 51, 129], [47, 21, 123, 59], [84, 132, 1, 55]], ![[54, 98, 54, 112], [17, 142, 95, 85], [120, 6, 15, 61], [134, 5, 10, 78], [52, 146, 115, 95], [14, 79, 67, 72], [107, 101, 88, 59], [61, 83, 102, 147]], ![[0, 1], [65, 144, 101, 133], [155, 23, 137, 43], [35, 63, 96, 51], [118, 119, 68, 72], [82, 88, 107, 71], [61, 35, 102, 39], [54, 98, 54, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 127, 138], []]
 b := ![[], [], [153, 132, 48, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [134, 126, 68, 115, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![336313688, 822199987, -359377798, -1154601985, -926135]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2767414, 6115886, -1427784, -6864540, -926135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2165, 1490, -595, 153, -217]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![2165, 1490, -595, 153, -217]] 
 ![![157, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![2165, 1490, -595, 153, -217], ![-1302, -1090, 420, -123, 153], ![918, 993, -319, 135, -123], ![-582, -651, 225, -85, 84], ![-324, -282, 129, -27, 44]]]
  hmulB := by decide  
  f := ![![![209, 316, -743, -1473, 667]], ![![124, 214, -370, -771, 305]], ![![-31, -77, 30, 102, 4]], ![![10, -55, -223, -343, 272]], ![![355, 752, -688, -1668, 397]]]
  g := ![![![-611, 1490, -595, 153, -217], ![455, -1090, 420, -123, 153], ![-434, 993, -319, 135, -123], ![281, -651, 225, -85, 84], ![113, -282, 129, -27, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-209, -316, 743, 1473, -667]] ![![2165, 1490, -595, 153, -217]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, 347, 278, 153, 45]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![133, 347, 278, 153, 45]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![5, 34, 117, 1, 0], ![91, 37, 101, 0, 1]] where
  M :=![![![133, 347, 278, 153, 45], ![270, 808, 848, 399, 153], ![918, 2565, 2341, 1137, 399], ![-60, -132, -28, 7, -10], ![678, 1959, 2074, 1149, 376]]]
  hmulB := by decide  
  f := ![![![-23189, -12365, 5480, -999, 1965]], ![![11790, 6286, -2786, 507, -999]], ![![-5994, -3195, 1417, -255, 507]], ![![-2533, -1350, 599, -107, 214]], ![![-13967, -7447, 3301, -600, 1183]]]
  g := ![![![-29, -40, -136, 153, 45], ![-96, -113, -376, 399, 153], ![-252, -312, -1049, 1137, 399], ![5, 0, 1, 7, -10], ![-241, -313, -1045, 1149, 376]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [44, 29, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 101, 96], [37, 61, 67], [0, 1]]
 g := ![![[91, 144, 35], [40, 78, 161], [146, 90], [69, 57], [78, 118], [62, 108, 1], []], ![[108, 40, 78, 21], [84, 94, 93, 21], [29, 158], [78, 9], [121, 14], [125, 137, 32, 83], [45, 88]], ![[136, 69, 12, 66], [125, 77, 119, 5], [162, 34], [159, 14], [37, 65], [123, 78, 117, 8], [74, 88]]]
 h' := ![![[71, 101, 96], [33, 33, 19], [77, 19, 145], [151, 140, 116], [47, 72, 63], [43, 133, 97], [0, 0, 1], [0, 1]], ![[37, 61, 67], [62, 124, 89], [118, 112, 74], [47, 13, 141], [120, 149, 160], [126, 70, 103], [127, 37, 61], [71, 101, 96]], ![[0, 1], [120, 6, 55], [27, 32, 107], [132, 10, 69], [49, 105, 103], [84, 123, 126], [69, 126, 101], [37, 61, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 101], []]
 b := ![[], [161, 60, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [44, 29, 55, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-307909, -688374, 110511, -170749, -171876]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![99304, 70408, 229740, -170749, -171876]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15055, 25162, -7992, 3654, -3028]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![15055, 25162, -7992, 3654, -3028]] 
 ![![163, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![15055, 25162, -7992, 3654, -3028], ![-18168, -30365, 9644, -4410, 3654], ![21924, 36642, -11639, 5322, -4410], ![-15372, -25692, 8160, -3731, 3092], ![-5640, -9426, 2992, -1374, 1135]]]
  hmulB := by decide  
  f := ![![![84181, 44882, -19904, 3630, -7136]], ![![17813, 9497, -4212, 768, -1510]], ![![40933, 21824, -9679, 1764, -3470]], ![![22129, 11798, -5232, 955, -1876]], ![![3553, 1892, -840, 156, -301]]]
  g := ![![![-2271, 25162, -7992, 3654, -3028], ![2741, -30365, 9644, -4410, 3654], ![-3307, 36642, -11639, 5322, -4410], ![2319, -25692, 8160, -3731, 3092], ![853, -9426, 2992, -1374, 1135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3625, 10335, 9967, 4916, 1724]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![3625, 10335, 9967, 4916, 1724]] 
 ![![163, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![122, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![3625, 10335, 9967, 4916, 1724], ![10344, 29485, 28424, 14022, 4916], ![29496, 84084, 81071, 39990, 14022], ![-726, -2071, -1999, -985, -346], ![25242, 71955, 69375, 34224, 11999]]]
  hmulB := by decide  
  f := ![![![-165713, -88411, 39171, -7156, 14050]], ![![-81831, -43658, 19343, -3534, 6938]], ![![-124294, -66314, 29381, -5366, 10538]], ![![-86261, -46022, 20390, -3725, 7314]], ![![-12078, -6441, 2853, -528, 1025]]]
  g := ![![![-15264, 10335, 9967, 4916, 1724], ![-43537, 29485, 28424, 14022, 4916], ![-124168, 84084, 81071, 39990, 14022], ![3060, -2071, -1999, -985, -346], ![-106257, 71955, 69375, 34224, 11999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![133, 347, 278, 153, 45]] ![![15055, 25162, -7992, 3654, -3028]]
  ![![-812825, -1358679, 431010, -197445, 163385]] where
 M := ![![![-812825, -1358679, 431010, -197445, 163385]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-812825, -1358679, 431010, -197445, 163385]] ![![3625, 10335, 9967, 4916, 1724]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-20086001, -54875580, -48580031, -24983173, -8181459]]]
 hmul := by decide  
 g := ![![![![-123227, -336660, -298037, -153271, -50193]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1183, -298, -870, -322, -190]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![1183, -298, -870, -322, -190]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![72, 42, 154, 14, 1]] where
  M :=![![![1183, -298, -870, -322, -190], ![-1140, -1667, -1826, -834, -322], ![-1932, -5970, -5023, -2658, -834], ![132, 578, 4, 137, -26], ![-1692, -4494, -4454, -2166, -775]]]
  hmulB := by decide  
  f := ![![![-7, -18, 6, 22, 2]], ![![12, 23, -30, -66, 22]], ![![132, 342, -89, -378, -66]], ![![-132, -314, 164, 487, -30]], ![![108, 280, -72, -308, -55]]]
  g := ![![![89, 46, 170, 14, -190], ![132, 71, 286, 22, -322], ![348, 174, 739, 54, -834], ![12, 10, 24, 3, -26], ![324, 168, 688, 52, -775]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [44, 7, 117, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 90, 88, 104], [108, 110, 14, 56], [66, 133, 65, 7], [0, 1]]
 g := ![![[107, 5, 1, 107], [6, 131, 14, 115], [150, 61, 45, 42], [70, 30, 48], [140, 48, 49], [142, 1], []], ![[90, 149, 53, 57, 78, 70], [14, 138, 7, 148, 79, 113], [58, 83, 2, 159, 38, 90], [11, 76, 157], [1, 43, 130], [145, 12, 23, 60, 147, 95], [119, 74, 128]], ![[110, 147, 1, 51, 30, 54], [127, 68, 83, 117, 40, 99], [16, 110, 71, 154, 166, 162], [10, 15, 6], [108, 160, 25], [91, 150, 63, 71, 21, 98], [111, 155, 130]], ![[32, 54, 127, 125, 37, 16], [53, 54, 105, 113, 35, 47], [54, 71, 150, 161, 144, 154], [104, 149, 114], [15, 131, 24], [162, 9, 115, 36, 80, 47], [46, 19, 49]]]
 h' := ![![[135, 90, 88, 104], [70, 93, 151, 146], [80, 17, 7, 99], [54, 123, 93, 84], [104, 39, 79, 86], [98, 131, 79, 7], [0, 0, 1], [0, 1]], ![[108, 110, 14, 56], [112, 70, 38, 6], [55, 114, 28, 155], [7, 131, 129, 42], [18, 43, 23, 18], [79, 44, 13, 56], [130, 4, 97, 162], [135, 90, 88, 104]], ![[66, 133, 65, 7], [91, 145, 40, 117], [145, 107, 129, 111], [51, 54, 155, 73], [149, 71, 144, 138], [15, 34, 5, 162], [100, 131, 8, 36], [108, 110, 14, 56]], ![[0, 1], [113, 26, 105, 65], [143, 96, 3, 136], [147, 26, 124, 135], [106, 14, 88, 92], [91, 125, 70, 109], [161, 32, 61, 136], [66, 133, 65, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [136, 89, 45], []]
 b := ![[], [], [8, 52, 24, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [44, 7, 117, 25, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28207190, 68559558, -30940144, -98075522, 1468114]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-464054, 41310, -1539100, -710354, 1468114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 18, -6, -22, -2]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![7, 18, -6, -22, -2]] 
 ![![167, 0, 0, 0, 0], ![153, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![86, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![7, 18, -6, -22, -2], ![-12, -23, 30, 66, -22], ![-132, -342, 89, 378, 66], ![132, 314, -164, -487, 30], ![444, 1182, -214, -1146, -331]]]
  hmulB := by decide  
  f := ![![![-1183, 298, 870, 322, 190]], ![![-1077, 283, 808, 300, 176]], ![![-966, 282, 749, 282, 162]], ![![-610, 150, 448, 165, 98]], ![![-677, 200, 532, 200, 115]]]
  g := ![![![1, 18, -6, -22, -2], ![-25, -23, 30, 66, -22], ![6, -342, 89, 378, 66], ![82, 314, -164, -487, 30], ![-121, 1182, -214, -1146, -331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![1183, -298, -870, -322, -190]] ![![7, 18, -6, -22, -2]]
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
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1293487, 2161859, -686640, 313949, -260157]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![1293487, 2161859, -686640, 313949, -260157]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![111, 10, 69, 1, 0], ![51, 153, 56, 0, 1]] where
  M :=![![![1293487, 2161859, -686640, 313949, -260157], ![-1560942, -2608868, 828618, -378861, 313949], ![1883694, 3148293, -999949, 457209, -378861], ![-1320708, -2207350, 701088, -320575, 265632], ![-484638, -809985, 257276, -117639, 97460]]]
  hmulB := by decide  
  f := ![![![-17449, -9279, 4158, -737, 1485]], ![![8910, 4826, -2008, 429, -737]], ![![-4422, -2145, 1321, -69, 429]], ![![-12429, -6522, 3075, -475, 1080]], ![![1317, 846, -124, 141, -76]]]
  g := ![![![-117265, 224430, -44973, 313949, -260157], ![141510, -270835, 54271, -378861, 313949], ![-170778, 326832, -65498, 457209, -378861], ![119745, -229152, 45927, -320575, 265632], ![43947, -84075, 16859, -117639, 97460]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [153, 171, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 69, 29], [149, 103, 144], [0, 1]]
 g := ![![[65, 53, 54], [18, 52], [64, 130, 51], [145, 123, 167], [26, 64], [75, 65, 1], []], ![[75, 140, 94, 152], [98, 4], [64, 55, 9, 16], [83, 171, 152, 77], [54, 35], [15, 62, 171, 67], [20, 149]], ![[131, 43, 12, 133], [23, 116], [51, 121, 98, 67], [96, 88, 96, 159], [20, 138], [84, 94, 55, 158], [78, 149]]]
 h' := ![![[89, 69, 29], [104, 39, 20], [69, 84, 15], [132, 140, 140], [136, 36, 72], [116, 66, 8], [0, 0, 1], [0, 1]], ![[149, 103, 144], [109, 99, 77], [15, 46, 2], [94, 166, 142], [66, 142, 156], [71, 161, 143], [17, 78, 103], [89, 69, 29]], ![[0, 1], [22, 35, 76], [164, 43, 156], [155, 40, 64], [132, 168, 118], [50, 119, 22], [60, 95, 69], [149, 103, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 132], []]
 b := ![[], [31, 74, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [153, 171, 108, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1803337, 4415542, -1618336, -5841754, 144948]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3715871, 235006, 2273674, -5841754, 144948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17449, -9279, 4158, -737, 1485]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-17449, -9279, 4158, -737, 1485]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![28, 108, 1, 0, 0], ![1, 25, 0, 1, 0], ![23, 79, 0, 0, 1]] where
  M :=![![![-17449, -9279, 4158, -737, 1485], ![8910, 4826, -2008, 429, -737], ![-4422, -2145, 1321, -69, 429], ![2640, 1408, -632, 103, -226], ![2142, 1329, -262, 207, -146]]]
  hmulB := by decide  
  f := ![![![1293487, 2161859, -686640, 313949, -260157]], ![![-1560942, -2608868, 828618, -378861, 313949]], ![![-754222, -1260563, 400375, -183059, 151695]], ![![-225727, -377267, 119826, -54787, 45400]], ![![-543635, -908600, 288586, -131947, 109340]]]
  g := ![![![-967, -3221, 4158, -737, 1485], ![472, 1556, -2008, 429, -737], ![-296, -1023, 1321, -69, 429], ![147, 491, -632, 103, -226], ![73, 208, -262, 207, -146]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [109, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 172], [0, 1]]
 g := ![![[26, 100], [64], [128, 92], [50, 77], [163], [59, 31], [1]], ![[0, 73], [64], [111, 81], [158, 96], [163], [89, 142], [1]]]
 h' := ![![[107, 172], [32, 163], [61, 165], [86, 28], [87, 115], [143, 110], [64, 107], [0, 1]], ![[0, 1], [0, 10], [70, 8], [141, 145], [109, 58], [149, 63], [95, 66], [107, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [136, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [109, 66, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1946, 3982, -3612, -8618, 2081]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![369, 2573, -3612, -8618, 2081]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![1293487, 2161859, -686640, 313949, -260157]] ![![-17449, -9279, 4158, -737, 1485]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 5 2 7 [120, 20, 126, 124, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 127, 65, 177, 176], [89, 55, 95, 133, 132], [107, 66, 132, 12, 150], [55, 109, 66, 36, 79], [0, 1]]
 g := ![![[114, 3, 94, 92, 87], [51, 42, 143, 37, 121], [87, 133, 117, 139], [38, 161, 19, 89], [136, 90, 127, 33, 16], [1], []], ![[8, 39, 103, 91, 137, 24, 17, 30], [27, 60, 132, 112, 170, 177, 159, 157], [11, 36, 133, 116], [96, 71, 156, 68], [22, 144, 164, 101, 138, 61, 141, 38], [140, 42, 92, 125, 38, 96, 107, 112], [0, 26, 155, 9]], ![[161, 149, 155, 50, 164, 126, 140, 79], [44, 150, 87, 151, 84, 53, 162, 6], [89, 166, 33, 68], [139, 78, 100, 142], [128, 79, 116, 47, 143, 108, 38, 24], [103, 157, 78, 39, 65, 95, 26, 137], [174, 90, 142, 61]], ![[51, 41, 129, 173, 168, 142, 92, 97], [107, 56, 119, 106, 105, 71, 114, 123], [144, 149, 160, 106], [9, 29, 58, 107], [97, 157, 2, 42, 143, 159, 55, 118], [41, 42, 84, 56, 108, 162, 55, 73], [30, 30, 57, 125]], ![[75, 34, 159, 76, 169, 38, 128, 26], [103, 1, 114, 4, 47, 104, 163, 122], [81, 10, 44, 110], [91, 106, 47, 70], [83, 143, 129, 125, 91, 171, 150, 165], [98, 11, 44, 35, 12, 69, 106, 33], [67, 156, 56, 155]]]
 h' := ![![[103, 127, 65, 177, 176], [145, 8, 124, 144, 96], [124, 86, 99, 17, 168], [160, 3, 127, 99, 26], [148, 164, 159, 53, 39], [59, 159, 53, 55, 175], [0, 0, 1], [0, 1]], ![[89, 55, 95, 133, 132], [12, 157, 19, 91, 166], [159, 160, 53, 139, 109], [91, 75, 167, 25, 37], [100, 66, 57, 133, 151], [163, 20, 165, 43, 88], [48, 130, 17, 50, 34], [103, 127, 65, 177, 176]], ![[107, 66, 132, 12, 150], [139, 146, 44, 86, 53], [170, 8, 134, 103, 93], [162, 67, 158, 47, 28], [4, 161, 15, 86, 58], [66, 36, 110, 35, 7], [108, 164, 114, 177, 73], [89, 55, 95, 133, 132]], ![[55, 109, 66, 36, 79], [164, 87, 4, 146, 3], [28, 103, 88, 54, 104], [53, 6, 158, 117, 105], [136, 178, 145, 58, 69], [51, 177, 45, 136, 41], [152, 79, 83, 111, 175], [107, 66, 132, 12, 150]], ![[0, 1], [31, 139, 167, 70, 40], [14, 1, 163, 45, 63], [28, 28, 106, 70, 162], [108, 147, 161, 28, 41], [12, 145, 164, 89, 47], [176, 164, 143, 20, 76], [55, 109, 66, 36, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 21, 26, 136], [], [], []]
 b := ![[], [99, 87, 161, 120, 105], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 5
  hpos := by decide
  P := [120, 20, 126, 124, 4, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34983294600, 95512538400, -10660975080, -81218842808, -34363788488]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![195437400, 533589600, -59558520, -453736552, -191976472]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 78, -18, -80, -26]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![29, 78, -18, -80, -26]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![91, 142, 71, 1, 0], ![60, 117, 5, 0, 1]] where
  M :=![![![29, 78, -18, -80, -26], ![-156, -361, 208, 600, -80], ![-480, -1356, -17, 888, 600], ![840, 2098, -774, -2705, -152], ![1128, 3498, 750, -1020, -2561]]]
  hmulB := by decide  
  f := ![![![-2911, -2798, 1010, -344, 374]], ![![2244, 2699, -920, 360, -344]], ![![-2064, -2916, 955, -408, 360]], ![![-505, -422, 157, -49, 58]], ![![432, 741, -235, 108, -89]]]
  g := ![![![49, 80, 32, -80, -26], ![-276, -421, -232, 600, -80], ![-648, -1092, -365, 888, 600], ![1415, 2232, 1061, -2705, -152], ![1368, 2475, 475, -1020, -2561]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [66, 68, 162, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 57, 6], [160, 123, 175], [0, 1]]
 g := ![![[142, 96, 148], [0, 170], [76, 45, 34], [22, 59], [79, 111, 125], [112, 19, 1], []], ![[41, 117, 10, 54], [113, 49], [77, 61, 78, 98], [90, 180], [65, 40, 7, 131], [163, 102, 99, 93], [101, 36]], ![[64, 11, 95, 18], [101, 34], [70, 86, 151, 110], [102, 14], [2, 128, 132, 17], [23, 142, 125, 54], [113, 36]]]
 h' := ![![[40, 57, 6], [170, 155, 94], [52, 132, 129], [135, 116, 45], [35, 89, 125], [29, 180, 46], [0, 0, 1], [0, 1]], ![[160, 123, 175], [42, 43, 3], [160, 45, 7], [159, 0, 77], [44, 40, 162], [81, 50, 41], [2, 22, 123], [40, 57, 6]], ![[0, 1], [139, 164, 84], [164, 4, 45], [132, 65, 59], [158, 52, 75], [172, 132, 94], [42, 159, 57], [160, 123, 175]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 35], []]
 b := ![[], [67, 82, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [66, 68, 162, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-763245, -1922028, 939660, 2866344, -80961]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1418469, -2207019, -1116939, 2866344, -80961]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2911, 2798, -1010, 344, -374]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![2911, 2798, -1010, 344, -374]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![169, 120, 1, 0, 0], ![65, 72, 0, 1, 0], ![142, 87, 0, 0, 1]] where
  M :=![![![2911, 2798, -1010, 344, -374], ![-2244, -2699, 920, -360, 344], ![2064, 2916, -955, 408, -360], ![-1392, -2014, 658, -283, 248], ![-624, -798, 270, -108, 101]]]
  hmulB := by decide  
  f := ![![![-29, -78, 18, 80, 26]], ![![156, 361, -208, -600, 80]], ![![79, 174, -121, -328, 74]], ![![47, 104, -72, -195, 42]], ![![46, 93, -90, -220, 73]]]
  g := ![![![1129, 728, -1010, 344, -374], ![-1012, -647, 920, -360, 344], ![1039, 660, -955, 408, -360], ![-715, -454, 658, -283, 248], ![-296, -189, 270, -108, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [9, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 180], [0, 1]]
 g := ![![[83, 161], [129], [2, 161], [137], [64, 55], [12, 167], [1]], ![[0, 20], [129], [100, 20], [137], [66, 126], [153, 14], [1]]]
 h' := ![![[158, 180], [68, 121], [163, 55], [37, 121], [148, 104], [73, 112], [172, 158], [0, 1]], ![[0, 1], [0, 60], [165, 126], [150, 60], [109, 77], [31, 69], [158, 23], [158, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [62, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [9, 23, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![89, 145, -196, -565, 207]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![224, 256, -196, -565, 207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![29, 78, -18, -80, -26]] ![![2911, 2798, -1010, 344, -374]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4231, 12007, 11481, 5690, 1980]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![4231, 12007, 11481, 5690, 1980]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![85, 16, 134, 54, 1]] where
  M :=![![![4231, 12007, 11481, 5690, 1980], ![11880, 33931, 32840, 16176, 5690], ![34140, 97230, 93515, 46092, 16176], ![-894, -2485, -2261, -1105, -406], ![29022, 82791, 80193, 39834, 13853]]]
  hmulB := by decide  
  f := ![![![18053, 9629, -4267, 778, -1530]], ![![-9180, -4897, 2170, -396, 778]], ![![4668, 2490, -1103, 204, -396]], ![![-2730, -1457, 645, -119, 232]], ![![9757, 5204, -2306, 422, -827]]]
  g := ![![![-859, -103, -1329, -530, 1980], ![-2470, -299, -3820, -1524, 5690], ![-7020, -846, -10859, -4332, 16176], ![176, 21, 273, 109, -406], ![-6013, -727, -9299, -3708, 13853]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [73, 154, 122, 155, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 172, 58, 115], [14, 27, 8, 86], [100, 182, 125, 181], [0, 1]]
 g := ![![[22, 111, 40, 108], [104, 162, 86, 79], [10, 97, 87, 97], [84, 25, 57, 108], [156, 136, 174, 20], [36, 1], []], ![[172, 34, 109, 39, 82, 160], [135, 134, 87, 167, 190, 129], [190, 106, 60, 11, 9, 64], [115, 57, 40, 176, 27, 15], [34, 162, 21, 99, 159, 172], [134, 101, 11, 105, 144, 72], [157, 98, 46]], ![[134, 2, 7, 6, 22, 5], [60, 86, 144, 85, 51, 69], [39, 9, 78, 14, 16, 184], [161, 128, 133, 112, 147, 108], [112, 4, 108, 73, 100, 8], [116, 23, 138, 172, 45, 4], [44, 41, 138]], ![[142, 13, 144, 105, 13, 111], [46, 55, 172, 159, 156, 7], [179, 143, 164, 141, 178, 185], [76, 88, 179, 36, 77, 124], [100, 151, 147, 167, 68, 88], [18, 148, 137, 180, 163, 182], [39, 145, 100]]]
 h' := ![![[113, 172, 58, 115], [48, 54, 45, 144], [34, 183, 154, 156], [171, 164, 75, 111], [72, 61, 120, 144], [46, 113, 38, 28], [0, 0, 1], [0, 1]], ![[14, 27, 8, 86], [140, 91, 62, 171], [56, 21, 10, 185], [148, 164, 158, 55], [117, 98, 68, 18], [65, 21, 18, 96], [162, 91, 122, 84], [113, 172, 58, 115]], ![[100, 182, 125, 181], [137, 114, 3, 181], [51, 78, 57, 59], [4, 174, 158, 54], [12, 86, 113, 21], [180, 145, 63, 55], [40, 155, 16, 135], [14, 27, 8, 86]], ![[0, 1], [93, 123, 81, 77], [49, 100, 161, 173], [69, 71, 182, 162], [9, 137, 81, 8], [71, 103, 72, 12], [86, 136, 52, 163], [100, 182, 125, 181]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [67, 5, 177], []]
 b := ![[], [], [60, 176, 28, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [73, 154, 122, 155, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8116789, 24914414, 6729436, -6254322, -15906958]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7121509, 1462962, 11195088, 4464510, -15906958]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18053, 9629, -4267, 778, -1530]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![18053, 9629, -4267, 778, -1530]] 
 ![![191, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![140, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![165, 0, 0, 0, 1]] where
  M :=![![![18053, 9629, -4267, 778, -1530], ![-9180, -4897, 2170, -396, 778], ![4668, 2490, -1103, 204, -396], ![-2730, -1457, 645, -119, 232], ![-2130, -1131, 501, -102, 181]]]
  hmulB := by decide  
  f := ![![![4231, 12007, 11481, 5690, 1980]], ![![3097, 8790, 8407, 4166, 1450]], ![![3280, 9310, 8905, 4412, 1536]], ![![970, 2753, 2633, 1305, 454]], ![![3807, 10806, 10338, 5124, 1783]]]
  g := ![![![-2542, 9629, -4267, 778, -1530], ![1293, -4897, 2170, -396, 778], ![-658, 2490, -1103, 204, -396], ![385, -1457, 645, -119, 232], ![300, -1131, 501, -102, 181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![4231, 12007, 11481, 5690, 1980]] ![![18053, 9629, -4267, 778, -1530]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1549, 4103, 3388, 1805, 557]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![1549, 4103, 3388, 1805, 557]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![93, 24, 1, 0, 0], ![64, 4, 0, 1, 0], ![106, 4, 0, 0, 1]] where
  M :=![![![1549, 4103, 3388, 1805, 557], ![3342, 9904, 10234, 4887, 1805], ![10830, 30417, 28499, 14253, 4887], ![-528, -1186, -564, -415, -68], ![8838, 25311, 24616, 12093, 4268]]]
  hmulB := by decide  
  f := ![![![21817, 11649, -5158, 923, -1853]], ![![-11118, -5978, 2664, -363, 923]], ![![9159, 4884, -2161, 402, -780]], ![![6988, 3732, -1652, 295, -594]], ![![11740, 6271, -2774, 497, -1000]]]
  g := ![![![-2529, -449, 3388, 1805, 557], ![-7526, -1360, 10234, 4887, 1805], ![-21087, -3783, 28499, 14253, 4887], ![444, 74, -564, -415, -68], ![-18170, -3269, 24616, 12093, 4268]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [116, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 192], [0, 1]]
 g := ![![[127, 49], [169], [93], [85], [137], [118], [129, 1]], ![[79, 144], [169], [93], [85], [137], [118], [65, 192]]]
 h' := ![![[129, 192], [84, 186], [52, 13], [15, 38], [15, 144], [9, 152], [90, 120], [0, 1]], ![[0, 1], [146, 7], [185, 180], [92, 155], [63, 49], [124, 41], [130, 73], [129, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149]]
 b := ![[], [68, 171]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [116, 64, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![835, 1438, -1115, -3046, 1121]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![936, 186, -1115, -3046, 1121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26209, -44133, 13998, -6419, 5305]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-26209, -44133, 13998, -6419, 5305]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![24, 141, 1, 0, 0], ![3, 94, 0, 1, 0], ![93, 103, 0, 0, 1]] where
  M :=![![![-26209, -44133, 13998, -6419, 5305], ![31830, 53366, -16940, 7755, -6419], ![-38514, -64455, 20467, -9363, 7755], ![27012, 45196, -14352, 6565, -5438], ![9894, 16575, -5262, 2409, -1994]]]
  hmulB := by decide  
  f := ![![![59, 157, 92, -5, 23]], ![![138, 404, 346, 153, -5]], ![![108, 315, 271, 120, 0]], ![![69, 201, 168, 70, -1]], ![![111, 314, 226, 57, 8]]]
  g := ![![![-4333, -10160, 13998, -6419, 5305], ![5244, 12301, -16940, 7755, -6419], ![-6336, -14865, 20467, -9363, 7755], ![4443, 10424, -14352, 6565, -5438], ![1629, 3821, -5262, 2409, -1994]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [88, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [132, 192], [0, 1]]
 g := ![![[95, 147], [83], [3], [192], [54], [191], [132, 1]], ![[6, 46], [83], [3], [192], [54], [191], [71, 192]]]
 h' := ![![[132, 192], [3, 95], [121, 58], [81, 179], [46, 81], [121, 61], [157, 159], [0, 1]], ![[0, 1], [191, 98], [57, 135], [163, 14], [123, 112], [67, 132], [108, 34], [132, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [98, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [88, 61, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![342, -14, 7, 89, -1]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![0, -48, 7, 89, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3419, -1777, 868, -121, 301]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-3419, -1777, 868, -121, 301]] 
 ![![193, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![181, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![175, 0, 0, 0, 1]] where
  M :=![![![-3419, -1777, 868, -121, 301], ![1806, 1096, -256, 153, -121], ![-726, -9, 659, 183, 153], ![516, 266, -134, 17, -46], ![546, 615, 288, 207, 32]]]
  hmulB := by decide  
  f := ![![![-383, -675, 126, -187, 179]], ![![-50, -86, 14, -37, 25]], ![![-365, -642, 131, -154, 158]], ![![-130, -238, 42, -39, 66]], ![![-323, -564, 60, -292, 199]]]
  g := ![![![-808, -1777, 868, -121, 301], ![151, 1096, -256, 153, -121], ![-818, -9, 659, 183, 153], ![126, 266, -134, 17, -46], ![-452, 615, 288, 207, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![1549, 4103, 3388, 1805, 557]] ![![-26209, -44133, 13998, -6419, 5305]]
  ![![13782935, 23036196, -7316016, 3345528, -2772020]] where
 M := ![![![13782935, 23036196, -7316016, 3345528, -2772020]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![13782935, 23036196, -7316016, 3345528, -2772020]] ![![-3419, -1777, 868, -121, 301]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![3712355, 6357613, -1575652, 1037761, -665657]]]
 hmul := by decide  
 g := ![![![![19235, 32941, -8164, 5377, -3449]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-443381, -740257, 235171, -107476, 89098]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-443381, -740257, 235171, -107476, 89098]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![45, 56, 156, 184, 1]] where
  M :=![![![-443381, -740257, 235171, -107476, 89098], ![534588, 893089, -283660, 129690, -107476], ![-644856, -1077552, 342323, -156462, 129690], ![452118, 755525, -239975, 109715, -90922], ![165966, 277311, -88029, 40284, -33361]]]
  hmulB := by decide  
  f := ![![![11, 27, -15, -44, 4]], ![![24, 71, 10, -30, -44]], ![![-264, -636, 307, 942, -30]], ![![102, 199, -243, -545, 172]], ![![-99, -278, 10, 200, 125]]]
  g := ![![![-22603, -29085, -69361, -83764, 89098], ![27264, 35085, 83668, 101042, -107476], ![-32898, -42336, -100961, -121926, 129690], ![23064, 29681, 70781, 85479, -90922], ![8463, 10891, 25971, 31364, -33361]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [133, 3, 160, 152, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [160, 116, 74, 118], [191, 5, 184, 81], [88, 75, 136, 195], [0, 1]]
 g := ![![[101, 66, 78, 181], [25, 156, 156], [60, 97, 156, 7], [112, 143, 160], [146, 179, 41], [92, 45, 1], []], ![[85, 27, 168, 105, 187, 123], [126, 74, 112], [78, 70, 26, 104, 158, 166], [108, 23, 55], [97, 179, 174], [131, 37, 51], [67, 55, 1, 68, 174, 52]], ![[184, 53, 72, 45, 81, 1], [21, 105, 144], [117, 176, 160, 101, 122, 143], [11, 97, 65], [116, 112, 47], [29, 2, 191], [178, 13, 44, 31, 54, 132]], ![[34, 8, 6, 21, 125, 179], [100, 127, 146], [12, 143, 110, 162, 167, 2], [12, 190, 61], [191, 142, 81], [175, 87, 173], [10, 34, 25, 58, 90, 189]]]
 h' := ![![[160, 116, 74, 118], [174, 171, 81, 56], [97, 94, 29, 133], [166, 90, 147, 106], [175, 64, 192, 95], [175, 43, 181, 89], [0, 0, 0, 1], [0, 1]], ![[191, 5, 184, 81], [125, 176, 125, 166], [27, 32, 42, 30], [7, 83, 101, 67], [37, 148, 36, 152], [85, 87, 177, 78], [127, 36, 196, 144], [160, 116, 74, 118]], ![[88, 75, 136, 195], [136, 65, 130, 175], [163, 39, 44, 185], [20, 52, 5, 38], [164, 48, 25, 38], [134, 60, 154, 21], [144, 50, 23, 83], [191, 5, 184, 81]], ![[0, 1], [63, 179, 58, 194], [19, 32, 82, 46], [149, 169, 141, 183], [184, 134, 141, 109], [119, 7, 79, 9], [98, 111, 175, 166], [88, 75, 136, 195]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [186, 65, 56], []]
 b := ![[], [], [150, 25, 114, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [133, 3, 160, 152, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48213986345, 119580890484, -46138391216, -157916235702, -5450600586]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1489802095, 2156418900, 4082006600, 4289311026, -5450600586]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -27, 15, 44, -4]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-11, -27, 15, 44, -4]] 
 ![![197, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![188, 0, 0, 1, 0], ![118, 0, 0, 0, 1]] where
  M :=![![![-11, -27, 15, 44, -4], ![-24, -71, -10, 30, 44], ![264, 636, -307, -942, 30], ![-102, -199, 243, 545, -172], ![-1074, -2643, 1095, 3612, 59]]]
  hmulB := by decide  
  f := ![![![443381, 740257, -235171, 107476, -89098]], ![![26545, 44316, -14079, 6434, -5334]], ![![66292, 110684, -35163, 16070, -13322]], ![![420830, 702603, -223209, 102009, -84566]], ![![264736, 441995, -140417, 64172, -53199]]]
  g := ![![![-40, -27, 15, 44, -4], ![-49, -71, -10, 30, 44], ![884, 636, -307, -942, 30], ![-439, -199, 243, 545, -172], ![-3469, -2643, 1095, 3612, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-443381, -740257, 235171, -107476, 89098]] ![![-11, -27, 15, 44, -4]]
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


lemma PB1556I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB1556I4 : PrimesBelowBoundCertificateInterval O 151 197 1556 where
  m := 9
  g := ![2, 3, 2, 2, 1, 2, 2, 3, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1556I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![4330747, 163, 163]
    · exact ![777796321, 167]
    · exact ![5177717, 29929]
    · exact ![183765996899]
    · exact ![5929741, 32761]
    · exact ![1330863361, 191]
    · exact ![37249, 37249, 193]
    · exact ![1506138481, 197]
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I163N1, I163N2, I167N1, I191N1, I193N2, I197N1]
  Il := ![[I157N1], [I163N1, I163N2], [I167N1], [], [], [], [I191N1], [I193N2], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
