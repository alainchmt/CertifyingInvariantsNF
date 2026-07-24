
import IdealArithmetic.Examples.NF5_3_67500000_1.RI5_3_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12883, -8486, -850, 1634, 4020]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![12883, -8486, -850, 1634, 4020]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![6, 65, 135, 1, 0], ![120, 128, 148, 0, 1]] where
  M :=![![![12883, -8486, -850, 1634, 4020], ![-7158, 4875, 306, -818, -2256], ![4314, -2538, -257, 414, 1860], ![1410, -2578, 954, -157, -420], ![-1998, 2774, -878, 118, 1]]]
  hmulB := by decide  
  f := ![![![-893, 3230, 12394, 29062, 29940]], ![![-2634, 8867, 34926, 82034, 84552]], ![![-7554, 24738, 98455, 231402, 238548]], ![![-7680, 25259, 100365, 235867, 243144]], ![![-9954, 33026, 130794, 307314, 316777]]]
  g := ![![![-3053, -4008, -5200, 1634, 4020], ![1710, 2209, 2832, -818, -2256], ![-1410, -1704, -2111, 414, 1860], ![336, 391, 537, -157, -420], ![-18, -32, -108, 118, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [9, 108, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 140, 148], [155, 16, 9], [0, 1]]
 g := ![![[6, 151, 121], [118, 35], [82, 68, 33], [18, 67, 25], [131, 87, 141], [101, 1], []], ![[48, 62, 59, 153], [71, 9], [155, 59, 156, 148], [129, 67], [42, 22, 132, 75], [32, 99], [9, 81]], ![[53, 97, 102, 19], [125, 46], [131, 48, 147, 153], [144, 39, 111, 68], [44, 21, 48, 100], [24, 132], [148, 81]]]
 h' := ![![[103, 140, 148], [48, 8, 11], [47, 134, 105], [152, 85, 87], [77, 131, 5], [33, 73, 45], [0, 0, 1], [0, 1]], ![[155, 16, 9], [29, 93, 104], [36, 122, 3], [113, 95, 156], [113, 18], [107, 124, 63], [9, 135, 16], [103, 140, 148]], ![[0, 1], [25, 56, 42], [69, 58, 49], [155, 134, 71], [83, 8, 152], [101, 117, 49], [85, 22, 140], [155, 16, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 59], []]
 b := ![[], [34, 84, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [9, 108, 56, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23888, 16552, -25931, -18334, 12268]
  a := ![-5, -7, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8524, -2306, 4035, -18334, 12268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 11, 1, -2, -6]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-17, 11, 1, -2, -6]] 
 ![![157, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![121, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-17, 11, 1, -2, -6], ![12, -4, -3, 2, 6], ![-12, -3, 10, -6, -6], ![-6, 1, -3, 3, -12], ![9, 1, -1, -1, 13]]]
  hmulB := by decide  
  f := ![![![289, 607, 35, -268, -378]], ![![142, 298, 17, -132, -186]], ![![63, 132, 7, -60, -84]], ![![223, 468, 26, -209, -294]], ![![100, 210, 12, -93, -131]]]
  g := ![![![-2, 11, 1, -2, -6], ![-1, -4, -3, 2, 6], ![6, -3, 10, -6, -6], ![2, 1, -3, 3, -12], ![-4, 1, -1, -1, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3679, 9063, 40575, 96030, 99186]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-3679, 9063, 40575, 96030, 99186]] 
 ![![157, 0, 0, 0, 0], ![125, 1, 0, 0, 0], ![75, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![-3679, 9063, 40575, 96030, 99186], ![-9468, 27428, 114561, 270054, 278622], ![-25704, 79389, 323186, 760662, 784458], ![-30960, 99333, 398439, 936923, 965988], ![-1047, 5265, 18183, 42327, 43517]]]
  hmulB := by decide  
  f := ![![![284267, -183861, -20919, 36756, 90462]], ![![225301, -145735, -16566, 29124, 71700]], ![![136347, -88218, -10033, 17640, 43344]], ![![212283, -137160, -15714, 27479, 67626]], ![![245753, -159075, -17997, 31743, 78155]]]
  g := ![![![-184105, 9063, 40575, 96030, 99186], ![-519229, 27428, 114561, 270054, 278622], ![-1464153, 79389, 323186, 760662, 784458], ![-1804617, 99333, 398439, 936923, 965988], ![-82124, 5265, 18183, 42327, 43517]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![12883, -8486, -850, 1634, 4020]] ![![-17, 11, 1, -2, -6]]
  ![![-284267, 183861, 20919, -36756, -90462]] where
 M := ![![![-284267, 183861, 20919, -36756, -90462]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-284267, 183861, 20919, -36756, -90462]] ![![-3679, 9063, 40575, 96030, 99186]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![207, 282, -330, -990, -1082]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![207, 282, -330, -990, -1082]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![121, 28, 1, 0, 0], ![99, 158, 0, 1, 0], ![65, 25, 0, 0, 1]] where
  M :=![![![207, 282, -330, -990, -1082], ![276, 153, -984, -2548, -2694], ![438, -270, -2833, -6918, -7206], ![294, -842, -3534, -8333, -8598], ![-110, -294, -182, -282, -249]]]
  hmulB := by decide  
  f := ![![![-231, 42, 142, -102, -38]], ![![-192, -281, 132, 16, -498]], ![![-195, -8, 117, -68, -104]], ![![-333, -254, 228, -55, -504]], ![![-119, -23, 68, -32, -97]]]
  g := ![![![1279, 1184, -330, -990, -1082], ![3354, 3053, -984, -2548, -2694], ![9181, 8296, -2833, -6918, -7206], ![11115, 9998, -3534, -8333, -8598], ![405, 341, -182, -282, -249]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [140, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 162], [0, 1]]
 g := ![![[48, 85], [27, 58], [24], [46], [96], [131, 65], [1]], ![[0, 78], [0, 105], [24], [46], [96], [8, 98], [1]]]
 h' := ![![[126, 162], [132, 30], [99, 104], [157, 26], [136, 131], [79, 111], [23, 126], [0, 1]], ![[0, 1], [0, 133], [0, 59], [10, 137], [16, 32], [47, 52], [88, 37], [126, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [142, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [140, 37, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5714, 15785, -18813, 64736, 7050]
  a := ![6, -59, -1, -60, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28129, -60503, -18813, 64736, 7050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3207, 2169, 163, -384, -992]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-3207, 2169, 163, -384, -992]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![139, 4, 1, 0, 0], ![48, 62, 0, 1, 0], ![135, 19, 0, 0, 1]] where
  M :=![![![-3207, 2169, 163, -384, -992], ![1824, -1220, -39, 166, 672], ![-1518, 267, 464, -252, -1020], ![240, 1235, -1125, 513, 438], ![103, -1113, 909, -423, -105]]]
  hmulB := by decide  
  f := ![![![3453, -6885, -34077, -81078, -83864]], ![![8358, -22266, -96321, -227524, -234876]], ![![3285, -6822, -33091, -78652, -81332]], ![![4356, -11009, -48729, -115255, -119022]], ![![3838, -8328, -39545, -93889, -97059]]]
  g := ![![![776, 271, 163, -384, -992], ![-561, -148, -39, 166, 672], ![514, 205, 464, -252, -1020], ![447, -211, -1125, 513, 438], ![-563, 144, 909, -423, -105]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [80, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 162], [0, 1]]
 g := ![![[52, 39], [109, 85], [145], [77], [83], [130, 53], [1]], ![[160, 124], [56, 78], [145], [77], [83], [26, 110], [1]]]
 h' := ![![[78, 162], [82, 107], [19, 30], [131, 54], [89, 27], [32, 75], [83, 78], [0, 1]], ![[0, 1], [115, 56], [77, 133], [105, 109], [76, 136], [14, 88], [136, 85], [78, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [40, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [80, 85, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![200, -179, -81, -26, 204]
  a := ![-1, -5, 1, -6, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-91, -13, -81, -26, 204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 3, 3, 6, 6]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![1, 3, 3, 6, 6]] 
 ![![163, 0, 0, 0, 0], ![131, 1, 0, 0, 0], ![117, 0, 1, 0, 0], ![95, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![1, 3, 3, 6, 6], ![0, 4, 9, 18, 18], ![0, 9, 22, 54, 54], ![0, 9, 27, 67, 72], ![-3, -3, 3, 3, 1]]]
  hmulB := by decide  
  f := ![![![2413, -1551, -165, 300, 750]], ![![1931, -1241, -132, 240, 600]], ![![1737, -1116, -119, 216, 540]], ![![1409, -906, -96, 175, 438]], ![![1181, -759, -81, 147, 367]]]
  g := ![![![-11, 3, 3, 6, 6], ![-29, 4, 9, 18, 18], ![-81, 9, 22, 54, 54], ![-101, 9, 27, 67, 72], ![-2, -3, 3, 3, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![207, 282, -330, -990, -1082]] ![![-3207, 2169, 163, -384, -992]]
  ![![2413, -1551, -165, 300, 750]] where
 M := ![![![2413, -1551, -165, 300, 750]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![2413, -1551, -165, 300, 750]] ![![1, 3, 3, 6, 6]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0, 0, 0]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![0, 0, 0, 0, 167]] where
  M :=![![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![0, 0, 0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 5 2 7 [130, 31, 76, 104, 120, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 164, 93, 160, 44], [158, 151, 107, 111, 109], [29, 89, 121, 32, 31], [104, 96, 13, 31, 150], [0, 1]]
 g := ![![[25, 165, 89, 22, 62], [132, 73, 41, 155, 112], [66, 22, 94, 116, 85], [67, 100, 5, 89], [140, 107, 26, 38], [1], []], ![[75, 34, 0, 83, 31, 64, 60, 29], [90, 12, 100, 82, 146, 117, 12, 29], [25, 52, 113, 165, 83, 149, 137, 32], [159, 23, 37, 6], [45, 166, 84, 61], [101, 153, 2, 50, 25, 125, 104, 22], [84, 135, 29, 99]], ![[19, 60, 92, 93, 93, 122, 117, 39], [42, 30, 109, 58, 149, 45, 75, 131], [135, 72, 47, 47, 4, 102, 83, 23], [131, 76, 125, 137], [106, 15, 16, 97], [23, 103, 21, 95, 121, 87, 8, 13], [46, 31, 109, 24]], ![[116, 75, 13, 12, 118, 75, 50, 75], [34, 129, 63, 1, 121, 62, 145, 144], [79, 153, 40, 87, 148, 97, 106, 77], [71, 73, 131, 144], [147, 142, 57, 99], [115, 11, 105, 114, 111, 0, 86, 63], [21, 105, 57, 126]], ![[143, 35, 90, 137, 48, 78, 129, 16], [94, 69, 106, 112, 95, 83, 71, 88], [63, 5, 14, 155, 122, 112, 56, 7], [31, 115, 157, 76], [121, 135, 8, 89], [125, 153, 53, 126, 81, 57, 117, 9], [62, 43, 4, 122]]]
 h' := ![![[90, 164, 93, 160, 44], [41, 73, 72, 124, 88], [104, 118, 98, 8, 46], [101, 71, 13, 128, 69], [36, 164, 44, 141, 151], [37, 136, 91, 63, 47], [0, 0, 1], [0, 1]], ![[158, 151, 107, 111, 109], [61, 75, 104, 29, 65], [103, 60, 87, 163, 102], [154, 124, 82, 41, 146], [139, 86, 16, 105, 138], [155, 62, 113, 67, 140], [19, 14, 72, 153, 77], [90, 164, 93, 160, 44]], ![[29, 89, 121, 32, 31], [121, 12, 87, 91, 71], [98, 26, 131, 16, 134], [29, 49, 151, 56, 66], [162, 104, 64, 6, 114], [158, 93, 55, 129, 40], [113, 9, 77, 144, 20], [158, 151, 107, 111, 109]], ![[104, 96, 13, 31, 150], [93, 94, 77, 25, 125], [24, 162, 72, 122, 146], [82, 34, 64, 110, 156], [131, 141, 155, 33, 155], [6, 65, 101, 75, 123], [115, 46, 6, 93, 123], [29, 89, 121, 32, 31]], ![[0, 1], [114, 80, 161, 65, 152], [159, 135, 113, 25, 73], [92, 56, 24, 166, 64], [92, 6, 55, 49, 110], [142, 145, 141, 0, 151], [84, 98, 11, 111, 114], [104, 96, 13, 31, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 142, 112, 153], [], [], []]
 b := ![[], [16, 165, 125, 40, 99], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 5
  hpos := by decide
  P := [130, 31, 76, 104, 120, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4962258541, 35433806828, 136872852306, 262526964751, 347037757134]
  a := ![8, 26, -3, 25, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![29714123, 212178484, 819597918, 1572017753, 2078070402]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 129891985607 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![689, 392, -2436, -6314, -6678]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![689, 392, -2436, -6314, -6678]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![15, 116, 70, 84, 1]] where
  M :=![![![689, 392, -2436, -6314, -6678], ![1092, -655, -7014, -17136, -17850], ![2142, -3780, -19933, -47586, -49266], ![1974, -6048, -24696, -58111, -59934], ![-252, -980, -1176, -2380, -2335]]]
  hmulB := by decide  
  f := ![![![1201, -784, -84, 154, 378]], ![![-672, 445, 42, -84, -210]], ![![378, -252, -17, 42, 126]], ![![210, -168, 0, 25, 42]], ![![-93, 48, 14, -14, -37]]]
  g := ![![![583, 4480, 2688, 3206, -6678], ![1554, 11965, 7182, 8568, -17850], ![4284, 33012, 19819, 23646, -49266], ![5208, 40152, 24108, 28765, -59934], ![201, 1560, 938, 1120, -2335]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [172, 10, 0, 50, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 113, 38, 54], [167, 42, 111, 81], [45, 17, 24, 38], [0, 1]]
 g := ![![[84, 102, 152, 83], [120, 114, 142], [137, 170, 119, 151], [155, 131, 153, 10], [50, 104, 29], [123, 1], []], ![[118, 23, 145, 12, 97, 60], [70, 130, 73], [0, 59, 104, 28, 134, 132], [11, 32, 44, 119, 61, 89], [25, 125, 73], [160, 45, 65, 36, 82, 51], [85, 164, 148]], ![[4, 78, 151, 22, 20, 43], [134, 41, 73], [94, 81, 163, 156, 93, 106], [153, 27, 121, 158, 122, 130], [50, 104, 29], [101, 3, 162, 81, 68, 106], [100, 121, 160]], ![[154, 47, 58, 127, 112, 117], [115, 59, 43], [86, 61, 65, 22, 61, 38], [67, 132, 59, 121, 131, 78], [25, 125, 73], [91, 61, 152, 158, 31, 73], [118, 35, 60]]]
 h' := ![![[84, 113, 38, 54], [32, 52, 71, 157], [137, 162, 131, 83], [155, 87, 157, 155], [128, 20, 140, 150], [123, 155, 163, 78], [0, 0, 1], [0, 1]], ![[167, 42, 111, 81], [154, 135, 41, 50], [118, 143, 69, 65], [117, 136, 37, 39], [142, 91, 18, 126], [109, 74, 124, 108], [48, 133, 15, 166], [84, 113, 38, 54]], ![[45, 17, 24, 38], [56, 169, 69, 34], [21, 2, 59, 65], [120, 37, 147, 151], [28, 79, 19, 125], [18, 18, 10, 95], [136, 1, 74, 22], [167, 42, 111, 81]], ![[0, 1], [137, 163, 165, 105], [56, 39, 87, 133], [149, 86, 5, 1], [11, 156, 169, 118], [32, 99, 49, 65], [67, 39, 83, 158], [45, 17, 24, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [86, 14, 93], []]
 b := ![[], [], [72, 114, 14, 127], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [172, 10, 0, 50, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33742950, -43056132, 93983729, -61873682, 36791207]
  a := ![-10, -8, 5, -6, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3385035, -24918128, -14343357, -18221590, 36791207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1201, -784, -84, 154, 378]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![1201, -784, -84, 154, 378]] 
 ![![173, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![89, 0, 0, 0, 1]] where
  M :=![![![1201, -784, -84, 154, 378], ![-672, 445, 42, -84, -210], ![378, -252, -17, 42, 126], ![210, -168, 0, 25, 42], ![-252, 196, 0, -28, -59]]]
  hmulB := by decide  
  f := ![![![689, 392, -2436, -6314, -6678]], ![![78, 37, -294, -756, -798]], ![![100, 28, -425, -1078, -1134]], ![![565, 280, -2100, -5409, -5712]], ![![353, 196, -1260, -3262, -3449]]]
  g := ![![![-219, -784, -84, 154, 378], ![120, 445, 42, -84, -210], ![-68, -252, -17, 42, 126], ![-23, -168, 0, 25, 42], ![31, 196, 0, -28, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![689, 392, -2436, -6314, -6678]] ![![1201, -784, -84, 154, 378]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 5 2 7 [67, 163, 123, 133, 65, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 91, 20, 36, 177], [74, 69, 33, 81, 164], [64, 74, 98, 144, 151], [116, 123, 28, 97, 45], [0, 1]]
 g := ![![[133, 29, 167, 134, 59], [138, 33, 79, 131, 141], [11, 167, 152, 141], [130, 70, 56, 108], [132, 137, 103, 67, 108], [1], []], ![[17, 173, 28, 3, 78, 163, 63, 61], [49, 58, 81, 15, 144, 85, 78, 25], [101, 101, 121, 59], [35, 164, 69, 65], [4, 110, 167, 99, 16, 38, 154, 47], [142, 123, 70, 42, 89, 97, 130, 13], [55, 94, 133, 4]], ![[52, 170, 19, 141, 124, 170, 125, 90], [47, 139, 159, 78, 19, 23, 153, 128], [178, 65, 44, 22], [155, 5, 55, 169], [60, 57, 94, 32, 176, 53, 42, 97], [145, 9, 135, 125, 150, 5, 122, 55], [55, 18, 129, 46]], ![[0, 44, 170, 28, 132, 38, 165, 121], [28, 24, 121, 99, 49, 165, 23, 43], [31, 94, 176, 1], [80, 9, 51, 147], [160, 169, 36, 3, 98, 26, 9, 25], [116, 55, 157, 78, 138, 171, 161, 16], [94, 171, 46, 68]], ![[117, 133, 27, 102, 74, 64, 13, 51], [45, 151, 45, 78, 17, 171, 162, 139], [122, 147, 137, 65], [75, 31, 60, 124], [167, 65, 40, 156, 115, 173, 47, 68], [113, 171, 149, 2, 2, 70, 95, 80], [114, 127, 78, 56]]]
 h' := ![![[39, 91, 20, 36, 177], [62, 80, 93, 60, 136], [21, 51, 17, 94, 118], [20, 26, 53, 19, 118], [106, 107, 2, 75, 114], [112, 16, 56, 46, 114], [0, 0, 1], [0, 1]], ![[74, 69, 33, 81, 164], [16, 162, 112, 86, 136], [120, 88, 56, 70, 163], [117, 92, 178, 46, 43], [99, 158, 73, 40, 85], [112, 130, 117, 90, 31], [163, 69, 144, 171, 21], [39, 91, 20, 36, 177]], ![[64, 74, 98, 144, 151], [74, 68, 36, 134, 50], [84, 78, 109, 110, 84], [14, 63, 9, 16, 102], [165, 36, 61, 16, 166], [25, 157, 99, 50, 39], [1, 41, 74, 88, 45], [74, 69, 33, 81, 164]], ![[116, 123, 28, 97, 45], [152, 30, 128, 39, 31], [17, 97, 15, 119, 45], [29, 148, 162, 31, 1], [127, 55, 77, 155, 46], [31, 155, 160, 150, 51], [125, 56, 26, 56, 174], [64, 74, 98, 144, 151]], ![[0, 1], [71, 18, 168, 39, 5], [149, 44, 161, 144, 127], [140, 29, 135, 67, 94], [137, 2, 145, 72, 126], [155, 79, 105, 22, 123], [90, 13, 113, 43, 118], [116, 123, 28, 97, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 157, 8, 96], [], [], []]
 b := ![[], [83, 163, 137, 50, 48], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 5
  hpos := by decide
  P := [67, 163, 123, 133, 65, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![397695081349, 321151269788, -279186024698, 60494150134, 616907445132]
  a := ![6, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2221760231, 1794141172, -1559698462, 337956146, 3446410308]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -197, -17, 68, 106]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-27, -197, -17, 68, 106]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![179, 50, 1, 1, 0], ![153, 19, 158, 0, 1]] where
  M :=![![![-27, -197, -17, 68, 106], ![-114, -158, -15, 64, 90], ![-78, -207, -16, 72, 114], ![-6, -31, 3, 3, 0], ![49, 125, 3, -41, -57]]]
  hmulB := by decide  
  f := ![![![3, -1, -3, -2, -2]], ![![0, 0, -3, -10, -6]], ![![-12, -15, 2, -30, -42]], ![![3, -1, -4, -5, -4]], ![![-8, -14, -1, -29, -39]]]
  g := ![![![-157, -31, -93, 68, 106], ![-140, -28, -79, 64, 90], ![-168, -33, -100, 72, 114], ![-3, -1, 0, 3, 0], ![89, 18, 50, -41, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [56, 44, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 154, 139], [92, 26, 42], [0, 1]]
 g := ![![[62, 150, 20], [70, 177], [109, 37, 168], [56, 15], [52, 95, 129], [179, 59, 1], []], ![[49, 165, 57, 136], [62, 132], [124, 54, 175, 44], [52, 55], [17, 156, 27, 99], [49, 25, 62, 25], [97, 135]], ![[146, 104, 115, 81], [162, 100], [14, 93, 164, 38], [106, 11], [35, 132, 68, 144], [102, 101, 164, 29], [13, 135]]]
 h' := ![![[148, 154, 139], [28, 33, 127], [50, 85, 38], [16, 15, 63], [165, 49, 167], [112, 42, 126], [0, 0, 1], [0, 1]], ![[92, 26, 42], [152, 41, 106], [179, 39, 133], [127, 16, 103], [163, 132, 112], [119, 70, 64], [1, 90, 26], [148, 154, 139]], ![[0, 1], [172, 107, 129], [111, 57, 10], [64, 150, 15], [82, 0, 83], [45, 69, 172], [134, 91, 154], [92, 26, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151, 44], []]
 b := ![[], [152, 158, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [56, 44, 122, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-115502, -43298, 182450, 251789, 48249]
  a := ![6, 6, 4, 7, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-290430, -74859, -42501, 251789, 48249]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -1, -3, -2, -2]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![3, -1, -3, -2, -2]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![86, 179, 1, 0, 0], ![86, 132, 0, 1, 0], ![55, 143, 0, 0, 1]] where
  M :=![![![3, -1, -3, -2, -2], ![0, 0, -3, -10, -6], ![-12, -15, 2, -30, -42], ![18, 13, -39, -17, -24], ![-11, -11, 19, -13, -3]]]
  hmulB := by decide  
  f := ![![![-27, -197, -17, 68, 106]], ![![-114, -158, -15, 64, 90]], ![![-126, -251, -23, 96, 140]], ![![-96, -209, -19, 79, 116]], ![![-98, -184, -17, 71, 103]]]
  g := ![![![3, 6, -3, -2, -2], ![8, 15, -3, -10, -6], ![26, 53, 2, -30, -42], ![34, 70, -39, -17, -24], ![-2, -7, 19, -13, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [24, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 180], [0, 1]]
 g := ![![[21, 12], [168], [19, 11], [136], [51, 14], [70, 73], [1]], ![[127, 169], [168], [86, 170], [136], [54, 167], [21, 108], [1]]]
 h' := ![![[39, 180], [98, 115], [87, 118], [33, 98], [43, 91], [130, 106], [157, 39], [0, 1]], ![[0, 1], [58, 66], [164, 63], [54, 83], [153, 90], [101, 75], [49, 142], [39, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [77, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [24, 142, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-107, -564, 43, -266, -35]
  a := ![2, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![116, 176, 43, -266, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-27, -197, -17, 68, 106]] ![![3, -1, -3, -2, -2]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123, -217, 65, 290, 338]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-123, -217, 65, 290, 338]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![143, 38, 41, 1, 0], ![12, 34, 30, 0, 1]] where
  M :=![![![-123, -217, 65, 290, 338], ![-144, -202, 217, 662, 726], ![-192, -119, 652, 1694, 1794], ![-78, 181, 829, 1965, 2028], ![77, 173, 51, 27, 3]]]
  hmulB := by decide  
  f := ![![![-111, 73, 5, -12, -38]], ![![78, -28, -17, 12, 42]], ![![-90, -29, 74, -40, -54]], ![![-87, 43, 16, -15, -32]], ![![-7, -5, 9, -5, -3]]]
  g := ![![![-239, -119, -115, 290, 338], ![-542, -262, -255, 662, 726], ![-1382, -657, -642, 1694, 1794], ![-1599, -751, -736, 1965, 2028], ![-20, -5, -6, 27, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [111, 142, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 94, 161], [41, 96, 30], [0, 1]]
 g := ![![[185, 78, 4], [76, 8, 134], [158, 177, 10], [108, 87, 97], [108, 15, 67], [51, 134, 1], []], ![[137, 101, 145, 71], [57, 149, 116, 7], [137, 170, 91, 42], [158, 55, 156, 119], [144, 174, 53, 161], [55, 152, 115, 88], [169, 136]], ![[40, 102], [161, 60, 179, 150], [185, 39, 112, 5], [118, 10, 7, 4], [143, 24, 131, 45], [58, 148, 146, 163], [109, 136]]]
 h' := ![![[93, 94, 161], [159, 172, 2], [34, 52, 158], [45, 143, 34], [45, 175, 111], [69, 40, 110], [0, 0, 1], [0, 1]], ![[41, 96, 30], [137, 70, 189], [48, 49, 47], [34, 109, 120], [0, 83, 58], [62, 26, 1], [13, 164, 96], [93, 94, 161]], ![[0, 1], [127, 140], [59, 90, 177], [80, 130, 37], [69, 124, 22], [10, 125, 80], [87, 27, 94], [41, 96, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 182], []]
 b := ![[], [139, 147, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [111, 142, 57, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![546995, 478952, -522632, 233220, 684880]
  a := ![10, 6, 0, 2, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-214775, -165808, -160372, 233220, 684880]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, 73, 5, -12, -38]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-111, 73, 5, -12, -38]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![155, 109, 1, 0, 0], ![52, 154, 0, 1, 0], ![27, 4, 0, 0, 1]] where
  M :=![![![-111, 73, 5, -12, -38], ![78, -28, -17, 12, 42], ![-90, -29, 74, -40, -54], ![-18, 27, -47, 35, -60], ![43, -9, 17, -19, 75]]]
  hmulB := by decide  
  f := ![![![-123, -217, 65, 290, 338]], ![![-144, -202, 217, 662, 726]], ![![-183, -292, 180, 622, 698]], ![![-150, -221, 197, 623, 688]], ![![-20, -34, 14, 55, 63]]]
  g := ![![![4, 8, 5, -12, -38], ![5, -1, -17, 12, 42], ![-42, -9, 74, -40, -54], ![37, 0, -47, 35, -60], ![-19, 4, 17, -19, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [122, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 190], [0, 1]]
 g := ![![[93, 77], [181, 59], [71, 118], [105, 121], [51, 169], [27, 8], [1]], ![[85, 114], [31, 132], [153, 73], [147, 70], [26, 22], [175, 183], [1]]]
 h' := ![![[114, 190], [74, 162], [124, 170], [178, 140], [81, 11], [144, 178], [69, 114], [0, 1]], ![[0, 1], [15, 29], [22, 21], [94, 51], [189, 180], [190, 13], [77, 77], [114, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [69, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [122, 77, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51, -106, 662, 189, 538]
  a := ![6, 6, -3, 5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-665, -542, 662, 189, 538]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-123, -217, 65, 290, 338]] ![![-111, 73, 5, -12, -38]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81, -142, 64, 248, 284]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-81, -142, 64, 248, 284]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![120, 96, 41, 183, 1]] where
  M :=![![![-81, -142, 64, 248, 284], ![-108, -125, 214, 588, 636], ![-144, -38, 607, 1556, 1620], ![-42, 198, 748, 1837, 1920], ![26, 98, 70, 30, -3]]]
  hmulB := by decide  
  f := ![![![63, -42, -4, 8, 20]], ![![-36, 23, 2, -4, -12]], ![![24, -10, -5, 4, 12]], ![![6, -14, 8, -3, 0]], ![![32, -30, 5, 1, 9]]]
  g := ![![![-177, -142, -60, -268, 284], ![-396, -317, -134, -600, 636], ![-1008, -806, -341, -1528, 1620], ![-1194, -954, -404, -1811, 1920], ![2, 2, 1, 3, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [167, 2, 105, 90, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 34, 129, 82], [182, 148, 51, 94], [27, 10, 13, 17], [0, 1]]
 g := ![![[85, 82, 137, 95], [58, 64, 161], [79, 78, 54], [59, 153, 32], [96, 43, 130], [82, 103, 1], []], ![[9, 191, 118, 57, 131, 183], [40, 17, 190], [31, 44, 143], [19, 126, 28], [134, 56, 48], [157, 148, 67], [101, 91, 136, 166, 44, 160]], ![[21, 80, 160, 68, 44, 123], [186, 163, 95], [192, 138, 184], [34, 172, 18], [153, 58, 157], [73, 10, 2], [138, 121, 85, 192, 143, 105]], ![[127, 155, 8, 88, 170, 160], [27, 120, 101], [13, 11, 7], [95, 52, 145], [11, 55, 165], [165, 41, 24], [174, 177, 152, 12, 70, 88]]]
 h' := ![![[87, 34, 129, 82], [141, 5, 163, 45], [62, 179, 192, 57], [175, 181, 12, 61], [68, 51, 34, 178], [9, 5, 88, 138], [0, 0, 0, 1], [0, 1]], ![[182, 148, 51, 94], [19, 35, 127, 173], [152, 44, 146, 169], [120, 97, 29, 23], [28, 99, 118, 75], [37, 87, 108, 56], [104, 79, 182, 35], [87, 34, 129, 82]], ![[27, 10, 13, 17], [39, 177, 91, 75], [118, 188, 159, 45], [181, 190, 1, 50], [164, 66, 19, 37], [168, 15, 152, 100], [134, 45, 154, 52], [182, 148, 51, 94]], ![[0, 1], [144, 169, 5, 93], [139, 168, 82, 115], [90, 111, 151, 59], [69, 170, 22, 96], [13, 86, 38, 92], [82, 69, 50, 105], [27, 10, 13, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [102, 183, 175], []]
 b := ![[], [], [22, 73, 4, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [167, 2, 105, 90, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1205175, 1591776, -602278, 3932352, 3847438]
  a := ![3, 4, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2385945, -1905504, -820452, -3627714, 3847438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, -42, -4, 8, 20]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![63, -42, -4, 8, 20]] 
 ![![193, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![121, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![63, -42, -4, 8, 20], ![-36, 23, 2, -4, -12], ![24, -10, -5, 4, 12], ![6, -14, 8, -3, 0], ![-10, 14, -6, 2, -3]]]
  hmulB := by decide  
  f := ![![![-81, -142, 64, 248, 284]], ![![-27, -47, 22, 84, 96]], ![![-36, -62, 31, 116, 132]], ![![-51, -88, 44, 165, 188]], ![![-7, -12, 6, 22, 25]]]
  g := ![![![9, -42, -4, 8, 20], ![-5, 23, 2, -4, -12], ![2, -10, -5, 4, 12], ![3, -14, 8, -3, 0], ![-3, 14, -6, 2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-81, -142, 64, 248, 284]] ![![63, -42, -4, 8, 20]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1123, 128, 728, -502, -240]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-1123, 128, 728, -502, -240]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![104, 52, 148, 30, 1]] where
  M :=![![![-1123, 128, 728, -502, -240], ![-786, -1181, 412, 190, -2292], ![7446, 7072, -8437, 3686, 8016], ![-6102, -6400, 11668, -7011, 180], ![2892, 3416, -7856, 5244, -3253]]]
  hmulB := by decide  
  f := ![![![-323, -704, -144, 54, 168]], ![![-342, -809, -308, -294, -180]], ![![-342, -992, -761, -1318, -1224]], ![![30, -288, -860, -1979, -2028]], ![![-512, -1372, -860, -1342, -1189]]]
  g := ![![![121, 64, 184, 34, -240], ![1206, 599, 1724, 350, -2292], ![-4194, -2080, -6065, -1202, 8016], ![-126, -80, -76, -63, 180], ![1732, 876, 2404, 522, -3253]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [104, 62, 112, 159, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 117, 176, 47], [145, 16, 43, 51], [44, 63, 175, 99], [0, 1]]
 g := ![![[117, 29, 23, 51], [83, 112, 9], [58, 195, 164, 26], [16, 62, 146], [43, 27, 9], [150, 38, 1], []], ![[104, 181, 38, 187, 62, 64], [88, 3, 64], [162, 72, 106, 171, 91, 163], [96, 187, 33], [171, 140, 53], [57, 68, 10], [132, 43, 111, 24, 67, 4]], ![[115, 116, 64, 90, 97, 54], [140, 90, 173], [142, 7, 148, 196, 5, 64], [155, 162, 168], [148, 71, 144], [140, 182, 24], [40, 101, 178, 79, 137, 70]], ![[27, 132, 16, 189, 38, 87], [61, 1, 188], [183, 196, 42, 89, 92, 45], [32, 33, 96], [92, 160, 163], [178, 0, 133], [6, 65, 45, 165, 136, 74]]]
 h' := ![![[46, 117, 176, 47], [145, 101, 124, 144], [75, 1, 93, 3], [146, 34, 19, 82], [49, 24, 56, 46], [160, 144, 46, 3], [0, 0, 0, 1], [0, 1]], ![[145, 16, 43, 51], [148, 89, 144, 188], [108, 132, 156, 8], [82, 157, 50, 148], [120, 40, 32, 128], [78, 58, 56, 29], [80, 175, 75, 124], [46, 117, 176, 47]], ![[44, 63, 175, 99], [99, 73, 38, 181], [9, 76, 67, 31], [168, 121, 37, 186], [79, 157, 31, 103], [156, 58, 13, 12], [27, 184, 83, 157], [145, 16, 43, 51]], ![[0, 1], [182, 131, 88, 78], [5, 185, 78, 155], [55, 82, 91, 175], [25, 173, 78, 117], [48, 134, 82, 153], [47, 35, 39, 112], [44, 63, 175, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [158, 11, 17], []]
 b := ![[], [], [47, 8, 99, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [104, 62, 112, 159, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1748578186, -1614763828, 2159514668, -977365678, -1513000668]
  a := ![-16, -14, -1, -14, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![789865438, 391173964, 1147632556, 225444946, -1513000668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-323, -704, -144, 54, 168]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-323, -704, -144, 54, 168]] 
 ![![197, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![191, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![158, 0, 0, 0, 1]] where
  M :=![![![-323, -704, -144, 54, 168], ![-342, -809, -308, -294, -180], ![-342, -992, -761, -1318, -1224], ![30, -288, -860, -1979, -2028], ![228, 456, 0, -268, -353]]]
  hmulB := by decide  
  f := ![![![-1123, 128, 728, -502, -240]], ![![-118, 7, 76, -50, -36]], ![![-1051, 160, 663, -468, -192]], ![![-316, 0, 244, -163, -60]], ![![-886, 120, 544, -376, -209]]]
  g := ![![![61, -704, -144, 54, 168], ![598, -809, -308, -294, -180], ![2153, -992, -761, -1318, -1224], ![2992, -288, -860, -1979, -2028], ![306, 456, 0, -268, -353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-1123, 128, 728, -502, -240]] ![![-323, -704, -144, 54, 168]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB402I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB402I4 : PrimesBelowBoundCertificateInterval O 151 197 402 where
  m := 9
  g := ![3, 3, 1, 2, 1, 2, 2, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB402I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
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
    · exact ![3869893, 157, 157]
    · exact ![26569, 26569, 163]
    · exact ![129891985607]
    · exact ![895745041, 173]
    · exact ![183765996899]
    · exact ![5929741, 32761]
    · exact ![6967871, 36481]
    · exact ![1387488001, 193]
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
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I157N2, I163N2, I173N1, I193N1, I197N1]
  Il := ![[I157N1, I157N2], [I163N2], [], [I173N1], [], [], [], [I193N1], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
