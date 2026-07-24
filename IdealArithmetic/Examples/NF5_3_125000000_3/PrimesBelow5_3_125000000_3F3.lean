
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -2, -4, -2, -12]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![7, -2, -4, -2, -12]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![51, 9, 1, 0, 0], ![38, 39, 0, 1, 0], ![92, 62, 0, 0, 1]] where
  M :=![![![7, -2, -4, -2, -12], ![0, -7, 10, 8, 40], ![-32, 18, 1, -12, -32], ![80, 38, -100, -35, -220], ![0, -22, 26, 16, 79]]]
  hmulB := by decide  
  f := ![![![-227, -170, 72, 50, 220]], ![![-320, -225, 90, 64, 280]], ![![-139, -103, 43, 30, 132]], ![![-198, -143, 58, 41, 180]], ![![-380, -276, 114, 80, 351]]]
  g := ![![![13, 8, -4, -2, -12], ![-42, -27, 10, 8, 40], ![31, 23, 1, -12, -32], ![250, 149, -100, -35, -220], ![-86, -54, 26, 16, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [19, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 106], [0, 1]]
 g := ![![[56, 62], [21, 62], [102], [71, 4], [75], [6, 1]], ![[0, 45], [72, 45], [102], [95, 103], [75], [12, 106]]]
 h' := ![![[6, 106], [29, 13], [40, 13], [42, 40], [15, 105], [100, 17], [0, 1]], ![[0, 1], [0, 94], [11, 94], [68, 67], [3, 2], [95, 90], [6, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [48, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [19, 101, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-557826, -339260, 666455, 347933, 1294375]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1559355, -936056, 666455, 347933, 1294375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 2, -14, -4, -32]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-23, 2, -14, -4, -32]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![41, 3, 1, 0, 0], ![99, 70, 0, 1, 0], ![54, 30, 0, 0, 1]] where
  M :=![![![-23, 2, -14, -4, -32], ![-32, -89, 82, 36, 208], ![-32, 198, -249, -92, -592], ![-64, -406, 474, 181, 1136], ![16, -10, 10, 4, 25]]]
  hmulB := by decide  
  f := ![![![-77, -38, 82, 44, 160]], ![![-416, -191, 426, 228, 784]], ![![-63, -31, 67, 36, 128]], ![![-405, -190, 420, 225, 784]], ![![-138, -64, 142, 76, 265]]]
  g := ![![![25, 12, -14, -4, -32], ![-170, -85, 82, 36, 208], ![479, 235, -249, -92, -592], ![-923, -454, 474, 181, 1136], ![-20, -10, 10, 4, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [88, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 106], [0, 1]]
 g := ![![[82, 62], [0, 100], [89], [0, 83], [40], [60, 1]], ![[57, 45], [8, 7], [89], [58, 24], [40], [13, 106]]]
 h' := ![![[60, 106], [0, 94], [86, 97], [0, 93], [96, 61], [70, 88], [0, 1]], ![[0, 1], [76, 13], [21, 10], [16, 14], [11, 46], [0, 19], [60, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [41, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [88, 47, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108288020, -72530404, 137266558, 70399636, 271029174]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-255526694, -126571774, 137266558, 70399636, 271029174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 49, -25, -20, -92]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-39, 49, -25, -20, -92]] 
 ![![107, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![105, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![-39, 49, -25, -20, -92], ![112, -52, -27, -2, -48], ![-144, -69, 212, 106, 616], ![-96, 285, -269, -171, -876], ![112, -33, -55, -18, -135]]]
  hmulB := by decide  
  f := ![![![3, -429, 507, 188, 1244]], ![![7, -363, 428, 158, 1052]], ![![6, -339, 396, 146, 976]], ![![49, -290, 326, 113, 824]], ![![-7, -262, 314, 118, 765]]]
  g := ![![![48, 49, -25, -20, -92], ![96, -52, -27, -2, -48], ![-557, -69, 212, 106, 616], ![622, 285, -269, -171, -876], ![166, -33, -55, -18, -135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![7, -2, -4, -2, -12]] ![![-23, 2, -14, -4, -32]]
  ![![-33, 332, -334, -142, -844]] where
 M := ![![![-33, 332, -334, -142, -844]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-33, 332, -334, -142, -844]] ![![-39, 49, -25, -20, -92]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![5671, -8453, 5671, 4066, 19688]]]
 hmul := by decide  
 g := ![![![![53, -79, 53, 38, 184]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2217, 1611, -669, -470, -2044]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![2217, 1611, -669, -470, -2044]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![84, 55, 0, 1, 0], ![91, 28, 60, 0, 1]] where
  M :=![![![2217, 1611, -669, -470, -2044], ![3104, 2302, -1001, -682, -3016], ![4304, 2997, -1138, -850, -3576], ![1496, 1355, -785, -445, -2184], ![-852, -615, 251, 178, 769]]]
  hmulB := by decide  
  f := ![![![-11, 15, -7, -6, -20]], ![![64, 16, -61, -30, -136]], ![![176, 29, -112, -58, -104]], ![![28, 23, -42, -23, -96]], ![![103, 32, -82, -44, -107]]]
  g := ![![![2089, 777, 1119, -470, -2044], ![3072, 1140, 1651, -682, -3016], ![3680, 1375, 1958, -850, -3576], ![2180, 798, 1195, -445, -2184], ![-787, -293, -421, 178, 769]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [90, 27, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 33, 108], [11, 75, 1], [0, 1]]
 g := ![![[52, 16, 31], [66, 108], [53, 34, 43], [12, 31, 28], [64, 106], [1]], ![[22, 66, 69, 75], [4, 45], [99, 42, 9, 43], [15, 72, 74, 80], [22, 74], [102, 92, 81, 108]], ![[28, 78, 102, 25], [108, 28], [47, 68, 91, 105], [29, 26, 27, 43], [78, 48], [88, 0, 25, 1]]]
 h' := ![![[7, 33, 108], [77, 75, 24], [26, 78, 76], [10, 32, 77], [51, 23, 30], [19, 82, 18], [0, 1]], ![[11, 75, 1], [55, 106, 90], [57, 68, 63], [55, 0, 75], [46, 5, 47], [101, 30, 69], [7, 33, 108]], ![[0, 1], [81, 37, 104], [10, 72, 79], [76, 77, 66], [68, 81, 32], [60, 106, 22], [11, 75, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 81], []]
 b := ![[], [34, 45, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [90, 27, 91, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1560056861, 799061539, -1702787919, -908167832, -3225268937]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3406840624, 1294090115, 1759755489, -908167832, -3225268937]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 0, 0, -2]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-1, 0, 0, 0, -2]] 
 ![![109, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 0, 0, -2], ![-8, -9, 14, 8, 32], ![-64, -18, 55, 28, 96], ![-140, -74, 152, 83, 280], ![46, 16, -42, -22, -73]]]
  hmulB := by decide  
  f := ![![![-289, -256, 140, 84, 402]], ![![-17, -13, 6, 4, 18]], ![![-228, -206, 115, 68, 328]], ![![-160, -134, 68, 43, 200]], ![![-145, -128, 70, 42, 201]]]
  g := ![![![1, 0, 0, 0, -2], ![-31, -9, 14, 8, 32], ![-106, -18, 55, 28, 96], ![-302, -74, 152, 83, 280], ![81, 16, -42, -22, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 3, -3, -2, -10]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-1, 3, -3, -2, -10]] 
 ![![109, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-1, 3, -3, -2, -10], ![8, -6, 1, 2, 8], ![-16, 3, 10, 2, 24], ![20, 29, -47, -23, -120], ![6, -9, 5, 4, 15]]]
  hmulB := by decide  
  f := ![![![-513, -381, 167, 114, 506]], ![![-496, -368, 161, 110, 488]], ![![-404, -301, 132, 90, 400]], ![![-233, -172, 74, 51, 226]], ![![-135, -100, 44, 30, 133]]]
  g := ![![![3, 3, -3, -2, -10], ![2, -6, 1, 2, 8], ![-18, 3, 10, 2, 24], ![51, 29, -47, -23, -120], ![-1, -9, 5, 4, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![2217, 1611, -669, -470, -2044]] ![![-1, 0, 0, 0, -2]]
  ![![-513, -381, 167, 114, 506]] where
 M := ![![![-513, -381, 167, 114, 506]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-513, -381, 167, 114, 506]] ![![-1, 3, -3, -2, -10]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![405, 233, -45, -56, -186]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![405, 233, -45, -56, -186]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![109, 3, 13, 89, 1]] where
  M :=![![![405, 233, -45, -56, -186], ![600, 680, -481, -242, -1280], ![688, -403, 928, 286, 2088], ![444, 1927, -2121, -839, -5196], ![-150, -57, -21, 4, -19]]]
  hmulB := by decide  
  f := ![![![1, 5, -7, -4, -22]], ![![8, -18, 15, 10, 48]], ![![-48, 25, 6, -2, -8]], ![![4, -9, -3, 1, -36]], ![![-1, 0, -8, -3, -49]]]
  g := ![![![183, 7, 21, 146, -186], ![1240, 40, 143, 1006, -1280], ![-2008, -59, -232, -1642, 2088], ![5016, 155, 579, 4085, -5196], ![17, 0, 2, 15, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [27, 99, 63, 45, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 36, 89, 42], [37, 17, 13, 75], [60, 59, 11, 109], [0, 1]]
 g := ![![[22, 36, 90, 18], [69, 30, 50], [92, 0, 13], [64, 26, 85], [100, 41, 68, 1], []], ![[8, 45, 61, 39, 48, 21], [24, 19, 44], [64, 104, 52], [74, 10, 11], [19, 74, 12, 86, 23, 84], [24, 42, 27, 12, 109, 73]], ![[101, 46, 105, 25, 7, 76], [83, 70, 28], [11, 79, 13], [72, 89, 36], [111, 31, 45, 97, 68, 29], [21, 95, 109, 21, 6, 46]], ![[48, 55, 77, 46, 77, 72], [80, 27, 106], [64], [96, 3, 111], [21, 3, 103, 73, 105, 26], [4, 29, 91, 82, 18, 49]]]
 h' := ![![[84, 36, 89, 42], [94, 80, 96, 40], [6, 69, 51, 29], [111, 107, 98, 37], [12, 67, 9, 57], [0, 0, 0, 1], [0, 1]], ![[37, 17, 13, 75], [23, 79, 25, 82], [28, 53, 22, 48], [93, 78, 69, 39], [31, 29, 27, 24], [49, 82, 80, 62], [84, 36, 89, 42]], ![[60, 59, 11, 109], [82, 85, 42, 26], [17, 107, 51, 64], [38, 78, 67, 37], [20, 34, 20, 6], [27, 87, 44, 79], [37, 17, 13, 75]], ![[0, 1], [98, 95, 63, 78], [87, 110, 102, 85], [32, 76, 105], [5, 96, 57, 26], [62, 57, 102, 84], [60, 59, 11, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [54, 64, 1], []]
 b := ![[], [], [95, 9, 105, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [27, 99, 63, 45, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8227381855354482, -4084279951071215, 8832692661061652, 4736037565316689, 16641898859236111]
  a := ![-995, -783, 1516, 663, 3151]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16125613783292837, -477964394059996, -1836389314239007, -13065424432802630, 16641898859236111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -5, 7, 4, 22]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-1, -5, 7, 4, 22]] 
 ![![113, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![96, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![-1, -5, 7, 4, 22], ![-8, 18, -15, -10, -48], ![48, -25, -6, 2, 8], ![-4, 9, 3, -1, 36], ![-22, 15, -3, -4, -25]]]
  hmulB := by decide  
  f := ![![![-405, -233, 45, 56, 186]], ![![-120, -72, 17, 18, 64]], ![![-386, -215, 34, 50, 156]], ![![-348, -215, 57, 55, 204]], ![![-375, -216, 42, 52, 173]]]
  g := ![![![-29, -5, 7, 4, 22], ![62, 18, -15, -10, -48], ![4, -25, -6, 2, 8], ![-38, 9, 3, -1, 36], ![25, 15, -3, -4, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![405, 233, -45, -56, -186]] ![![-1, -5, 7, 4, 22]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0, 0, 0]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]] where
  M :=![![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [40, 10, 61, 52, 86, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 90, 126, 111, 30], [72, 26, 56, 32, 39], [113, 55, 13, 42, 124], [0, 82, 59, 69, 61], [0, 1]]
 g := ![![[29, 2, 9, 113, 104], [42, 58, 26, 0, 32], [91, 101, 47, 43, 120], [84, 121, 103, 119, 50], [105, 41, 1], []], ![[81, 58, 69, 17, 45, 4, 100, 49], [113, 57, 39, 29, 30, 17, 19, 21], [15, 92, 43, 109, 110, 33, 125, 79], [17, 94, 104, 104, 77, 65, 89, 82], [23, 62, 73, 109, 56, 124, 12, 31], [38, 92, 28, 35, 77, 68, 48, 76]], ![[6, 46, 91, 55, 76, 105, 121, 59], [126, 25, 11, 22, 35, 20, 29, 75], [90, 6, 90, 64, 103, 3, 26, 33], [32, 120, 96, 23, 8, 80, 23, 118], [64, 65, 47, 28, 119, 107, 83, 39], [36, 3, 15, 78, 79, 88, 122, 10]], ![[57, 89, 44, 100, 29, 72, 51, 44], [81, 59, 112, 32, 125, 13, 41, 1], [3, 27, 125, 94, 86, 96, 122, 38], [29, 21, 46, 71, 94, 58, 92, 49], [0, 46, 67, 50, 48, 48, 35, 73], [12, 20, 93, 14, 28, 67, 27, 100]], ![[0, 69, 111, 65, 78, 78, 110, 16], [118, 30, 36, 29, 57, 87, 30, 25], [101, 13, 43, 73, 34, 29, 72, 21], [57, 112, 117, 87, 91, 16, 113, 15], [105, 115, 76, 14, 91, 34, 6, 18], [107, 81, 97, 65, 35, 22, 34, 32]]]
 h' := ![![[110, 90, 126, 111, 30], [98, 125, 11, 35, 55], [43, 65, 74, 42, 63], [69, 116, 120, 81, 82], [118, 104, 3, 30, 80], [0, 0, 0, 1], [0, 1]], ![[72, 26, 56, 32, 39], [55, 84, 105, 3, 37], [35, 107, 13, 21, 78], [0, 70, 53, 91, 117], [77, 124, 26, 102, 69], [44, 56, 13, 30, 94], [110, 90, 126, 111, 30]], ![[113, 55, 13, 42, 124], [7, 26, 81, 126, 73], [91, 70, 22, 117, 101], [42, 36, 62, 14, 98], [6, 9, 12, 13, 25], [79, 12, 7, 98, 126], [72, 26, 56, 32, 39]], ![[0, 82, 59, 69, 61], [33, 125, 55, 120, 109], [45, 114, 80, 36, 114], [71, 91, 47, 88, 96], [41, 35, 89, 9, 91], [78, 51, 21, 42, 48], [113, 55, 13, 42, 124]], ![[0, 1], [106, 21, 2, 97, 107], [24, 25, 65, 38, 25], [6, 68, 99, 107, 115], [118, 109, 124, 100, 116], [38, 8, 86, 83, 113], [0, 82, 59, 69, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 45, 110, 37], [], [], []]
 b := ![[], [120, 4, 26, 112, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [40, 10, 61, 52, 86, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![62118931802205674, 30617965679120033, -66441184061899893, -35666846750920752, -125034277730677446]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![489125447261462, 241086343930079, -523158929621259, -280841312999376, -984521871895098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 33038369407 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![102, 54, -3, -11, -29]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![102, 54, -3, -11, -29]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![102, 63, 1, 0, 0], ![62, 32, 0, 1, 0], ![116, 115, 0, 0, 1]] where
  M :=![![![102, 54, -3, -11, -29], ![148, 192, -139, -66, -372], ![96, -225, 420, 154, 936], ![-50, 571, -547, -187, -1450], ![17, 14, -67, -31, -122]]]
  hmulB := by decide  
  f := ![![![-564, 182, 253, 77, 605]], ![![572, 646, -1281, -682, -3828]], ![![-156, 429, -397, -254, -1298]], ![![-154, 267, -199, -137, -676]], ![![5, 736, -912, -537, -2860]]]
  g := ![![![34, 30, -3, -11, -29], ![470, 411, -139, -66, -372], ![-1228, -1063, 420, 154, 936], ![1798, 1586, -547, -187, -1450], ![175, 147, -67, -31, -122]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [115, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 130], [0, 1]]
 g := ![![[26, 35], [79, 60], [64], [114], [33], [5], [1]], ![[45, 96], [18, 71], [64], [114], [33], [5], [1]]]
 h' := ![![[23, 130], [85, 64], [118, 45], [81, 123], [109, 30], [74, 65], [16, 23], [0, 1]], ![[0, 1], [116, 67], [105, 86], [28, 8], [13, 101], [128, 66], [21, 108], [23, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [44, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [115, 108, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-180301, -336088, 472340, 208540, 1063544]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1409615, -1214308, 472340, 208540, 1063544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 24, -27, -11, -67]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![2, 24, -27, -11, -67]] 
 ![![131, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![118, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![2, 24, -27, -11, -67], ![-4, -84, 97, 38, 236], ![32, 315, -368, -142, -888], ![-70, -553, 661, 253, 1590], ![3, -18, 17, 7, 42]]]
  hmulB := by decide  
  f := ![![![-108, -36, 157, 81, 283]], ![![-40, -14, 56, 29, 101]], ![![-56, -25, 68, 36, 126]], ![![-206, -85, 257, 135, 472]], ![![-45, -10, 77, 39, 136]]]
  g := ![![![54, 24, -27, -11, -67], ![-190, -84, 97, 38, 236], ![715, 315, -368, -142, -888], ![-1283, -553, 661, 253, 1590], ![-33, -18, 17, 7, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24, -3, 24, 11, 67]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-24, -3, 24, 11, 67]] 
 ![![131, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-24, -3, 24, 11, 67], ![4, 59, -76, -44, -236], ![112, -180, 127, 88, 432], ![-194, 118, 20, -11, 6], ![-15, 75, -80, -49, -256]]]
  hmulB := by decide  
  f := ![![![1990, 1443, -616, -429, -1859]], ![![1070, 776, -332, -231, -1001]], ![![1340, 970, -417, -290, -1254]], ![![1192, 863, -380, -262, -1131]], ![![887, 644, -272, -190, -825]]]
  g := ![![![-51, -3, 24, 11, 67], ![151, 59, -76, -44, -236], ![-234, -180, 127, 88, 432], ![-73, 118, 20, -11, 6], ![157, 75, -80, -49, -256]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2

def I131N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 41, -17, -12, -52]] i)))

def SI131N3: IdealEqSpanCertificate' Table ![![57, 41, -17, -12, -52]] 
 ![![131, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![57, 41, -17, -12, -52], ![80, 60, -27, -18, -80], ![112, 75, -28, -22, -88], ![48, 45, -37, -19, -92], ![-24, -17, 9, 6, 25]]]
  hmulB := by decide  
  f := ![![![123, -157, 91, 68, 324]], ![![81, -105, 62, 46, 220]], ![![70, -83, 44, 34, 160]], ![![50, -65, 39, 29, 140]], ![![72, -95, 57, 42, 201]]]
  g := ![![![18, 41, -17, -12, -52], ![30, 60, -27, -18, -80], ![27, 75, -28, -22, -88], ![53, 45, -37, -19, -92], ![-11, -17, 9, 6, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N3 : Nat.card (O ⧸ I131N3) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N3)

lemma isPrimeI131N3 : Ideal.IsPrime I131N3 := prime_ideal_of_norm_prime hp131.out _ NI131N3
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![102, 54, -3, -11, -29]] ![![2, 24, -27, -11, -67]]
  ![![575, 3572, -4176, -1630, -10134]] where
 M := ![![![575, 3572, -4176, -1630, -10134]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![575, 3572, -4176, -1630, -10134]] ![![-24, -3, 24, 11, 67]]
  ![![1006, 8313, -9904, -3835, -23975]] where
 M := ![![![1006, 8313, -9904, -3835, -23975]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N2 : IdealMulLeCertificate' Table 
  ![![1006, 8313, -9904, -3835, -23975]] ![![57, 41, -17, -12, -52]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![4454, 32226, -38121, -14803, -92355]]]
 hmul := by decide  
 g := ![![![![34, 246, -291, -113, -705]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2, I131N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
    exact isPrimeI131N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1 ⊙ MulI131N2)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![748, -1071, 690, 503, 2417]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![748, -1071, 690, 503, 2417]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![77, 61, 67, 82, 1]] where
  M :=![![![748, -1071, 690, 503, 2417], ![-2404, 1549, 118, -240, -444], ![3984, 498, -3983, -1828, -11136], ![866, -5680, 6262, 3785, 19846], ![-2585, 1201, 706, 85, 1356]]]
  hmulB := by decide  
  f := ![![![-230, -167, 70, 49, 213]], ![![-324, -239, 106, 72, 316]], ![![-464, -322, 141, 100, 416]], ![![-206, -160, 130, 73, 314]], ![![-623, -453, 233, 152, 651]]]
  g := ![![![-1353, -1084, -1177, -1443, 2417], ![232, 209, 218, 264, -444], ![6288, 4962, 5417, 6652, -11136], ![-11148, -8878, -9660, -11851, 19846], ![-781, -595, -658, -811, 1356]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [102, 130, 81, 123, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 7, 12, 57], [21, 35, 9, 79], [115, 94, 116, 1], [0, 1]]
 g := ![![[20, 91, 112, 81], [65, 65, 120], [101, 81, 7], [42, 50, 113, 98], [11, 65, 59], [1], []], ![[38, 69, 0, 113, 48, 33], [127, 0, 112], [21, 93, 2], [95, 74, 77, 81, 85, 26], [9, 81, 30], [24, 124, 99], [128, 0, 98]], ![[37, 63, 108, 116, 77, 66], [49, 66, 107], [26, 50, 130], [77, 6, 12, 98, 10, 92], [16, 39, 123], [133, 46, 99], [9, 20, 76]], ![[48, 27, 86, 57, 25, 76], [89, 84, 4], [40, 54, 101], [49, 97, 112, 74, 62, 81], [38, 89, 98], [46, 91, 122], [19, 109, 1]]]
 h' := ![![[15, 7, 12, 57], [45, 36, 72, 128], [109, 53, 60, 95], [100, 49, 132, 125], [103, 102, 118, 80], [35, 7, 56, 14], [0, 0, 1], [0, 1]], ![[21, 35, 9, 79], [43, 63, 16, 120], [16, 17, 62, 89], [69, 40, 127, 31], [33, 110, 11, 28], [35, 105, 57, 116], [47, 10, 47, 109], [15, 7, 12, 57]], ![[115, 94, 116, 1], [63, 117, 69, 105], [102, 1, 22, 92], [98, 23, 23, 33], [14, 9, 81, 38], [106, 6, 50, 64], [71, 41, 112, 109], [21, 35, 9, 79]], ![[0, 1], [83, 58, 117, 58], [16, 66, 130, 135], [73, 25, 129, 85], [89, 53, 64, 128], [35, 19, 111, 80], [53, 86, 114, 56], [115, 94, 116, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [89, 24, 3], []]
 b := ![[], [], [44, 18, 111, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [102, 130, 81, 123, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-246614765924, -120723554444, 262838579831, 141250405670, 494066518900]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-279487129352, -220867016112, -239705242237, -294687621490, 494066518900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-230, -167, 70, 49, 213]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-230, -167, 70, 49, 213]] 
 ![![137, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![-230, -167, 70, 49, 213], ![-324, -239, 106, 72, 316], ![-464, -322, 141, 100, 416], ![-206, -160, 130, 73, 314], ![103, 71, -42, -27, -110]]]
  hmulB := by decide  
  f := ![![![748, -1071, 690, 503, 2417]], ![![452, -661, 434, 314, 1514]], ![![40, -12, -19, -6, -46]], ![![50, -104, 86, 57, 286]], ![![407, -601, 398, 287, 1386]]]
  g := ![![![-22, -167, 70, 49, 213], ![-38, -239, 106, 72, 316], ![-46, -322, 141, 100, 416], ![-86, -160, 130, 73, 314], ![21, 71, -42, -27, -110]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![748, -1071, 690, 503, 2417]] ![![-230, -167, 70, 49, 213]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![259, 238, -404, -194, -842]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![259, 238, -404, -194, -842]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![124, 5, 120, 59, 1]] where
  M :=![![![259, 238, -404, -194, -842], ![1288, 173, -852, -544, -1272], ![7968, 5684, -10507, -5320, -20992], ![21212, 7200, -19020, -10811, -33588], ![-6190, -3126, 6708, 3590, 12691]]]
  hmulB := by decide  
  f := ![![![541, 390, -164, -114, -498]], ![![744, 551, -228, -160, -696]], ![![1056, 772, -337, -232, -1024]], ![![364, 240, -92, -65, -276]], ![![1574, 1135, -484, -335, -1469]]]
  g := ![![![753, 32, 724, 356, -842], ![1144, 47, 1092, 536, -1272], ![18784, 796, 18047, 8872, -20992], ![30116, 1260, 28860, 14179, -33588], ![-11366, -479, -10908, -5361, 12691]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [46, 37, 88, 115, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 9, 96, 98], [129, 97, 90, 10], [58, 32, 92, 31], [0, 1]]
 g := ![![[67, 126, 133, 79], [82, 138, 4, 116], [128, 39, 51], [122, 9, 8, 89], [115, 9, 20], [1], []], ![[104, 105, 33, 62, 86, 61], [4, 24, 19, 76, 26, 97], [36, 36, 38], [79, 132, 21, 102, 120, 90], [131, 32, 44], [10, 136, 24], [61, 85, 13]], ![[65, 18, 91, 138, 133, 109], [55, 108, 46, 48, 114, 90], [8, 137, 29], [26, 118, 28, 0, 72, 123], [53, 15, 24], [127, 106, 9], [14, 30, 100]], ![[128, 132, 138, 28, 4, 49], [45, 109, 76, 69, 47, 25], [61, 135, 35], [67, 71, 12, 111, 20, 28], [46, 82, 125], [5, 42, 20], [125, 134, 127]]]
 h' := ![![[115, 9, 96, 98], [120, 100, 53, 45], [13, 50, 0, 33], [87, 49, 12, 107], [23, 125, 38, 111], [93, 102, 51, 24], [0, 0, 1], [0, 1]], ![[129, 97, 90, 10], [50, 123, 13, 61], [134, 138, 115, 94], [119, 40, 79, 49], [0, 19, 94, 25], [132, 4, 34, 34], [133, 73, 123, 118], [115, 9, 96, 98]], ![[58, 32, 92, 31], [1, 64, 4, 54], [17, 105, 131, 136], [61, 129, 38, 53], [65, 112, 52, 38], [1, 61, 76, 21], [12, 54, 111, 136], [129, 97, 90, 10]], ![[0, 1], [34, 130, 69, 118], [28, 124, 32, 15], [38, 60, 10, 69], [132, 22, 94, 104], [21, 111, 117, 60], [116, 12, 43, 24], [58, 32, 92, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [95, 39, 52], []]
 b := ![[], [], [6, 102, 126, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [46, 37, 88, 115, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-148001161469, -72563402405, 157863095726, 84817454525, 296814971439]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-265849335395, -11198836400, -255107435086, -125376013384, 296814971439]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-541, -390, 164, 114, 498]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-541, -390, 164, 114, 498]] 
 ![![139, 0, 0, 0, 0], ![119, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-541, -390, 164, 114, 498], ![-744, -551, 228, 160, 696], ![-1056, -772, 337, 232, 1024], ![-364, -240, 92, 65, 276], ![214, 150, -68, -46, -205]]]
  hmulB := by decide  
  f := ![![![-259, -238, 404, 194, 842]], ![![-231, -205, 352, 170, 730]], ![![-89, -70, 125, 62, 254]], ![![-229, -122, 256, 135, 490]], ![![-30, -46, 68, 30, 151]]]
  g := ![![![133, -390, 164, 114, 498], ![191, -551, 228, 160, 696], ![249, -772, 337, 232, 1024], ![93, -240, 92, 65, 276], ![-46, 150, -68, -46, -205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![259, 238, -404, -194, -842]] ![![-541, -390, 164, 114, 498]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] where
  M :=![![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [100, 101, 59, 147, 135, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 85, 125, 139, 47], [111, 130, 90, 135, 26], [130, 28, 51, 138, 51], [132, 54, 32, 35, 25], [0, 1]]
 g := ![![[17, 61, 125, 80, 110], [52, 83, 41, 80], [126, 67, 76, 109, 107], [130, 21, 34, 64], [146, 59, 49, 14, 1], [], []], ![[29, 7, 14, 42, 104, 89, 2, 119], [62, 33, 81, 123], [6, 28, 59, 118, 55, 128, 15, 17], [17, 23, 56, 53], [26, 53, 40, 134, 135, 104, 117, 76], [39, 75, 142, 76], [126, 98, 37, 123]], ![[137, 126, 58, 56, 31, 74, 103, 88], [89, 127, 120, 95], [107, 5, 118, 95, 86, 80, 101, 140], [55, 24, 8, 124], [42, 99, 69, 74, 105, 116, 45, 5], [136, 127, 13, 88], [130, 94, 94, 80]], ![[105, 80, 2, 148, 27, 88, 97, 89], [104, 98, 90, 95], [56, 38, 131, 9, 78, 120, 23, 101], [68, 130], [56, 57, 137, 29, 11, 72, 29, 126], [4, 118, 102, 107], [109, 99, 128, 68]], ![[119, 122, 39, 126, 10, 36, 46, 63], [118, 120, 96, 148], [127, 33, 100, 81, 8, 118, 4, 76], [133, 19, 117, 143], [128, 115, 143, 0, 145, 41, 39, 113], [135, 24, 144, 47], [86, 138, 70, 29]]]
 h' := ![![[88, 85, 125, 139, 47], [68, 48, 25, 19, 40], [65, 139, 103, 58, 123], [116, 79, 9, 76, 133], [2, 65, 46, 147, 141], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[111, 130, 90, 135, 26], [19, 30, 114, 37, 47], [109, 44, 134, 19, 47], [135, 72, 19, 121, 71], [14, 13, 58, 91, 65], [119, 37, 13, 7, 33], [61, 33, 147, 9, 15], [88, 85, 125, 139, 47]], ![[130, 28, 51, 138, 51], [143, 20, 76, 4, 72], [38, 119, 83, 64, 86], [58, 28, 117, 95, 57], [94, 113, 128, 34, 71], [143, 54, 20, 53, 79], [66, 72, 35, 45, 104], [111, 130, 90, 135, 26]], ![[132, 54, 32, 35, 25], [133, 76, 103, 73, 113], [38, 127, 95, 121, 86], [8, 117, 90, 40, 34], [38, 112, 46, 117], [8, 76, 45, 101, 13], [40, 79, 12, 124, 16], [130, 28, 51, 138, 51]], ![[0, 1], [94, 124, 129, 16, 26], [47, 18, 32, 36, 105], [28, 2, 63, 115, 3], [31, 144, 20, 58, 21], [105, 131, 71, 137, 23], [33, 114, 103, 120, 14], [132, 54, 32, 35, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 78, 20, 145], [], [], []]
 b := ![[], [72, 37, 13, 90, 73], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [100, 101, 59, 147, 135, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-540918681854193105, -265373595478644397, 577152649964731943, 310062559032195393, 1085283957321701604]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3630326723853645, -1781030842138553, 3873507717884107, 2080956772028157, 7283784948467796]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 73439775749 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1779, -608, 2256, 1102, 6482]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-1779, -608, 2256, 1102, 6482]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![148, 69, 42, 92, 1]] where
  M :=![![![-1779, -608, 2256, 1102, 6482], ![-520, 5467, -6310, -3784, -19960], ![10976, -14774, 8963, 6676, 31776], ![-16300, 7366, 4720, 711, 9460], ![-2186, 6790, -6542, -4134, -21267]]]
  hmulB := by decide  
  f := ![![![1919, 1400, -588, -410, -1790]], ![![2680, 1961, -830, -576, -2520]], ![![3744, 2714, -1135, -796, -3456]], ![![1300, 974, -460, -303, -1340]], ![![4934, 3613, -1550, -1070, -4679]]]
  g := ![![![-6365, -2966, -1788, -3942, 6482], ![19560, 9157, 5510, 12136, -19960], ![-31072, -14618, -8779, -19316, 31776], ![-9380, -4274, -2600, -5759, 9460], ![20830, 9763, 5872, 12930, -21267]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [124, 36, 37, 90, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 78, 30, 140], [58, 4, 35, 11], [107, 68, 86], [0, 1]]
 g := ![![[108, 40, 28, 38], [74, 35, 42, 58], [15, 65, 100, 39], [57, 37, 81], [112, 149, 44, 97], [1], []], ![[22, 125, 52, 130, 73, 3], [95, 7, 35, 40, 67, 130], [63, 42, 66, 139, 109, 12], [81, 25, 58], [142, 122, 127, 94, 43, 71], [56, 104, 34], [8, 77, 121]], ![[92, 22, 139, 92, 84, 17], [81, 150, 143, 23, 56, 55], [22, 127, 148, 85, 28, 44], [142, 35, 91], [88, 128, 81, 80, 21, 110], [41, 52, 45], [126, 148, 121]], ![[35, 38, 14, 48, 17], [113, 11, 102, 8, 36], [43, 116, 87, 136, 116], [94, 102, 88], [16, 96, 113, 92, 9], [17, 103, 10], [148]]]
 h' := ![![[47, 78, 30, 140], [35, 132, 25, 75], [103, 69, 31, 80], [45, 26, 3, 48], [4, 116, 4, 142], [27, 115, 114, 61], [0, 0, 1], [0, 1]], ![[58, 4, 35, 11], [74, 19, 19, 52], [131, 149, 76, 131], [13, 110, 0, 47], [98, 116, 38, 71], [83, 114, 147, 126], [9, 63, 43, 100], [47, 78, 30, 140]], ![[107, 68, 86], [90, 107, 138, 28], [9, 11, 76, 96], [31, 134, 60, 2], [24, 55, 136, 53], [136, 108, 88, 37], [122, 75, 71, 14], [58, 4, 35, 11]], ![[0, 1], [140, 44, 120, 147], [7, 73, 119, 146], [115, 32, 88, 54], [12, 15, 124, 36], [43, 116, 104, 78], [43, 13, 36, 37], [107, 68, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 63, 129], []]
 b := ![[], [], [56, 62, 113, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [124, 36, 37, 90, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5168276449134, -2598167319400, 5585273672316, 2988618610782, 10545481753400]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10370195867234, -4836002704000, -2896191787884, -6405269554318, 10545481753400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1919, 1400, -588, -410, -1790]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![1919, 1400, -588, -410, -1790]] 
 ![![151, 0, 0, 0, 0], ![121, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![105, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![1919, 1400, -588, -410, -1790], ![2680, 1961, -830, -576, -2520], ![3744, 2714, -1135, -796, -3456], ![1300, 974, -460, -303, -1340], ![-746, -542, 234, 162, 703]]]
  hmulB := by decide  
  f := ![![![-1779, -608, 2256, 1102, 6482]], ![![-1429, -451, 1766, 858, 5062]], ![![2, -122, 149, 88, 468]], ![![-1345, -374, 1600, 771, 4570]], ![![-1334, -406, 1630, 790, 4667]]]
  g := ![![![527, 1400, -588, -410, -1790], ![749, 1961, -830, -576, -2520], ![1012, 2714, -1135, -796, -3456], ![451, 974, -460, -303, -1340], ![-214, -542, 234, 162, 703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-1779, -608, 2256, 1102, 6482]] ![![1919, 1400, -588, -410, -1790]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB547I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB547I3 : PrimesBelowBoundCertificateInterval O 103 151 547 where
  m := 9
  g := ![3, 3, 2, 1, 4, 2, 2, 1, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB547I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2, I131N3]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
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
    · exact ![1295029, 109, 109]
    · exact ![163047361, 113]
    · exact ![33038369407]
    · exact ![17161, 131, 131, 131]
    · exact ![352275361, 137]
    · exact ![373301041, 139]
    · exact ![73439775749]
    · exact ![519885601, 151]
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
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
      exact NI131N3
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N2, I109N1, I109N2, I113N1, I131N1, I131N2, I131N3, I137N1, I139N1, I151N1]
  Il := ![[I107N2], [I109N1, I109N2], [I113N1], [], [I131N1, I131N2, I131N3], [I137N1], [I139N1], [], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
