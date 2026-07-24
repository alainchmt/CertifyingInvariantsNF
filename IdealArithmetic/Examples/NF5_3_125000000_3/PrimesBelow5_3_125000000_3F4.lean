
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2718, -1963, 898, 611, 2633]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-2718, -1963, 898, 611, 2633]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![154, 24, 71, 31, 1]] where
  M :=![![![-2718, -1963, 898, 611, 2633], ![-4132, -2897, 1602, 1040, 4308], ![-7728, -5058, 4387, 2612, 10112], ![-9054, -4812, 8294, 4539, 16206], ![3095, 1773, -2546, -1419, -5166]]]
  hmulB := by decide  
  f := ![![![-12, -63, 78, 29, 185]], ![![44, 255, -314, -120, -756]], ![![-144, -1014, 1227, 476, 2976]], ![![218, 1844, -2198, -857, -5342]], ![![-27, -117, 149, 56, 356]]]
  g := ![![![-2600, -415, -1185, -516, 2633], ![-4252, -677, -1938, -844, 4308], ![-9968, -1578, -4545, -1980, 10112], ![-15954, -2508, -7276, -3171, 16206], ![5087, 801, 2320, 1011, -5166]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [78, 35, 0, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 5, 10, 50], [39, 133, 28, 39], [128, 18, 119, 68], [0, 1]]
 g := ![![[135, 66, 107, 122], [29, 88, 39], [124, 94, 126, 147], [83, 91, 77, 147], [50, 71, 156, 1], [1], []], ![[143, 107, 153, 118, 156, 74], [140, 130, 57], [118, 152, 60, 82, 137, 128], [55, 64, 82, 104, 108, 5], [41, 81, 94, 91, 61, 50], [36, 111, 121], [59, 70, 145]], ![[117, 72, 110, 142, 133, 127], [141, 2, 30], [92, 76, 11, 88, 100, 30], [93, 40, 18, 108, 84, 118], [137, 59, 109, 17, 33, 144], [150, 7, 132], [133, 35, 108]], ![[140, 86, 134, 61, 149, 33], [93, 100, 64], [140, 23, 62, 116, 46, 4], [126, 43, 126, 4], [142, 86, 140, 9, 18, 82], [144, 71, 156], [25, 99, 71]]]
 h' := ![![[146, 5, 10, 50], [12, 65, 116, 114], [62, 59, 102, 143], [120, 42, 3, 124], [25, 52, 70, 33], [79, 122, 0, 156], [0, 0, 1], [0, 1]], ![[39, 133, 28, 39], [61, 149, 92, 23], [84, 82, 115, 123], [13, 11, 17, 33], [115, 140, 39, 96], [21, 4, 12, 1], [72, 58, 18, 146], [146, 5, 10, 50]], ![[128, 18, 119, 68], [6, 80, 1, 77], [93, 135, 126, 40], [35, 1, 88, 42], [108, 65, 6, 28], [28, 66, 51, 44], [96, 6, 19, 140], [39, 133, 28, 39]], ![[0, 1], [25, 20, 105, 100], [123, 38, 128, 8], [3, 103, 49, 115], [140, 57, 42], [15, 122, 94, 113], [147, 93, 119, 28], [128, 18, 119, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [82, 20, 155], []]
 b := ![[], [], [146, 137, 118, 149], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [78, 35, 0, 1, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10122272663951, -4986649958508, 10823699661914, 5810854689258, 20367143067016]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20042435063595, -3145210723356, -9141678077046, -3984525989734, 20367143067016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, -63, 78, 29, 185]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-12, -63, 78, 29, 185]] 
 ![![157, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![-12, -63, 78, 29, 185], ![44, 255, -314, -120, -756], ![-144, -1014, 1227, 476, 2976], ![218, 1844, -2198, -857, -5342], ![19, 43, -62, -23, -148]]]
  hmulB := by decide  
  f := ![![![-2718, -1963, 898, 611, 2633]], ![![-286, -206, 96, 65, 279]], ![![-1590, -1145, 537, 363, 1557]], ![![-1962, -1406, 682, 457, 1948]], ![![-1573, -1139, 510, 349, 1510]]]
  g := ![![![-167, -63, 78, 29, 185], ![681, 255, -314, -120, -756], ![-2677, -1014, 1227, 476, 2976], ![4802, 1844, -2198, -857, -5342], ![134, 43, -62, -23, -148]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-2718, -1963, 898, 611, 2633]] ![![-12, -63, 78, 29, 185]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, -79, 61, 42, 208]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![45, -79, 61, 42, 208]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![143, 110, 68, 1, 0], ![74, 160, 119, 0, 1]] where
  M :=![![![45, -79, 61, 42, 208], ![-176, 140, -23, -38, -136], ![368, -21, -276, -110, -712], ![-16, -403, 513, 287, 1584], ![-208, 123, 21, -14, -11]]]
  hmulB := by decide  
  f := ![![![79, 59, -27, -18, -80]], ![![112, 74, -29, -22, -88]], ![![176, 149, -102, -58, -264]], ![![219, 164, -86, -55, -240]], ![![274, 208, -115, -72, -315]]]
  g := ![![![-131, -233, -169, 42, 208], ![94, 160, 115, -38, -136], ![422, 773, 564, -110, -712], ![-971, -1751, -1273, 287, 1584], ![16, 21, 14, -14, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [91, 77, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 56, 2], [82, 106, 161], [0, 1]]
 g := ![![[30, 9, 22], [53, 138, 161], [96, 10], [24, 36], [39, 118], [56, 123, 1], []], ![[137, 78, 131, 79], [144, 61, 4, 82], [1, 26], [54, 150], [102, 77], [109, 87, 124, 141], [64, 4]], ![[45, 37, 82, 33], [151, 114, 43, 49], [116, 51], [22, 151], [63, 10], [28, 10, 88, 85], [68, 4]]]
 h' := ![![[41, 56, 2], [67, 23, 115], [157, 98, 145], [108, 57, 93], [93, 41, 157], [120, 143, 97], [0, 0, 1], [0, 1]], ![[82, 106, 161], [36, 6, 11], [20, 158, 81], [33, 32, 29], [63, 139, 98], [39, 92, 136], [95, 115, 106], [41, 56, 2]], ![[0, 1], [23, 134, 37], [12, 70, 100], [25, 74, 41], [76, 146, 71], [105, 91, 93], [47, 48, 56], [82, 106, 161]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 3], []]
 b := ![[], [135, 13, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [91, 77, 40, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6199914294301, 3246864746106, -6847545473638, -3638993154554, -13017108730412]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9140134855497, 15253211709282, 10979386061074, -3638993154554, -13017108730412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 1, 0, 4]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![1, -1, 1, 0, 4]] 
 ![![163, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![111, 0, 0, 1, 0], ![162, 0, 0, 0, 1]] where
  M :=![![![1, -1, 1, 0, 4], ![16, 18, -29, -14, -64], ![80, -3, -38, -26, -40], ![224, 179, -315, -159, -636], ![-64, -27, 63, 34, 113]]]
  hmulB := by decide  
  f := ![![![7683, 5645, -2375, -1656, -7236]], ![![4167, 3061, -1288, -898, -3924]], ![![4428, 3253, -1368, -954, -4168]], ![![5263, 3868, -1628, -1135, -4960]], ![![7618, 5597, -2355, -1642, -7175]]]
  g := ![![![-4, -1, 1, 0, 4], ![80, 18, -29, -14, -64], ![81, -3, -38, -26, -40], ![824, 179, -315, -159, -636], ![-157, -27, 63, 34, 113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -16, 19, 7, 45]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-2, -16, 19, 7, 45]] 
 ![![163, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![149, 0, 1, 0, 0], ![99, 0, 0, 1, 0], ![143, 0, 0, 0, 1]] where
  M :=![![![-2, -16, 19, 7, 45], ![12, 64, -79, -30, -188], ![-32, -249, 300, 114, 728], ![82, 475, -581, -229, -1398], ![-1, 6, -7, -1, -18]]]
  hmulB := by decide  
  f := ![![![-6264, -4588, 1943, 1351, 5915]], ![![-4012, -2938, 1244, 865, 3787]], ![![-5800, -4249, 1799, 1251, 5477]], ![![-3830, -2805, 1188, 826, 3617]], ![![-5481, -4014, 1700, 1182, 5175]]]
  g := ![![![-51, -16, 19, 7, 45], ![215, 64, -79, -30, -188], ![-825, -249, 300, 114, 728], ![1597, 475, -581, -229, -1398], ![19, 6, -7, -1, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![45, -79, 61, 42, 208]] ![![1, -1, 1, 0, 4]]
  ![![-243, 252, -108, -86, -412]] where
 M := ![![![-243, 252, -108, -86, -412]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-243, 252, -108, -86, -412]] ![![-2, -16, 19, 7, 45]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![326, 3586, -4075, -1467, -9291]]]
 hmul := by decide  
 g := ![![![![2, 22, -25, -9, -57]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-185, -134, 58, 40, 174]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-185, -134, 58, 40, 174]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![12, 166, 1, 0, 0], ![6, 6, 0, 1, 0], ![150, 98, 0, 0, 1]] where
  M :=![![![-185, -134, 58, 40, 174], ![-264, -191, 88, 60, 256], ![-416, -292, 177, 112, 464], ![-284, -160, 202, 115, 416], ![118, 74, -72, -42, -161]]]
  hmulB := by decide  
  f := ![![![-59, -6, 54, 20, 134]], ![![56, 151, -224, -108, -624]], ![![52, 146, -215, -104, -600]], ![![-2, 10, -10, -5, -28]], ![![-20, 84, -84, -46, -249]]]
  g := ![![![-163, -162, 58, 40, 174], ![-240, -241, 88, 60, 256], ![-436, -454, 177, 112, 464], ![-394, -450, 202, 115, 416], ![152, 168, -72, -42, -161]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [94, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 166], [0, 1]]
 g := ![![[33, 16], [35, 150], [148, 65], [19], [137], [42, 31], [1]], ![[0, 151], [164, 17], [87, 102], [19], [137], [72, 136], [1]]]
 h' := ![![[71, 166], [50, 4], [116, 145], [16, 137], [74, 55], [60, 53], [73, 71], [0, 1]], ![[0, 1], [0, 163], [57, 22], [57, 30], [138, 112], [149, 114], [104, 96], [71, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [115, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [94, 96, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-423408, -268116, 517567, 268899, 1011498]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-957918, -1119308, 517567, 268899, 1011498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, -33, 24, 13, 69]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![18, -33, 24, 13, 69]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![7, 15, 1, 0, 0], ![31, 142, 0, 1, 0], ![113, 45, 0, 0, 1]] where
  M :=![![![18, -33, 24, 13, 69], ![-36, 71, -48, -20, -116], ![16, -168, 163, 48, 336], ![114, 270, -372, -115, -806], ![-41, 13, 20, 9, 58]]]
  hmulB := by decide  
  f := ![![![108, 85, -8, -11, -65]], ![![4, 49, 144, 68, 204]], ![![0, 6, 19, 9, 27]], ![![6, 49, 140, 66, 197]], ![![79, 73, 28, 8, 1]]]
  g := ![![![-50, -32, 24, 13, 69], ![84, 53, -48, -20, -116], ![-243, -147, 163, 48, 336], ![583, 350, -372, -115, -806], ![-42, -25, 20, 9, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [34, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 166], [0, 1]]
 g := ![![[119, 89], [31, 96], [150, 141], [108], [87], [150, 108], [1]], ![[77, 78], [57, 71], [136, 26], [108], [87], [54, 59], [1]]]
 h' := ![![[129, 166], [115, 151], [77, 51], [58, 59], [132, 129], [77, 134], [133, 129], [0, 1]], ![[0, 1], [55, 16], [143, 116], [154, 108], [73, 38], [162, 33], [74, 38], [129, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [61, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [34, 38, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16486014, -11053270, 20917248, 10720416, 41312574]
  a := ![-995, -783, 1516, 663, 3151]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30919524, -22192676, 20917248, 10720416, 41312574]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, -2, -1, -5]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![2, 1, -2, -1, -5]] 
 ![![167, 0, 0, 0, 0], ![153, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![138, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![2, 1, -2, -1, -5], ![4, -1, 0, 0, 4], ![16, 20, -29, -16, -64], ![62, 18, -54, -29, -98], ![-15, -11, 20, 11, 42]]]
  hmulB := by decide  
  f := ![![![152, 91, -46, -25, -119]], ![![140, 84, -42, -23, -109]], ![![128, 78, -41, -22, -106]], ![![126, 72, -34, -19, -88]], ![![73, 44, -22, -12, -57]]]
  g := ![![![4, 1, -2, -1, -5], ![-1, -1, 0, 0, 4], ![50, 20, -29, -16, -64], ![100, 18, -54, -29, -98], ![-36, -11, 20, 11, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-185, -134, 58, 40, 174]] ![![18, -33, 24, 13, 69]]
  ![![-152, -91, 46, 25, 119]] where
 M := ![![![-152, -91, 46, 25, 119]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-152, -91, 46, 25, 119]] ![![2, 1, -2, -1, -5]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![172, 321, -488, -181, -1169]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![172, 321, -488, -181, -1169]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![70, 20, 79, 41, 1]] where
  M :=![![![172, 321, -488, -181, -1169], ![-332, -1553, 1988, 804, 4948], ![496, 6172, -7245, -2952, -18064], ![-538, -10682, 12180, 4865, 29862], ![-115, -453, 624, 291, 1716]]]
  hmulB := by decide  
  f := ![![![-546, -399, 168, 117, 511]], ![![-764, -557, 236, 164, 716]], ![![-1072, -780, 335, 232, 1008]], ![![-386, -278, 140, 93, 394]], ![![-889, -647, 281, 194, 842]]]
  g := ![![![474, 137, 531, 276, -1169], ![-2004, -581, -2248, -1168, 4948], ![7312, 2124, 8207, 4264, -18064], ![-12086, -3514, -13566, -7049, 29862], ![-695, -201, -780, -405, 1716]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [84, 0, 25, 102, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 70, 155, 128], [166, 113, 90, 169], [117, 162, 101, 49], [0, 1]]
 g := ![![[19, 22, 50, 73], [108, 95, 160], [130, 161, 19, 1], [137, 104, 84, 150], [105, 161, 1], [71, 1], []], ![[14, 103, 165, 101, 135, 11], [161, 2, 157], [172, 95, 113, 39, 51, 12], [169, 114, 162, 2, 144, 80], [93, 99, 135], [113, 111, 55, 26, 43, 145], [105, 75, 122]], ![[128, 91, 66, 93, 74, 116], [126, 11, 89], [59, 37, 132, 75, 69, 172], [110, 101, 154, 87, 49, 172], [153, 120, 9], [69, 33, 93, 160, 91, 159], [2, 70, 16]], ![[35, 41, 11, 27, 74, 150], [65, 44, 159], [17, 1, 89, 65, 92, 113], [149, 128, 108, 148, 5, 96], [156, 102, 21], [118, 28, 38, 60, 128, 64], [7, 103, 152]]]
 h' := ![![[134, 70, 155, 128], [19, 118, 55, 65], [152, 112, 49, 81], [83, 141, 26, 172], [153, 79, 136, 82], [91, 89, 128, 172], [0, 0, 1], [0, 1]], ![[166, 113, 90, 169], [120, 105, 50, 83], [91, 88, 135, 26], [56, 162, 46, 28], [136, 153, 94, 49], [110, 44, 108, 57], [140, 4, 5, 169], [134, 70, 155, 128]], ![[117, 162, 101, 49], [95, 23, 29, 12], [105, 63, 162, 98], [90, 118, 51, 86], [82, 35, 127, 87], [88, 27, 0, 3], [54, 150, 81, 104], [166, 113, 90, 169]], ![[0, 1], [131, 100, 39, 13], [125, 83, 0, 141], [84, 98, 50, 60], [11, 79, 162, 128], [113, 13, 110, 114], [126, 19, 86, 73], [117, 162, 101, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [34, 168, 120], []]
 b := ![[], [], [136, 40, 144, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [84, 0, 25, 102, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13593962106920, -6849947261100, 14708890156374, 7867657322012, 27782520849648]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11320060240360, -3251447192220, -12601793392866, -6538819060772, 27782520849648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![546, 399, -168, -117, -511]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![546, 399, -168, -117, -511]] 
 ![![173, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![150, 0, 1, 0, 0], ![154, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![546, 399, -168, -117, -511], ![764, 557, -236, -164, -716], ![1072, 780, -335, -232, -1008], ![386, 278, -140, -93, -394], ![-217, -157, 72, 49, 210]]]
  hmulB := by decide  
  f := ![![![-172, -321, 488, 181, 1169]], ![![-12, -17, 28, 10, 66]], ![![-152, -314, 465, 174, 1118]], ![![-150, -224, 364, 133, 868]], ![![-57, -105, 160, 59, 382]]]
  g := ![![![392, 399, -168, -117, -511], ![550, 557, -236, -164, -716], ![778, 780, -335, -232, -1008], ![316, 278, -140, -93, -394], ![-165, -157, 72, 49, 210]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![172, 321, -488, -181, -1169]] ![![546, 399, -168, -117, -511]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8043, -5889, 2491, 1728, 7566]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-8043, -5889, 2491, 1728, 7566]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![50, 150, 137, 1, 0], ![35, 127, 158, 0, 1]] where
  M :=![![![-8043, -5889, 2491, 1728, 7566], ![-11208, -8120, 3357, 2366, 10272], ![-15696, -11717, 5152, 3482, 15464], ![-5252, -3363, 1015, 897, 3468], ![3098, 2271, -967, -668, -2931]]]
  hmulB := by decide  
  f := ![![![-29, -15, 39, 20, 102]], ![![-72, 38, -9, -10, -112]], ![![-208, -339, 462, 270, 1032]], ![![-234, -234, 363, 207, 736]], ![![-239, -274, 407, 234, 847]]]
  g := ![![![-2007, -6849, -7987, 1728, 7566], ![-2732, -9316, -10859, 2366, 10272], ![-4084, -13955, -16286, 3482, 15464], ![-958, -3231, -3742, 897, 3468], ![777, 2652, 3093, -668, -2931]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [83, 51, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 150, 25], [173, 28, 154], [0, 1]]
 g := ![![[167, 122, 66], [167, 92, 177], [93, 171], [73, 156], [135, 149, 116], [24, 95, 1], []], ![[68, 41, 156, 117], [48, 114, 174, 17], [109, 110], [107, 177], [135, 169, 80, 110], [135, 152, 156, 89], [108, 88]], ![[66, 126, 75, 73], [103, 94, 126, 34], [92, 36], [42, 5], [102, 84, 126, 58], [151, 167, 83, 97], [158, 88]]]
 h' := ![![[101, 150, 25], [101, 178, 31], [20, 129, 101], [20, 141, 156], [72, 72, 48], [156, 20, 37], [0, 0, 1], [0, 1]], ![[173, 28, 154], [41, 145, 127], [156, 113, 146], [130, 17, 17], [132, 153, 101], [152, 107, 104], [163, 125, 28], [101, 150, 25]], ![[0, 1], [124, 35, 21], [104, 116, 111], [143, 21, 6], [7, 133, 30], [166, 52, 38], [168, 54, 150], [173, 28, 154]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 100], []]
 b := ![[], [82, 45, 175], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [83, 51, 84, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-349251813, -474066970, 714611544, 325931986, 1549500844]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-395968607, -1375142302, -1613179910, 325931986, 1549500844]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40, -321, 384, 149, 931]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-40, -321, 384, 149, 931]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![109, 84, 1, 0, 0], ![76, 107, 0, 1, 0], ![73, 124, 0, 0, 1]] where
  M :=![![![-40, -321, 384, 149, 931], ![148, 1237, -1474, -572, -3572], ![-560, -4746, 5649, 2188, 13680], ![1030, 8500, -10132, -3921, -24510], ![21, 237, -278, -109, -680]]]
  hmulB := by decide  
  f := ![![![1118, 829, -356, -247, -1083]], ![![1596, 1123, -482, -332, -1444]], ![![1442, 1041, -447, -309, -1349]], ![![1434, 1027, -442, -305, -1330]], ![![1559, 1114, -478, -330, -1439]]]
  g := ![![![-677, -916, 384, 149, 931], ![2598, 3515, -1474, -572, -3572], ![-9951, -13462, 5649, 2188, 13680], ![17836, 24125, -10132, -3921, -24510], ![493, 668, -278, -109, -680]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [40, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 178], [0, 1]]
 g := ![![[178, 5], [118, 149], [46], [149], [47, 4], [119, 168], [1]], ![[20, 174], [171, 30], [46], [149], [28, 175], [37, 11], [1]]]
 h' := ![![[40, 178], [113, 30], [14, 111], [171, 164], [89, 68], [73, 177], [139, 40], [0, 1]], ![[0, 1], [60, 149], [158, 68], [108, 15], [124, 111], [172, 2], [128, 139], [40, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [5, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [40, 139, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-90003, -49731, 104720, 56175, 202565]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-170732, -223324, 104720, 56175, 202565]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-8043, -5889, 2491, 1728, 7566]] ![![-40, -321, 384, 149, 931]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-6086, -44034, 52089, 20227, 126195]]]
 hmul := by decide  
 g := ![![![![-34, -246, 291, 113, 705]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0, 0, 0]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![0, 0, 0, 0, 181]] where
  M :=![![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![0, 0, 0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 5 2 7 [137, 25, 178, 20, 41, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 7, 89, 128, 150], [61, 85, 156, 29, 162], [58, 101, 0, 143, 141], [43, 168, 117, 62, 90], [0, 1]]
 g := ![![[90, 125, 34, 175, 135], [70, 158, 24, 111], [6, 24, 33, 24, 177], [94, 146, 161, 79], [93, 43, 100, 51, 52], [1], []], ![[137, 112, 9, 26, 57, 58, 97, 30], [57, 26, 164, 99], [84, 174, 162, 176, 120, 98, 31, 10], [57, 121, 153, 108], [71, 44, 123, 107, 35, 166, 39, 128], [90, 111, 99, 50, 40, 85, 43, 89], [141, 107, 85, 56]], ![[104, 145, 77, 117, 176, 143, 89, 158], [10, 96, 23, 87], [50, 111, 60, 67, 45, 88, 157, 115], [88, 134, 100, 39], [86, 166, 68, 124, 138, 119, 0, 89], [3, 4, 146, 62, 109, 125, 162, 50], [58, 62, 25, 180]], ![[55, 120, 27, 100, 87, 107, 3, 93], [97, 70, 108, 114], [177, 28, 0, 137, 117, 171, 86, 41], [47, 158, 52, 147], [40, 170, 144, 107, 77, 38, 76, 89], [63, 69, 158, 74, 88, 80, 178, 57], [13, 42, 66, 152]], ![[3, 95, 129, 40, 141, 87, 177, 85], [125, 7, 173, 147], [169, 132, 69, 26, 54, 78, 151, 66], [148, 29, 39, 56], [173, 153, 158, 49, 101, 1, 136, 104], [104, 77, 87, 24, 55, 166, 14, 78], [109, 123, 154, 136]]]
 h' := ![![[159, 7, 89, 128, 150], [14, 0, 50, 57, 139], [83, 21, 4, 2, 103], [127, 65, 138, 122, 38], [110, 55, 137, 169, 160], [44, 156, 3, 161, 140], [0, 0, 1], [0, 1]], ![[61, 85, 156, 29, 162], [156, 168, 77, 36, 67], [180, 47, 0, 122, 113], [53, 8, 95, 9, 13], [160, 28, 1, 9, 164], [6, 9, 120, 152, 90], [172, 151, 155, 151, 20], [159, 7, 89, 128, 150]], ![[58, 101, 0, 143, 141], [120, 41, 155, 13, 123], [59, 140, 63, 80, 79], [104, 74, 4, 164, 70], [24, 98, 112, 96, 138], [40, 34, 35, 104, 116], [119, 64, 98, 179, 81], [61, 85, 156, 29, 162]], ![[43, 168, 117, 62, 90], [116, 46, 101, 100, 131], [83, 113, 147, 39, 117], [147, 101, 54, 67, 53], [34, 23, 42, 135, 50], [67, 59, 116, 28, 126], [135, 26, 148, 134, 85], [58, 101, 0, 143, 141]], ![[0, 1], [32, 107, 160, 156, 83], [18, 41, 148, 119, 131], [125, 114, 71, 0, 7], [55, 158, 70, 134, 31], [121, 104, 88, 98, 71], [129, 121, 141, 79, 176], [43, 168, 117, 62, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137, 69, 143, 118], [], [], []]
 b := ![[], [162, 103, 161, 5, 33], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 5
  hpos := by decide
  P := [137, 25, 178, 20, 41, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![233066836038360, 114077441375145, -248379835714234, -133487106613333, -466874911708967]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1287662077560, 630262107045, -1372264285714, -737497826593, -2579419401707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 194264244901 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 5, -23, -6, -50]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-19, 5, -23, -6, -50]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![125, 126, 45, 1, 0], ![142, 65, 60, 0, 1]] where
  M :=![![![-19, 5, -23, -6, -50], ![-56, -128, 139, 58, 344], ![-16, 357, -448, -170, -1096], ![-124, -745, 885, 355, 2136], ![14, -9, 15, 4, 45]]]
  hmulB := by decide  
  f := ![![![7, -9, 1, 2, 6]], ![![-24, -6, 21, 10, 56]], ![![-16, 31, -38, -22, -136]], ![![-15, -3, 6, 3, 10]], ![![-8, 1, -4, -2, -19]]]
  g := ![![![41, 21, 17, -6, -50], ![-294, -156, -121, 58, 344], ![926, 487, 382, -170, -1096], ![-1821, -965, -750, 355, 2136], ![-36, -18, -15, 4, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [135, 39, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [182, 102, 144], [133, 88, 47], [0, 1]]
 g := ![![[51, 73, 65], [53, 154, 54], [3, 61, 130], [85, 70, 138], [154, 124, 16], [57, 124, 1], []], ![[69, 182, 25, 40], [56, 37, 162, 26], [36, 83, 123, 46], [122, 141, 79, 153], [135, 24, 119, 23], [61, 38, 64, 78], [175, 108]], ![[102, 27, 48, 14], [59, 36, 20, 186], [184, 96, 97, 74], [79, 97, 97, 19], [43, 17, 113, 93], [189, 178, 97, 28], [81, 108]]]
 h' := ![![[182, 102, 144], [103, 19, 16], [168, 86, 93], [176, 109, 148], [29, 143, 86], [136, 137, 187], [0, 0, 1], [0, 1]], ![[133, 88, 47], [71, 49, 133], [190, 120, 131], [51, 91, 70], [86, 159, 83], [62, 169, 85], [140, 61, 88], [182, 102, 144]], ![[0, 1], [105, 123, 42], [69, 176, 158], [55, 182, 164], [152, 80, 22], [127, 76, 110], [69, 130, 102], [133, 88, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 171], []]
 b := ![[], [45, 94, 154], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [135, 39, 67, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11055808734, -5780390405, 12199672217, 6485489017, 23184634902]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21539058073, -12198708247, -8747253548, 6485489017, 23184634902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -9, 1, 2, 6]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![7, -9, 1, 2, 6]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![184, 101, 1, 0, 0], ![67, 149, 0, 1, 0], ![171, 123, 0, 0, 1]] where
  M :=![![![7, -9, 1, 2, 6], ![-24, -6, 21, 10, 56], ![-16, 31, -38, -22, -136], ![4, -87, 85, 53, 224], ![-2, -1, 9, 4, 39]]]
  hmulB := by decide  
  f := ![![![-19, 5, -23, -6, -50]], ![![-56, -128, 139, 58, 344]], ![![-48, -61, 49, 24, 128]], ![![-51, -102, 105, 45, 262]], ![![-53, -78, 69, 32, 177]]]
  g := ![![![-7, -6, 1, 2, 6], ![-74, -55, 21, 10, 56], ![166, 125, -38, -22, -136], ![-301, -231, 85, 53, 224], ![-45, -33, 9, 4, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [134, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 190], [0, 1]]
 g := ![![[146, 67], [175, 79], [144, 85], [147, 153], [120, 59], [60, 39], [1]], ![[0, 124], [0, 112], [50, 106], [16, 38], [57, 132], [109, 152], [1]]]
 h' := ![![[109, 190], [43, 110], [186, 156], [166, 64], [155, 150], [173, 170], [57, 109], [0, 1]], ![[0, 1], [0, 81], [0, 35], [75, 127], [79, 41], [176, 21], [96, 82], [109, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [14, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [134, 82, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-422734, -309114, 566576, 285404, 1135058]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1664344, -1254820, 566576, 285404, 1135058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-19, 5, -23, -6, -50]] ![![7, -9, 1, 2, 6]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![570, -493, 134, 163, 651]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![570, -493, 134, 163, 651]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![24, 28, 93, 80, 1]] where
  M :=![![![570, -493, 134, 163, 651], ![-1308, 211, 818, 272, 1972], ![1360, 2230, -3801, -1900, -10880], ![1694, -5036, 4586, 2623, 13854], ![-1247, 57, 982, 411, 2642]]]
  hmulB := by decide  
  f := ![![![464, 339, -142, -99, -433]], ![![644, 471, -194, -136, -596]], ![![880, 650, -253, -180, -800]], ![![238, 188, -18, -25, -142]], ![![673, 501, -175, -129, -584]]]
  g := ![![![-78, -97, -313, -269, 651], ![-252, -285, -946, -816, 1972], ![1360, 1590, 5223, 4500, -10880], ![-1714, -2036, -6652, -5729, 13854], ![-335, -383, -1268, -1093, 2642]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [60, 4, 78, 52, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 137, 0, 168], [143, 109, 179, 65], [105, 139, 14, 153], [0, 1]]
 g := ![![[5, 33, 166, 97], [134, 3, 56], [12, 91, 118], [31, 191, 27], [73, 106, 175], [117, 141, 1], []], ![[160, 190, 33, 83, 106, 98], [18, 44, 23], [3, 92, 32], [81, 151, 24], [40, 118, 172], [105, 154, 165], [110, 118, 81, 156, 163, 8]], ![[56, 120, 116, 111, 64, 165], [70, 185, 12], [62, 57, 185], [185, 91, 8], [2, 165, 8], [84, 181, 85], [40, 7, 23, 63, 66, 179]], ![[145, 65, 29, 102, 95, 82], [66, 9, 7], [151, 65, 100], [114, 187, 83], [106, 180, 2], [42, 131, 92], [77, 71, 124, 97, 137, 76]]]
 h' := ![![[86, 137, 0, 168], [20, 98, 26, 167], [95, 179, 145, 40], [129, 135, 118, 73], [32, 162, 89, 151], [121, 143, 93, 91], [0, 0, 0, 1], [0, 1]], ![[143, 109, 179, 65], [124, 113, 166, 9], [25, 153, 100, 122], [28, 167, 83, 178], [16, 15, 88, 88], [10, 25, 138, 65], [83, 13, 16, 92], [86, 137, 0, 168]], ![[105, 139, 14, 153], [23, 174, 178, 99], [39, 64, 182, 165], [142, 111, 163, 125], [137, 66, 82, 89], [185, 28, 180, 89], [173, 144, 108, 49], [143, 109, 179, 65]], ![[0, 1], [157, 1, 16, 111], [8, 183, 152, 59], [24, 166, 22, 10], [63, 143, 127, 58], [132, 190, 168, 141], [23, 36, 69, 51], [105, 139, 14, 153]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [93, 118, 83], []]
 b := ![[], [], [100, 118, 95, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [60, 4, 78, 52, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42890150732, -20983314666, 45697051672, 24560918955, 85889102438]
  a := ![-32, -23, 49, 25, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10902738908, -12569317010, -41150204534, -35474441845, 85889102438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-464, -339, 142, 99, 433]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-464, -339, 142, 99, 433]] 
 ![![193, 0, 0, 0, 0], ![112, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-464, -339, 142, 99, 433], ![-644, -471, 194, 136, 596], ![-880, -650, 253, 180, 800], ![-238, -188, 18, 25, 142], ![159, 121, -34, -27, -128]]]
  hmulB := by decide  
  f := ![![![-570, 493, -134, -163, -651]], ![![-324, 285, -82, -96, -388]], ![![-10, -9, 19, 9, 53]], ![![-248, 233, -80, -82, -345]], ![![-91, 84, -28, -30, -125]]]
  g := ![![![78, -339, 142, 99, 433], ![110, -471, 194, 136, 596], ![159, -650, 253, 180, 800], ![73, -188, 18, 25, 142], ![-36, 121, -34, -27, -128]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![570, -493, 134, 163, 651]] ![![-464, -339, 142, 99, 433]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, 171, -95, -52, -272]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![175, 171, -95, -52, -272]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![52, 176, 67, 1, 0], ![177, 162, 52, 0, 1]] where
  M :=![![![175, 171, -95, -52, -272], ![160, -20, 203, 66, 400], ![16, 709, -444, -138, -1384], ![-1192, -1661, 2613, 1187, 5628], ![260, 81, -297, -162, -513]]]
  hmulB := by decide  
  f := ![![![27, 135, -189, -108, -584]], ![![256, -446, 335, 230, 1136]], ![![-976, 765, -118, -194, -696]], ![![-92, -102, 205, 109, 612]], ![![-21, -46, 76, 42, 231]]]
  g := ![![![259, 271, 89, -52, -272], ![-376, -388, -127, 66, 400], ![1280, 1265, 410, -138, -1384], ![-5376, -5697, -1876, 1187, 5628], ![505, 567, 189, -162, -513]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [49, 56, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 41, 120], [179, 155, 77], [0, 1]]
 g := ![![[22, 124, 41], [174, 172], [3, 159, 28], [70, 190], [77, 1], [161, 107], [1]], ![[135, 168, 172, 78], [75, 187], [191, 104, 57, 12], [32, 107], [8, 81], [39, 61], [128, 86, 38, 113]], ![[75, 169, 133, 120], [70, 23], [124, 12, 123, 95], [169, 164], [166, 100], [87, 4], [75, 175, 102, 84]]]
 h' := ![![[104, 41, 120], [81, 65, 89], [50, 141, 127], [90, 29, 182], [163, 115, 92], [28, 94, 1], [148, 141, 86], [0, 1]], ![[179, 155, 77], [111, 59, 122], [35, 6, 160], [59, 50, 170], [53, 91, 86], [144, 95, 9], [26, 71, 109], [104, 41, 120]], ![[0, 1], [74, 73, 183], [130, 50, 107], [129, 118, 42], [50, 188, 19], [111, 8, 187], [146, 182, 2], [179, 155, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 8], []]
 b := ![[], [99, 15, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [49, 56, 111, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149145765961, 74865942455, -161056735077, -86197109066, -304022790912]
  a := ![649, 505, -992, -453, -2054]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![296667154461, 327397204395, 108747891877, -86197109066, -304022790912]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 135, -189, -108, -584]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![27, 135, -189, -108, -584]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![47, 63, 1, 0, 0], ![194, 108, 0, 1, 0], ![129, 122, 0, 0, 1]] where
  M :=![![![27, 135, -189, -108, -584], ![256, -446, 335, 230, 1136], ![-976, 765, -118, -194, -696], ![808, 127, -841, -393, -2372], ![364, -485, 291, 218, 1035]]]
  hmulB := by decide  
  f := ![![![175, 171, -95, -52, -272]], ![![160, -20, 203, 66, 400]], ![![93, 38, 40, 8, 56]], ![![254, 149, 31, -9, -20]], ![![215, 100, 62, 6, 67]]]
  g := ![![![534, 482, -189, -108, -584], ![-1049, -939, 335, 230, 1136], ![670, 579, -118, -194, -696], ![2145, 1954, -841, -393, -2372], ![-960, -856, 291, 218, 1035]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [79, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 196], [0, 1]]
 g := ![![[139, 182], [70], [], [], [], [142], [51, 1]], ![[162, 15], [70], [], [], [], [142], [102, 196]]]
 h' := ![![[51, 196], [183, 24], [0, 142], [158], [143], [52], [108, 158], [0, 1]], ![[0, 1], [28, 173], [150, 55], [158], [143], [52], [89, 39], [51, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [139, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [79, 146, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-365245, -191166, 400773, 213739, 759296]
  a := ![121, 93, -185, -88, -383]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-805158, -716537, 400773, 213739, 759296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![175, 171, -95, -52, -272]] ![![27, 135, -189, -108, -584]]
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


lemma PB547I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB547I4 : PrimesBelowBoundCertificateInterval O 151 197 547 where
  m := 9
  g := ![2, 3, 3, 2, 2, 1, 2, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB547I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
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
    · exact ![607573201, 157]
    · exact ![4330747, 163, 163]
    · exact ![27889, 27889, 167]
    · exact ![895745041, 173]
    · exact ![5735339, 32041]
    · exact ![194264244901]
    · exact ![6967871, 36481]
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
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
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
  β := ![I157N1, I163N1, I163N2, I167N2, I173N1, I193N1]
  Il := ![[I157N1], [I163N1, I163N2], [I167N2], [I173N1], [], [], [], [I193N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
