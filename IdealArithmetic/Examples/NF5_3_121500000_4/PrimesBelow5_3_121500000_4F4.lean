
import IdealArithmetic.Examples.NF5_3_121500000_4.RI5_3_121500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![493, 468, 114, -10, -134]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![493, 468, 114, -10, -134]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![119, 33, 103, 1, 0], ![80, 62, 118, 0, 1]] where
  M :=![![![493, 468, 114, -10, -134], ![1638, 1689, 488, -10, -522], ![6294, 6312, 1709, -38, -1686], ![9354, 9920, 2950, 85, -2496], ![6122, 6472, 1904, 66, -1521]]]
  hmulB := by decide  
  f := ![![![3405, 604, -622, -190, 494]], ![![-5358, -979, 984, 314, -798]], ![![8634, 1696, -1607, -570, 1374]], ![![7089, 1357, -1313, -449, 1102]], ![![6118, 1198, -1138, -402, 971]]]
  g := ![![![79, 58, 108, -10, -134], ![284, 219, 402, -10, -522], ![928, 714, 1303, -38, -1686], ![1267, 1031, 1839, 85, -2496], ![764, 628, 1112, 66, -1521]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [12, 90, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 8, 34], [126, 148, 123], [0, 1]]
 g := ![![[106, 18, 31], [26, 121], [81, 37, 16], [121, 123, 30], [87, 127, 118], [110, 1], []], ![[43, 134, 78, 135], [125, 47], [5, 17, 121, 28], [135, 142, 128, 65], [67, 148, 118, 149], [92, 81], [63, 57]], ![[115, 89, 117, 119], [51, 64], [13, 44, 105, 43], [45, 132, 130, 73], [40, 46, 55, 133], [74, 64], [131, 57]]]
 h' := ![![[141, 8, 34], [117, 38, 38], [127, 67, 11], [118, 79, 4], [55, 80, 40], [93, 136, 78], [0, 0, 1], [0, 1]], ![[126, 148, 123], [134, 10, 8], [149, 46, 138], [151, 97, 138], [127, 0, 5], [51, 154, 154], [128, 141, 148], [141, 8, 34]], ![[0, 1], [56, 109, 111], [121, 44, 8], [92, 138, 15], [139, 77, 112], [29, 24, 82], [17, 16, 8], [126, 148, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 101], []]
 b := ![[], [70, 48, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [12, 90, 47, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![210989142, 235633476, 95565312, 15613962, -149722380]
  a := ![17, 4, 8, 14, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![65800752, 57344970, 102895338, 15613962, -149722380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3405, 604, -622, -190, 494]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![3405, 604, -622, -190, 494]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![108, 108, 1, 0, 0], ![134, 110, 0, 1, 0], ![121, 74, 0, 0, 1]] where
  M :=![![![3405, 604, -622, -190, 494], ![-5358, -979, 984, 314, -798], ![8634, 1696, -1607, -570, 1374], ![-4710, -1208, 926, 465, -960], ![1510, 336, -288, -122, 271]]]
  hmulB := by decide  
  f := ![![![493, 468, 114, -10, -134]], ![![1638, 1689, 488, -10, -522]], ![![1506, 1524, 425, -14, -462]], ![![1628, 1646, 458, -15, -496]], ![![1191, 1198, 330, -12, -359]]]
  g := ![![![231, 332, -622, -190, 494], ![-364, -527, 984, 314, -798], ![588, 868, -1607, -570, 1374], ![-324, -518, 926, 465, -960], ![103, 158, -288, -122, 271]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [43, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 156], [0, 1]]
 g := ![![[155, 86], [130], [1, 117], [6, 115], [104, 82], [17], [1]], ![[15, 71], [130], [15, 40], [5, 42], [91, 75], [17], [1]]]
 h' := ![![[86, 156], [27, 20], [114, 75], [56, 91], [81, 127], [19, 32], [114, 86], [0, 1]], ![[0, 1], [20, 137], [127, 82], [32, 66], [13, 30], [102, 125], [131, 71], [86, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [43, 156]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [43, 71, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12118960, -11443307, -3325493, 185633, 6606311]
  a := ![113, -4, 57, 50, -449]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3039517, -1029151, -3325493, 185633, 6606311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![493, 468, 114, -10, -134]] ![![3405, 604, -622, -190, 494]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1917, -1026, 474, 478, -788]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-1917, -1026, 474, 478, -788]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![92, 125, 90, 66, 1]] where
  M :=![![![-1917, -1026, 474, 478, -788], ![8022, 4383, -1982, -2062, 3372], ![-34278, -18874, 8507, 8966, -14628], ![70308, 38952, -17412, -18539, 30168], ![-13480, -7458, 3354, 3568, -5809]]]
  hmulB := by decide  
  f := ![![![-31, -6, 6, 2, -4]], ![![42, 5, -10, -2, 12]], ![![-138, -62, 9, 10, 12]], ![![-108, -120, -36, 7, 72]], ![![-106, -83, -14, 8, 43]]]
  g := ![![![433, 598, 438, 322, -788], ![-1854, -2559, -1874, -1378, 3372], ![8046, 11102, 8129, 5978, -14628], ![-16596, -22896, -16764, -12329, 30168], ![3196, 4409, 3228, 2374, -5809]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [115, 105, 52, 49, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 110, 17, 135], [145, 5, 114, 127], [29, 47, 32, 64], [0, 1]]
 g := ![![[121, 88, 67, 118], [132, 64, 97, 85], [1, 45, 53], [42, 80, 152], [139, 147, 88], [114, 1], []], ![[62, 4, 37, 129, 152, 152], [147, 36, 150, 74, 62, 140], [42, 135, 51], [4, 28, 77], [86, 10, 38], [88, 79, 111, 139, 54, 4], [69, 78, 132]], ![[85, 114, 101, 20, 47, 125], [68, 0, 77, 79, 151, 122], [113, 127, 146], [22, 87, 133], [158, 94, 21], [11, 79, 146, 140, 120, 125], [109, 8, 155]], ![[102, 88, 85, 115, 49, 57], [103, 61, 68, 19, 9, 143], [17, 64, 36], [144, 120, 100], [89, 64, 39], [32, 59, 76, 59, 115, 113], [83, 133, 21]]]
 h' := ![![[103, 110, 17, 135], [142, 44, 90, 66], [20, 38, 33, 30], [61, 81, 65, 78], [162, 82, 137, 106], [93, 140, 161, 67], [0, 0, 1], [0, 1]], ![[145, 5, 114, 127], [1, 99, 12, 130], [58, 25, 77, 141], [18, 156, 111, 122], [106, 144, 7, 27], [78, 62, 113, 53], [66, 88, 54, 147], [103, 110, 17, 135]], ![[29, 47, 32, 64], [78, 102, 76, 36], [60, 0, 37, 68], [129, 47, 85, 132], [41, 111, 107, 40], [97, 104, 74, 99], [14, 6, 113, 127], [145, 5, 114, 127]], ![[0, 1], [120, 81, 148, 94], [157, 100, 16, 87], [112, 42, 65, 157], [32, 152, 75, 153], [18, 20, 141, 107], [98, 69, 158, 52], [29, 47, 32, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 62, 28], []]
 b := ![[], [], [60, 93, 157, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [115, 105, 52, 49, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44377556372, -44808654685, -13288267979, -44239969, 17443987494]
  a := ![10, 1, 5, 6, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10117941140, -13652190745, -9713172653, -7063481071, 17443987494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -6, 6, 2, -4]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-31, -6, 6, 2, -4]] 
 ![![163, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-31, -6, 6, 2, -4], ![42, 5, -10, -2, 12], ![-138, -62, 9, 10, 12], ![-108, -120, -36, 7, 72], ![-128, -102, -18, 8, 45]]]
  hmulB := by decide  
  f := ![![![-1917, -1026, 474, 478, -788]], ![![-186, -99, 46, 46, -76]], ![![-1257, -676, 311, 316, -520]], ![![-486, -252, 120, 115, -192]], ![![-412, -222, 102, 104, -171]]]
  g := ![![![-3, -6, 6, 2, -4], ![4, 5, -10, -2, 12], ![-5, -62, 9, 10, 12], ![18, -120, -36, 7, 72], ![10, -102, -18, 8, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-1917, -1026, 474, 478, -788]] ![![-31, -6, 6, 2, -4]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 24, 6, -10, -2]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-23, 24, 6, -10, -2]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![95, 155, 164, 5, 1]] where
  M :=![![![-23, 24, 6, -10, -2], ![54, 9, 44, 38, -126], ![1398, 1068, -67, -278, 78], ![-78, 488, 790, 409, -1488], ![1598, 1324, 164, -162, -333]]]
  hmulB := by decide  
  f := ![![![-237, -88, 58, 22, -50]], ![![534, 199, -132, -50, 114]], ![![-1218, -460, 299, 114, -258]], ![![1110, 416, -278, -105, 240]], ![![-803, -305, 196, 75, -169]]]
  g := ![![![1, 2, 2, 0, -2], ![72, 117, 124, 4, -126], ![-36, -66, -77, -4, 78], ![846, 1384, 1466, 47, -1488], ![199, 317, 328, 9, -333]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [4, 122, 50, 156, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 143, 16, 3], [145, 115, 127, 29], [119, 75, 24, 135], [0, 1]]
 g := ![![[105, 104, 9, 3], [126, 154, 84, 144], [161, 148, 75, 33], [53, 131, 130], [60, 107, 31], [11, 1], []], ![[98, 126, 28, 120, 69, 42], [20, 0, 133, 120, 36, 121], [136, 117, 114, 4, 51, 99], [109, 46, 4], [163, 132, 157], [97, 69, 139, 76, 157, 50], [137, 28, 9]], ![[32, 78, 163, 82, 165, 33], [137, 69, 149, 162, 134, 56], [120, 91, 136, 149, 149, 65], [15, 101, 2], [38, 164, 4], [9, 148, 31, 39, 58, 36], [43, 84, 6]], ![[39, 142, 143, 60, 24, 10], [155, 2, 7, 84, 87, 106], [161, 140, 50, 72, 48, 78], [11, 79, 31], [128, 38, 98], [98, 152, 73, 141, 86, 80], [148, 42, 22]]]
 h' := ![![[81, 143, 16, 3], [164, 119, 81, 105], [24, 6, 21, 12], [130, 101, 40, 130], [26, 146, 139, 56], [123, 157, 163, 71], [0, 0, 1], [0, 1]], ![[145, 115, 127, 29], [112, 82, 115, 101], [149, 107, 119, 51], [149, 112, 11, 37], [77, 149, 84, 2], [27, 87, 16, 18], [1, 161, 47, 63], [81, 143, 16, 3]], ![[119, 75, 24, 135], [119, 28, 162, 57], [47, 32, 35, 81], [66, 148, 116, 141], [31, 130, 48, 13], [4, 135, 30, 2], [145, 46, 58, 95], [145, 115, 127, 29]], ![[0, 1], [150, 105, 143, 71], [12, 22, 159, 23], [83, 140, 0, 26], [36, 76, 63, 96], [106, 122, 125, 76], [42, 127, 61, 9], [119, 75, 24, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [23, 141, 1], []]
 b := ![[], [], [118, 127, 33, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [4, 122, 50, 156, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60925132144550, -63442094596120, -20686227117348, -1241851086246, 28055856265058]
  a := ![-61, -8, -30, -43, 245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16324739385180, -26419759375330, -27675728470580, -847431930608, 28055856265058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-237, -88, 58, 22, -50]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-237, -88, 58, 22, -50]] 
 ![![167, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![-237, -88, 58, 22, -50], ![534, 199, -132, -50, 114], ![-1218, -460, 299, 114, -258], ![1110, 416, -278, -105, 240], ![-154, -60, 36, 14, -31]]]
  hmulB := by decide  
  f := ![![![-23, 24, 6, -10, -2]], ![![-14, 15, 4, -6, -2]], ![![3, 12, 1, -4, 0]], ![![-13, 16, 8, -3, -10]], ![![-2, 20, 4, -6, -3]]]
  g := ![![![53, -88, 58, 22, -50], ![-120, 199, -132, -50, 114], ![277, -460, 299, 114, -258], ![-251, 416, -278, -105, 240], ![36, -60, 36, 14, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-23, 24, 6, -10, -2]] ![![-237, -88, 58, 22, -50]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5391, -2054, 1340, 512, -1160]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-5391, -2054, 1340, 512, -1160]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![16, 110, 1, 0, 0], ![158, 100, 0, 1, 0], ![96, 48, 0, 0, 1]] where
  M :=![![![-5391, -2054, 1340, 512, -1160], ![12384, 4717, -3078, -1176, 2664], ![-28440, -10830, 7069, 2700, -6120], ![26478, 10086, -6576, -2513, 5688], ![-3496, -1328, 872, 332, -757]]]
  hmulB := by decide  
  f := ![![![157, 22, -40, -16, 40]], ![![-432, -187, 54, 48, -72]], ![![-256, -116, 29, 28, -40]], ![![-116, -94, -4, 15, -8]], ![![-32, -40, -8, 4, 3]]]
  g := ![![![21, -838, 1340, 512, -1160], ![-48, 1925, -3078, -1176, 2664], ![112, -4420, 7069, 2700, -6120], ![-100, 4114, -6576, -2513, 5688], ![16, -544, 872, 332, -757]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [33, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 172], [0, 1]]
 g := ![![[142, 21], [117], [62, 95], [138, 133], [149], [37, 52], [1]], ![[0, 152], [117], [21, 78], [46, 40], [149], [122, 121], [1]]]
 h' := ![![[158, 172], [153, 114], [30, 109], [117, 152], [27, 126], [163, 29], [140, 158], [0, 1]], ![[0, 1], [0, 59], [125, 64], [86, 21], [40, 47], [74, 144], [19, 15], [158, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [11, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [33, 15, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50858, -188218, -205370, -96977, 378813]
  a := ![29, 11, 15, 32, -117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-102940, 80446, -205370, -96977, 378813]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![344, 63, -61, -19, 45]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![344, 63, -61, -19, 45]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![139, 143, 1, 0, 0], ![9, 139, 0, 1, 0], ![73, 104, 0, 0, 1]] where
  M :=![![![344, 63, -61, -19, 45], ![-483, -58, 101, 25, -93], ![1041, 337, -108, -59, 21], ![204, 441, 177, -11, -276], ![549, 394, 58, -29, -142]]]
  hmulB := by decide  
  f := ![![![-1880, -703, 467, 165, -387]], ![![4149, 1518, -1033, -335, 819]], ![![1868, 672, -466, -141, 357]], ![![3273, 1194, -815, -261, 642]], ![![1697, 615, -423, -132, 329]]]
  g := ![![![33, 39, -61, -19, 45], ![-46, -48, 101, 25, -93], ![87, 126, -108, -59, 21], ![-24, 31, 177, -11, -276], ![18, 63, 58, -29, -142]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [137, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [156, 172], [0, 1]]
 g := ![![[62, 24], [169], [117, 167], [89, 22], [148], [91, 116], [1]], ![[0, 149], [169], [46, 6], [61, 151], [148], [22, 57], [1]]]
 h' := ![![[156, 172], [169, 71], [60, 13], [90, 101], [86, 56], [162, 119], [36, 156], [0, 1]], ![[0, 1], [0, 102], [12, 160], [103, 72], [172, 117], [42, 54], [152, 17], [156, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165]]
 b := ![[], [139, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [137, 17, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![414995, 233076, -111804, -126722, 208968]
  a := ![-18, -16, -8, -38, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10645, 69958, -111804, -126722, 208968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-110, -61, 27, 29, -47]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![-110, -61, 27, 29, -47]] 
 ![![173, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-110, -61, 27, 29, -47], ![477, 264, -119, -127, 207], ![-2103, -1171, 518, 557, -903], ![4344, 2409, -1083, -1157, 1884], ![-847, -474, 206, 223, -360]]]
  hmulB := by decide  
  f := ![![![-126, 169, -21, -27, 25]], ![![-69, 89, -10, -14, 12]], ![![15, 12, -3, -2, 2]], ![![-66, 79, -3, -11, 4]], ![![-23, 48, -4, -7, 4]]]
  g := ![![![30, -61, 27, 29, -47], ![-130, 264, -119, -127, 207], ![576, -1171, 518, 557, -903], ![-1186, 2409, -1083, -1157, 1884], ![233, -474, 206, 223, -360]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-5391, -2054, 1340, 512, -1160]] ![![344, 63, -61, -19, 45]]
  ![![126, -169, 21, 27, -25]] where
 M := ![![![126, -169, 21, 27, -25]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![126, -169, 21, 27, -25]] ![![-110, -61, 27, 29, -47]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-60, -61, -17, 1, 19]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-60, -61, -17, 1, 19]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![114, 142, 1, 0, 0], ![140, 89, 0, 1, 0], ![148, 138, 0, 0, 1]] where
  M :=![![![-60, -61, -17, 1, 19], ![-231, -230, -63, 1, 69], ![-831, -847, -232, 9, 219], ![-1212, -1297, -401, -27, 348], ![-817, -864, -252, -7, 194]]]
  hmulB := by decide  
  f := ![![![15664, 2751, -2859, -853, 2245]], ![![-24381, -4302, 4457, 1331, -3501]], ![![-9153, -1623, 1676, 501, -1317]], ![![31, -5, -2, 0, 1]], ![![-5811, -1036, 1066, 319, -838]]]
  g := ![![![-6, -2, -17, 1, 19], ![-19, -5, -63, 1, 69], ![-45, 6, -232, 9, 219], ![-18, 56, -401, -27, 348], ![1, 49, -252, -7, 194]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [71, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 178], [0, 1]]
 g := ![![[2, 156], [176, 101], [144], [95], [160, 52], [112, 116], [1]], ![[46, 23], [154, 78], [144], [95], [115, 127], [108, 63], [1]]]
 h' := ![![[37, 178], [34, 131], [130, 82], [144, 167], [96, 128], [103, 54], [108, 37], [0, 1]], ![[0, 1], [48, 48], [121, 97], [58, 12], [178, 51], [132, 125], [45, 142], [37, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [101, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [71, 142, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-179417, -153684, -34079, 10740, 83064]
  a := ![-3, 8, -1, 11, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-56377, -43202, -34079, 10740, 83064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-170, -103, 43, 51, -81]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-170, -103, 43, 51, -81]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![28, 46, 1, 0, 0], ![72, 120, 0, 1, 0], ![175, 46, 0, 0, 1]] where
  M :=![![![-170, -103, 43, 51, -81], ![819, 470, -205, -229, 369], ![-3741, -2109, 928, 1015, -1641], ![7914, 4415, -1967, -2121, 3444], ![-1533, -858, 378, 409, -662]]]
  hmulB := by decide  
  f := ![![![194, 105, -3, -11, -15]], ![![213, 322, 127, -3, -177]], ![![97, 109, 34, -3, -51]], ![![240, 277, 89, -7, -132]], ![![259, 199, 33, -12, -65]]]
  g := ![![![51, -25, 43, 51, -81], ![-232, 114, -205, -229, 369], ![1030, -509, 928, 1015, -1641], ![-2162, 1067, -1967, -2121, 3444], ![415, -206, 378, 409, -662]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [111, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 178], [0, 1]]
 g := ![![[1, 87], [17, 88], [138], [42], [126, 80], [48, 149], [1]], ![[10, 92], [94, 91], [138], [42], [17, 99], [156, 30], [1]]]
 h' := ![![[68, 178], [82, 96], [142, 25], [31, 106], [155, 20], [42, 120], [68, 68], [0, 1]], ![[0, 1], [166, 83], [52, 154], [79, 73], [83, 159], [147, 59], [38, 111], [68, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142]]
 b := ![[], [92, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [111, 111, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5146, 1466, -3278, -3587, 7593]
  a := ![-1, -4, 0, -7, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5439, 1304, -3278, -3587, 7593]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, -7, 3, 3, -5]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-14, -7, 3, 3, -5]] 
 ![![179, 0, 0, 0, 0], ![170, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![177, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![-14, -7, 3, 3, -5], ![51, 26, -13, -13, 21], ![-213, -117, 52, 55, -93], ![450, 251, -107, -117, 180], ![-73, -38, 22, 21, -42]]]
  hmulB := by decide  
  f := ![![![3822, 1529, -979, -379, 853]], ![![3579, 1432, -917, -355, 799]], ![![2211, 883, -566, -219, 493]], ![![3666, 1468, -940, -364, 819]], ![![1573, 629, -403, -156, 351]]]
  g := ![![![4, -7, 3, 3, -5], ![-13, 26, -13, -13, 21], ![65, -117, 52, 55, -93], ![-135, 251, -107, -117, 180], ![20, -38, 22, 21, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-60, -61, -17, 1, 19]] ![![-170, -103, 43, 51, -81]]
  ![![2625, 1476, -636, -696, 1114]] where
 M := ![![![2625, 1476, -636, -696, 1114]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![2625, 1476, -636, -696, 1114]] ![![-14, -7, 3, 3, -5]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-220528, -122615, 54595, 58533, -95049]]]
 hmul := by decide  
 g := ![![![![-1232, -685, 305, 327, -531]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-248, -191, -21, 11, 33]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-248, -191, -21, 11, 33]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![29, 136, 106, 1, 0], ![98, 86, 156, 0, 1]] where
  M :=![![![-248, -191, -21, 11, 33], ![-429, -544, -213, -9, 231], ![-2745, -2481, -526, 63, 585], ![-3390, -3735, -1197, -31, 1140], ![-2535, -2580, -716, 3, 664]]]
  hmulB := by decide  
  f := ![![![-236, -17, 39, -1, -15]], ![![183, -76, -15, 51, -57]], ![![531, 573, -178, -297, 441]], ![![398, 268, -106, -132, 207]], ![![419, 450, -140, -233, 346]]]
  g := ![![![-21, -25, -35, 11, 33], ![-126, -106, -195, -9, 231], ![-342, -339, -544, 63, 585], ![-631, -539, -971, -31, 1140], ![-374, -332, -578, 3, 664]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [5, 152, 173, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 6, 45], [162, 174, 136], [0, 1]]
 g := ![![[67, 59, 80], [119, 139], [119, 17, 75], [108, 116], [45, 42, 12], [93, 8, 1], []], ![[119, 20, 7, 13], [156, 39], [81, 1, 21, 64], [134, 81], [175, 123, 102, 39], [28, 49, 74, 33], [88, 34]], ![[155, 89, 69, 114], [118, 64], [124, 86, 46, 102], [151, 45], [68, 122, 111, 129], [29, 148, 28, 9], [178, 34]]]
 h' := ![![[27, 6, 45], [118, 89, 73], [129, 97, 35], [129, 137, 165], [137, 120, 72], [78, 123, 66], [0, 0, 1], [0, 1]], ![[162, 174, 136], [88, 58, 55], [12, 86, 138], [109, 61, 123], [112, 72, 9], [29, 144, 5], [108, 172, 174], [27, 6, 45]], ![[0, 1], [173, 34, 53], [43, 179, 8], [17, 164, 74], [132, 170, 100], [113, 95, 110], [14, 9, 6], [162, 174, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 141], []]
 b := ![[], [23, 118, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [5, 152, 173, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![172414490, -233318854, -458178566, -249903343, 757841181]
  a := ![-27, -11, -10, -32, 111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-369330521, -173595612, -509346124, -249903343, 757841181]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-236, -17, 39, -1, -15]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-236, -17, 39, -1, -15]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![117, 150, 1, 0, 0], ![94, 31, 0, 1, 0], ![12, 15, 0, 0, 1]] where
  M :=![![![-236, -17, 39, -1, -15], ![183, -76, -15, 51, -57], ![531, 573, -178, -297, 441], ![-2292, -1401, 591, 683, -1092], ![393, 264, -104, -129, 202]]]
  hmulB := by decide  
  f := ![![![-248, -191, -21, 11, 33]], ![![-429, -544, -213, -9, 231]], ![![-531, -588, -193, 0, 216]], ![![-221, -213, -54, 4, 63]], ![![-66, -72, -23, 0, 25]]]
  g := ![![![-25, -31, 39, -1, -15], ![-12, 8, -15, 51, -57], ![243, 165, -178, -297, 441], ![-677, -524, 591, 683, -1092], ![123, 93, -104, -129, 202]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [52, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 180], [0, 1]]
 g := ![![[156, 94], [20], [49, 94], [34], [80, 80], [106, 3], [1]], ![[0, 87], [20], [74, 87], [34], [5, 101], [24, 178], [1]]]
 h' := ![![[33, 180], [61, 53], [167, 54], [51, 128], [3, 136], [99, 73], [129, 33], [0, 1]], ![[0, 1], [0, 128], [139, 127], [112, 53], [147, 45], [155, 108], [132, 148], [33, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [157, 166]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [52, 148, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78846, -122398, -90010, -36194, 176664]
  a := ![-19, -6, -10, -19, 77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![64832, 65476, -90010, -36194, 176664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-248, -191, -21, 11, 33]] ![![-236, -17, 39, -1, -15]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12010, -2072, 2186, 645, -1711]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-12010, -2072, 2186, 645, -1711]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![170, 123, 130, 9, 1]] where
  M :=![![![-12010, -2072, 2186, 645, -1711], ![18597, 3219, -3362, -985, 2607], ![-28329, -4636, 5189, 1445, -3999], ![12528, 2094, -2082, -485, 1368], ![-4289, -500, 866, 201, -678]]]
  hmulB := by decide  
  f := ![![![156, 58, -40, -15, 35]], ![![-375, -149, 88, 35, -75]], ![![795, 278, -219, -79, 195]], ![![-864, -378, 174, 77, -144]], ![![398, 127, -120, -41, 109]]]
  g := ![![![1460, 1091, 1176, 84, -1711], ![-2223, -1662, -1792, -128, 2607], ![3411, 2551, 2749, 196, -3999], ![-1152, -870, -942, -67, 1368], ![581, 434, 466, 33, -678]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [32, 49, 57, 109, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 189, 24, 26], [147, 71, 132, 103], [119, 121, 35, 62], [0, 1]]
 g := ![![[149, 73, 20, 153], [2, 161, 84, 135], [175, 40, 118, 97], [81, 109, 183, 30], [157, 55, 57, 133], [82, 1], []], ![[185, 99, 76, 35, 155, 97], [9, 57, 176, 146, 48, 23], [30, 90, 135, 123, 73, 3], [122, 120, 89, 10, 187, 144], [34, 186, 189, 18, 119, 109], [71, 65, 82, 30, 142, 67], [106, 144, 103]], ![[119, 34, 119, 87, 2, 68], [132, 159, 21, 144, 177, 162], [40, 186, 169, 106, 186, 60], [118, 94, 0, 3, 145, 109], [126, 12, 40, 86, 89, 72], [59, 181, 119, 136, 99, 154], [10, 3, 104]], ![[95, 0, 84, 155, 32, 179], [68, 15, 169, 31, 82, 105], [35, 178, 104, 140, 135, 132], [94, 10, 34, 123, 18, 132], [149, 160, 124, 190, 122, 190], [145, 15, 125, 27, 9, 155], [182, 5, 24]]]
 h' := ![![[7, 189, 24, 26], [127, 190, 178, 41], [130, 116, 64, 138], [82, 109, 185, 80], [133, 114, 13, 52], [50, 152, 52, 173], [0, 0, 1], [0, 1]], ![[147, 71, 132, 103], [43, 71, 19, 106], [28, 123, 39, 110], [154, 145, 163, 70], [15, 156, 8, 35], [165, 125, 31, 64], [95, 102, 181, 98], [7, 189, 24, 26]], ![[119, 121, 35, 62], [98, 8, 185, 99], [154, 35, 181, 17], [146, 23, 57, 77], [107, 83, 189, 68], [30, 63, 183, 116], [88, 42, 76, 76], [147, 71, 132, 103]], ![[0, 1], [172, 113, 0, 136], [13, 108, 98, 117], [131, 105, 168, 155], [80, 29, 172, 36], [99, 42, 116, 29], [124, 47, 124, 17], [119, 121, 35, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 89, 106], []]
 b := ![[], [], [84, 45, 69, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [32, 49, 57, 109, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40548024052, -38672289318, -9756316620, 1148290170, 13577818620]
  a := ![-5, 2, -3, 1, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12297262772, -8946303558, -9292527420, -633780510, 13577818620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-156, -58, 40, 15, -35]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-156, -58, 40, 15, -35]] 
 ![![191, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-156, -58, 40, 15, -35], ![375, 149, -88, -35, 75], ![-795, -278, 219, 79, -195], ![864, 378, -174, -77, 144], ![-49, 14, 40, 9, -40]]]
  hmulB := by decide  
  f := ![![![12010, 2072, -2186, -645, 1711]], ![![4933, 851, -898, -265, 703]], ![![6059, 1044, -1103, -325, 863]], ![![1192, 206, -218, -65, 172]], ![![2349, 404, -428, -126, 335]]]
  g := ![![![9, -58, 40, 15, -35], ![-28, 149, -88, -35, 75], ![34, -278, 219, 79, -195], ![-88, 378, -174, -77, 144], ![-19, 14, 40, 9, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-12010, -2072, 2186, 645, -1711]] ![![-156, -58, 40, 15, -35]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0, 0, 0]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![0, 0, 0, 0, 193]] where
  M :=![![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![0, 0, 0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 5 2 7 [186, 171, 143, 112, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 109, 166, 180, 125], [42, 3, 0, 54, 42], [65, 15, 126, 158, 86], [169, 65, 94, 187, 133], [0, 1]]
 g := ![![[43, 92, 72, 106, 95], [103, 95, 113, 43], [170, 147, 173, 27], [42, 60, 53, 46], [25, 114, 92, 84], [191, 1], []], ![[8, 103, 54, 32, 90, 145, 72, 103], [174, 112, 117, 43], [4, 184, 68, 169], [180, 57, 23, 144], [180, 185, 62, 75], [18, 103, 36, 186], [149, 90, 135, 113, 29, 15, 189, 158]], ![[175, 65, 5, 115, 47, 168, 72, 143], [112, 172, 147, 128], [77, 73, 185, 32], [116, 81, 148, 32], [165, 192, 81, 143], [87, 85, 25, 14], [16, 62, 112, 114, 30, 157, 176, 169]], ![[50, 132, 4, 35, 172, 180, 80, 168], [113, 119, 182, 118], [133, 183, 71, 170], [131, 55, 130, 6], [13, 188, 177, 151], [123, 161, 71, 83], [45, 131, 0, 34, 184, 144, 3, 121]], ![[67, 125, 64, 75, 62, 80, 8, 51], [143, 77, 100, 187], [129, 36, 62, 134], [48, 15, 14, 145], [89, 179, 63, 48], [185, 97, 188, 129], [177, 137, 9, 53, 98, 96, 114, 160]]]
 h' := ![![[108, 109, 166, 180, 125], [16, 52, 12, 192, 45], [158, 88, 57, 9, 129], [133, 76, 14, 5, 42], [178, 68, 42, 138, 25], [179, 156, 115, 81, 85], [0, 0, 0, 1], [0, 1]], ![[42, 3, 0, 54, 42], [91, 3, 191, 101, 59], [113, 182, 25, 178, 64], [144, 24, 107, 118, 180], [106, 168, 95, 21, 12], [191, 162, 22, 4, 123], [79, 110, 156, 38, 46], [108, 109, 166, 180, 125]], ![[65, 15, 126, 158, 86], [95, 180, 73, 131, 104], [58, 123, 35, 100, 30], [171, 21, 53, 182, 15], [18, 182, 134, 110, 15], [54, 70, 155, 180, 23], [88, 64, 29, 93, 20], [42, 3, 0, 54, 42]], ![[169, 65, 94, 187, 133], [37, 110, 131, 192, 131], [156, 119, 16, 180, 73], [169, 53, 106, 176, 39], [105, 38, 13, 6, 44], [173, 97, 14, 173, 99], [108, 190, 153, 27, 58], [65, 15, 126, 158, 86]], ![[0, 1], [84, 41, 172, 156, 47], [137, 67, 60, 112, 90], [149, 19, 106, 98, 110], [44, 123, 102, 111, 97], [0, 94, 80, 141, 56], [153, 22, 48, 34, 69], [169, 65, 94, 187, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148, 157, 109, 109], [], [], []]
 b := ![[], [65, 20, 161, 172, 135], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 5
  hpos := by decide
  P := [186, 171, 143, 112, 2, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78792141955006919, -37914159294274787, 26187495471822743, 24201706626439830, -42526519528626019]
  a := ![51, 23, 13, 60, -197]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-408249440181383, -196446421213859, 135686505035351, 125397443660310, -220344660770083]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 267785184193 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀

instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0, 0, 0]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]] where
  M :=![![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 5 2 7 [163, 133, 113, 162, 136, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 15, 187, 4, 36], [83, 3, 141, 165, 129], [171, 145, 138, 164, 23], [19, 33, 125, 61, 9], [0, 1]]
 g := ![![[156, 114, 25, 157, 15], [13, 59, 30, 33], [36, 107, 64, 172, 134], [36, 79, 0, 132], [64, 45, 38, 169], [61, 1], []], ![[44, 68, 122, 56, 153, 102, 164, 4], [128, 43], [50, 164, 196, 70, 58, 113, 156, 160], [69, 9, 91, 121], [191, 94, 160, 92], [181, 58, 107, 33], [52, 2, 178, 107, 62, 163, 143, 164]], ![[11, 74, 155, 15, 95, 160, 143, 122], [97, 38, 94, 101], [71, 111, 192, 178, 109, 122, 142, 14], [62, 40, 132, 81], [80, 148, 99, 112], [3, 94, 151, 90], [24, 168, 101, 176, 39, 94, 96, 177]], ![[61, 83, 174, 158, 105, 173, 34, 16], [143, 185, 137, 15], [131, 100, 193, 14, 3, 149, 58, 136], [151, 185, 137, 37], [42, 129, 109, 158], [87, 145, 59, 163], [63, 179, 89, 124, 12, 124, 119, 150]], ![[101, 97, 162, 161, 81, 1, 73, 76], [61, 140, 68, 64], [148, 20, 126, 193, 34, 58, 12, 134], [56, 15, 25, 112], [180, 74, 140, 96], [101, 48, 170, 101], [93, 169, 140, 58, 122, 28, 192, 138]]]
 h' := ![![[182, 15, 187, 4, 36], [39, 177, 87, 139, 139], [42, 102, 119, 67, 69], [142, 78, 172, 108, 118], [187, 88, 34, 125, 138], [104, 195, 66, 52, 13], [0, 0, 0, 1], [0, 1]], ![[83, 3, 141, 165, 129], [166, 15, 16, 190, 66], [98, 183, 91, 35], [15, 73, 125, 153, 180], [128, 195, 72, 9, 186], [23, 93, 8, 114, 180], [166, 125, 174, 148, 128], [182, 15, 187, 4, 36]], ![[171, 145, 138, 164, 23], [110, 132, 176, 114, 2], [113, 72, 18, 102, 62], [139, 86, 116, 175, 114], [1, 137, 10, 103, 188], [165, 98, 160, 180, 30], [121, 102, 145, 90, 175], [83, 3, 141, 165, 129]], ![[19, 33, 125, 61, 9], [115, 96, 138, 87, 70], [104, 163, 2, 85, 58], [48, 146, 4, 67, 87], [6, 193, 161, 103, 49], [96, 76, 84, 96, 54], [129, 10, 76, 175, 153], [171, 145, 138, 164, 23]], ![[0, 1], [49, 171, 174, 61, 117], [158, 71, 164, 105, 8], [80, 11, 174, 88, 92], [151, 175, 117, 54, 30], [170, 129, 76, 149, 117], [171, 157, 196, 177, 135], [19, 33, 125, 61, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149, 131, 44, 158], [], [], []]
 b := ![[], [135, 47, 155, 177, 116], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 5
  hpos := by decide
  P := [163, 133, 113, 162, 136, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-166777409619504, -74858827705993, 61166621995651, 54074839360329, -95981026055310]
  a := ![16, 7, 5, 18, -63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-846585835632, -379994049269, 310490466983, 274491570357, -487213330230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 296709280757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀



lemma PB539I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB539I4 : PrimesBelowBoundCertificateInterval O 151 197 539 where
  m := 9
  g := ![2, 2, 2, 3, 3, 2, 2, 1, 1]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB539I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
    · exact ![I197N0]
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
    · exact ![3869893, 24649]
    · exact ![705911761, 163]
    · exact ![777796321, 167]
    · exact ![29929, 29929, 173]
    · exact ![32041, 32041, 179]
    · exact ![5929741, 32761]
    · exact ![1330863361, 191]
    · exact ![267785184193]
    · exact ![296709280757]
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
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
  β := ![I163N1, I167N1, I173N2, I179N2, I191N1]
  Il := ![[], [I163N1], [I167N1], [I173N2], [I179N2], [], [I191N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
