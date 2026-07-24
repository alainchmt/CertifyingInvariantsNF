
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0, 0, 0]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 0, 0, 0, 157]] where
  M :=![![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 0, 0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 5 2 7 [94, 69, 133, 136, 69, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 111, 112, 79, 49], [133, 26, 117, 134, 74], [15, 10, 51, 29, 19], [27, 9, 34, 72, 15], [0, 1]]
 g := ![![[36, 142, 132, 88, 140], [98, 102, 30, 46], [57, 93, 35, 151, 140], [9, 36, 68, 90, 130], [48, 44, 72, 88, 1], [], []], ![[49, 103, 20, 85, 135, 92, 138, 122], [149, 47, 58, 82], [131, 100, 99, 80, 74, 155, 95, 30], [146, 98, 102, 146, 59, 24, 73, 17], [43, 135, 123, 101, 45, 11, 76, 27], [69, 96, 1, 147], [103, 35, 15, 46]], ![[26, 8, 106, 148, 35, 104, 93, 88], [125, 24, 73, 109], [6, 15, 25, 103, 16, 132, 102, 137], [128, 10, 41, 99, 110, 118, 88, 84], [87, 125, 122, 149, 45, 130, 146, 38], [138, 147, 91, 16], [20, 153, 105, 138]], ![[25, 151, 58, 152, 39, 83, 150, 3], [85, 102, 101, 10], [122, 90, 136, 72, 22, 74, 55, 13], [4, 6, 149, 153, 137, 34, 129, 3], [146, 89, 147, 112, 17, 111, 146, 30], [14, 35, 15, 138], [73, 147, 57, 47]], ![[102, 104, 109, 6, 51, 87, 91, 2], [56, 65, 77, 36], [127, 112, 143, 19, 129, 68, 106, 85], [124, 74, 27, 21, 123, 151, 3, 85], [151, 35, 104, 11, 142, 83, 85, 74], [112, 31, 1, 90], [147, 63, 137, 68]]]
 h' := ![![[70, 111, 112, 79, 49], [137, 21, 79, 89, 53], [137, 152, 125, 41, 108], [96, 31, 126, 60, 104], [41, 88, 140, 128, 82], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[133, 26, 117, 134, 74], [113, 112, 90, 113, 106], [60, 41, 155, 156, 125], [133, 101, 133, 87, 73], [109, 23, 133, 93, 55], [111, 8, 75, 47, 14], [85, 119, 115, 127, 124], [70, 111, 112, 79, 49]], ![[15, 10, 51, 29, 19], [131, 72, 58, 68, 77], [109, 38, 42, 152, 57], [34, 4, 46, 112, 12], [20, 87, 67, 136, 20], [8, 56, 17, 116, 154], [109, 103, 76, 12, 4], [133, 26, 117, 134, 74]], ![[27, 9, 34, 72, 15], [84, 79, 35, 128, 23], [58, 96, 150, 131, 18], [100, 57, 151, 140, 102], [133, 116, 138, 31, 134], [62, 122, 89, 152, 100], [114, 128, 127, 13, 83], [15, 10, 51, 29, 19]], ![[0, 1], [62, 30, 52, 73, 55], [50, 144, 156, 148, 6], [75, 121, 15, 72, 23], [18, 0, 150, 83, 23], [58, 128, 133, 156, 45], [99, 121, 152, 5, 103], [27, 9, 34, 72, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 44, 95, 148], [], [], []]
 b := ![[], [47, 59, 96, 9, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 5
  hpos := by decide
  P := [94, 69, 133, 136, 69, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81790950162, -56304289850, 2137044593, -57127366589, -53199257832]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-520961466, -358626050, 13611749, -363868577, -338848776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 95388992557 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0, 0, 0]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]] where
  M :=![![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 5 2 7 [63, 47, 147, 78, 138, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 79, 67, 89, 97], [79, 142, 22, 8, 147], [44, 37, 15, 13, 147], [47, 67, 59, 53, 98], [0, 1]]
 g := ![![[23, 46, 71, 134, 51], [60, 2, 87, 71, 71], [66, 38, 21, 24], [110, 23, 135, 100], [88, 76, 152, 136], [1], []], ![[80, 38, 109, 153, 43, 29, 6, 104], [52, 29, 119, 127, 56, 91, 161, 39], [79, 24, 19, 144], [83, 143, 7, 135], [110, 108, 13, 132], [76, 139, 21, 153, 53, 6, 88, 95], [159, 79, 4, 118]], ![[29, 80, 61, 129, 97, 5, 90, 137], [155, 136, 30, 101, 104, 146, 130, 141], [111, 162, 90, 65], [68, 63, 6, 134], [145, 145, 161, 16], [151, 24, 64, 25, 148, 116, 26, 18], [144, 147, 113, 93]], ![[61, 135, 121, 122, 95, 132, 26, 120], [154, 105, 36, 157, 103, 140, 112, 106], [152, 1, 33, 71], [47, 80, 157, 83], [14, 139, 17, 33], [110, 23, 22, 157, 2, 103, 97, 99], [42, 62, 116, 93]], ![[11, 91, 128, 88, 33, 40, 22, 98], [152, 60, 48, 3, 151, 6, 36, 137], [24, 97, 147, 38], [136, 24, 51, 25], [42, 65, 38, 6], [150, 68, 44, 141, 39, 55, 30, 148], [53, 131, 120, 150]]]
 h' := ![![[18, 79, 67, 89, 97], [132, 3, 94, 0, 41], [129, 53, 46, 66, 76], [7, 82, 147, 8, 137], [55, 95, 26, 4, 10], [100, 116, 16, 85, 25], [0, 0, 1], [0, 1]], ![[79, 142, 22, 8, 147], [59, 82, 111, 98, 149], [125, 143, 126, 141, 36], [156, 59, 94, 7, 12], [150, 9, 145, 57, 102], [76, 22, 55, 114, 135], [87, 11, 60, 83, 30], [18, 79, 67, 89, 97]], ![[44, 37, 15, 13, 147], [94, 102, 12, 157, 115], [162, 33, 138, 25, 12], [31, 60, 114, 96, 37], [27, 4, 125, 1, 121], [69, 66, 1, 72, 4], [103, 50, 17, 13, 68], [79, 142, 22, 8, 147]], ![[47, 67, 59, 53, 98], [154, 119, 30, 161, 20], [77, 147, 5, 115, 25], [157, 12, 105, 138, 87], [64, 58, 4, 28, 88], [91, 1, 54, 122, 149], [105, 147, 148, 69, 161], [44, 37, 15, 13, 147]], ![[0, 1], [65, 20, 79, 73, 1], [43, 113, 11, 142, 14], [96, 113, 29, 77, 53], [158, 160, 26, 73, 5], [149, 121, 37, 96, 13], [11, 118, 100, 161, 67], [47, 67, 59, 53, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 99, 149, 44], [], [], []]
 b := ![[], [62, 29, 134, 40, 55], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 5
  hpos := by decide
  P := [63, 47, 147, 78, 138, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6894125296884450, -4737652404846110, 162651960148644, -4840583294975738, -4387782452972742]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42295247220150, -29065352176970, 997864786188, -29696830030526, -26918910754434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 115063617043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

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


def P167P0 : CertificateIrreducibleZModOfList' 167 5 2 7 [143, 129, 54, 130, 121, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 122, 13, 6, 65], [146, 76, 112, 47, 116], [123, 10, 59, 127, 141], [18, 125, 150, 154, 12], [0, 1]]
 g := ![![[150, 150, 110, 31, 66], [3, 107, 101, 88, 121], [103, 59, 121, 73, 88], [158, 46, 32, 66], [118, 1, 39, 112], [1], []], ![[145, 6, 166, 64, 93, 88, 72, 24], [16, 119, 142, 83, 80, 80, 13, 112], [75, 94, 160, 11, 61, 7, 62, 14], [74, 1, 69, 3], [116, 96, 110, 28], [138, 156, 97, 134, 91, 41, 152, 57], [128, 133, 74, 50]], ![[90, 115, 130, 60, 141, 103, 32, 162], [4, 130, 148, 68, 116, 2, 55, 63], [121, 114, 32, 54, 102, 113, 158, 9], [35, 157, 58, 89], [16, 96, 114, 65], [93, 98, 160, 4, 94, 138, 157, 21], [76, 162, 123, 96]], ![[138, 105, 160, 32, 44, 117, 32, 11], [79, 41, 30, 20, 99, 138, 86, 116], [74, 1, 162, 149, 98, 120, 100, 100], [81, 85, 98, 150], [155, 1, 40, 24], [163, 13, 29, 47, 9, 6, 88, 7], [59, 47, 110, 8]], ![[158, 14, 88, 145, 9, 58, 65, 63], [146, 15, 79, 36, 32, 75, 91, 16], [64, 23, 76, 12, 25, 59, 83, 124], [136, 162, 59, 38], [136, 114, 33, 100], [52, 21, 72, 30, 55, 33, 86, 63], [79, 18, 133, 144]]]
 h' := ![![[93, 122, 13, 6, 65], [72, 97, 149, 96, 147], [134, 0, 142, 82, 156], [66, 27, 46, 12, 64], [68, 153, 134, 142, 20], [24, 38, 113, 37, 46], [0, 0, 1], [0, 1]], ![[146, 76, 112, 47, 116], [148, 75, 57, 107, 76], [21, 117, 17, 156, 43], [125, 151, 132, 19, 98], [112, 32, 139, 122, 62], [0, 68, 43, 47, 23], [31, 20, 19, 9, 58], [93, 122, 13, 6, 65]], ![[123, 10, 59, 127, 141], [40, 85, 109, 138, 34], [75, 160, 41, 126, 40], [33, 82, 120, 120, 149], [144, 80, 161, 20, 16], [42, 14, 79, 30, 30], [94, 77, 64, 60, 103], [146, 76, 112, 47, 116]], ![[18, 125, 150, 154, 12], [104, 3, 159, 20, 138], [100, 83, 144, 94, 25], [92, 9, 152, 155, 3], [94, 43, 140, 20, 22], [81, 72, 2, 106, 58], [12, 152, 156, 33, 112], [123, 10, 59, 127, 141]], ![[0, 1], [124, 74, 27, 140, 106], [89, 141, 157, 43, 70], [119, 65, 51, 28, 20], [23, 26, 94, 30, 47], [44, 142, 97, 114, 10], [49, 85, 94, 65, 61], [18, 125, 150, 154, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 90, 153, 31], [], [], []]
 b := ![[], [5, 33, 104, 12, 110], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 5
  hpos := by decide
  P := [143, 129, 54, 130, 121, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46219546918, -31575295208, 693301502, -33028070626, -27225909132]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-276763754, -189073624, 4151506, -197772878, -163029396]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10319, 7855, 20178, 717, -4997]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-10319, 7855, 20178, 717, -4997]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![29, 90, 92, 131, 1]] where
  M :=![![![-10319, 7855, 20178, 717, -4997], ![-39976, -15843, 14276, 4660, -2846], ![-11384, -22295, -20503, 1985, 5567], ![42256, 4903, -31418, -4341, 7184], ![12328, -1477, -13220, -1306, 3211]]]
  hmulB := by decide  
  f := ![![![1037, 629, 36, 699, 545]], ![![4360, 3099, -140, 3188, 2642]], ![![10568, 7121, -89, 7513, 6103]], ![![22232, 15191, -322, 15921, 13000]], ![![25189, 17207, -362, 18036, 14726]]]
  g := ![![![778, 2645, 2774, 3788, -4997], ![246, 1389, 1596, 2182, -2846], ![-999, -3025, -3079, -4204, 5567], ![-960, -3709, -4002, -5465, 7184], ![-467, -1679, -1784, -2439, 3211]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [130, 123, 120, 110, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 111, 53, 67], [21, 137, 46, 98], [128, 97, 74, 8], [0, 1]]
 g := ![![[171, 20, 129, 130], [113, 146, 54], [153, 96, 69, 51], [8, 3, 88, 167], [72, 7, 119], [63, 1], []], ![[100, 76, 5, 164, 146, 15], [48, 155, 149], [76, 72, 130, 145, 33, 14], [165, 80, 4, 43, 11, 1], [39, 91, 24], [15, 35, 138, 64, 145, 77], [44, 134, 164]], ![[1, 119, 78, 67, 41, 68], [100, 126, 24], [59, 101, 8, 36, 89, 12], [26, 157, 122, 92, 48, 71], [49, 152, 169], [13, 125, 38, 122, 32, 171], [147, 91, 89]], ![[17, 107, 56, 28, 115, 105], [139, 36, 38], [22, 55, 115, 103, 5, 82], [68, 119, 157, 87, 42, 5], [112, 23, 40], [19, 15, 170, 56, 171, 82], [121, 26, 64]]]
 h' := ![![[87, 111, 53, 67], [40, 171, 70, 87], [5, 18, 57, 20], [171, 19, 31, 33], [3, 115, 28, 101], [114, 79, 102, 43], [0, 0, 1], [0, 1]], ![[21, 137, 46, 98], [28, 6, 59, 130], [127, 153, 16, 144], [130, 118, 92, 112], [157, 34, 117, 66], [27, 17, 57, 71], [119, 115, 86, 151], [87, 111, 53, 67]], ![[128, 97, 74, 8], [27, 80, 129, 6], [15, 36, 134, 71], [81, 166, 146, 141], [44, 62, 31, 130], [94, 74, 122, 13], [15, 63, 20, 135], [21, 137, 46, 98]], ![[0, 1], [96, 89, 88, 123], [172, 139, 139, 111], [11, 43, 77, 60], [26, 135, 170, 49], [20, 3, 65, 46], [135, 168, 66, 60], [128, 97, 74, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [96, 152, 65], []]
 b := ![[], [], [106, 84, 27, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [130, 123, 120, 110, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44421457404, 32246946157, -4708669423, 25882505020, 48456877791]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7866057795, -25022381821, -25796193215, -36543170437, 48456877791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1037, 629, 36, 699, 545]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![1037, 629, 36, 699, 545]] 
 ![![173, 0, 0, 0, 0], ![125, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![1037, 629, 36, 699, 545], ![4360, 3099, -140, 3188, 2642], ![10568, 7121, -89, 7513, 6103], ![22232, 15191, -322, 15921, 13000], ![50576, 34507, -700, 36190, 29537]]]
  hmulB := by decide  
  f := ![![![-10319, 7855, 20178, 717, -4997]], ![![-7687, 5584, 14662, 545, -3627]], ![![-3585, 2550, 6763, 256, -1672]], ![![-3096, 2571, 6350, 207, -1576]], ![![-4283, 3306, 8438, 295, -2090]]]
  g := ![![![-917, 629, 36, 699, 545], ![-4313, 3099, -140, 3188, 2642], ![-10061, 7121, -89, 7513, 6103], ![-21377, 15191, -322, 15921, 13000], ![-48580, 34507, -700, 36190, 29537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-10319, 7855, 20178, 717, -4997]] ![![1037, 629, 36, 699, 545]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175, -99, -9, -114, -87]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-175, -99, -9, -114, -87]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![89, 22, 1, 0, 0], ![11, 98, 0, 1, 0], ![36, 105, 0, 0, 1]] where
  M :=![![![-175, -99, -9, -114, -87], ![-696, -505, 30, -513, -429], ![-1716, -1149, 8, -1215, -984], ![-3588, -2454, 51, -2572, -2100], ![-8172, -5574, 111, -5847, -4771]]]
  hmulB := by decide  
  f := ![![![259, 144, 45, 300, -159]], ![![-1272, -791, -312, -1323, 741]], ![![-11, -16, -13, 3, 3]], ![![-713, -443, -174, -739, 414]], ![![-648, -408, -165, -669, 377]]]
  g := ![![![28, 114, -9, -114, -87], ![99, 526, 30, -513, -429], ![259, 1235, 8, -1215, -984], ![535, 2620, 51, -2572, -2100], ![1218, 5955, 111, -5847, -4771]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [51, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 178], [0, 1]]
 g := ![![[55, 172], [22, 48], [110], [68], [60, 110], [134, 80], [1]], ![[0, 7], [169, 131], [110], [68], [106, 69], [21, 99], [1]]]
 h' := ![![[59, 178], [131, 107], [177, 76], [43, 17], [162, 28], [147, 162], [128, 59], [0, 1]], ![[0, 1], [0, 72], [7, 103], [151, 162], [24, 151], [39, 17], [29, 120], [59, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [128, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [51, 120, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4772, -1544, -1138, -5064, 6048]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-366, -644, -1138, -5064, 6048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, 39, -69, -13, 14]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![135, 39, -69, -13, 14]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![125, 58, 1, 0, 0], ![89, 100, 0, 1, 0], ![133, 113, 0, 0, 1]] where
  M :=![![![135, 39, -69, -13, 14], ![112, 149, 104, -27, -25], ![-100, 59, 176, 30, -53], ![-268, -184, -23, -11, 31], ![-36, -14, 29, 68, -34]]]
  hmulB := by decide  
  f := ![![![621, 480, -45, 475, 406]], ![![3248, 2131, 10, 2277, 1831]], ![![1527, 1054, -29, 1099, 901]], ![![2211, 1489, -18, 1571, 1276]], ![![2711, 1838, -30, 1933, 1574]]]
  g := ![![![45, 21, -69, -13, 14], ![-40, -2, 104, -27, -25], ![-99, -40, 176, 30, -53], ![-3, -7, -23, -11, 31], ![-29, -26, 29, 68, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [79, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 178], [0, 1]]
 g := ![![[169, 5], [83, 43], [108], [135], [162, 19], [90, 106], [1]], ![[2, 174], [43, 136], [108], [135], [136, 160], [58, 73], [1]]]
 h' := ![![[74, 178], [66, 149], [140, 143], [120, 65], [90, 99], [50, 52], [100, 74], [0, 1]], ![[0, 1], [173, 30], [161, 36], [97, 114], [77, 80], [139, 127], [27, 105], [74, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [90, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [79, 105, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10481, -7540, -2224, -13918, 8142]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2365, 3314, -2224, -13918, 8142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 3, 0, 4, -2]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![3, 3, 0, 4, -2]] 
 ![![179, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![3, 3, 0, 4, -2], ![-16, -11, -2, -18, 10], ![40, 25, 7, 42, -22], ![-80, -47, -16, -82, 47], ![120, 71, 22, 121, -62]]]
  hmulB := by decide  
  f := ![![![129, -87, -294, -16, 74]], ![![17, -8, -32, -2, 8]], ![![64, -41, -143, -8, 36]], ![![97, -68, -226, -12, 57]], ![![90, -61, -206, -11, 52]]]
  g := ![![![-2, 3, 0, 4, -2], ![9, -11, -2, -18, 10], ![-23, 25, 7, 42, -22], ![43, -47, -16, -82, 47], ![-68, 71, 22, 121, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-175, -99, -9, -114, -87]] ![![135, 39, -69, -13, 14]]
  ![![-129, 87, 294, 16, -74]] where
 M := ![![![-129, 87, 294, 16, -74]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-129, 87, 294, 16, -74]] ![![3, 3, 0, 4, -2]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 17, -53, -6, 19]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-53, 17, -53, -6, 19]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![91, 43, 137, 1, 0], ![45, 24, 50, 0, 1]] where
  M :=![![![-53, 17, -53, -6, 19], ![152, -5, 46, 33, 1], ![4, 85, -38, 33, 50], ![124, 94, 29, 104, 74], ![292, 226, -7, 225, 187]]]
  hmulB := by decide  
  f := ![![![31, 20, 7, 30, -17]], ![![-136, -77, -20, -135, 73]], ![![292, 172, 58, 303, -166]], ![![201, 120, 42, 209, -115]], ![![75, 45, 16, 78, -43]]]
  g := ![![![-2, -1, -1, -6, 19], ![-16, -8, -25, 33, 1], ![-29, -14, -39, 33, 50], ![-70, -34, -99, 104, 74], ![-158, -77, -222, 225, 187]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [10, 23, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 36, 100], [23, 144, 81], [0, 1]]
 g := ![![[131, 124, 45], [], [119, 84, 111], [94, 121], [147, 87, 56], [15, 161, 1], []], ![[21, 72, 138, 33], [120, 156], [101, 35, 55, 55], [22, 111], [71, 67, 88, 132], [51, 171, 36, 64], [146, 45]], ![[15, 103, 119, 27], [29, 156], [44, 46, 40, 122], [157, 138], [50, 0, 40, 136], [71, 20, 47, 177], [165, 45]]]
 h' := ![![[138, 36, 100], [137, 92, 100], [77, 10], [87, 27, 103], [159, 149, 170], [31, 36, 150], [0, 0, 1], [0, 1]], ![[23, 144, 81], [148, 169, 70], [9, 179, 95], [78, 104, 156], [152, 39, 103], [180, 111, 41], [27, 155, 144], [138, 36, 100]], ![[0, 1], [20, 101, 11], [126, 173, 86], [180, 50, 103], [170, 174, 89], [134, 34, 171], [146, 26, 36], [23, 144, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 27], []]
 b := ![[], [105, 90, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [10, 23, 20, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![627142, 197719, 487360, 1163530, -2354232]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3792, 36837, -227650, 1163530, -2354232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 20, 7, 30, -17]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![31, 20, 7, 30, -17]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![157, 44, 1, 0, 0], ![151, 134, 0, 1, 0], ![127, 115, 0, 0, 1]] where
  M :=![![![31, 20, 7, 30, -17], ![-136, -77, -20, -135, 73], ![292, 172, 58, 303, -166], ![-596, -353, -121, -607, 335], ![844, 493, 161, 858, -470]]]
  hmulB := by decide  
  f := ![![![-53, 17, -53, -6, 19]], ![![152, -5, 46, 33, 1]], ![![-9, 14, -35, 3, 17]], ![![69, 11, -10, 20, 17]], ![![61, 10, -8, 18, 15]]]
  g := ![![![-19, -13, 7, 30, -17], ![78, 58, -20, -135, 73], ![-185, -132, 58, 303, -166], ![373, 264, -121, -607, 335], ![-521, -373, 161, 858, -470]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [9, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 180], [0, 1]]
 g := ![![[70, 161], [108], [38, 82], [55], [63, 13], [93, 148], [1]], ![[0, 20], [108], [144, 99], [55], [18, 168], [68, 33], [1]]]
 h' := ![![[94, 180], [152, 60], [20, 164], [81, 156], [157, 112], [68, 70], [172, 94], [0, 1]], ![[0, 1], [0, 121], [51, 17], [84, 25], [6, 69], [132, 111], [139, 87], [94, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [17, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [9, 87, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-77, -164, -25, -303, 144]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![173, 138, -25, -303, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-53, 17, -53, -6, 19]] ![![31, 20, 7, 30, -17]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1265159, 214674, -847624, -135409, 192189]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![1265159, 214674, -847624, -135409, 192189]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![146, 173, 23, 18, 1]] where
  M :=![![![1265159, 214674, -847624, -135409, 192189], ![1537512, 1513889, 700166, -214516, -214038], ![-856152, 691002, 1728405, 58291, -428793], ![-2483928, -1421946, 282628, 305742, -19941], ![-939416, -377600, 328076, 109245, -64760]]]
  hmulB := by decide  
  f := ![![![-13175, 4200, -8288, -2231, 2583]], ![![20664, -6317, 12862, 3736, -4110]], ![![-16440, 4620, -10053, -3391, 3549]], ![![3864, 480, 1580, 2196, -1257]], ![![6998, -1909, 4237, 1462, -1427]]]
  g := ![![![-140285, -172953, -27581, -18821, 192189], ![171660, 201793, 29440, 19048, -214038], ![323286, 392001, 60684, 40715, -428793], ![2238, 10617, 3881, 3480, -19941], ![44584, 56680, 9516, 6675, -64760]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [118, 60, 129, 189, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 118, 72, 171], [151, 79, 141, 181], [163, 184, 169, 30], [0, 1]]
 g := ![![[103, 4, 187, 163], [116, 2, 102, 79], [74, 175, 190, 156], [147, 6, 135, 67], [108, 122, 161, 154], [2, 1], []], ![[182, 167, 172, 63, 4, 151], [76, 21, 153, 183, 83, 56], [190, 165, 34, 91, 94, 173], [67, 72, 175, 108, 100, 41], [181, 164, 166, 190, 166, 137], [108, 43, 64, 180, 34, 105], [94, 21, 18]], ![[143, 91, 32, 95, 168, 131], [36, 125, 153, 13, 62, 111], [152, 77, 2, 48, 138, 29], [108, 1, 148, 155, 125, 173], [79, 139, 57, 115, 40, 124], [32, 176, 149, 22, 155, 14], [161, 54, 100]], ![[75, 167, 177, 3, 2, 162], [142, 119, 131, 149, 105, 125], [26, 16, 36, 94, 85, 13], [160, 113, 76, 101, 139, 104], [159, 171, 110, 72, 172, 170], [15, 121, 22, 158, 14, 65], [97, 98, 136]]]
 h' := ![![[70, 118, 72, 171], [64, 113, 127, 113], [54, 10, 39, 156], [35, 157, 118, 27], [53, 58, 79, 81], [146, 144, 64, 66], [0, 0, 1], [0, 1]], ![[151, 79, 141, 181], [50, 119, 5, 134], [38, 93, 186, 155], [47, 143, 170, 28], [55, 186, 77, 165], [158, 136, 48, 99], [111, 189, 90, 86], [70, 118, 72, 171]], ![[163, 184, 169, 30], [64, 72, 20, 31], [149, 36, 171, 77], [111, 113, 143, 178], [84, 29, 177, 123], [135, 28, 115, 8], [174, 186, 26, 120], [151, 79, 141, 181]], ![[0, 1], [5, 78, 39, 104], [88, 52, 177, 185], [137, 160, 142, 149], [90, 109, 49, 13], [51, 74, 155, 18], [34, 7, 74, 176], [163, 184, 169, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [185, 148, 8], []]
 b := ![[], [], [73, 102, 162, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [118, 60, 129, 189, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-195564749, -115273291, -36862067, -198330755, 106500561]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-82432705, -97067384, -13017670, -11075083, 106500561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13175, 4200, -8288, -2231, 2583]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-13175, 4200, -8288, -2231, 2583]] 
 ![![191, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![111, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![-13175, 4200, -8288, -2231, 2583], ![20664, -6317, 12862, 3736, -4110], ![-16440, 4620, -10053, -3391, 3549], ![3864, 480, 1580, 2196, -1257], ![-6136, 122, -3032, -2895, 2354]]]
  hmulB := by decide  
  f := ![![![1265159, 214674, -847624, -135409, 192189]], ![![908896, 160783, -599878, -97540, 135726]], ![![730767, 128376, -483549, -78388, 109446]], ![![145968, 19530, -105028, -15414, 24045]], ![![379266, 63212, -255676, -40547, 58022]]]
  g := ![![![1253, 4200, -8288, -2231, 2583], ![-2090, -6317, 12862, 3736, -4110], ![1815, 4620, -10053, -3391, 3549], ![-1134, 480, 1580, 2196, -1257], ![1292, 122, -3032, -2895, 2354]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![1265159, 214674, -847624, -135409, 192189]] ![![-13175, 4200, -8288, -2231, 2583]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -23, -11, -19, 16]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-17, -23, -11, -19, 16]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![11, 83, 132, 35, 1]] where
  M :=![![![-17, -23, -11, -19, 16], ![128, 71, -8, 109, -41], ![-164, -97, -38, -206, 143], ![508, 324, 113, 511, -217], ![-476, -258, -115, -532, 448]]]
  hmulB := by decide  
  f := ![![![7, 0, 7, 1, -2]], ![![-16, 3, -2, -1, 1]], ![![4, -6, 4, 2, -1]], ![![4, -1, -7, 0, 2]], ![![-3, -3, 1, 1, 0]]]
  g := ![![![-1, -7, -11, -3, 16], ![3, 18, 28, 8, -41], ![-9, -62, -98, -27, 143], ![15, 95, 149, 42, -217], ![-28, -194, -307, -84, 448]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [162, 93, 86, 117, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 74, 101, 14], [34, 10, 57, 15], [25, 108, 35, 164], [0, 1]]
 g := ![![[13, 109, 135, 187], [180, 127, 129], [149, 48, 187], [118, 41, 83], [48, 110, 107], [93, 76, 1], []], ![[168, 171, 53, 80, 68, 144], [131, 41, 192], [155, 15, 9], [42, 79, 27], [80, 15, 23], [187, 114, 126], [96, 161, 153, 105, 48, 42]], ![[125, 149, 19, 140, 85, 154], [175, 135, 138], [59, 36, 32], [122, 187, 191], [130, 61, 96], [192, 189, 186], [70, 118, 160, 113, 71, 94]], ![[166, 179, 42, 5, 9, 102], [134, 15, 49], [168, 98, 175], [191, 142, 131], [19, 85, 1], [168, 148, 169], [129, 0, 144, 72, 112, 122]]]
 h' := ![![[17, 74, 101, 14], [151, 41, 90, 103], [19, 145, 189, 124], [15, 44, 80, 90], [88, 17, 69, 135], [181, 76, 19, 53], [0, 0, 0, 1], [0, 1]], ![[34, 10, 57, 15], [155, 137, 37, 38], [98, 16, 10, 112], [120, 137, 15, 190], [180, 102, 181, 42], [4, 185, 19, 122], [169, 5, 185, 133], [17, 74, 101, 14]], ![[25, 108, 35, 164], [71, 43, 47, 187], [67, 164, 184, 157], [19, 33, 126, 15], [167, 4, 110, 34], [24, 104, 54, 17], [172, 176, 140, 46], [34, 10, 57, 15]], ![[0, 1], [93, 165, 19, 58], [125, 61, 3, 186], [163, 172, 165, 91], [178, 70, 26, 175], [174, 21, 101, 1], [131, 12, 61, 13], [25, 108, 35, 164]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [164, 163, 147], []]
 b := ![[], [], [19, 81, 151, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [162, 93, 86, 117, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-243063297, -104401572, -127478016, -363813198, 580008279]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34316862, -249974553, -397350108, -107067891, 580008279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 0, -7, -1, 2]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-7, 0, -7, -1, 2]] 
 ![![193, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![172, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![165, 0, 0, 0, 1]] where
  M :=![![![-7, 0, -7, -1, 2], ![16, -3, 2, 1, -1], ![-4, 6, -4, -2, 1], ![-4, 1, 7, 0, -2], ![-4, 1, 1, -1, -1]]]
  hmulB := by decide  
  f := ![![![17, 23, 11, 19, -16]], ![![7, 10, 5, 8, -7]], ![![16, 21, 10, 18, -15]], ![![6, 10, 5, 7, -7]], ![![17, 21, 10, 19, -16]]]
  g := ![![![5, 0, -7, -1, 2], ![0, -3, 2, 1, -1], ![1, 6, -4, -2, 1], ![-5, 1, 7, 0, -2], ![0, 1, 1, -1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-17, -23, -11, -19, 16]] ![![-7, 0, -7, -1, 2]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 97, 2, 104, 84]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![149, 97, 2, 104, 84]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![1, 45, 158, 1, 0], ![92, 187, 53, 0, 1]] where
  M :=![![![149, 97, 2, 104, 84], ![672, 467, -14, 488, 396], ![1584, 1075, -21, 1128, 930], ![3384, 2309, -46, 2426, 1959], ![7632, 5211, -112, 5455, 4484]]]
  hmulB := by decide  
  f := ![![![-47, -39, 4, 8, 0]], ![![0, -51, -94, 0, 24]], ![![96, 13, -51, -10, 12]], ![![77, -1, -62, -8, 15]], ![![4, -63, -101, 1, 26]]]
  g := ![![![-39, -103, -106, 104, 84], ![-184, -485, -498, 488, 396], ![-432, -1135, -1155, 1128, 930], ![-910, -2402, -2473, 2426, 1959], ![-2083, -5476, -5582, 5455, 4484]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [119, 35, 153, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 56, 79], [82, 140, 118], [0, 1]]
 g := ![![[146, 129, 70], [1, 96], [30, 88, 143], [3, 144], [134, 100], [152, 163], [1]], ![[15, 151, 196, 111], [75, 33], [61, 57, 20, 122], [49, 22], [158, 88], [176, 146], [162, 95, 130, 145]], ![[40, 156, 125, 147], [90, 121], [177, 61, 73, 72], [158, 174], [18, 70], [132, 23], [69, 113, 59, 52]]]
 h' := ![![[159, 56, 79], [63, 111, 142], [173, 194, 80], [129, 54, 52], [180, 7, 12], [13, 161, 10], [78, 162, 44], [0, 1]], ![[82, 140, 118], [165, 155, 84], [182, 177, 128], [28, 47, 120], [46, 99, 66], [112, 71, 132], [119, 52, 46], [159, 56, 79]], ![[0, 1], [124, 128, 168], [183, 23, 186], [153, 96, 25], [162, 91, 119], [48, 162, 55], [28, 180, 107], [82, 140, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 153], []]
 b := ![[], [136, 3, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [119, 35, 153, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![611, 355, -2283, -1973, 8619]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4012, -7729, -748, -1973, 8619]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -39, 4, 8, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-47, -39, 4, 8, 0]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![185, 39, 1, 0, 0], ![74, 148, 0, 1, 0], ![150, 126, 0, 0, 1]] where
  M :=![![![-47, -39, 4, 8, 0], ![0, -51, -94, 0, 24], ![96, 13, -51, -10, 12], ![48, 83, 70, -4, -21], ![24, 25, 16, -9, -2]]]
  hmulB := by decide  
  f := ![![![149, 97, 2, 104, 84]], ![![672, 467, -14, 488, 396]], ![![281, 189, -1, 200, 162]], ![![578, 399, -10, 418, 339]], ![![582, 399, -8, 419, 340]]]
  g := ![![![-7, -7, 4, 8, 0], ![70, 3, -94, 0, 24], ![43, 10, -51, -10, 12], ![-48, 3, 70, -4, -21], ![-10, 5, 16, -9, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [104, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [157, 196], [0, 1]]
 g := ![![[61, 36], [76], [196, 29], [169], [171], [96], [157, 1]], ![[0, 161], [76], [21, 168], [169], [171], [96], [117, 196]]]
 h' := ![![[157, 196], [154, 191], [104, 43], [8, 134], [144, 184], [1, 163], [23, 117], [0, 1]], ![[0, 1], [0, 6], [157, 154], [164, 63], [73, 13], [179, 34], [71, 80], [157, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [195]]
 b := ![[], [177, 196]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [104, 40, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![337, -804, -1718, -164, 496]
  a := ![7, -1, -26, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1299, 142, -1718, -164, 496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![149, 97, 2, 104, 84]] ![![-47, -39, 4, 8, 0]]
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


lemma PB1072I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB1072I4 : PrimesBelowBoundCertificateInterval O 151 197 1072 where
  m := 9
  g := ![1, 1, 1, 2, 3, 2, 2, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1072I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
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
    · exact ![95388992557]
    · exact ![115063617043]
    · exact ![129891985607]
    · exact ![895745041, 173]
    · exact ![32041, 32041, 179]
    · exact ![5929741, 32761]
    · exact ![1330863361, 191]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
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
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I173N1, I179N2, I191N1, I193N1]
  Il := ![[], [], [], [I173N1], [I179N2], [], [I191N1], [I193N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
