
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57369, 5837, -6572, 4529, -5098]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![57369, 5837, -6572, 4529, -5098]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![150, 48, 123, 146, 1]] where
  M :=![![![57369, 5837, -6572, 4529, -5098], ![-101960, -10379, 11674, -8046, 9058], ![90580, 9205, -10379, 7145, -8046], ![-29480, -2986, 3368, -2333, 2616], ![26160, 2640, -2986, 2060, -2333]]]
  hmulB := by decide  
  f := ![![![-9, -3, 2, -1, 0]], ![![0, -7, -6, 4, -2]], ![![-20, -15, -7, -5, 4]], ![![40, 14, -12, -11, -4]], ![![10, -3, -13, -11, -1]]]
  g := ![![![4131, 1259, 3118, 3763, -5098], ![-7340, -2237, -5540, -6686, 9058], ![6520, 1987, 4921, 5939, -8046], ![-2120, -646, -1600, -1931, 2616], ![1890, 576, 1427, 1722, -2333]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 4 2 7 [131, 97, 186, 115, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [121, 19, 181, 79], [60, 74, 92, 24], [102, 105, 125, 96], [0, 1]]
 g := ![![[192, 127, 59, 112], [129, 96, 150, 32], [45, 19, 137, 94], [148, 54, 182], [58, 41, 2], [104, 84, 1], []], ![[125, 111, 82, 50, 186, 178], [2, 85, 90, 151, 167, 45], [49, 53, 42, 142, 57, 91], [13, 185, 98], [179, 34, 13], [186, 18, 100], [155, 159, 41, 189, 85, 116]], ![[12, 1, 191, 87, 187, 30], [18, 6, 14, 198, 190, 189], [155, 1, 86, 167, 71, 19], [179, 82, 56], [50, 152, 46], [43, 70, 46], [104, 192, 131, 194, 26, 93]], ![[121, 80, 28, 109, 72, 69], [123, 61, 88, 71, 87, 198], [17, 25, 54, 147, 8, 185], [191, 148, 47], [63, 91, 46], [99, 22, 103], [95, 68, 170, 173, 47, 181]]]
 h' := ![![[121, 19, 181, 79], [16, 38, 8, 50], [75, 40, 111, 80], [39, 166, 6, 166], [70, 177, 74, 88], [107, 2, 38, 179], [0, 0, 0, 1], [0, 1]], ![[60, 74, 92, 24], [59, 187, 92, 154], [153, 130, 57, 129], [174, 23, 176, 141], [22, 87, 80, 140], [63, 177, 157, 150], [56, 86, 41, 189], [121, 19, 181, 79]], ![[102, 105, 125, 96], [159, 99, 38, 161], [80, 134, 190, 111], [84, 121, 25, 93], [161, 168, 190, 102], [187, 6, 1, 134], [192, 198, 20, 134], [60, 74, 92, 24]], ![[0, 1], [98, 74, 61, 33], [14, 94, 40, 78], [58, 88, 191, 197], [123, 165, 54, 68], [60, 14, 3, 134], [33, 114, 138, 74], [102, 105, 125, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [53, 115, 30], []]
 b := ![[], [], [143, 136, 105, 148], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 4
  hpos := by decide
  P := [131, 97, 186, 115, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7896711, 6356209, 1861293, -1063890, -190983]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![183639, 78007, 127398, 134772, -190983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 1568239201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 3, -2, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![9, 3, -2, 1, 0]] 
 ![![199, 0, 0, 0, 0], ![106, 1, 0, 0, 0], ![153, 0, 1, 0, 0], ![196, 0, 0, 1, 0], ![159, 0, 0, 0, 1]] where
  M :=![![![9, 3, -2, 1, 0], ![0, 7, 6, -4, 2], ![20, 15, 7, 5, -4], ![-40, -14, 12, 11, 4], ![40, 10, -14, 10, 11]]]
  hmulB := by decide  
  f := ![![![-57369, -5837, 6572, -4529, 5098]], ![![-30046, -3057, 3442, -2372, 2670]], ![![-44563, -4534, 5105, -3518, 3960]], ![![-56356, -5734, 6456, -4449, 5008]], ![![-45969, -4677, 5266, -3629, 4085]]]
  g := ![![![-1, 3, -2, 1, 0], ![-6, 7, 6, -4, 2], ![-15, 15, 7, 5, -4], ![-16, -14, 12, 11, 4], ![-13, 10, -14, 10, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![57369, 5837, -6572, 4529, -5098]] ![![9, 3, -2, 1, 0]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![-199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5219, 571, -570, 420, -454]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![5219, 571, -570, 420, -454]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![160, 147, 31, 66, 1]] where
  M :=![![![5219, 571, -570, 420, -454], ![-9080, -799, 1142, -686, 840], ![8400, 1071, -799, 722, -686], ![-2320, 84, 500, -113, 302], ![3020, 902, 84, 349, -113]]]
  hmulB := by decide  
  f := ![![![49, 13, -12, 8, -6]], ![![-120, -35, 26, -18, 16]], ![![160, 49, -35, 18, -18]], ![![-120, -28, 36, -17, 10]], ![![-60, -16, 15, -9, 7]]]
  g := ![![![369, 319, 64, 144, -454], ![-680, -589, -118, -266, 840], ![560, 483, 97, 218, -686], ![-240, -210, -42, -95, 302], ![100, 83, 17, 37, -113]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 4 2 7 [204, 160, 140, 104, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 123, 9, 43], [96, 80, 15, 162], [189, 7, 187, 6], [0, 1]]
 g := ![![[65, 120, 75, 107], [191, 95, 136, 203], [189, 58, 125], [100, 164, 49], [112, 82, 6, 56], [126, 107, 1], []], ![[189, 7, 174, 120, 151, 78], [18, 97, 41, 161, 123, 170], [185, 54, 78], [199, 55, 66], [45, 176, 132, 151, 78, 82], [136, 33, 101], [166, 18, 74, 126, 67, 171]], ![[128, 178, 34, 33, 4, 89], [41, 184, 134, 8, 172, 141], [133, 79, 161], [120, 202, 120], [124, 191, 147, 177, 90, 90], [37, 25, 161], [15, 79, 91, 207, 41, 89]], ![[45, 68, 169, 148, 133, 203], [113, 32, 22, 70, 172, 120], [27, 208, 148], [107, 78, 43], [210, 111, 162, 206, 163, 78], [145, 193, 64], [142, 43, 110, 59, 53, 5]]]
 h' := ![![[33, 123, 9, 43], [71, 160, 83, 23], [127, 13, 73, 186], [80, 85, 11, 114], [151, 134, 14, 7], [38, 1, 62, 30], [0, 0, 0, 1], [0, 1]], ![[96, 80, 15, 162], [68, 122, 29, 186], [26, 90, 109, 23], [182, 164, 54, 17], [104, 151, 88, 158], [0, 135, 56, 29], [174, 38, 96, 34], [33, 123, 9, 43]], ![[189, 7, 187, 6], [36, 38, 24, 162], [143, 146, 144, 132], [30, 56, 62, 168], [178, 11, 91, 72], [46, 60, 4, 92], [118, 190, 43, 168], [96, 80, 15, 162]], ![[0, 1], [136, 102, 75, 51], [210, 173, 96, 81], [77, 117, 84, 123], [52, 126, 18, 185], [132, 15, 89, 60], [52, 194, 72, 8], [189, 7, 187, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [84, 107, 201], []]
 b := ![[], [], [149, 154, 210, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 4
  hpos := by decide
  P := [204, 160, 140, 104, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4922580887, 9895722569, 15736977028, 7055833412, 5030837855]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3838183117, -3457997356, -664545007, -1540187038, 5030837855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 1982119441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 13, -12, 8, -6]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![49, 13, -12, 8, -6]] 
 ![![211, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![150, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![49, 13, -12, 8, -6], ![-120, -35, 26, -18, 16], ![160, 49, -35, 18, -18], ![-120, -28, 36, -17, 10], ![100, 18, -28, 31, -17]]]
  hmulB := by decide  
  f := ![![![5219, 571, -570, 420, -454]], ![![1911, 210, -208, 154, -166]], ![![3750, 411, -409, 302, -326]], ![![1201, 133, -130, 97, -104]], ![![1721, 191, -186, 139, -149]]]
  g := ![![![4, 13, -12, 8, -6], ![-7, -35, 26, -18, 16], ![9, 49, -35, 18, -18], ![-15, -28, 36, -17, 10], ![12, 18, -28, 31, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![5219, 571, -570, 420, -454]] ![![49, 13, -12, 8, -6]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -14, -6, 11, -2]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![19, -14, -6, 11, -2]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![166, 96, 1, 0, 0], ![120, 122, 0, 1, 0], ![41, 167, 0, 0, 1]] where
  M :=![![![19, -14, -6, 11, -2], ![-40, -11, -28, -10, 22], ![220, 98, -11, -39, -10], ![-80, 50, 112, -1, -50], ![-500, -284, 50, 137, -1]]]
  hmulB := by decide  
  f := ![![![957, 1040, 614, 293, 176]], ![![3520, 3683, 2080, 1052, 586]], ![![2254, 2388, 1369, 679, 388]], ![![2480, 2616, 1492, 745, 422]], ![![2879, 3021, 1712, 862, 483]]]
  g := ![![![-1, -2, -6, 11, -2], ![22, 1, -28, -10, 22], ![32, 34, -11, -39, -10], ![-74, -10, 112, -1, -50], ![-113, -97, 50, 137, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [12, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [141, 222], [0, 1]]
 g := ![![[44, 29], [143, 112], [108, 81], [136, 16], [108, 39], [38], [141, 1]], ![[119, 194], [102, 111], [156, 142], [162, 207], [32, 184], [38], [59, 222]]]
 h' := ![![[141, 222], [68, 67], [42, 119], [152, 9], [42, 219], [203, 40], [92, 22], [0, 1]], ![[0, 1], [149, 156], [96, 104], [83, 214], [147, 4], [45, 183], [72, 201], [141, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [197, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [12, 82, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![215, 134, 473, -130, -88]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-265, -66, 473, -130, -88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, -21, -6, -8, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-51, -21, -6, -8, 0]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![29, 88, 1, 0, 0], ![124, 76, 0, 1, 0], ![26, 64, 0, 0, 1]] where
  M :=![![![-51, -21, -6, -8, 0], ![0, -57, -42, -12, -16], ![-160, -117, -57, -34, -12], ![-120, -152, -96, -45, -26], ![-260, -264, -152, -83, -45]]]
  hmulB := by decide  
  f := ![![![-613, -171, 140, -84, 72]], ![![1440, 391, -342, 208, -168]], ![![481, 130, -115, 70, -56]], ![![156, 40, -40, 25, -18]], ![![334, 90, -80, 49, -39]]]
  g := ![![![5, 5, -6, -8, 0], ![14, 25, -42, -12, -16], ![27, 37, -57, -34, -12], ![40, 60, -96, -45, -26], ![70, 100, -152, -83, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P1 : CertificateIrreducibleZModOfList' 223 2 2 7 [14, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 222], [0, 1]]
 g := ![![[11, 16], [44, 64], [88, 128], [205, 136], [203, 83], [82], [69, 1]], ![[0, 207], [0, 159], [0, 95], [0, 87], [132, 140], [82], [138, 222]]]
 h' := ![![[69, 222], [53, 219], [106, 215], [29, 103], [57, 164], [91, 200], [149, 64], [0, 1]], ![[0, 1], [0, 4], [0, 8], [0, 120], [0, 59], [65, 23], [105, 159], [69, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162]]
 b := ![[], [216, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N1 : CertifiedPrimeIdeal' SI223N1 223 where
  n := 2
  hpos := by decide
  P := [14, 154, 1]
  hirr := P223P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3169, 9385, 7514, 6136, 2351]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4649, -5689, 7514, 6136, 2351]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N1 B_one_repr
lemma NI223N1 : Nat.card (O ⧸ I223N1) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127, -39, 26, -19, 14]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-127, -39, 26, -19, 14]] 
 ![![223, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![186, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![-127, -39, 26, -19, 14], ![280, 67, -78, 38, -38], ![-380, -127, 67, -59, 38], ![240, 38, -88, 29, -40], ![-400, -164, 38, -68, 29]]]
  hmulB := by decide  
  f := ![![![-809, -43, 64, -109, 100]], ![![-274, -13, 22, -38, 34]], ![![-300, -17, 25, -39, 36]], ![![-678, -40, 52, -89, 84]], ![![-375, -19, 26, -53, 49]]]
  g := ![![![13, -39, 26, -19, 14], ![-8, 67, -78, 38, -38], ![50, -127, 67, -59, 38], ![14, 38, -88, 29, -40], ![85, -164, 38, -68, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![19, -14, -6, 11, -2]] ![![-51, -21, -6, -8, 0]]
  ![![-809, -43, 64, -109, 100]] where
 M := ![![![-809, -43, 64, -109, 100]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-809, -43, 64, -109, 100]] ![![-127, -39, 26, -19, 14]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11347, -1157, 1300, -897, 1008]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-11347, -1157, 1300, -897, 1008]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![3, 50, 159, 1, 0], ![204, 76, 193, 0, 1]] where
  M :=![![![-11347, -1157, 1300, -897, 1008], ![20160, 2049, -2314, 1592, -1794], ![-17940, -1841, 2049, -1417, 1592], ![5840, 582, -684, 457, -520], ![-5200, -542, 582, -424, 457]]]
  hmulB := by decide  
  f := ![![![-121, -37, 26, -15, 14]], ![![280, 73, -74, 38, -30]], ![![-300, -77, 73, -59, 38]], ![![-149, -38, 35, -33, 20]], ![![-272, -75, 61, -51, 35]]]
  g := ![![![-944, -145, -223, -897, 1008], ![1680, 259, 400, 1592, -1794], ![-1491, -229, -352, -1417, 1592], ![487, 76, 119, 457, -520], ![-428, -62, -89, -424, 457]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [150, 0, 162, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [140, 202, 32], [152, 24, 195], [0, 1]]
 g := ![![[105, 143, 53], [146, 79, 25], [49, 203], [27, 129], [207, 122], [48, 182, 139], [1]], ![[201, 107, 24, 32], [8, 41, 169, 54], [66, 69], [124, 43], [142, 33], [188, 16, 187, 126], [13, 168, 132, 80]], ![[203, 118, 218, 29], [100, 130, 40, 23], [100, 214], [84, 185], [66, 176], [154, 177, 100, 69], [19, 223, 201, 147]]]
 h' := ![![[140, 202, 32], [119, 2, 196], [200, 27, 5], [112, 56, 138], [59, 176, 122], [64, 194, 203], [77, 0, 65], [0, 1]], ![[152, 24, 195], [118, 213, 1], [159, 132, 76], [57, 80, 110], [66, 218, 161], [74, 84, 184], [117, 49, 198], [140, 202, 32]], ![[0, 1], [27, 12, 30], [194, 68, 146], [62, 91, 206], [75, 60, 171], [21, 176, 67], [219, 178, 191], [152, 24, 195]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 218], []]
 b := ![[], [193, 39, 206], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [150, 0, 162, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60069, 9008, 45720, -45549, 49601]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-44238, -6534, -10066, -45549, 49601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 4, 3, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-3, 1, 4, 3, 0]] 
 ![![227, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![210, 0, 1, 0, 0], ![157, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![-3, 1, 4, 3, 0], ![0, 1, 2, 8, 6], ![60, 37, 1, -1, 8], ![80, 78, 36, -7, -4], ![-40, 34, 78, 38, -7]]]
  hmulB := by decide  
  f := ![![![-94169, -9531, 10754, -7415, 8358]], ![![-19176, -1941, 2190, -1510, 1702]], ![![-87770, -8883, 10023, -6911, 7790]], ![![-64919, -6571, 7414, -5112, 5762]], ![![-37937, -3839, 4332, -2987, 3367]]]
  g := ![![![-6, 1, 4, 3, 0], ![-10, 1, 2, 8, 6], ![-11, 37, 1, -1, 8], ![-43, 78, 36, -7, -4], ![-103, 34, 78, 38, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187, 50, -42, 26, -22]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![187, 50, -42, 26, -22]] 
 ![![227, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![214, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![149, 0, 0, 0, 1]] where
  M :=![![![187, 50, -42, 26, -22], ![-440, -119, 100, -62, 52], ![520, 142, -119, 74, -62], ![-400, -112, 92, -57, 48], ![480, 134, -112, 68, -57]]]
  hmulB := by decide  
  f := ![![![-39, -98, -70, -14, -10]], ![![-16, -39, -28, -6, -4]], ![![-38, -94, -67, -14, -10]], ![![-18, -36, -24, -5, -4]], ![![-33, -72, -50, -10, -7]]]
  g := ![![![27, 50, -42, 26, -22], ![-64, -119, 100, -62, 52], ![76, 142, -119, 74, -62], ![-58, -112, 92, -57, 48], ![71, 134, -112, 68, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-11347, -1157, 1300, -897, 1008]] ![![-3, 1, 4, 3, 0]]
  ![![-39, -98, -70, -14, -10]] where
 M := ![![![-39, -98, -70, -14, -10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![-39, -98, -70, -14, -10]] ![![187, 50, -42, 26, -22]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0, 0, 0]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]] where
  M :=![![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 5 2 7 [83, 183, 151, 205, 158, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [216, 197, 223, 160, 16], [156, 116, 212, 78, 131], [190, 77, 166, 69, 64], [196, 67, 86, 151, 18], [0, 1]]
 g := ![![[105, 169, 187, 179, 15], [135, 82, 52, 12], [86, 103, 89, 143, 138], [80, 73, 220, 12], [53, 21, 179, 80], [27, 71, 1], []], ![[8, 158, 57, 118, 65, 201, 129, 83], [53, 165, 175, 37], [45, 180, 216, 70, 94, 165, 2, 100], [60, 53, 173, 3], [71, 139, 90, 97], [97, 226, 60, 193, 173, 217, 89, 12], [206, 174, 38, 19, 169, 210, 122, 203]], ![[199, 80, 207, 191, 185, 210, 193, 93], [191, 194, 157, 103], [225, 25, 226, 97, 11, 20, 184, 105], [209, 77, 20, 169], [153, 139, 71, 94], [181, 115, 111, 168, 213, 17, 214, 128], [5, 224, 100, 158, 160, 64, 17, 227]], ![[90, 26, 143, 128, 150, 103, 87, 228], [142, 188, 53, 180], [176, 119, 39, 7, 181, 141, 149, 3], [98, 179, 116, 1], [18, 52, 67, 174], [32, 119, 102, 224, 151, 4, 58, 178], [126, 17, 44, 46, 75, 84, 134, 168]], ![[214, 145, 82, 157, 86, 222, 186, 84], [12, 225, 29, 49], [145, 185, 113, 75, 148, 130, 111, 145], [55, 84, 44, 46], [208, 174, 132, 149], [191, 160, 8, 94, 176, 143, 183, 156], [89, 57, 49, 149, 122, 7, 23, 107]]]
 h' := ![![[216, 197, 223, 160, 16], [163, 78, 139, 106, 106], [190, 191, 42, 152, 142], [77, 136, 129, 43, 162], [63, 149, 188, 228, 87], [49, 158, 22, 49, 35], [0, 0, 0, 1], [0, 1]], ![[156, 116, 212, 78, 131], [224, 91, 114, 161, 135], [57, 204, 0, 135, 91], [57, 74, 22, 19, 117], [122, 160, 121, 61, 71], [53, 207, 177, 79, 28], [170, 107, 153, 80, 79], [216, 197, 223, 160, 16]], ![[190, 77, 166, 69, 64], [189, 173, 8, 214, 184], [142, 132, 145, 181, 65], [115, 159, 100, 163, 55], [150, 2, 71, 147, 13], [5, 15, 138, 183, 134], [97, 8, 56, 208, 74], [156, 116, 212, 78, 131]], ![[196, 67, 86, 151, 18], [217, 117, 108, 55, 42], [211, 31, 55, 38, 167], [101, 182, 101, 210, 77], [92, 168, 143, 92, 228], [208, 22, 206, 50, 113], [68, 99, 191, 126, 215], [190, 77, 166, 69, 64]], ![[0, 1], [11, 228, 89, 151, 220], [159, 129, 216, 181, 222], [217, 136, 106, 23, 47], [120, 208, 164, 159, 59], [74, 56, 144, 97, 148], [186, 15, 58, 43, 90], [196, 67, 86, 151, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184, 136, 149, 191], [], [], []]
 b := ![[], [153, 5, 5, 13, 31], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 5
  hpos := by decide
  P := [83, 183, 151, 205, 158, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-87938215117, -31272819370, 25854249308, 12157742820, -4019190450]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-384009673, -136562530, 112900652, 53090580, -17551050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 629763392149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2857, 262, -350, 218, -262]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![2857, 262, -350, 218, -262]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![120, 48, 140, 1, 0], ![209, 167, 20, 0, 1]] where
  M :=![![![2857, 262, -350, 218, -262], ![-5240, -637, 524, -438, 436], ![4360, 258, -637, 306, -438], ![-1760, -448, -4, -199, 88], ![880, -354, -448, -48, -199]]]
  hmulB := by decide  
  f := ![![![1249, 350, -294, 182, -150]], ![![-3000, -845, 700, -438, 364]], ![![3640, 1034, -845, 518, -438]], ![![2200, 624, -512, 313, -264]], ![![-703, -199, 162, -104, 87]]]
  g := ![![![135, 144, -110, 218, -262], ![-188, -225, 228, -438, 436], ![254, 252, -149, 306, -438], ![16, -24, 112, -199, 88], ![207, 151, 44, -48, -199]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [216, 51, 219, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 85, 227], [218, 147, 6], [0, 1]]
 g := ![![[221, 123, 120], [220, 104], [177, 195], [158, 139, 23], [208, 18], [88, 151, 196], [1]], ![[118, 168, 78, 222], [91, 197], [197, 132], [61, 153, 75, 114], [202, 18], [18, 98, 72, 54], [7, 106, 98, 17]], ![[130, 200, 161, 47], [208, 81], [159, 46], [59, 26, 57, 118], [], [131, 57, 43, 77], [206, 176, 27, 216]]]
 h' := ![![[29, 85, 227], [143, 228, 179], [197, 228, 77], [123, 206, 112], [92, 220, 16], [98, 232, 22], [17, 182, 14], [0, 1]], ![[218, 147, 6], [18, 181, 14], [58, 83, 165], [196, 202, 83], [37, 217, 100], [104, 160, 211], [43, 142, 34], [29, 85, 227]], ![[0, 1], [15, 57, 40], [48, 155, 224], [181, 58, 38], [71, 29, 117], [49, 74], [127, 142, 185], [218, 147, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 62], []]
 b := ![[], [98, 21, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [216, 51, 219, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68507, 32822, -12111, 25071, 58843]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-65400, -47199, -20167, 25071, 58843]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1249, 350, -294, 182, -150]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![1249, 350, -294, 182, -150]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![194, 93, 1, 0, 0], ![132, 186, 0, 1, 0], ![31, 10, 0, 0, 1]] where
  M :=![![![1249, 350, -294, 182, -150], ![-3000, -845, 700, -438, 364], ![3640, 1034, -845, 518, -438], ![-2880, -808, 684, -407, 336], ![3360, 918, -808, 516, -407]]]
  hmulB := by decide  
  f := ![![![2857, 262, -350, 218, -262]], ![![-5240, -637, 524, -438, 436]], ![![306, -35, -85, 8, -46]], ![![-2572, -362, 220, -227, 200]], ![![159, 6, -26, 10, -17]]]
  g := ![![![167, -20, -294, 182, -150], ![-396, 51, 700, -438, 364], ![484, -53, -845, 518, -438], ![-396, 34, 684, -407, 336], ![449, -68, -808, 516, -407]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [102, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [174, 232], [0, 1]]
 g := ![![[12, 16], [217], [92], [185, 64], [201], [120, 175], [174, 1]], ![[0, 217], [217], [92], [137, 169], [201], [47, 58], [115, 232]]]
 h' := ![![[174, 232], [230, 229], [178, 123], [3, 32], [0, 8], [109, 203], [193, 117], [0, 1]], ![[0, 1], [0, 4], [144, 110], [212, 201], [227, 225], [15, 30], [47, 116], [174, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [184, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [102, 59, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-236, -267, 240, -573, 314]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![82, 347, 240, -573, 314]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![2857, 262, -350, 218, -262]] ![![1249, 350, -294, 182, -150]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1659, -1809, -1022, -514, -292]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-1659, -1809, -1022, -514, -292]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![88, 38, 158, 1, 0], ![197, 94, 169, 0, 1]] where
  M :=![![![-1659, -1809, -1022, -514, -292], ![-5840, -6185, -3618, -1752, -1028], ![-10280, -10897, -6185, -3104, -1752], ![-14600, -15652, -9088, -4433, -2590], ![-25900, -27384, -15652, -7793, -4433]]]
  hmulB := by decide  
  f := ![![![19, -39, -60, 6, 28]], ![![560, 295, -78, -148, 12]], ![![120, 313, 295, -84, -148]], ![![168, 236, 162, -75, -86]], ![![317, 300, 125, -111, -75]]]
  g := ![![![423, 189, 542, -514, -292], ![1468, 657, 1870, -1752, -1028], ![2544, 1137, 3265, -3104, -1752], ![3706, 1658, 4724, -4433, -2590], ![6415, 2868, 8221, -7793, -4433]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [190, 155, 190, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [184, 95, 78], [104, 143, 161], [0, 1]]
 g := ![![[233, 143, 100], [197, 235, 32], [235, 71, 170], [86, 180, 34], [189, 32], [172, 167, 11], [1]], ![[132, 71, 218, 231], [43, 121, 165, 53], [76, 45, 61, 21], [98, 221, 130, 23], [4, 213], [196, 233, 76, 184], [220, 89, 16, 137]], ![[34, 34, 176, 4], [228, 197, 21, 102], [159, 129, 123, 113], [74, 116], [234, 64], [192, 63, 144, 136], [82, 149, 135, 102]]]
 h' := ![![[184, 95, 78], [93, 37, 10], [43, 132, 157], [151, 86, 109], [85, 185, 89], [63, 176, 157], [49, 84, 49], [0, 1]], ![[104, 143, 161], [170, 164, 14], [225, 153, 4], [230, 109, 68], [55, 203, 150], [215, 31, 90], [233, 188, 175], [184, 95, 78]], ![[0, 1], [34, 38, 215], [16, 193, 78], [136, 44, 62], [16, 90], [71, 32, 231], [85, 206, 15], [104, 143, 161]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 131], []]
 b := ![[], [0, 41, 222], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [190, 155, 190, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-270788, 30487, 178258, -278431, 179082]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-46226, -26037, 58182, -278431, 179082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -39, -60, 6, 28]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![19, -39, -60, 6, 28]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![141, 81, 1, 0, 0], ![51, 202, 0, 1, 0], ![198, 35, 0, 0, 1]] where
  M :=![![![19, -39, -60, 6, 28], ![560, 295, -78, -148, 12], ![120, 313, 295, -84, -148], ![-1760, -828, 352, 443, -90], ![-900, -1244, -828, 397, 443]]]
  hmulB := by decide  
  f := ![![![-1659, -1809, -1022, -514, -292]], ![![-5840, -6185, -3618, -1752, -1028]], ![![-3001, -3209, -1855, -910, -528]], ![![-5351, -5679, -3314, -1609, -942]], ![![-2338, -2519, -1442, -715, -411]]]
  g := ![![![11, 11, -60, 6, 28], ![70, 151, -78, -148, 12], ![-33, -6, 295, -84, -148], ![-235, -484, 352, 443, -90], ![33, -125, -828, 397, 443]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [223, 168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 238], [0, 1]]
 g := ![![[109, 124], [63, 64], [123, 213], [184, 88], [202], [50, 10], [71, 1]], ![[70, 115], [66, 175], [189, 26], [218, 151], [202], [43, 229], [142, 238]]]
 h' := ![![[71, 238], [52, 29], [56, 231], [76, 90], [83, 142], [83, 21], [180, 38], [0, 1]], ![[0, 1], [199, 210], [205, 8], [13, 149], [127, 97], [140, 218], [10, 201], [71, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [137, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [223, 168, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![512, 97, 346, -46, 1161]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1154, -248, 346, -46, 1161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-1659, -1809, -1022, -514, -292]] ![![19, -39, -60, 6, 28]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [47, 115, 137, 144, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [165, 91, 237, 98, 84], [178, 222, 24, 169, 234], [132, 32, 162, 139, 211], [218, 136, 59, 76, 194], [0, 1]]
 g := ![![[17, 0, 239, 119, 100], [176, 59, 37, 154], [40, 77, 125, 61], [20, 117, 15, 113], [66, 2, 228, 226, 226], [33, 211, 1], []], ![[157, 33, 137, 88, 65, 87, 200, 146], [163, 99, 52, 15], [224, 197, 93, 240], [33, 210, 75, 10], [24, 43, 91, 232, 235, 71, 140, 208], [148, 25, 42, 222, 115, 225, 232, 63], [163, 110, 104, 227, 60, 151, 37, 85]], ![[178, 125, 28, 134, 146, 97, 191, 140], [118, 69, 100, 166], [158, 76, 182, 150], [90, 196, 112, 67], [75, 162, 180, 146, 187, 124, 154, 34], [152, 110, 138, 125, 107, 78, 99, 34], [115, 24, 49, 10, 125, 112, 188, 139]], ![[52, 39, 150, 176, 230, 30, 217, 90], [102, 142, 181, 205], [134, 9, 177, 119], [41, 38, 83, 32], [228, 197, 158, 70, 217, 24, 171, 231], [103, 215, 97, 95, 159, 52, 124, 223], [181, 94, 45, 7, 137, 166, 62, 233]], ![[99, 122, 73, 40, 229, 213, 76, 240], [187, 154, 150, 1], [64, 64, 224, 77], [149, 162, 55, 87], [21, 121, 110, 231, 83, 235, 132, 196], [118, 105, 68, 178, 167, 11, 146, 9], [84, 143, 83, 33, 87, 87, 209, 48]]]
 h' := ![![[165, 91, 237, 98, 84], [212, 215, 162, 168, 10], [7, 41, 2, 7, 40], [21, 36, 152, 22, 28], [31, 208, 67, 82, 178], [136, 25, 87, 207, 60], [0, 0, 0, 1], [0, 1]], ![[178, 222, 24, 169, 234], [24, 228, 217, 6, 113], [148, 228, 207, 91, 16], [109, 165, 59, 88, 177], [148, 120, 237, 49, 144], [109, 48, 168, 115, 49], [177, 170, 159, 0, 28], [165, 91, 237, 98, 84]], ![[132, 32, 162, 139, 211], [177, 16, 12, 10, 170], [136, 22, 82, 108, 86], [36, 155, 138, 203, 135], [228, 11, 152, 105, 157], [151, 93, 171, 99, 8], [8, 173, 65, 191, 233], [178, 222, 24, 169, 234]], ![[218, 136, 59, 76, 194], [71, 15, 31, 114, 210], [173, 40, 155, 186, 98], [98, 65, 128, 179, 100], [45, 164, 205, 42, 153], [91, 186, 60, 72, 142], [33, 236, 63, 82, 45], [132, 32, 162, 139, 211]], ![[0, 1], [186, 8, 60, 184, 220], [96, 151, 36, 90, 1], [104, 61, 5, 231, 42], [29, 220, 62, 204, 91], [63, 130, 237, 230, 223], [32, 144, 195, 208, 176], [218, 136, 59, 76, 194]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [224, 158, 140, 60], [], [], []]
 b := ![[], [129, 44, 223, 213, 137], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [47, 115, 137, 144, 30, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33981, 44103, 73987, -15424, -27233]
  a := ![4, 1, -1, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-141, 183, 307, -64, -113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 3, 10, 1, -2]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-9, 3, 10, 1, -2]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![107, 87, 1, 0, 0], ![229, 15, 0, 1, 0], ![152, 190, 0, 0, 1]] where
  M :=![![![-9, 3, 10, 1, -2], ![-40, -23, 6, 22, 2], ![20, -5, -23, 5, 22], ![240, 142, -8, -45, 4], ![40, 140, 142, -10, -45]]]
  hmulB := by decide  
  f := ![![![13701, 1387, -1564, 1079, -1216]], ![![-24320, -2455, 2774, -1912, 2158]], ![![-2503, -251, 285, -196, 222]], ![![11019, 1116, -1258, 868, -978]], ![![-10088, -1016, 1150, -792, 895]]]
  g := ![![![-4, -2, 10, 1, -2], ![-24, -5, 6, 22, 2], ![-8, -9, -23, 5, 22], ![43, 3, -8, -45, 4], ![-24, -14, 142, -10, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [123, 182, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 250], [0, 1]]
 g := ![![[128, 100], [226, 4], [119], [119, 201], [75, 221], [127, 93], [69, 1]], ![[0, 151], [0, 247], [119], [183, 50], [13, 30], [18, 158], [138, 250]]]
 h' := ![![[69, 250], [63, 10], [138, 249], [172, 133], [62, 47], [192, 35], [47, 120], [0, 1]], ![[0, 1], [0, 241], [0, 2], [62, 118], [42, 204], [97, 216], [44, 131], [69, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [249]]
 b := ![[], [160, 250]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [123, 182, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-474, 7027, 5082, 4482, 2425]
  a := ![7, 2, -24, 2, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7726, -3837, 5082, 4482, 2425]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -7, 8, -4, 4]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-31, -7, 8, -4, 4]] 
 ![![251, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![219, 0, 1, 0, 0], ![124, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-31, -7, 8, -4, 4], ![80, 25, -14, 12, -8], ![-80, -15, 25, -10, 12], ![80, 32, -8, 13, -6], ![-60, 0, 32, -5, 13]]]
  hmulB := by decide  
  f := ![![![-261, -13, 66, -16, 4]], ![![-8, -1, 2, 0, 0]], ![![-229, -12, 57, -14, 4]], ![![-124, -4, 32, -9, 2]], ![![-6, 2, 4, -1, -1]]]
  g := ![![![-5, -7, 8, -4, 4], ![6, 25, -14, 12, -8], ![-17, -15, 25, -10, 12], ![0, 32, -8, 13, -6], ![-26, 0, 32, -5, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 4, -4, 3, -4]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![39, 4, -4, 3, -4]] 
 ![![251, 0, 0, 0, 0], ![92, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![123, 0, 0, 0, 1]] where
  M :=![![![39, 4, -4, 3, -4], ![-80, -13, 8, -4, 6], ![60, 0, -13, 5, -4], ![0, 6, -4, -9, 2], ![20, 10, 6, -5, -9]]]
  hmulB := by decide  
  f := ![![![-17851, -5034, 4180, -2583, 2146]], ![![-6372, -1797, 1492, -922, 766]], ![![-2695, -760, 631, -390, 324]], ![![-7021, -1980, 1644, -1016, 844]], ![![-8943, -2522, 2094, -1294, 1075]]]
  g := ![![![0, 4, -4, 3, -4], ![2, -13, 8, -4, 6], ![2, 0, -13, 5, -4], ![1, 6, -4, -9, 2], ![2, 10, 6, -5, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2

def I251N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 11, 10, 2, 4]] i)))

def SI251N3: IdealEqSpanCertificate' Table ![![-9, 11, 10, 2, 4]] 
 ![![251, 0, 0, 0, 0], ![228, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![198, 0, 0, 0, 1]] where
  M :=![![![-9, 11, 10, 2, 4], ![80, 49, 22, 16, 4], ![40, 75, 49, 20, 16], ![120, 116, 64, 33, 18], ![180, 200, 116, 55, 33]]]
  hmulB := by decide  
  f := ![![![1901, 529, -456, 298, -236]], ![![1708, 475, -410, 268, -212]], ![![872, 243, -209, 136, -108]], ![![1270, 354, -304, 199, -158]], ![![1518, 422, -364, 239, -189]]]
  g := ![![![-19, 11, 10, 2, 4], ![-68, 49, 22, 16, 4], ![-116, 75, 49, 20, 16], ![-170, 116, 64, 33, 18], ![-296, 200, 116, 55, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N3 : Nat.card (O ⧸ I251N3) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N3)

lemma isPrimeI251N3 : Ideal.IsPrime I251N3 := prime_ideal_of_norm_prime hp251.out _ NI251N3
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-9, 3, 10, 1, -2]] ![![-31, -7, 8, -4, 4]]
  ![![-81, 20, 64, -5, 28]] where
 M := ![![![-81, 20, 64, -5, 28]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![-81, 20, 64, -5, 28]] ![![39, 4, -4, 3, -4]]
  ![![-359, -334, -160, -98, -74]] where
 M := ![![![-359, -334, -160, -98, -74]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N2 : IdealMulLeCertificate' Table 
  ![![-359, -334, -160, -98, -74]] ![![-9, 11, 10, 2, 4]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![-54969, -58483, -33634, -16566, -9538]]]
 hmul := by decide  
 g := ![![![![-219, -233, -134, -66, -38]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2, I251N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
    exact isPrimeI251N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1 ⊙ MulI251N2)


lemma PB547I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB547I5 : PrimesBelowBoundCertificateInterval O 197 251 547 where
  m := 9
  g := ![2, 2, 3, 3, 1, 2, 2, 1, 4]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB547I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1, I251N2, I251N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1568239201, 199]
    · exact ![1982119441, 211]
    · exact ![49729, 49729, 223]
    · exact ![11697083, 227, 227]
    · exact ![629763392149]
    · exact ![12649337, 54289]
    · exact ![13651919, 57121]
    · exact ![812990017201]
    · exact ![63001, 251, 251, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
      exact NI251N3
  β := ![I199N1, I211N1, I223N2, I227N1, I227N2, I251N1, I251N2, I251N3]
  Il := ![[I199N1], [I211N1], [I223N2], [I227N1, I227N2], [], [], [], [], [I251N1, I251N2, I251N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
