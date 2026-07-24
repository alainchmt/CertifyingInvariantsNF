
import IdealArithmetic.Examples.NF5_1_13500000_3.RI5_1_13500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, 68, -66, 172, 323]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-101, 68, -66, 172, 323]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![168, 63, 92, 1, 0], ![47, 125, 119, 0, 1]] where
  M :=![![![-101, 68, -66, 172, 323], ![-604, 5, -318, 556, 1116], ![-2240, -366, -1099, 1588, 3320], ![-3162, -878, -1468, 1799, 3918], ![-590, -128, -284, 382, 811]]]
  hmulB := by decide  
  f := ![![![-69, 28, 10, -6, -23]], ![![68, -65, 18, -4, 8]], ![![-48, 82, -25, 20, -88]], ![![-58, 41, 2, 3, -56]], ![![-3, 15, -1, 8, -54]]]
  g := ![![![-222, -257, -273, 172, 323], ![-736, -877, -926, 556, 1116], ![-2136, -2590, -2725, 1588, 3320], ![-2460, -3035, -3182, 1799, 3918], ![-517, -631, -663, 382, 811]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [171, 158, 191, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [140, 116, 198], [67, 82, 1], [0, 1]]
 g := ![![[5, 168, 14], [139, 147, 14], [131, 166, 14], [152, 25], [53, 29], [173, 64], [1]], ![[23, 198, 34, 149], [165, 131, 74, 78], [93, 110, 44, 60], [77, 131], [171, 103], [148, 125], [141, 143, 141, 198]], ![[8, 106, 36, 115], [72, 15, 142, 8], [64, 138, 68, 7], [27, 125], [121, 92], [74, 79], [33, 158, 55, 1]]]
 h' := ![![[140, 116, 198], [111, 97, 148], [86, 185, 148], [135, 141, 51], [43, 164, 194], [56, 37, 167], [28, 41, 8], [0, 1]], ![[67, 82, 1], [16, 7, 99], [172, 66, 11], [118, 139, 61], [143, 113, 23], [23, 194, 125], [156, 109, 18], [140, 116, 198]], ![[0, 1], [103, 95, 151], [4, 147, 40], [169, 118, 87], [127, 121, 181], [91, 167, 106], [3, 49, 173], [67, 82, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 105], []]
 b := ![[], [55, 103, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [171, 158, 191, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-833275, 48328, -334296, 482146, 1223824]
  a := ![-22, -8, 30, -26, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-700269, -921130, -956416, 482146, 1223824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, 28, 10, -6, -23]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-69, 28, 10, -6, -23]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![95, 15, 1, 0, 0], ![183, 35, 0, 1, 0], ![135, 100, 0, 0, 1]] where
  M :=![![![-69, 28, 10, -6, -23], ![68, -65, 18, -4, 8], ![-48, 82, -25, 20, -88], ![182, 6, -116, 17, 312], ![-142, 36, 56, -6, -193]]]
  hmulB := by decide  
  f := ![![![-101, 68, -66, 172, 323]], ![![-604, 5, -318, 556, 1116]], ![![-105, 31, -61, 132, 255]], ![![-215, 59, -124, 265, 513]], ![![-375, 48, -206, 398, 784]]]
  g := ![![![16, 12, 10, -6, -23], ![-10, -5, 18, -4, 8], ![53, 43, -25, 20, -88], ![-171, -151, -116, 17, 312], ![109, 94, 56, -6, -193]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [183, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 198], [0, 1]]
 g := ![![[127, 114], [45, 98], [83, 111], [112], [13], [121], [42, 1]], ![[139, 85], [181, 101], [168, 88], [112], [13], [121], [84, 198]]]
 h' := ![![[42, 198], [123, 121], [134, 140], [101, 132], [10, 50], [198, 49], [75, 188], [0, 1]], ![[0, 1], [31, 78], [44, 59], [73, 67], [120, 149], [67, 150], [11, 11], [42, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [172]]
 b := ![[], [184, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [183, 157, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![108859, -70450, -60718, 47976, 163667]
  a := ![17, -58, -22, -45, 58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-125616, -86460, -60718, 47976, 163667]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-101, 68, -66, 172, 323]] ![![-69, 28, 10, -6, -23]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![867, -303, -199, 64, 576]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![867, -303, -199, 64, 576]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![164, 126, 117, 1, 0], ![106, 169, 9, 0, 1]] where
  M :=![![![867, -303, -199, 64, 576], ![-2048, 732, 465, -142, -1408], ![5064, -1725, -1232, 362, 3644], ![-5540, 1731, 1463, -437, -4050], ![4684, -1522, -1190, 356, 3375]]]
  hmulB := by decide  
  f := ![![![-151, -81, -63, 40, 108]], ![![-272, -174, -105, 34, 128]], ![![-376, -343, -122, -74, -36]], ![![-488, -358, -179, 9, 138]], ![![-310, -195, -121, 44, 155]]]
  g := ![![![-335, -501, -61, 64, 576], ![808, 1216, 141, -142, -1408], ![-2088, -3143, -362, 362, 3644], ![2348, 3513, 422, -437, -4050], ![-1950, -2923, -347, 356, 3375]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [72, 138, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 20, 194], [65, 190, 17], [0, 1]]
 g := ![![[51, 100, 179], [91, 140, 183], [85, 53], [124, 59], [125, 80, 21], [52, 189], [1]], ![[35, 119, 129, 70], [2, 109, 130, 43], [153, 76], [103, 101], [132, 106, 185, 96], [173, 107], [115, 200, 183, 151]], ![[142, 175, 33, 210], [91, 179, 111, 116], [138, 171], [172, 201], [46, 123, 161, 72], [101, 9], [56, 203, 5, 60]]]
 h' := ![![[126, 20, 194], [200, 132, 161], [143, 18, 129], [199, 90, 106], [73, 92, 108], [174, 143, 77], [139, 73, 191], [0, 1]], ![[65, 190, 17], [143, 173, 72], [15, 129, 150], [103, 143, 42], [61, 96, 177], [119, 38, 172], [45, 9, 23], [126, 20, 194]], ![[0, 1], [68, 117, 189], [82, 64, 143], [34, 189, 63], [32, 23, 137], [165, 30, 173], [91, 129, 208], [65, 190, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 67], []]
 b := ![[], [17, 10, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [72, 138, 20, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72127, 33713, 22348, -15217, -40611]
  a := ![-7, -5, 10, -11, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32571, 41774, 10276, -15217, -40611]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7385, -4183, 7155, -2004, -10886]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-7385, -4183, 7155, -2004, -10886]] 
 ![![211, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![-7385, -4183, 7155, -2004, -10886], ![35528, -2234, -13931, 6294, 15488], ![-36776, 27891, -9022, -2686, 26164], ![-75464, -23125, 55133, -17541, -78874], ![22896, 17210, -26070, 6848, 40747]]]
  hmulB := by decide  
  f := ![![![39349, -5289, -2029, -2804, 8398]], ![![9858, -1190, -385, -790, 1804]], ![![8178, -1103, -458, -526, 1880]], ![![-298, 357, 269, -125, -630]], ![![24107, -3353, -1361, -1620, 5453]]]
  g := ![![![6215, -4183, 7155, -2004, -10886], ![-5986, -2234, -13931, 6294, 15488], ![-21162, 27891, -9022, -2686, 26164], ![42524, -23125, 55133, -17541, -78874], ![-23805, 17210, -26070, 6848, 40747]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![793, -160, -210, 124, 164]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![793, -160, -210, 124, 164]] 
 ![![211, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![190, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![793, -160, -210, 124, 164], ![-160, 707, -576, 76, 1080], ![-4016, -660, 2411, -848, -3256], ![4896, -1580, -754, 677, 36], ![-3152, 508, 952, -512, -863]]]
  hmulB := by decide  
  f := ![![![363, 1624, 1498, -1092, -3596]], ![![278, 1035, 956, -700, -2288]], ![![318, 1508, 1383, -1000, -3312]], ![![218, 572, 522, -379, -1228]], ![![20, 300, 272, -192, -655]]]
  g := ![![![223, -160, -210, 124, 164], ![-142, 707, -576, 76, 1080], ![-918, -660, 2411, -848, -3256], ![1462, -1580, -754, 677, 36], ![-868, 508, 952, -512, -863]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![867, -303, -199, 64, 576]] ![![-7385, -4183, 7155, -2004, -10886]]
  ![![-1490955, -67108, 732048, -288212, -915326]] where
 M := ![![![-1490955, -67108, 732048, -288212, -915326]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![-1490955, -67108, 732048, -288212, -915326]] ![![793, -160, -210, 124, 164]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-2637473203, -301654884, 1462643982, -537227944, -1920990842]]]
 hmul := by decide  
 g := ![![![![-12499873, -1429644, 6931962, -2546104, -9104222]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2583, -1029, -1133, 1092, 2543]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-2583, -1029, -1133, 1092, 2543]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![172, 219, 89, 27, 1]] where
  M :=![![![-2583, -1029, -1133, 1092, 2543], ![-5804, -2624, -2495, 2102, 5116], ![-12056, -6197, -5004, 3418, 8964], ![-8190, -5509, -3141, 781, 3440], ![-2434, -1354, -982, 554, 1565]]]
  hmulB := by decide  
  f := ![![![-23, 13, -1, -2, 5]], ![![-28, -26, 35, -10, -48]], ![![152, -3, -62, 30, 52]], ![![-30, 73, -57, 3, 130]], ![![12, -8, 2, 1, -7]]]
  g := ![![![-1973, -2502, -1020, -303, 2543], ![-3972, -5036, -2053, -610, 5116], ![-6968, -8831, -3600, -1070, 8964], ![-2690, -3403, -1387, -413, 3440], ![-1218, -1543, -629, -187, 1565]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [17, 30, 182, 97, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 29, 181, 194], [199, 99, 99, 186], [148, 94, 166, 66], [0, 1]]
 g := ![![[13, 1, 15, 119], [152, 203, 107, 181], [29, 219, 102, 172], [89, 72, 18, 81], [117, 158, 116, 58], [84, 126, 1], []], ![[140, 18, 217, 101, 131, 48], [114, 17, 153, 27, 12, 140], [85, 193, 9, 37, 209, 111], [127, 196, 159, 118, 206, 24], [55, 108, 190, 116, 88, 85], [38, 220, 105], [74, 191, 1, 190, 108, 141]], ![[130, 8, 108, 25, 199, 129], [19, 95, 201, 108, 214, 137], [47, 47, 51, 50, 195, 118], [120, 131, 40, 34, 94, 206], [18, 91, 117, 136, 219, 95], [53, 158, 38], [107, 200, 97, 194, 46, 191]], ![[183, 35, 38, 102, 97, 143], [127, 75, 202, 5, 219, 15], [134, 60, 151, 85, 177, 25], [202, 40, 22, 169, 126, 14], [120, 95, 28, 126, 137, 62], [73, 125, 76], [53, 74, 216, 14, 97, 49]]]
 h' := ![![[2, 29, 181, 194], [92, 219, 78, 157], [176, 164, 52, 187], [48, 221, 151, 29], [18, 120, 103, 9], [133, 21, 93, 110], [0, 0, 0, 1], [0, 1]], ![[199, 99, 99, 186], [78, 159, 38, 38], [89, 39, 1, 7], [105, 158, 54, 75], [169, 176, 53, 62], [185, 2, 78, 190], [88, 10, 45, 128], [2, 29, 181, 194]], ![[148, 94, 166, 66], [31, 186, 178, 128], [34, 118, 80, 61], [25, 147, 26, 40], [176, 61, 181, 11], [188, 217, 156, 74], [190, 111, 14, 201], [199, 99, 99, 186]], ![[0, 1], [103, 105, 152, 123], [130, 125, 90, 191], [198, 143, 215, 79], [166, 89, 109, 141], [6, 206, 119, 72], [32, 102, 164, 116], [148, 94, 166, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [41, 210, 214], []]
 b := ![[], [], [29, 114, 0, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 4
  hpos := by decide
  P := [17, 30, 182, 97, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2626093223, -1518194508, -862836184, 295950228, 1102259292]
  a := ![31, 27, -42, 50, 108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-861949289, -1089295872, -443784364, -132130272, 1102259292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 13, -1, -2, 5]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-23, 13, -1, -2, 5]] 
 ![![223, 0, 0, 0, 0], ![72, 1, 0, 0, 0], ![168, 0, 1, 0, 0], ![160, 0, 0, 1, 0], ![218, 0, 0, 0, 1]] where
  M :=![![![-23, 13, -1, -2, 5], ![-28, -26, 35, -10, -48], ![152, -3, -62, 30, 52], ![-30, 73, -57, 3, 130], ![46, -30, 10, 6, -47]]]
  hmulB := by decide  
  f := ![![![-2583, -1029, -1133, 1092, 2543]], ![![-860, -344, -377, 362, 844]], ![![-2000, -803, -876, 838, 1956]], ![![-1890, -763, -827, 787, 1840]], ![![-2536, -1012, -1112, 1070, 2493]]]
  g := ![![![-7, 13, -1, -2, 5], ![36, -26, 35, -10, -48], ![-24, -3, -62, 30, 52], ![-110, 73, -57, 3, 130], ![44, -30, 10, 6, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-2583, -1029, -1133, 1092, 2543]] ![![-23, 13, -1, -2, 5]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-571, 324, -18, -74, 183]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-571, 324, -18, -74, 183]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![111, 199, 52, 12, 1]] where
  M :=![![![-571, 324, -18, -74, 183], ![-1028, -663, 1134, -332, -1768], ![5744, -226, -2207, 940, 2424], ![-2454, 2570, -1076, -161, 2616], ![2606, -1140, -88, 294, -543]]]
  hmulB := by decide  
  f := ![![![249, -84, -62, 20, 177]], ![![-628, 207, 150, -44, -428]], ![![1536, -522, -385, 124, 1096]], ![![-1630, 534, 388, -115, -1110]], ![![-157, 47, 32, -6, -92]]]
  g := ![![![-92, -159, -42, -10, 183], ![860, 1547, 410, 92, -1768], ![-1160, -2126, -565, -124, 2424], ![-1290, -2282, -604, -139, 2616], ![277, 471, 124, 30, -543]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 4 2 7 [204, 164, 108, 168, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [208, 95, 58, 138], [4, 49, 31, 95], [74, 82, 138, 221], [0, 1]]
 g := ![![[88, 39, 157, 7], [165, 83, 222, 175], [164, 39, 182], [218, 116, 85], [65, 37, 73], [202, 195, 59, 1], []], ![[168, 131, 23, 62, 75, 178], [180, 158, 158, 180, 112, 58], [126, 80, 214], [36, 134, 196], [65, 193, 49], [220, 44, 50, 170, 49, 218], [215, 161, 137, 134, 176, 93]], ![[106, 133, 27, 51, 80, 140], [152, 100, 195, 177, 74, 152], [117, 12, 81], [194, 171, 30], [1, 201, 159], [217, 167, 215, 102, 160, 80], [147, 18, 145, 9, 97, 223]], ![[50, 80, 93, 1, 134, 112], [161, 37, 166, 131, 146, 75], [181, 123, 87], [37, 76, 209], [159], [73, 107, 3, 136, 202, 166], [153, 69, 194, 21, 117, 11]]]
 h' := ![![[208, 95, 58, 138], [163, 33, 28, 190], [21, 87, 150, 185], [154, 39, 201, 149], [19, 113, 63, 53], [106, 186, 225, 46], [0, 0, 0, 1], [0, 1]], ![[4, 49, 31, 95], [100, 55, 200, 15], [122, 127, 28, 37], [42, 104, 169, 206], [203, 62, 62, 14], [98, 17, 63, 220], [129, 50, 181, 26], [208, 95, 58, 138]], ![[74, 82, 138, 221], [35, 43, 119, 136], [101, 200, 205, 156], [208, 190, 0, 218], [115, 202, 155, 205], [41, 200, 205, 188], [40, 223, 52, 173], [4, 49, 31, 95]], ![[0, 1], [3, 96, 107, 113], [152, 40, 71, 76], [204, 121, 84, 108], [48, 77, 174, 182], [134, 51, 188], [143, 181, 221, 27], [74, 82, 138, 221]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [117, 220, 165], []]
 b := ![[], [], [219, 196, 43, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 4
  hpos := by decide
  P := [204, 164, 108, 168, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27696733, 170358062, 9010033, -64894213, 23540759]
  a := ![-35, -7, 48, -31, -122]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11389108, -19886577, -5352905, -1530323, 23540759]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 2655237841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-249, 84, 62, -20, -177]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-249, 84, 62, -20, -177]] 
 ![![227, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![117, 0, 1, 0, 0], ![142, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![-249, 84, 62, -20, -177], ![628, -207, -150, 44, 428], ![-1536, 522, 385, -124, -1096], ![1630, -534, -388, 115, 1110], ![-1382, 464, 340, -106, -969]]]
  hmulB := by decide  
  f := ![![![571, -324, 18, 74, -183]], ![![163, -87, 0, 22, -43]], ![![269, -166, 19, 34, -105]], ![![368, -214, 16, 47, -126]], ![![230, -132, 8, 30, -75]]]
  g := ![![![31, 84, 62, -20, -177], ![-71, -207, -150, 44, 428], ![191, 522, 385, -124, -1096], ![-186, -534, -388, 115, 1110], ![166, 464, 340, -106, -969]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-571, 324, -18, -74, 183]] ![![-249, 84, 62, -20, -177]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![-227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)


lemma PB229I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 228 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 228 (by omega)

def PB229I5 : PrimesBelowBoundCertificateInterval O 197 228 229 where
  m := 4
  g := ![2, 3, 2, 2]
  P := ![199, 211, 223, 227]
  hP := PB229I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7880599, 39601]
    · exact ![9393931, 211, 211]
    · exact ![2472973441, 223]
    · exact ![2655237841, 227]
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
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
  β := ![I211N1, I211N2, I223N1, I227N1]
  Il := ![[], [I211N1, I211N2], [I223N1], [I227N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
