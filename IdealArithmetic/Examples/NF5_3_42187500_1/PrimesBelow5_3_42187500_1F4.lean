
import IdealArithmetic.Examples.NF5_3_42187500_1.RI5_3_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1799, 550, -121, 464, -386]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-1799, 550, -121, 464, -386]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![136, 81, 60, 1, 0], ![75, 39, 46, 0, 1]] where
  M :=![![![-1799, 550, -121, 464, -386], ![5326, -1943, 449, -1478, 1470], ![-12949, 4129, -922, 3397, -2956], ![13997, -5081, 1173, -3878, 3838], ![-11705, 3491, -764, 2991, -2423]]]
  hmulB := by decide  
  f := ![![![46, 49, 12, -15, -16]], ![![255, 32, 54, 7, -76]], ![![439, 17, -98, -29, 14]], ![![340, 67, 1, -21, -48]], ![![215, 37, -9, -14, -23]]]
  g := ![![![-229, -140, -65, 464, -386], ![612, 385, 137, -1478, 1470], ![-1613, -992, -438, 3397, -2956], ![1615, 1015, 365, -3878, 3838], ![-1508, -919, -438, 2991, -2423]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [17, 12, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 62, 26], [17, 94, 131], [0, 1]]
 g := ![![[82, 31, 68], [85, 140], [87, 146, 141], [88, 140, 144], [17, 97, 156], [36, 1], []], ![[146, 85, 100, 114], [116, 19], [109, 58, 34, 63], [81, 101, 84, 55], [149, 98, 35, 50], [120, 44], [85, 48]], ![[58, 126, 141, 137], [79, 13], [87, 81, 134, 102], [24, 40, 96, 103], [54, 75, 21, 50], [114, 76], [137, 48]]]
 h' := ![![[19, 62, 26], [85, 134, 15], [91, 66, 104], [74, 15, 45], [25, 130, 12], [16, 22, 28], [0, 0, 1], [0, 1]], ![[17, 94, 131], [30, 94, 27], [79, 82, 31], [92, 152, 67], [6, 13, 112], [69, 67, 64], [15, 49, 94], [19, 62, 26]], ![[0, 1], [23, 86, 115], [61, 9, 22], [60, 147, 45], [49, 14, 33], [104, 68, 65], [1, 108, 62], [17, 94, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 47], []]
 b := ![[], [87, 124, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [17, 12, 121, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30647117, 10744988, -2924200, -3727684, -12649452]
  a := ![15, -20, -8, 12, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9467013, 5133860, 5112176, -3727684, -12649452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, -94, -26, 32, -6]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![197, -94, -26, 32, -6]] 
 ![![157, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![197, -94, -26, 32, -6], ![58, 117, -174, -96, 122], ![-896, 164, 413, 44, -192], ![970, -550, -28, 221, -104], ![612, -108, -290, -34, 137]]]
  hmulB := by decide  
  f := ![![![4269, -1082, 194, -1028, 642]], ![![1196, -291, 50, -284, 166]], ![![674, -176, 33, -164, 108]], ![![1652, -386, 64, -387, 212]], ![![2094, -524, 94, -502, 309]]]
  g := ![![![21, -94, -26, 32, -6], ![-28, 117, -174, -96, 122], ![-34, 164, 413, 44, -192], ![124, -550, -28, 221, -104], ![22, -108, -290, -34, 137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![130, 33, 6, -9, -22]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![130, 33, 6, -9, -22]] 
 ![![157, 0, 0, 0, 0], ![148, 1, 0, 0, 0], ![121, 0, 1, 0, 0], ![134, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![130, 33, 6, -9, -22], ![339, 88, 16, -23, -58], ![277, 71, 14, -19, -46], ![493, 131, 25, -32, -84], ![394, 104, 21, -26, -65]]]
  hmulB := by decide  
  f := ![![![239, -100, -49, 24, 12]], ![![224, -93, -47, 22, 12]], ![![180, -77, -35, 19, 8]], ![![211, -89, -43, 22, 10]], ![![38, -15, -9, 3, 3]]]
  g := ![![![-24, 33, 6, -9, -22], ![-65, 88, 16, -23, -58], ![-53, 71, 14, -19, -46], ![-100, 131, 25, -32, -84], ![-80, 104, 21, -26, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-1799, 550, -121, 464, -386]] ![![197, -94, -26, 32, -6]]
  ![![-239, 100, 49, -24, -12]] where
 M := ![![![-239, 100, 49, -24, -12]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-239, 100, 49, -24, -12]] ![![130, 33, 6, -9, -22]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0, 0, 0]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]] where
  M :=![![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 5 2 7 [143, 25, 105, 72, 71, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 85, 50, 127, 5], [112, 15, 13, 77, 74], [132, 123, 138, 93, 73], [141, 102, 125, 29, 11], [0, 1]]
 g := ![![[75, 104, 23, 127, 146], [159, 136, 154, 87, 118], [103, 139, 158, 56], [1, 92, 29, 6], [73, 10, 155, 151], [1], []], ![[77, 44, 103, 131, 31, 100, 99, 28], [134, 129, 104, 87, 162, 150, 46, 128], [40, 88, 31, 69], [55, 42, 140, 90], [156, 38, 145, 121], [155, 83, 21, 10, 103, 37, 90, 105], [2, 154, 147, 25]], ![[111, 144, 81, 30, 123, 52, 78, 58], [107, 118, 87, 30, 12, 151, 110, 69], [93, 125, 65, 34], [85, 134, 11, 46], [125, 153, 150, 41], [141, 159, 7, 27, 5, 103, 30, 161], [39, 47, 108, 97]], ![[8, 31, 37, 159, 0, 66, 22, 142], [19, 132, 75, 99, 40, 23, 113, 42], [132, 112, 122, 115], [120, 51, 86, 26], [149, 86, 10, 57], [91, 79, 26, 31, 156, 113, 75, 157], [94, 15, 13, 113]], ![[3, 47, 63, 107, 38, 57, 38, 79], [4, 40, 120, 74, 16, 63, 17, 78], [75, 75, 22, 160], [93, 40, 17, 60], [116, 63, 30, 47], [113, 44, 41, 4, 118, 123, 78, 159], [65, 126, 34, 121]]]
 h' := ![![[33, 85, 50, 127, 5], [83, 95, 26, 93, 31], [32, 116, 81, 95, 66], [108, 26, 45, 5, 120], [67, 146, 86, 99, 13], [20, 138, 58, 91, 92], [0, 0, 1], [0, 1]], ![[112, 15, 13, 77, 74], [159, 53, 148, 99, 25], [25, 107, 104, 35, 112], [23, 124, 148, 91, 45], [155, 132, 3, 97, 116], [28, 105, 154, 160, 11], [151, 1, 114, 1, 64], [33, 85, 50, 127, 5]], ![[132, 123, 138, 93, 73], [51, 67, 43, 157, 60], [160, 61, 83, 110, 120], [147, 136, 147, 47, 94], [27, 116, 13, 150, 131], [61, 91, 92, 36, 81], [121, 65, 27, 7, 115], [112, 15, 13, 77, 74]], ![[141, 102, 125, 29, 11], [116, 113, 10, 106, 95], [145, 157, 92, 86, 80], [90, 62, 98, 77, 21], [102, 18, 120, 51, 134], [43, 33, 0, 93, 63], [70, 104, 11, 95, 24], [132, 123, 138, 93, 73]], ![[0, 1], [148, 161, 99, 34, 115], [76, 48, 129, 0, 111], [83, 141, 51, 106, 46], [159, 77, 104, 92, 95], [152, 122, 22, 109, 79], [154, 156, 10, 60, 123], [141, 102, 125, 29, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 50, 78, 24], [], [], []]
 b := ![[], [85, 93, 77, 85, 93], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 5
  hpos := by decide
  P := [143, 25, 105, 72, 71, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![702175631783458404, 91479948311826047, -41912709429193221, -76963092906630441, -173174210528334718]
  a := ![120, -180, -58, 54, -477]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4307825961861708, 561226676759669, -257133186682167, -472166214151107, -1062418469498986]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, 30, -9, -30, -54]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![253, 30, -9, -30, -54]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![65, 75, 152, 1, 0], ![86, 32, 92, 0, 1]] where
  M :=![![![253, 30, -9, -30, -54], ![840, 91, -39, -96, -174], ![933, 111, -44, -117, -192], ![1965, 231, -81, -236, -426], ![2001, 213, -90, -237, -419]]]
  hmulB := by decide  
  f := ![![![14, 3, 0, -3, 0]], ![![3, 14, 6, 3, -12]], ![![87, -15, -4, -9, 6]], ![![86, -6, -1, -8, 0]], ![![56, -4, -1, -6, 1]]]
  g := ![![![41, 24, 57, -30, -54], ![132, 77, 183, -96, -174], ![150, 90, 212, -117, -192], ![323, 189, 449, -236, -426], ![320, 188, 446, -237, -419]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [67, 63, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 75, 10], [83, 91, 157], [0, 1]]
 g := ![![[63, 107, 31], [44, 159, 58], [90, 145, 50], [4, 27], [46, 1], [137, 37, 1], []], ![[91, 36, 13, 149], [56, 3, 0, 68], [6, 117, 151, 151], [145, 31], [112, 126], [7, 9, 12, 145], [23, 100]], ![[141, 19, 125, 27], [70, 21, 2, 141], [148, 30, 158, 25], [31, 32], [59, 65], [84, 148, 148, 29], [43, 100]]]
 h' := ![![[121, 75, 10], [58, 92, 96], [149, 162, 15], [163, 148, 102], [127, 154, 19], [6, 79, 166], [0, 0, 1], [0, 1]], ![[83, 91, 157], [91, 66, 137], [153, 8, 146], [68, 144, 74], [127, 0, 96], [139, 99, 31], [74, 148, 91], [121, 75, 10]], ![[0, 1], [12, 9, 101], [68, 164, 6], [89, 42, 158], [50, 13, 52], [50, 156, 137], [0, 19, 75], [83, 91, 157]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 28], []]
 b := ![[], [152, 58, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [67, 63, 130, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14135419, 3621966, -1000354, -1979852, -4376916]
  a := ![11, -15, -5, 6, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3109225, 1749534, 4207266, -1979852, -4376916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, -3, 0, 3, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-14, -3, 0, 3, 0]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![30, 99, 1, 0, 0], ![51, 166, 0, 1, 0], ![111, 62, 0, 0, 1]] where
  M :=![![![-14, -3, 0, 3, 0], ![-3, -14, -6, -3, 12], ![-87, 15, 4, 9, -6], ![-3, -33, 9, -2, 12], ![-48, -6, -9, 12, 1]]]
  hmulB := by decide  
  f := ![![![-253, -30, 9, 30, 54]], ![![-840, -91, 39, 96, 174]], ![![-549, -60, 25, 63, 114]], ![![-924, -101, 42, 106, 192]], ![![-492, -55, 21, 57, 103]]]
  g := ![![![-1, -3, 0, 3, 0], ![-6, 2, -6, -3, 12], ![0, -9, 4, 9, -6], ![-9, -8, 9, -2, 12], ![-3, -7, -9, 12, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [19, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 166], [0, 1]]
 g := ![![[0, 44], [0, 66], [], [], [61], [], [1]], ![[0, 123], [0, 101], [], [], [61], [], [1]]]
 h' := ![![[0, 166], [0, 82], [0, 147], [100], [10], [0, 27], [148], [0, 1]], ![[0, 1], [0, 85], [0, 20], [100], [10], [0, 140], [148], [0, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [0, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [19, 0, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1191470, -92768, 230291, 82596, 355603]
  a := ![-52, 75, 27, -35, 209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-310087, -351197, 230291, 82596, 355603]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![253, 30, -9, -30, -54]] ![![-14, -3, 0, 3, 0]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9751, 2454, 409, -684, -1700]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![9751, 2454, 409, -684, -1700]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![54, 151, 54, 81, 1]] where
  M :=![![![9751, 2454, 409, -684, -1700], ![26184, 6421, 1099, -1898, -4436], ![21127, 5489, 886, -1439, -3796], ![39753, 9639, 1693, -2910, -6674], ![31585, 8033, 1310, -2187, -5563]]]
  hmulB := by decide  
  f := ![![![92, 9, -6, -11, -18]], ![![281, 36, -12, -37, -62]], ![![343, 29, -14, -37, -74]], ![![745, 71, -45, -88, -148]], ![![734, 77, -38, -89, -153]]]
  g := ![![![587, 1498, 533, 792, -1700], ![1536, 3909, 1391, 2066, -4436], ![1307, 3345, 1190, 1769, -3796], ![2313, 5881, 2093, 3108, -6674], ![1919, 4902, 1744, 2592, -5563]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [60, 105, 57, 117, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [171, 13, 26, 154], [56, 44, 101, 125], [2, 115, 46, 67], [0, 1]]
 g := ![![[75, 59, 119, 67], [63, 17, 77], [106, 117, 0, 73], [87, 66, 140, 85], [139, 100, 14], [56, 1], []], ![[105, 96, 114, 70, 75, 44], [114, 5, 33], [10, 154, 86, 6, 153, 155], [119, 162, 40, 22, 10, 93], [102, 144, 124], [14, 38, 156, 107, 12, 94], [35, 25, 15]], ![[55, 138, 19, 23, 121, 162], [117, 135, 92], [153, 71, 133, 81, 52, 32], [48, 137, 7, 135, 41, 146], [152, 158, 152], [118, 8, 39, 40, 93, 93], [144, 131, 55]], ![[105, 44, 104, 19, 130, 57], [52, 110, 23], [48, 97, 49, 93, 129, 148], [50, 152, 161, 17, 19, 13], [122, 129, 119], [124, 96, 138, 146, 123, 56], [71, 124, 164]]]
 h' := ![![[171, 13, 26, 154], [150, 98, 0, 97], [41, 50, 45, 58], [143, 109, 83, 65], [103, 156, 93, 137], [100, 115, 163, 138], [0, 0, 1], [0, 1]], ![[56, 44, 101, 125], [121, 124, 96, 168], [120, 154, 133, 129], [32, 17, 54, 28], [77, 9, 2, 141], [90, 47, 31, 41], [153, 136, 81, 58], [171, 13, 26, 154]], ![[2, 115, 46, 67], [106, 74, 140, 54], [44, 30, 0, 145], [113, 58, 65, 149], [62, 96, 92, 44], [94, 7, 57, 124], [32, 113, 95, 64], [56, 44, 101, 125]], ![[0, 1], [167, 50, 110, 27], [0, 112, 168, 14], [70, 162, 144, 104], [155, 85, 159, 24], [6, 4, 95, 43], [69, 97, 169, 51], [2, 115, 46, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [126, 18, 99], []]
 b := ![[], [], [72, 29, 71, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [60, 105, 57, 117, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2574435405, -3118898331, 738240909, -1060515909, 4200504726]
  a := ![14, -17, -7, 18, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1326021333, -3684364809, -1306872915, -1972840455, 4200504726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-426, -53, 16, 49, 88]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-426, -53, 16, 49, 88]] 
 ![![173, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![115, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![122, 0, 0, 0, 1]] where
  M :=![![![-426, -53, 16, 49, 88], ![-1369, -166, 54, 159, 284], ![-1525, -179, 64, 179, 318], ![-3237, -375, 139, 382, 676], ![-3204, -366, 141, 380, 671]]]
  hmulB := by decide  
  f := ![![![231, 2, -115, -86, 110]], ![![19, 3, -12, -10, 12]], ![![168, -5, -77, -57, 74]], ![![82, 3, -46, -30, 40]], ![![161, 3, -80, -63, 79]]]
  g := ![![![-86, -53, 16, 49, 88], ![-280, -166, 54, 159, 284], ![-317, -179, 64, 179, 318], ![-677, -375, 139, 382, 676], ![-675, -366, 141, 380, 671]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![9751, 2454, 409, -684, -1700]] ![![-426, -53, 16, 49, 88]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-476269, -118678, -20068, 33908, 82002]]]
 hmul := by decide  
 g := ![![![![-2753, -686, -116, 196, 474]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -2, 18, 6, -8]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-45, -2, 18, 6, -8]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![27, 70, 1, 0, 0], ![3, 106, 0, 1, 0], ![91, 103, 0, 0, 1]] where
  M :=![![![-45, -2, 18, 6, -8], ![114, -65, -38, 14, 16], ![-184, 88, -11, -36, 28], ![-284, 20, 116, 17, -44], ![50, -74, 2, 34, -11]]]
  hmulB := by decide  
  f := ![![![-6779, -722, 330, 822, 1432]], ![![-22302, -2383, 1090, 2702, 4720]], ![![-9887, -1056, 483, 1198, 2092]], ![![-13627, -1456, 666, 1651, 2884]], ![![-16587, -1771, 810, 2010, 3509]]]
  g := ![![![1, -6, 18, 6, -8], ![-2, -3, -38, 14, 16], ![-13, 10, -11, -36, 28], ![3, -30, 116, 17, -44], ![5, -15, 2, 34, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [47, 149, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 178], [0, 1]]
 g := ![![[106, 80], [168, 66], [147], [60], [152, 101], [15, 5], [1]], ![[0, 99], [0, 113], [147], [60], [139, 78], [165, 174], [1]]]
 h' := ![![[30, 178], [159, 120], [35, 148], [121, 46], [16, 113], [11, 97], [132, 30], [0, 1]], ![[0, 1], [0, 59], [0, 31], [69, 133], [5, 66], [57, 82], [137, 149], [30, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [82, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [47, 149, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47075, -2360, 3190, 4794, 9128]
  a := ![6, -12, -2, -14, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5465, -9352, 3190, 4794, 9128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 1, 5, 1, -2]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-14, 1, 5, 1, -2]] 
 ![![179, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-14, 1, 5, 1, -2], ![29, -18, -7, 5, 2], ![-32, 20, -9, -10, 10], ![-86, 14, 30, 1, -10], ![5, -17, 5, 9, -5]]]
  hmulB := by decide  
  f := ![![![-4194, -449, 197, 507, 878]], ![![-381, -41, 18, 46, 80]], ![![-2150, -230, 101, 260, 450]], ![![-398, -43, 19, 48, 84]], ![![-1571, -168, 74, 190, 329]]]
  g := ![![![-2, 1, 5, 1, -2], ![4, -18, -7, 5, 2], ![0, 20, -9, -10, 10], ![-13, 14, 30, 1, -10], ![0, -17, 5, 9, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-140, 45, 43, -7, -14]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-140, 45, 43, -7, -14]] 
 ![![179, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![116, 0, 1, 0, 0], ![168, 0, 0, 1, 0], ![162, 0, 0, 0, 1]] where
  M :=![![![-140, 45, 43, -7, -14], ![217, -144, 19, 65, -42], ![174, 78, -205, -88, 130], ![-844, 316, 208, -75, -46], ![-109, -59, 141, 63, -91]]]
  hmulB := by decide  
  f := ![![![-5104, -393, 307, 671, 1066]], ![![-1975, -154, 119, 259, 414]], ![![-3424, -264, 205, 450, 714]], ![![-5030, -394, 302, 659, 1054]], ![![-4871, -379, 291, 639, 1017]]]
  g := ![![![-26, 45, 43, -7, -14], ![19, -144, 19, 65, -42], ![70, 78, -205, -88, 130], ![-144, 316, 208, -75, -46], ![-47, -59, 141, 63, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2

def I179N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26, -3, 1, 3, 6]] i)))

def SI179N3: IdealEqSpanCertificate' Table ![![-26, -3, 1, 3, 6]] 
 ![![179, 0, 0, 0, 0], ![140, 1, 0, 0, 0], ![154, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![111, 0, 0, 0, 1]] where
  M :=![![![-26, -3, 1, 3, 6], ![-93, -8, 5, 11, 18], ![-94, -14, 5, 12, 22], ![-218, -22, 8, 27, 46], ![-217, -23, 11, 25, 47]]]
  hmulB := by decide  
  f := ![![![-930, -241, -31, 69, 158]], ![![-741, -192, -25, 55, 126]], ![![-812, -210, -27, 60, 138]], ![![-214, -55, -7, 16, 36]], ![![-593, -154, -20, 44, 101]]]
  g := ![![![-3, -3, 1, 3, 6], ![-12, -8, 5, 11, 18], ![-10, -14, 5, 12, 22], ![-25, -22, 8, 27, 46], ![-27, -23, 11, 25, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N3 : Nat.card (O ⧸ I179N3) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N3)

lemma isPrimeI179N3 : Ideal.IsPrime I179N3 := prime_ideal_of_norm_prime hp179.out _ NI179N3
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-45, -2, 18, 6, -8]] ![![-14, 1, 5, 1, -2]]
  ![![-560, 571, -233, -301, 246]] where
 M := ![![![-560, 571, -233, -301, 246]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-560, 571, -233, -301, 246]] ![![-140, 45, 43, -7, -14]]
  ![![388995, -235228, 6612, 99612, -54972]] where
 M := ![![![388995, -235228, 6612, 99612, -54972]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N2 : IdealMulLeCertificate' Table 
  ![![388995, -235228, 6612, 99612, -54972]] ![![-26, -3, 1, 3, 6]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![1354314, -304837, -561881, -25955, 243798]]]
 hmul := by decide  
 g := ![![![![7566, -1703, -3139, -145, 1362]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2, I179N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
    exact isPrimeI179N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1 ⊙ MulI179N2)
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


def P181P0 : CertificateIrreducibleZModOfList' 181 5 2 7 [169, 139, 87, 159, 17, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [167, 56, 111, 90, 159], [14, 129, 7, 54, 157], [112, 151, 17, 44, 167], [52, 25, 46, 174, 60], [0, 1]]
 g := ![![[29, 21, 126, 93, 168], [29, 176, 8, 36], [116, 73, 97, 66, 126], [63, 109, 80, 170], [92, 126, 152, 131, 108], [1], []], ![[125, 57, 76, 41, 114, 166, 120, 160], [120, 161, 72, 81], [58, 91, 58, 125, 167, 90, 6, 93], [128, 73, 86, 16], [110, 47, 132, 77, 112, 127, 165, 8], [43, 92, 130, 9, 64, 24, 69, 8], [32, 59, 120, 122]], ![[81, 23, 116, 173, 129, 66, 144, 164], [149, 39, 156, 143], [138, 17, 124, 4, 140, 179, 111, 74], [117, 21, 69, 46], [100, 70, 175, 160, 128, 178, 45, 19], [89, 0, 36, 127, 57, 0, 124, 71], [2, 73, 105, 33]], ![[10, 128, 168, 146, 11, 127, 55, 3], [43, 121, 122, 126], [148, 81, 99, 134, 146, 143, 92, 111], [139, 161, 137, 11], [171, 178, 70, 81, 4, 45, 117, 148], [131, 33, 121, 80, 81, 6, 147, 3], [102, 100, 142, 15]], ![[39, 169, 47, 43, 10, 65, 96, 178], [31, 16, 21, 167], [10, 149, 34, 149, 101, 133, 94, 5], [108, 68, 124, 62], [23, 64, 18, 55, 119, 92, 132, 148], [37, 7, 81, 135, 109, 43, 17, 119], [142, 54, 43, 161]]]
 h' := ![![[167, 56, 111, 90, 159], [45, 63, 96, 157, 63], [125, 173, 120, 69, 175], [175, 135, 169, 123, 137], [18, 90, 120, 142, 129], [12, 42, 94, 22, 164], [0, 0, 1], [0, 1]], ![[14, 129, 7, 54, 157], [48, 28, 59, 76, 16], [150, 112, 83, 171, 9], [43, 72, 91, 16, 179], [91, 155, 118, 91, 177], [174, 61, 143, 180, 174], [37, 122, 76, 41, 174], [167, 56, 111, 90, 159]], ![[112, 151, 17, 44, 167], [122, 82, 28, 70, 12], [12, 55, 88, 97, 18], [23, 54, 160, 175, 115], [130, 114, 2, 51, 74], [99, 43, 153, 130, 41], [39, 47, 174, 7, 73], [14, 129, 7, 54, 157]], ![[52, 25, 46, 174, 60], [60, 4, 62, 5, 93], [79, 110, 63, 73, 137], [121, 41, 34, 143, 27], [156, 122, 140, 94, 98], [143, 17, 57, 120, 51], [12, 31, 109, 17, 88], [112, 151, 17, 44, 167]], ![[0, 1], [124, 4, 117, 54, 178], [64, 93, 8, 133, 23], [85, 60, 89, 86, 85], [150, 62, 163, 165, 65], [37, 18, 96, 91, 113], [64, 162, 2, 116, 27], [52, 25, 46, 174, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 15, 67, 2], [], [], []]
 b := ![[], [180, 64, 67, 82, 33], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 5
  hpos := by decide
  P := [169, 139, 87, 159, 17, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103579454399, -10536383222, 5869158671, 12743625913, 22749810541]
  a := ![0, 10, 7, 1, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-572262179, -58212062, 32426291, 70406773, 125689561]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1657, 336, -109, 370, -244]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-1657, 336, -109, 370, -244]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![173, 16, 48, 1, 0], ![93, 145, 2, 0, 1]] where
  M :=![![![-1657, 336, -109, 370, -244], ![3290, -1683, 293, -1076, 1236], ![-10377, 2961, -740, 2605, -2152], ![9649, -4153, 809, -2892, 3058], ![-9569, 2411, -648, 2295, -1733]]]
  hmulB := by decide  
  f := ![![![322, -141, -58, 43, 2]], ![![-73, 230, -220, -155, 174]], ![![-1191, 147, 624, 109, -310]], ![![-5, -76, 85, 55, -62]], ![![93, 107, -191, -96, 131]]]
  g := ![![![-225, 156, -91, 370, -244], ![390, -857, 259, -1076, 1236], ![-1366, 1431, -636, 2605, -2152], ![1181, -2101, 699, -2892, 3058], ![-1285, 1136, -562, 2295, -1733]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [13, 53, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 87, 169], [175, 103, 22], [0, 1]]
 g := ![![[53, 187, 144], [72, 177, 160], [44, 187, 156], [65, 181, 138], [155, 142, 78], [181, 59, 1], []], ![[29, 177, 15, 102], [148, 179, 10, 52], [58, 3, 102, 90], [170, 37, 76, 48], [176, 78, 102, 10], [56, 115, 52, 4], [89, 102]], ![[167, 70, 55, 22], [132, 104, 131, 63], [139, 71, 134, 74], [18, 36, 121, 95], [90, 185, 10, 91], [179, 160, 138, 157], [45, 102]]]
 h' := ![![[75, 87, 169], [19, 187, 12], [1, 79, 136], [110, 70, 27], [86, 154, 105], [130, 145, 90], [0, 0, 1], [0, 1]], ![[175, 103, 22], [46, 78, 178], [82, 50, 46], [127, 77, 95], [29, 31, 169], [183, 148, 159], [75, 131, 103], [75, 87, 169]], ![[0, 1], [146, 117, 1], [24, 62, 9], [39, 44, 69], [131, 6, 108], [97, 89, 133], [53, 60, 87], [175, 103, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 186], []]
 b := ![[], [43, 137, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [13, 53, 132, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![116487, 61294, 3927, -13082, -1988]
  a := ![2, -5, -1, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13427, 2926, 3329, -13082, -1988]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![322, -141, -58, 43, 2]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![322, -141, -58, 43, 2]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![131, 48, 1, 0, 0], ![176, 6, 0, 1, 0], ![176, 142, 0, 0, 1]] where
  M :=![![![322, -141, -58, 43, 2], ![-73, 230, -220, -155, 174], ![-1191, 147, 624, 109, -310], ![1675, -859, -163, 314, -92], ![784, -94, -435, -78, 225]]]
  hmulB := by decide  
  f := ![![![-1657, 336, -109, 370, -244]], ![![3290, -1683, 293, -1076, 1236]], ![![-364, -177, -5, -3, 132]], ![![-1373, 235, -87, 292, -170]], ![![869, -929, 114, -447, 685]]]
  g := ![![![0, 11, -58, 43, 2], ![133, -68, -220, -155, 174], ![-249, 71, 624, 109, -310], ![-84, 95, -163, 314, -92], ![167, -56, -435, -78, 225]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [70, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 190], [0, 1]]
 g := ![![[91, 107], [41, 118], [67, 125], [101, 48], [1, 40], [83, 96], [1]], ![[180, 84], [157, 73], [96, 66], [132, 143], [186, 151], [145, 95], [1]]]
 h' := ![![[124, 190], [186, 38], [85, 140], [188, 121], [121, 95], [111, 68], [121, 124], [0, 1]], ![[0, 1], [123, 153], [64, 51], [103, 70], [59, 96], [139, 123], [26, 67], [124, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [45, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [70, 67, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54873, -20573, 25691, -3219, 35674]
  a := ![-16, 22, 13, -24, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-47814, -32985, 25691, -3219, 35674]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-1657, 336, -109, 370, -244]] ![![322, -141, -58, 43, 2]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -6, 3, 4, -4]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![7, -6, 3, 4, -4]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![147, 139, 1, 0, 0], ![2, 95, 0, 1, 0], ![14, 56, 0, 0, 1]] where
  M :=![![![7, -6, 3, 4, -4], ![56, -7, -23, -6, 12], ![-115, 43, 28, -5, -12], ![35, -35, 31, 16, -22], ![75, -21, -22, 7, 1]]]
  hmulB := by decide  
  f := ![![![384, 85, 8, -31, -70]], ![![1081, 228, 22, -93, -194]], ![![1076, 230, 22, -91, -194]], ![![546, 115, 11, -47, -98]], ![![350, 74, 7, -30, -63]]]
  g := ![![![-2, -3, 3, 4, -4], ![17, 16, -23, -6, 12], ![-21, -14, 28, -5, -12], ![-22, -24, 31, 16, -22], ![17, 12, -22, 7, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [63, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [167, 192], [0, 1]]
 g := ![![[77, 144], [191], [86], [151], [28], [191], [167, 1]], ![[0, 49], [191], [86], [151], [28], [191], [141, 192]]]
 h' := ![![[167, 192], [119, 12], [147, 34], [136, 146], [81, 99], [84, 75], [94, 34], [0, 1]], ![[0, 1], [0, 181], [35, 159], [7, 47], [16, 94], [64, 118], [175, 159], [167, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [172, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [63, 26, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32394, -4890, 8973, 710, 12813]
  a := ![-10, 13, 5, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7939, -10555, 8973, 710, 12813]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84, 19, 1, -7, -14]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![84, 19, 1, -7, -14]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![82, 172, 1, 0, 0], ![26, 158, 0, 1, 0], ![42, 56, 0, 0, 1]] where
  M :=![![![84, 19, 1, -7, -14], ![217, 54, 9, -19, -42], ![216, 36, 3, -14, -38], ![400, 80, -2, -35, -66], ![323, 73, 5, -31, -61]]]
  hmulB := by decide  
  f := ![![![-84, 31, -5, 25, -26]], ![![365, -106, 15, -87, 74]], ![![286, -80, 11, -66, 54]], ![![292, -84, 12, -69, 58]], ![![85, -23, 3, -19, 15]]]
  g := ![![![4, 9, 1, -7, -14], ![9, 20, 9, -19, -42], ![10, 20, 3, -14, -38], ![22, 50, -2, -35, -66], ![17, 39, 5, -31, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [30, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [173, 192], [0, 1]]
 g := ![![[65, 46], [31], [59], [72], [4], [63], [173, 1]], ![[110, 147], [31], [59], [72], [4], [63], [153, 192]]]
 h' := ![![[173, 192], [39, 25], [191, 80], [113, 161], [27, 119], [95, 191], [21, 177], [0, 1]], ![[0, 1], [118, 168], [135, 113], [174, 32], [156, 74], [135, 2], [148, 16], [173, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [124, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [30, 20, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9476, -250, 1520, 894, 2944]
  a := ![-3, 7, 3, -1, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1456, -2942, 1520, 894, 2944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 2, -1, 2, -2]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-9, 2, -1, 2, -2]] 
 ![![193, 0, 0, 0, 0], ![152, 1, 0, 0, 0], ![145, 0, 1, 0, 0], ![150, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-9, 2, -1, 2, -2], ![28, -11, 1, -8, 6], ![-55, 19, -6, 15, -16], ![85, -25, 3, -22, 14], ![-35, 17, -6, 11, -17]]]
  hmulB := by decide  
  f := ![![![-242, 55, 66, -7, -20]], ![![-189, 42, 52, -5, -16]], ![![-181, 42, 48, -6, -14]], ![![-195, 45, 53, -6, -16]], ![![-52, 11, 15, -1, -5]]]
  g := ![![![-2, 2, -1, 2, -2], ![13, -11, 1, -8, 6], ![-19, 19, -6, 15, -16], ![32, -25, 3, -22, 14], ![-14, 17, -6, 11, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![7, -6, 3, 4, -4]] ![![84, 19, 1, -7, -14]]
  ![![242, -55, -66, 7, 20]] where
 M := ![![![242, -55, -66, 7, 20]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![242, -55, -66, 7, 20]] ![![-9, 2, -1, 2, -2]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-257, -90, -31, 20, 58]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-257, -90, -31, 20, 58]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![162, 46, 64, 143, 1]] where
  M :=![![![-257, -90, -31, 20, 58], ![-890, -153, -33, 34, 138], ![-607, -221, 18, 71, 68], ![-849, -387, -153, 86, 210], ![-863, -211, -88, 25, 171]]]
  hmulB := by decide  
  f := ![![![6, -1, 0, -1, 0]], ![![1, 4, -2, 1, -4]], ![![29, -5, 2, -7, 2]], ![![3, 9, -3, 4, -12]], ![![17, 5, -2, 0, -9]]]
  g := ![![![-49, -14, -19, -42, 58], ![-118, -33, -45, -100, 138], ![-59, -17, -22, -49, 68], ![-177, -51, -69, -152, 210], ![-145, -41, -56, -124, 171]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [54, 194, 79, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 153, 64, 144], [117, 64, 11, 101], [53, 176, 122, 149], [0, 1]]
 g := ![![[47, 39, 143, 90], [119, 39, 61], [64, 141, 161, 163], [78, 116, 93], [44, 142, 6], [134, 193, 1], []], ![[126, 39, 188, 142, 4, 142], [81, 106, 157], [11, 97, 92, 85, 58, 4], [77, 191, 163], [127, 149, 157], [187, 75, 163], [100, 109, 90, 100, 116, 55]], ![[19, 100, 92, 139, 49, 188], [61, 26, 114], [170, 161, 43, 59, 87, 156], [44, 100, 143], [174, 143, 104], [134, 67, 23], [137, 89, 130, 175, 193, 188]], ![[105, 14, 136, 69, 123, 73], [74, 165, 136], [196, 177, 139, 156, 14, 162], [91, 88, 193], [167, 29, 47], [109, 195, 55], [0, 161, 166, 76, 10, 122]]]
 h' := ![![[23, 153, 64, 144], [98, 44, 2, 175], [90, 22, 146, 88], [67, 152, 190, 153], [39, 54, 8, 129], [53, 27, 183, 177], [0, 0, 0, 1], [0, 1]], ![[117, 64, 11, 101], [141, 177, 22, 46], [56, 47, 19, 123], [83, 56, 14, 164], [164, 118, 173, 44], [179, 41, 153, 74], [69, 37, 109, 44], [23, 153, 64, 144]], ![[53, 176, 122, 149], [29, 107, 166, 96], [163, 50, 45, 36], [179, 59, 170, 90], [114, 121, 158, 52], [60, 171, 96, 164], [91, 50, 160, 107], [117, 64, 11, 101]], ![[0, 1], [112, 66, 7, 77], [94, 78, 184, 147], [39, 127, 20, 184], [15, 101, 55, 169], [94, 155, 159, 176], [142, 110, 125, 45], [53, 176, 122, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [77, 106, 138], []]
 b := ![[], [], [148, 35, 90, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [54, 194, 79, 4, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2876576069228, -1337897934436, 395891665306, -21693553658, 1824320624374]
  a := ![60, -75, -39, 62, -233]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1514804655928, -432774856120, -590663087790, -1324363161620, 1824320624374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-6, 1, 0, 1, 0]] 
 ![![197, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![173, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-6, 1, 0, 1, 0], ![-1, -4, 2, -1, 4], ![-29, 5, -2, 7, -2], ![-3, -9, 3, -4, 12], ![-46, 4, 1, 8, 1]]]
  hmulB := by decide  
  f := ![![![257, 90, 31, -20, -58]], ![![28, 9, 3, -2, -6]], ![![37, 13, 4, -3, -8]], ![![230, 81, 28, -18, -52]], ![![67, 23, 8, -5, -15]]]
  g := ![![![-1, 1, 0, 1, 0], ![0, -4, 2, -1, 4], ![-6, 5, -2, 7, -2], ![1, -9, 3, -4, 12], ![-8, 4, 1, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-257, -90, -31, 20, 58]] ![![-6, 1, 0, 1, 0]]
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


lemma PB318I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB318I4 : PrimesBelowBoundCertificateInterval O 151 197 318 where
  m := 9
  g := ![3, 1, 2, 2, 4, 1, 2, 3, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB318I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2, I179N3]
    · exact ![I181N0]
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
    · exact ![3869893, 157, 157]
    · exact ![115063617043]
    · exact ![4657463, 27889]
    · exact ![895745041, 173]
    · exact ![32041, 179, 179, 179]
    · exact ![194264244901]
    · exact ![6967871, 36481]
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
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
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
      exact NI179N1
      exact NI179N2
      exact NI179N3
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
      exact NI193N2
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I157N2, I173N1, I179N1, I179N2, I179N3, I193N2, I197N1]
  Il := ![[I157N1, I157N2], [], [], [I173N1], [I179N1, I179N2, I179N3], [], [], [I193N2], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
