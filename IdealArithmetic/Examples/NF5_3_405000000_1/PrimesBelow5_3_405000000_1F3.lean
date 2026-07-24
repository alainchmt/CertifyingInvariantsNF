
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -7, -30, 7, -18]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![7, -7, -30, 7, -18]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![65, 91, 9, 1, 0], ![13, 12, 23, 0, 1]] where
  M :=![![![7, -7, -30, 7, -18], ![-14, 93, -148, -8, 6], ![16, -54, 123, -144, -36], ![288, -128, -810, 483, -936], ![-66, 784, -1476, 254, -131]]]
  hmulB := by decide  
  f := ![![![-88041, 225093, -38488, 8637, -28728]], ![![-17274, 44145, -7548, 1694, -5634]], ![![-3388, 8650, -1479, 332, -1104]], ![![-68465, 175026, -29927, 6716, -22338]], ![![-13569, 34687, -5931, 1331, -4427]]]
  g := ![![![-2, -4, 3, 7, -18], ![4, 7, -2, -8, 6], ![92, 126, 21, -144, -36], ![-177, -307, 153, 483, -936], ![-139, -194, -7, 254, -131]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [73, 6, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 68, 31], [55, 38, 76], [0, 1]]
 g := ![![[43, 55, 64], [62, 21, 9], [7, 76], [51, 105, 23], [104, 40], [1]], ![[8, 27, 54, 84], [48, 52, 55, 63], [81, 102], [72, 45, 32, 63], [105, 1], [84, 92, 19, 45]], ![[87, 79, 74, 83], [60, 93, 70, 89], [55, 34], [65, 66, 94, 12], [92, 79], [44, 7, 94, 62]]]
 h' := ![![[71, 68, 31], [75, 1, 8], [80, 25, 104], [22, 96, 41], [91, 7, 68], [34, 101, 19], [0, 1]], ![[55, 38, 76], [104, 27, 14], [25, 97, 19], [69, 45, 40], [17, 74, 19], [70, 43, 1], [71, 68, 31]], ![[0, 1], [75, 79, 85], [98, 92, 91], [58, 73, 26], [62, 26, 20], [95, 70, 87], [55, 38, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 30], []]
 b := ![[], [76, 67, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [73, 6, 88, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1238160, 1816016, 1415975, -3022825, 3381315]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1413910, 2208573, -459335, -3022825, 3381315]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7683, -19650, 3360, -754, 2508]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![7683, -19650, 3360, -754, 2508]] 
 ![![107, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![7683, -19650, 3360, -754, 2508], ![1508, -3857, 660, -148, 492], ![296, -756, 127, -28, 96], ![56, -144, 24, -9, 24], ![1932, -4944, 852, -192, 631]]]
  hmulB := by decide  
  f := ![![![11985, -76482, 13656, -2618, 10020]], ![![833, -5315, 948, -182, 696]], ![![6518, -41592, 7423, -1424, 5448]], ![![2474, -15780, 2808, -541, 2064]], ![![6399, -40830, 7284, -1398, 5347]]]
  g := ![![![-1645, -19650, 3360, -754, 2508], ![-323, -3857, 660, -148, 492], ![-62, -756, 127, -28, 96], ![-14, -144, 24, -9, 24], ![-417, -4944, 852, -192, 631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3479, -22137, 3964, -757, 2904]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![3479, -22137, 3964, -757, 2904]] 
 ![![107, 0, 0, 0, 0], ![91, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![3479, -22137, 3964, -757, 2904], ![1514, -9651, 1728, -330, 1266], ![660, -4210, 753, -144, 552], ![288, -1836, 326, -63, 240], ![442, -2802, 500, -96, 367]]]
  hmulB := by decide  
  f := ![![![39, -113, 78, 9, -42]], ![![33, -94, 62, 9, -36]], ![![21, -65, 51, -1, -18]], ![![41, -127, 108, 8, -54]], ![![21, -45, 6, 23, -35]]]
  g := ![![![15829, -22137, 3964, -757, 2904], ![6901, -9651, 1728, -330, 1266], ![3011, -4210, 753, -144, 552], ![1315, -1836, 326, -63, 240], ![2005, -2802, 500, -96, 367]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![7, -7, -30, 7, -18]] ![![7683, -19650, 3360, -754, 2508]]
  ![![-39, 113, -78, -9, 42]] where
 M := ![![![-39, 113, -78, -9, 42]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-39, 113, -78, -9, 42]] ![![3479, -22137, 3964, -757, 2904]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2131, 13600, -2435, 465, -1784]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-2131, 13600, -2435, 465, -1784]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![50, 86, 1, 0, 0], ![60, 66, 0, 1, 0], ![26, 97, 0, 0, 1]] where
  M :=![![![-2131, 13600, -2435, 465, -1784], ![-930, 5935, -1061, 203, -778], ![-406, 2588, -458, 89, -338], ![-178, 1124, -187, 40, -142], ![-270, 1714, -297, 59, -221]]]
  hmulB := by decide  
  f := ![![![-275, 704, -121, 29, -92]], ![![-58, 151, -37, 5, -10]], ![![-172, 442, -84, 17, -50]], ![![-186, 478, -89, 20, -58]], ![![-118, 305, -64, 12, -31]]]
  g := ![![![1267, 3352, -2435, 465, -1784], ![552, 1461, -1061, 203, -778], ![238, 632, -458, 89, -338], ![96, 260, -187, 40, -142], ![154, 411, -297, 59, -221]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [88, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 108], [0, 1]]
 g := ![![[10, 83], [5], [44, 88], [78, 43], [31], [101, 1]], ![[0, 26], [5], [103, 21], [61, 66], [31], [93, 108]]]
 h' := ![![[101, 108], [84, 65], [52, 88], [3, 52], [99, 77], [50, 85], [0, 1]], ![[0, 1], [0, 44], [2, 21], [23, 57], [28, 32], [24, 24], [101, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [106, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [88, 8, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![898, -6293, 14376, -3706, -261]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4484, -8924, 14376, -3706, -261]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -22, 71, -29, 12]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-3, -22, 71, -29, 12]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![81, 4, 1, 0, 0], ![3, 65, 0, 1, 0], ![100, 68, 0, 0, 1]] where
  M :=![![![-3, -22, 71, -29, 12], ![58, -109, -1, 105, -150], ![-210, 868, -1144, 89, 330], ![-178, -1352, 4105, -1982, 1194], ![686, -2342, 2539, 197, -1297]]]
  hmulB := by decide  
  f := ![![![-2635, 16310, -2763, 571, -2088]], ![![-1142, 6859, -769, 271, -750]], ![![-2005, 12394, -2073, 436, -1578]], ![![-757, 4533, -497, 180, -492]], ![![-3134, 19250, -2993, 695, -2377]]]
  g := ![![![-63, 7, 71, -29, 12], ![136, 30, -1, 105, -150], ![543, -209, -1144, 89, 330], ![-4093, 274, 4105, -1982, 1194], ![-696, 577, 2539, 197, -1297]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [46, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 108], [0, 1]]
 g := ![![[66, 64], [80], [76, 34], [8, 29], [64], [16, 1]], ![[0, 45], [80], [75, 75], [36, 80], [64], [32, 108]]]
 h' := ![![[16, 108], [90, 8], [101, 25], [68, 19], [74, 47], [27, 101], [0, 1]], ![[0, 1], [0, 101], [65, 84], [45, 90], [63, 62], [8, 8], [16, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [85, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [46, 93, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![114, -383, 229, -88, -52]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-119, 73, 229, -88, -52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153, 398, -84, 14, -56]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-153, 398, -84, 14, -56]] 
 ![![109, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![75, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-153, 398, -84, 14, -56], ![-28, 99, -64, 0, -28], ![0, 84, -153, -8, -56], ![16, 208, -444, -25, -160], ![-28, 228, -296, -12, -113]]]
  hmulB := by decide  
  f := ![![![51, -350, 12, -6, 64]], ![![9, -63, 4, -2, 12]], ![![37, -246, 11, -2, 40]], ![![43, -302, -24, 1, 64]], ![![11, -98, 4, -10, 31]]]
  g := ![![![-9, 398, -84, 14, -56], ![35, 99, -64, 0, -28], ![115, 84, -153, -8, -56], ![341, 208, -444, -25, -160], ![209, 228, -296, -12, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-2131, 13600, -2435, 465, -1784]] ![![-3, -22, 71, -29, 12]]
  ![![-51, 350, -12, 6, -64]] where
 M := ![![![-51, 350, -12, 6, -64]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-51, 350, -12, 6, -64]] ![![-153, 398, -84, 14, -56]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -91, 16, -3, 12]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![11, -91, 16, -3, 12]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![46, 86, 1, 0, 0], ![112, 108, 0, 1, 0], ![90, 46, 0, 0, 1]] where
  M :=![![![11, -91, 16, -3, 12], ![6, -43, 8, -2, 6], ![4, -22, 5, 0, 0], ![0, 4, -22, 5, 0], ![-2, -2, -4, -4, 7]]]
  hmulB := by decide  
  f := ![![![-55, 131, -26, 5, -18]], ![![-10, 27, -16, 0, -6]], ![![-30, 74, -23, 2, -12]], ![![-64, 156, -42, 5, -24]], ![![-48, 116, -28, 4, -17]]]
  g := ![![![-13, -15, 16, -3, 12], ![-6, -7, 8, -2, 6], ![-2, -4, 5, 0, 0], ![4, 12, -22, 5, 0], ![0, 4, -4, -4, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [59, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 112], [0, 1]]
 g := ![![[76, 52], [111], [15], [98], [3, 36], [36, 1]], ![[27, 61], [111], [15], [98], [56, 77], [72, 112]]]
 h' := ![![[36, 112], [61, 39], [100, 87], [9, 69], [49, 95], [23, 107], [0, 1]], ![[0, 1], [109, 74], [68, 26], [7, 44], [79, 18], [33, 6], [36, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [35, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [59, 77, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4501, -30753, 55552, -9021, -540]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13203, -33709, 55552, -9021, -540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50431, 330444, -59225, 11273, -43372]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-50431, 330444, -59225, 11273, -43372]] 
 ![![113, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-50431, 330444, -59225, 11273, -43372], ![-22546, 145603, -26085, 4973, -19106], ![-9946, 63824, -11432, 2181, -8374], ![-4362, 27912, -4999, 954, -3662], ![-6094, 41038, -7361, 1397, -5389]]]
  hmulB := by decide  
  f := ![![![653, 7956, -17135, -1007, -6152]], ![![405, 4923, -10606, -622, -3810]], ![![229, 2800, -6031, -348, -2162]], ![![548, 6732, -14481, -862, -5190]], ![![393, 4702, -10146, -598, -3661]]]
  g := ![![![-167534, 330444, -59225, 11273, -43372], ![-73832, 145603, -26085, 4973, -19106], ![-32366, 63824, -11432, 2181, -8374], ![-14155, 27912, -4999, 954, -3662], ![-20800, 41038, -7361, 1397, -5389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, 732, -131, 25, -96]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-115, 732, -131, 25, -96]] 
 ![![113, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-115, 732, -131, 25, -96], ![-50, 319, -57, 11, -42], ![-22, 140, -26, 5, -18], ![-10, 60, -7, 0, -6], ![-14, 90, -13, 3, -13]]]
  hmulB := by decide  
  f := ![![![-575, 1460, -229, 57, -180]], ![![-403, 1023, -160, 40, -126]], ![![-443, 1124, -175, 44, -138]], ![![-102, 256, -35, 10, -30]], ![![-159, 402, -60, 16, -49]]]
  g := ![![![-390, 732, -131, 25, -96], ![-170, 319, -57, 11, -42], ![-74, 140, -26, 5, -18], ![-35, 60, -7, 0, -6], ![-50, 90, -13, 3, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2

def I113N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -38, 75, 5, 22]] i)))

def SI113N3: IdealEqSpanCertificate' Table ![![-1, -38, 75, 5, 22]] 
 ![![113, 0, 0, 0, 0], ![107, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-1, -38, 75, 5, 22], ![-10, -79, 175, 21, 74], ![-42, -264, 650, -15, 274], ![30, -1168, 2157, 132, 458], ![-10, -500, 919, 209, 283]]]
  hmulB := by decide  
  f := ![![![9038179, -23118830, 3953169, -887011, 2950658]], ![![8573975, -21931445, 3750134, -841454, 2799112]], ![![6161841, -15761426, 2695101, -604726, 2011632]], ![![800444, -2047464, 350103, -78556, 261318]], ![![2659577, -6802950, 1163260, -261012, 868261]]]
  g := ![![![-22, -38, 75, 5, 22], ![-68, -79, 175, 21, 74], ![-272, -264, 650, -15, 274], ![-509, -1168, 2157, 132, 458], ![-254, -500, 919, 209, 283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N3 : Nat.card (O ⧸ I113N3) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N3)

lemma isPrimeI113N3 : Ideal.IsPrime I113N3 := prime_ideal_of_norm_prime hp113.out _ NI113N3
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![11, -91, 16, -3, 12]] ![![-50431, 330444, -59225, 11273, -43372]]
  ![![1277767, -8185085, 1466013, -279742, 1073888]] where
 M := ![![![1277767, -8185085, 1466013, -279742, 1073888]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![1277767, -8185085, 1466013, -279742, 1073888]] ![![-115, 732, -131, 25, -96]]
  ![![217821747, -1390609451, 249043680, -47540031, 182437612]] where
 M := ![![![217821747, -1390609451, 249043680, -47540031, 182437612]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N2 : IdealMulLeCertificate' Table 
  ![![217821747, -1390609451, 249043680, -47540031, 182437612]] ![![-1, -38, 75, 5, 22]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-22138847, 141338931, -25312339, 4831880, -18542622]]]
 hmul := by decide  
 g := ![![![![-195919, 1250787, -224003, 42760, -164094]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2, I113N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
    exact isPrimeI113N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1 ⊙ MulI113N2)
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


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [118, 79, 34, 97, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 115, 113, 46, 119], [34, 5, 20, 44, 124], [102, 13, 84, 119, 29], [26, 120, 37, 45, 109], [0, 1]]
 g := ![![[21, 9, 19, 63, 52], [55, 4, 32, 28, 16], [110, 82, 104, 4, 94], [44, 60, 126, 19, 25], [41, 97, 1], []], ![[89, 0, 4, 28, 88, 30, 38, 48], [49, 85, 81, 121, 18, 32, 72, 78], [71, 13, 65, 101, 23, 27, 48, 23], [119, 95, 10, 79, 45, 82, 86, 93], [80, 30, 0, 43, 98, 50, 120, 3], [122, 68, 66, 71, 38, 47, 62, 123]], ![[120, 18, 121, 32, 89, 110, 42, 34], [76, 79, 57, 120, 41, 108, 18, 113], [115, 63, 114, 106, 104, 125, 25, 113], [13, 53, 69, 50, 62, 35, 14, 88], [106, 7, 83, 108, 68, 20, 110, 117], [86, 52, 111, 4, 2, 90, 93, 100]], ![[25, 16, 89, 51, 29, 42, 116, 126], [13, 7, 38, 21, 84, 97, 38, 91], [3, 53, 73, 116, 82, 86, 17, 46], [35, 81, 55, 30, 7, 8, 90, 28], [111, 53, 3, 99, 34, 25, 50, 3], [77, 73, 90, 125, 37, 11, 113, 5]], ![[118, 1, 13, 37, 29, 57, 39, 56], [99, 6, 90, 68, 103, 99, 41, 106], [32, 94, 99, 46, 0, 68, 94, 65], [60, 27, 86, 78, 88, 79, 80, 45], [2, 115, 123, 106, 102, 108, 115, 28], [24, 21, 39, 81, 90, 13, 6, 10]]]
 h' := ![![[62, 115, 113, 46, 119], [114, 50, 110, 11, 68], [101, 20, 49, 0, 4], [15, 2, 120, 70, 100], [115, 47, 96, 12, 122], [0, 0, 0, 1], [0, 1]], ![[34, 5, 20, 44, 124], [71, 27, 21, 98, 116], [17, 15, 113, 108, 28], [87, 99, 6, 109, 34], [104, 59, 18, 18, 121], [31, 37, 47, 3, 29], [62, 115, 113, 46, 119]], ![[102, 13, 84, 119, 29], [44, 72, 4, 46, 83], [91, 50, 124, 95, 89], [63, 59, 29, 41, 89], [22, 42, 2, 126, 93], [73, 92, 91, 96, 56], [34, 5, 20, 44, 124]], ![[26, 120, 37, 45, 109], [70, 29, 6, 64, 17], [33, 44, 95, 125, 25], [53, 104, 98, 84, 101], [108, 56, 25, 60, 121], [54, 26, 90, 120, 28], [102, 13, 84, 119, 29]], ![[0, 1], [32, 76, 113, 35, 97], [47, 125, 0, 53, 108], [119, 117, 1, 77, 57], [79, 50, 113, 38, 51], [12, 99, 26, 34, 14], [26, 120, 37, 45, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 52, 116, 71], [], [], []]
 b := ![[], [124, 12, 94, 50, 120], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [118, 79, 34, 97, 30, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5554181837004, 75296912173337, -157394750132019, 53729915971500, -14188367602507]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-43733715252, 592889072231, -1239328741197, 423070204500, -111719429941]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3337, 35281, -77990, -4465, -28002]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![3337, 35281, -77990, -4465, -28002]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![4, 33, 17, 1, 0], ![77, 115, 29, 0, 1]] where
  M :=![![![3337, 35281, -77990, -4465, -28002], ![8930, 106415, -230132, -13056, -82794], ![26112, 313994, -677899, -38432, -243924], ![76864, 924944, -1996618, -113187, -718440], ![48430, 581648, -1255972, -71210, -451921]]]
  hmulB := by decide  
  f := ![![![-31, 9, 92, -99, 108]], ![![198, -661, 684, 74, -378]], ![![-148, 1858, -3841, 1292, -312]], ![![10, 103, -301, 139, -78]], ![![131, -214, -111, 273, -343]]]
  g := ![![![16621, 25976, 6183, -4465, -28002], ![49132, 76783, 18266, -13056, -82794], ![144748, 226210, 53811, -38432, -243924], ![426332, 666265, 158491, -113187, -718440], ![268177, 419103, 99697, -71210, -451921]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [35, 95, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 54, 42], [100, 76, 89], [0, 1]]
 g := ![![[125, 124, 34], [75, 49, 59], [45, 107], [15, 91], [61, 62], [48, 1], []], ![[78, 116, 83, 82], [85, 27, 69, 87], [77, 59], [15, 13], [59, 20], [73, 12], [128, 61]], ![[55, 87, 124, 99], [114, 90, 107, 11], [13, 25], [36, 100], [60, 129], [83, 34], [81, 61]]]
 h' := ![![[79, 54, 42], [126, 111, 77], [49, 50, 94], [107, 12, 99], [97, 90, 109], [23, 121, 113], [0, 0, 1], [0, 1]], ![[100, 76, 89], [130, 45, 34], [19, 43, 74], [116, 92, 37], [36, 122, 12], [23, 97, 46], [58, 1, 76], [79, 54, 42]], ![[0, 1], [24, 106, 20], [110, 38, 94], [98, 27, 126], [21, 50, 10], [5, 44, 103], [91, 130, 54], [100, 76, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 109], []]
 b := ![[], [121, 44, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [35, 95, 83, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7428339, 36112822, -53621214, 8474368, 9315738]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5791127, -10037032, -3571312, 8474368, 9315738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 9, 92, -99, 108]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-31, 9, 92, -99, 108]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![130, 114, 1, 0, 0], ![114, 103, 0, 1, 0], ![99, 92, 0, 0, 1]] where
  M :=![![![-31, 9, 92, -99, 108], ![198, -661, 684, 74, -378], ![-148, 1858, -3841, 1292, -312], ![-2584, 3684, 2926, -5801, 7128], ![1070, -6594, 11104, -2592, -731]]]
  hmulB := by decide  
  f := ![![![3337, 35281, -77990, -4465, -28002]], ![![8930, 106415, -230132, -13056, -82794]], ![![11282, 130014, -282837, -16086, -101700]], ![![10512, 121433, -264054, -15015, -94950]], ![![9163, 105837, -230146, -13087, -82757]]]
  g := ![![![-87, -78, 92, -99, 108], ![-456, -393, 684, 74, -378], ![2922, 2560, -3841, 1292, -312], ![-3262, -2963, 2926, -5801, 7128], ![-8203, -7162, 11104, -2592, -731]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [88, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 130], [0, 1]]
 g := ![![[126, 33], [107, 27], [108], [123], [84], [113], [1]], ![[105, 98], [66, 104], [108], [123], [84], [113], [1]]]
 h' := ![![[47, 130], [16, 66], [66, 17], [111, 97], [18, 75], [27, 52], [43, 47], [0, 1]], ![[0, 1], [105, 65], [79, 114], [85, 34], [6, 56], [113, 79], [25, 84], [47, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [59, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [88, 84, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-984, -27971, 69552, -17786, 18089]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-67221, -59459, 69552, -17786, 18089]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![3337, 35281, -77990, -4465, -28002]] ![![-31, 9, 92, -99, 108]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 6, -7, -3, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-1, 6, -7, -3, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![42, 73, 1, 0, 0], ![85, 56, 0, 1, 0], ![26, 46, 0, 0, 1]] where
  M :=![![![-1, 6, -7, -3, 0], ![6, -7, -3, -1, -18], ![2, 76, -172, 35, -42], ![-70, 240, -197, -158, 126], ![26, -102, 169, -93, -47]]]
  hmulB := by decide  
  f := ![![![-4589, 21634, -3833, 761, -2820]], ![![-1522, 8213, -1463, 285, -1074]], ![![-2222, 11033, -1959, 386, -1440]], ![![-3471, 16790, -2978, 589, -2190]], ![![-1388, 6888, -1223, 241, -899]]]
  g := ![![![4, 5, -7, -3, 0], ![5, 8, -3, -1, -18], ![39, 92, -172, 35, -42], ![134, 129, -197, -158, 126], ![15, -37, 169, -93, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [70, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 136], [0, 1]]
 g := ![![[114, 87], [100], [122], [59, 112], [126], [60], [1]], ![[33, 50], [100], [122], [87, 25], [126], [60], [1]]]
 h' := ![![[103, 136], [85, 118], [80, 10], [117, 81], [36, 48], [15, 117], [67, 103], [0, 1]], ![[0, 1], [46, 19], [14, 127], [103, 56], [48, 89], [10, 20], [127, 34], [103, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [111, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [70, 34, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![392, -1457, 1697, -34, -539]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-394, -720, 1697, -34, -539]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1963, -5016, 851, -193, 638]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![1963, -5016, 851, -193, 638]] 
 ![![137, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![119, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![1963, -5016, 851, -193, 638], ![386, -975, 147, -39, 118], ![78, -164, -30, -11, 2], ![22, 48, -179, -12, -62], ![498, -1208, 99, -55, 119]]]
  hmulB := by decide  
  f := ![![![-521, 3276, -583, 91, -398]], ![![-355, 2233, -396, 62, -272]], ![![-453, 2852, -513, 82, -348]], ![![-120, 732, -133, 12, -74]], ![![-95, 592, -88, 10, -71]]]
  g := ![![![2606, -5016, 851, -193, 638], ![524, -975, 147, -39, 118], ![140, -164, -30, -11, 2], ![137, 48, -179, -12, -62], ![728, -1208, 99, -55, 119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -36, 78, 4, 28]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-3, -36, 78, 4, 28]] 
 ![![137, 0, 0, 0, 0], ![117, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![-3, -36, 78, 4, 28], ![-8, -107, 228, 14, 80], ![-28, -300, 655, 40, 244], ![-80, -924, 2016, 87, 728], ![-40, -604, 1276, 70, 433]]]
  hmulB := by decide  
  f := ![![![20165, -31732, 5158, -1356, 3932]], ![![17241, -27087, 4402, -1158, 3356]], ![![1619, -2520, 409, -108, 312]], ![![12215, -19208, 3122, -821, 2380]], ![![7990, -12596, 2048, -538, 1561]]]
  g := ![![![11, -36, 78, 4, 28], ![33, -107, 228, 14, 80], ![83, -300, 655, 40, 244], ![287, -924, 2016, 87, 728], ![200, -604, 1276, 70, 433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2

def I137N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![717205, -1834327, 313655, -70380, 234114]] i)))

def SI137N3: IdealEqSpanCertificate' Table ![![717205, -1834327, 313655, -70380, 234114]] 
 ![![137, 0, 0, 0, 0], ![128, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![93, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![717205, -1834327, 313655, -70380, 234114], ![140760, -360011, 61559, -13813, 45948], ![27626, -70658, 12082, -2711, 9018], ![5422, -13868, 2371, -532, 1770], ![180320, -461186, 78859, -17695, 58861]]]
  hmulB := by decide  
  f := ![![![143, 1251, -3005, -164, -1080]], ![![136, 1199, -2873, -157, -1032]], ![![66, 598, -1416, -79, -510]], ![![121, 1107, -2606, -138, -942]], ![![45, 453, -1044, -55, -371]]]
  g := ![![![1585651, -1834327, 313655, -70380, 234114], ![311205, -360011, 61559, -13813, 45948], ![61079, -70658, 12082, -2711, 9018], ![11988, -13868, 2371, -532, 1770], ![398664, -461186, 78859, -17695, 58861]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N3 : Nat.card (O ⧸ I137N3) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N3)

lemma isPrimeI137N3 : Ideal.IsPrime I137N3 := prime_ideal_of_norm_prime hp137.out _ NI137N3
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-1, 6, -7, -3, 0]] ![![1963, -5016, 851, -193, 638]]
  ![![-259, 170, 778, 72, 242]] where
 M := ![![![-259, 170, 778, 72, 242]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-259, 170, 778, 72, 242]] ![![-3, -36, 78, 4, 28]]
  ![![-37807, -454962, 982092, 55668, 353382]] where
 M := ![![![-37807, -454962, 982092, 55668, 353382]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N2 : IdealMulLeCertificate' Table 
  ![![-37807, -454962, 982092, 55668, 353382]] ![![717205, -1834327, 313655, -70380, 234114]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-872827, 2234059, -384833, 85488, -286056]]]
 hmul := by decide  
 g := ![![![![-6371, 16307, -2809, 624, -2088]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2, I137N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
    exact isPrimeI137N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1 ⊙ MulI137N2)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3977, 17311, -3058, 615, -2252]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-3977, 17311, -3058, 615, -2252]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![8, 42, 0, 122, 1]] where
  M :=![![![-3977, 17311, -3058, 615, -2252], ![-1230, 6261, -1112, 216, -814], ![-432, 2458, -417, 84, -332], ![-168, 1064, -278, 79, -160], ![-782, 2914, -556, 98, -341]]]
  hmulB := by decide  
  f := ![![![-9, -105, 228, 13, 82]], ![![-26, -311, 672, 38, 242]], ![![-76, -918, 1981, 112, 712]], ![![-224, -2700, 5826, 333, 2096]], ![![-206, -2482, 5356, 306, 1927]]]
  g := ![![![101, 805, -22, 1981, -2252], ![38, 291, -8, 716, -814], ![16, 118, -3, 292, -332], ![8, 56, -2, 141, -160], ![14, 124, -4, 300, -341]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [34, 95, 77, 119, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 82, 133, 107], [119, 39, 91, 19], [58, 17, 54, 13], [0, 1]]
 g := ![![[115, 71, 42, 36], [55, 47, 29, 96], [83, 68, 7], [47, 4, 120, 125], [90, 55, 122], [1], []], ![[86, 13, 8, 57, 5, 5], [50, 23, 20, 72, 35, 42], [72, 77, 5], [28, 82, 124, 127, 131, 96], [60, 87, 113], [15, 120, 121], [37, 14, 51]], ![[22, 7, 38, 122, 44, 88], [137, 132, 59, 46, 85, 22], [89, 19, 55], [81, 28, 5, 83, 4, 27], [98, 27, 100], [55, 38, 36], [92, 114, 83]], ![[74, 68, 83, 17, 70, 46], [132, 27, 51, 45, 34, 122], [33, 29, 52], [75, 124, 72, 68, 0, 127], [57, 74, 55], [6, 78, 11], [123, 58, 30]]]
 h' := ![![[121, 82, 133, 107], [76, 37, 13, 6], [132, 32, 138, 42], [70, 82, 109, 29], [42, 71, 43, 79], [105, 44, 62, 20], [0, 0, 1], [0, 1]], ![[119, 39, 91, 19], [118, 105, 58, 75], [90, 103, 136, 44], [133, 72, 111, 127], [99, 44, 0, 54], [38, 45, 102, 35], [39, 7, 54, 128], [121, 82, 133, 107]], ![[58, 17, 54, 13], [14, 39, 7, 44], [10, 132, 110, 22], [123, 72, 12, 65], [4, 58, 108, 90], [0, 85, 89, 10], [52, 2, 80, 133], [119, 39, 91, 19]], ![[0, 1], [86, 97, 61, 14], [20, 11, 33, 31], [13, 52, 46, 57], [71, 105, 127, 55], [52, 104, 25, 74], [16, 130, 4, 17], [58, 17, 54, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 7, 25], []]
 b := ![[], [], [50, 101, 85, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [34, 95, 77, 119, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31723897150, 85246887444, -61866239262, -30620894212, 70032861888]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4258897786, -20547721668, -445080858, -61687985932, 70032861888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -105, 228, 13, 82]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-9, -105, 228, 13, 82]] 
 ![![139, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![102, 0, 0, 0, 1]] where
  M :=![![![-9, -105, 228, 13, 82], ![-26, -311, 672, 38, 242], ![-76, -918, 1981, 112, 712], ![-224, -2700, 5826, 333, 2096], ![-142, -1696, 3664, 208, 1321]]]
  hmulB := by decide  
  f := ![![![-3977, 17311, -3058, 615, -2252]], ![![-2870, 12499, -2208, 444, -1626]], ![![-232, 1014, -179, 36, -132]], ![![-974, 4242, -750, 151, -552]], ![![-2924, 12724, -2248, 452, -1655]]]
  g := ![![![-1, -105, 228, 13, 82], ![-2, -311, 672, 38, 242], ![-4, -918, 1981, 112, 712], ![-14, -2700, 5826, 333, 2096], ![-12, -1696, 3664, 208, 1321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-3977, 17311, -3058, 615, -2252]] ![![-9, -105, 228, 13, 82]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [143, 24, 100, 3, 17, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 147, 14, 114, 107], [0, 55, 4, 49, 12], [77, 114, 65, 84, 145], [9, 130, 66, 51, 34], [0, 1]]
 g := ![![[107, 87, 70, 6, 133], [84, 13, 87, 114], [77, 134, 112, 67, 104], [112, 127, 120, 9], [120, 6, 137, 132, 1], [], []], ![[102, 97, 14, 108, 144, 111, 146, 53], [148, 113, 55, 37], [35, 58, 91, 43, 140, 44, 49, 24], [132, 89, 82, 110], [20, 3, 114, 129, 41, 90, 8, 7], [111, 57, 63, 144], [32, 123, 70, 125]], ![[137, 22, 93, 107, 129, 131, 6, 106], [114, 114, 53, 142], [142, 31, 148, 32, 103, 36, 132, 84], [103, 103, 21, 68], [137, 135, 117, 35, 35, 44, 12, 146], [47, 145, 125, 133], [102, 147, 69, 144]], ![[126, 68, 77, 36, 3, 36, 56, 103], [81, 90, 122, 53], [49, 145, 40, 91, 66, 57, 134, 68], [93, 33, 16, 142], [146, 114, 117, 51, 138, 73, 30, 148], [104, 99, 87, 68], [32, 37, 99, 16]], ![[47, 2, 20, 7, 10, 34, 110, 48], [101, 122, 68, 45], [148, 111, 144, 91, 71, 131, 95, 56], [22, 7, 29, 63], [64, 66, 19, 141, 48, 6, 138, 65], [126, 67, 7, 54], [141, 119, 57, 113]]]
 h' := ![![[46, 147, 14, 114, 107], [133, 88, 124, 122, 27], [15, 147, 128, 70, 73], [105, 65, 100, 138, 113], [124, 136, 2, 120, 3], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 55, 4, 49, 12], [55, 87, 24, 135, 32], [106, 47, 11, 147, 127], [48, 73, 70, 97, 41], [148, 62, 127, 65, 109], [35, 108, 91, 38, 71], [73, 84, 30, 86, 12], [46, 147, 14, 114, 107]], ![[77, 114, 65, 84, 145], [64, 17, 55, 145, 122], [107, 41, 89, 6, 69], [140, 19, 69, 91, 93], [77, 17, 131, 136, 98], [91, 141, 27, 113, 127], [16, 73, 141, 138, 27], [0, 55, 4, 49, 12]], ![[9, 130, 66, 51, 34], [124, 76, 147, 82, 58], [54, 102, 105, 46, 84], [65, 139, 23, 1, 70], [38, 58, 66, 50, 69], [23, 15, 74, 2, 75], [12, 24, 142, 75, 51], [77, 114, 65, 84, 145]], ![[0, 1], [98, 30, 97, 112, 59], [104, 110, 114, 29, 94], [63, 2, 36, 120, 130], [123, 25, 121, 76, 19], [57, 34, 106, 145, 24], [33, 117, 133, 148, 59], [9, 130, 66, 51, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 112, 33], [], [], []]
 b := ![[], [144, 70, 81, 54], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [143, 24, 100, 3, 17, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10129058293, -5009726784537, 12211891863753, -4947616969682, 2228783664721]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-67980257, -33622327413, 81959005797, -33205483018, 14958279629]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18343, -117033, 20702, -4021, 15270]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![18343, -117033, 20702, -4021, 15270]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![140, 27, 53, 1, 0], ![68, 71, 83, 0, 1]] where
  M :=![![![18343, -117033, 20702, -4021, 15270], ![8042, -50779, 8334, -1796, 6414], ![3592, -21206, 1559, -902, 2052], ![1804, -6420, -5444, -741, -1308], ![2486, -12696, -1874, -762, 313]]]
  hmulB := by decide  
  f := ![![![-5, -37, 128, -39, 0]], ![![78, -83, -154, 206, -234]], ![![-412, 1426, -1571, -98, 768]], ![![-134, 427, -407, -53, 234]], ![![-184, 705, -859, 32, 295]]]
  g := ![![![-3027, -7236, -6845, -4021, 15270], ![-1170, -3031, -2840, -1796, 6414], ![-64, -944, -801, -902, 2052], ![1288, 705, 943, -741, -1308], ![582, -95, 83, -762, 313]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [74, 56, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 29, 2], [141, 121, 149], [0, 1]]
 g := ![![[62, 23, 39], [142, 140, 99], [84, 40, 94], [19, 80], [63, 13, 85], [83, 1], []], ![[60, 87, 87, 40], [44, 93, 10, 94], [139, 124, 116, 138], [67, 36], [10, 69, 67, 90], [113, 145], [146, 4]], ![[26, 55, 57, 53], [99, 38, 128, 106], [104, 66, 65, 24], [59, 43], [23, 17, 83, 56], [83, 86], [150, 4]]]
 h' := ![![[93, 29, 2], [62, 131, 103], [126, 30, 34], [12, 6, 83], [19, 25, 82], [49, 110, 38], [0, 0, 1], [0, 1]], ![[141, 121, 149], [19, 90, 41], [12, 106, 97], [36, 41, 89], [39, 46, 6], [114, 80, 137], [110, 93, 121], [93, 29, 2]], ![[0, 1], [64, 81, 7], [4, 15, 20], [49, 104, 130], [145, 80, 63], [125, 112, 127], [23, 58, 29], [141, 121, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 10], []]
 b := ![[], [36, 74, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [74, 56, 68, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![928295, -3443991, 3786590, 682410, -1602757]
  a := ![-3, 7, 6, -2, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![95221, 608786, 666541, 682410, -1602757]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 37, -128, 39, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![5, 37, -128, 39, 0]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![69, 98, 1, 0, 0], ![33, 129, 0, 1, 0], ![53, 32, 0, 0, 1]] where
  M :=![![![5, 37, -128, 39, 0], ![-78, 83, 154, -206, 234], ![412, -1426, 1571, 98, -768], ![-196, 3680, -8044, 2911, -948], ![-1214, 3494, -2914, -992, 2585]]]
  hmulB := by decide  
  f := ![![![-18343, 117033, -20702, 4021, -15270]], ![![-8042, 50779, -8334, 1796, -6414]], ![![-13625, 86575, -14879, 3009, -11154]], ![![-10891, 69000, -11608, 2418, -8808]], ![![-8159, 51923, -9020, 1797, -6721]]]
  g := ![![![50, 50, -128, 39, 0], ![-108, 27, 154, -206, 234], ![-467, -950, 1571, 98, -768], ![3371, 2959, -8044, 2911, -948], ![633, 2214, -2914, -992, 2585]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [17, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 150], [0, 1]]
 g := ![![[90, 80], [132, 88], [146, 36], [137], [82, 50], [98], [1]], ![[0, 71], [33, 63], [30, 115], [137], [139, 101], [98], [1]]]
 h' := ![![[131, 150], [21, 69], [85, 36], [104, 145], [116, 99], [133, 79], [134, 131], [0, 1]], ![[0, 1], [0, 82], [120, 115], [73, 6], [99, 52], [63, 72], [81, 20], [131, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [100, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [17, 20, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14829, -75787, 110489, -8168, -16143]
  a := ![16, -7, -33, 16, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42939, -61811, 110489, -8168, -16143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![18343, -117033, 20702, -4021, 15270]] ![![5, 37, -128, 39, 0]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB984I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB984I3 : PrimesBelowBoundCertificateInterval O 103 151 984 where
  m := 9
  g := ![3, 3, 4, 1, 2, 4, 2, 1, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB984I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2, I113N3]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2, I137N3]
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
    · exact ![1225043, 107, 107]
    · exact ![11881, 11881, 109]
    · exact ![12769, 113, 113, 113]
    · exact ![33038369407]
    · exact ![2248091, 17161]
    · exact ![18769, 137, 137, 137]
    · exact ![373301041, 139]
    · exact ![73439775749]
    · exact ![3442951, 22801]
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
      exact NI113N2
      exact NI113N3
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
      exact NI137N3
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
  β := ![I107N1, I107N2, I109N2, I113N1, I113N2, I113N3, I137N1, I137N2, I137N3, I139N1]
  Il := ![[I107N1, I107N2], [I109N2], [I113N1, I113N2, I113N3], [], [], [I137N1, I137N2, I137N3], [I139N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
