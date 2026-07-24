
import IdealArithmetic.Examples.NF5_3_67500000_1.RI5_3_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35171, -21462, -3064, 4508, 12414]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![35171, -21462, -3064, 4508, 12414]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![91, 76, 73, 7, 1]] where
  M :=![![![35171, -21462, -3064, 4508, 12414], ![-23718, 8389, 6764, -5018, -10194], ![15528, -1426, -12157, 8668, 474], ![24150, 9782, -12052, 3117, 30390], ![-26262, -10450, 15910, -5938, -28225]]]
  hmulB := by decide  
  f := ![![![-3815, -6014, 3996, 13516, 15114]], ![![-4794, -4613, 12296, 33426, 35754]], ![![-6984, 518, 35797, 89116, 93294]], ![![-3870, 10446, 44936, 106111, 109530]], ![![-11647, -7304, 39517, 103005, 109085]]]
  g := ![![![-10229, -9018, -8498, -770, 12414], ![8448, 7319, 7018, 620, -10194], ![-258, -350, -437, 50, 474], ![-25620, -21494, -20846, -1959, 30390], ![23759, 19950, 19405, 1791, -28225]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [22, 4, 87, 51, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 91, 70, 53], [56, 13, 33, 43], [69, 2, 4, 11], [0, 1]]
 g := ![![[8, 6, 67, 33], [40, 27, 43, 89], [42, 99, 105], [55, 87, 47, 3], [53, 56, 1], []], ![[18, 70, 3, 76, 72, 27], [70, 18, 104, 37, 50, 12], [69, 20, 36], [1, 71, 78, 93, 26, 19], [69, 48, 75], [51, 53, 0, 52, 99, 40]], ![[65, 4, 83, 58, 53, 22], [72, 47, 62, 21, 63, 103], [58, 67, 53], [11, 95, 5, 103, 36, 95], [29, 22, 64], [98, 97, 65, 22, 96, 6]], ![[97, 30, 53, 41, 101, 25], [97, 62, 35, 14, 12, 102], [74, 2, 62], [98, 10, 23, 48, 75, 4], [47, 36, 41], [49, 68, 4, 99, 18, 47]]]
 h' := ![![[38, 91, 70, 53], [83, 42, 29, 56], [58, 79, 49, 14], [74, 20, 50, 31], [11, 54, 65, 18], [0, 0, 0, 1], [0, 1]], ![[56, 13, 33, 43], [67, 50, 101, 69], [13, 73, 84, 46], [56, 8, 95, 101], [99, 89, 52, 47], [36, 45, 34, 90], [38, 91, 70, 53]], ![[69, 2, 4, 11], [73, 2, 90, 18], [37, 81, 53, 80], [55, 25, 79, 69], [66, 35, 76, 49], [13, 45, 22, 99], [56, 13, 33, 43]], ![[0, 1], [20, 13, 101, 71], [84, 88, 28, 74], [0, 54, 97, 13], [50, 36, 21, 100], [11, 17, 51, 24], [69, 2, 4, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [79, 74, 105], []]
 b := ![[], [], [97, 105, 95, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [22, 4, 87, 51, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1403029, 1732464, -1354083, 3592512, 3036276]
  a := ![-5, -7, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2569141, -2140416, -2084133, -165060, 3036276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3815, 6014, -3996, -13516, -15114]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![3815, 6014, -3996, -13516, -15114]] 
 ![![107, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![106, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![3815, 6014, -3996, -13516, -15114], ![4794, 4613, -12296, -33426, -35754], ![6984, -518, -35797, -89116, -93294], ![3870, -10446, -44936, -106111, -109530], ![-2202, -5398, -2454, -2958, -2245]]]
  hmulB := by decide  
  f := ![![![-35171, 21462, 3064, -4508, -12414]], ![![-22130, 13561, 1884, -2818, -7794]], ![![-27756, 16862, 2519, -3620, -9750]], ![![-35068, 21170, 3148, -4495, -12582]], ![![-13560, 8522, 1054, -1714, -4609]]]
  g := ![![![18673, 6014, -3996, -13516, -15114], ![53914, 4613, -12296, -33426, -35754], ![153400, -518, -35797, -89116, -93294], ![190064, -10446, -44936, -106111, -109530], ![9148, -5398, -2454, -2958, -2245]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![35171, -21462, -3064, 4508, 12414]] ![![3815, 6014, -3996, -13516, -15114]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2518, 8694, 33912, 79603, 82032]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-2518, 8694, 33912, 79603, 82032]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![39, 3, 53, 101, 1]] where
  M :=![![![-2518, 8694, 33912, 79603, 82032], ![-7287, 24107, 95584, 224601, 231522], ![-20763, 67534, 269471, 633449, 653040], ![-25743, 82914, 332086, 780824, 805026], ![-1248, 3610, 15090, 35572, 36701]]]
  hmulB := by decide  
  f := ![![![-52, 2, 26, -15, -30]], ![![45, 19, -58, 37, 0]], ![![111, 98, -55, -5, 222]], ![![-363, -322, 416, -192, -348]], ![![-297, -247, 363, -183, -223]]]
  g := ![![![-29374, -2178, -39576, -75281, 82032], ![-82905, -6151, -111698, -212469, 231522], ![-233847, -17354, -315061, -599299, 653040], ![-288273, -21396, -388388, -738778, 805026], ![-13143, -977, -17707, -33681, 36701]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [38, 69, 91, 70, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 16, 102, 102], [53, 102, 58, 37], [39, 99, 58, 79], [0, 1]]
 g := ![![[10, 18, 78, 36], [62, 53, 21], [37, 43, 43, 43], [24, 30, 55, 102], [13, 39, 1], []], ![[44, 6, 104, 90, 28, 104], [80, 101, 66], [36, 72, 23, 76, 94, 20], [23, 44, 6, 98, 19, 87], [32, 16, 64], [72, 90, 91, 6, 91, 93]], ![[98, 61, 32, 89, 31, 58], [32, 97, 49], [15, 8, 88, 10, 50, 85], [34, 68, 95, 32], [32, 47, 83], [13, 107, 26, 90, 101, 77]], ![[51, 9, 15, 101, 8, 107], [107, 27, 74], [35, 100, 47, 38, 103, 107], [53, 46, 92, 15, 0, 101], [92, 62, 84], [40, 90, 10, 75, 16, 32]]]
 h' := ![![[56, 16, 102, 102], [54, 14, 53, 6], [11, 29, 2, 81], [69, 23, 63, 77], [51, 19, 12, 50], [0, 0, 0, 1], [0, 1]], ![[53, 102, 58, 37], [13, 3, 45, 64], [108, 61, 54, 75], [49, 66, 63, 27], [19, 66, 101, 9], [6, 4, 63, 8], [56, 16, 102, 102]], ![[39, 99, 58, 79], [17, 24, 52, 14], [90, 68, 5, 102], [66, 9, 100, 89], [49, 76, 87], [34, 31, 100, 44], [53, 102, 58, 37]], ![[0, 1], [10, 68, 68, 25], [77, 60, 48, 69], [80, 11, 101, 25], [70, 57, 18, 50], [29, 74, 55, 56], [39, 99, 58, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [99, 64, 74], []]
 b := ![[], [], [73, 9, 47, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [38, 69, 91, 70, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20496518654, 28483392305, -46620670715, 57040817182, 2931540675]
  a := ![6, -59, -1, -60, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-860858419, 180630920, -1853140610, -2193071477, 2931540675]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52, -2, -26, 15, 30]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![52, -2, -26, 15, 30]] 
 ![![109, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![52, -2, -26, 15, 30], ![-45, -19, 58, -37, 0], ![-111, -98, 55, 5, -222], ![363, 322, -416, 192, 348], ![-300, -270, 374, -184, -245]]]
  hmulB := by decide  
  f := ![![![2518, -8694, -33912, -79603, -82032]], ![![1245, -4289, -16744, -39306, -40506]], ![![537, -1816, -7139, -16766, -17280]], ![![883, -2994, -11758, -27612, -28458]], ![![1282, -4420, -17250, -40493, -41729]]]
  g := ![![![-14, -2, -26, 15, 30], ![10, -19, 58, -37, 0], ![148, -98, 55, 5, -222], ![-315, 322, -416, 192, 348], ![243, -270, 374, -184, -245]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-2518, 8694, 33912, 79603, 82032]] ![![52, -2, -26, 15, 30]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [48, 56, 3, 52, 72, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 76, 111, 9, 67], [43, 52, 107, 36, 65], [69, 53, 35, 77, 84], [2, 44, 86, 104, 10], [0, 1]]
 g := ![![[18, 61, 5, 68, 100], [92, 63, 15, 52], [46, 18, 108, 16], [44, 78, 103, 98], [47, 41, 1], []], ![[10, 49, 79, 55, 33, 20, 84, 80], [79, 53, 61, 13], [101, 52, 84, 91], [95, 3, 17, 11], [98, 95, 4, 59, 0, 29, 64, 29], [42, 98, 51, 99, 72, 17, 112, 70]], ![[16, 47, 109, 64, 92, 97, 93, 68], [17, 49, 73, 82], [18, 74, 84, 109], [66, 44, 1, 4], [21, 49, 109, 63, 110, 71, 104, 65], [45, 97, 37, 104, 81, 21, 85, 35]], ![[15, 100, 100, 55, 90, 28, 32, 73], [105, 91, 108, 8], [40, 88, 32, 99], [104, 83, 69, 105], [27, 69, 16, 63, 46, 27, 28, 79], [17, 15, 3, 93, 57, 30, 12, 19]], ![[75, 53, 78, 85, 70, 72, 85, 92], [67, 56, 45, 13], [67, 16, 63, 105], [38, 57, 22, 63], [91, 18, 88, 38, 37, 102, 71, 29], [56, 97, 4, 75, 47, 12, 106, 96]]]
 h' := ![![[40, 76, 111, 9, 67], [82, 86, 33, 47, 10], [54, 20, 50, 17, 74], [51, 45, 15, 101, 4], [4, 33, 1, 89, 18], [0, 0, 0, 1], [0, 1]], ![[43, 52, 107, 36, 65], [35, 3, 89, 51, 37], [18, 21, 57, 15, 37], [32, 20, 9, 39, 59], [80, 71, 69, 71, 24], [60, 99, 57, 108, 52], [40, 76, 111, 9, 67]], ![[69, 53, 35, 77, 84], [27, 80, 96, 51, 102], [39, 26, 40, 64, 67], [98, 43, 76, 87, 30], [21, 29, 49, 44, 2], [55, 11, 40, 40, 1], [43, 52, 107, 36, 65]], ![[2, 44, 86, 104, 10], [15, 106, 85, 84, 54], [99, 58, 110, 103, 11], [95, 26, 40, 56, 72], [51, 10, 65, 94, 52], [106, 35, 53, 16, 14], [69, 53, 35, 77, 84]], ![[0, 1], [52, 64, 36, 106, 23], [68, 101, 82, 27, 37], [81, 92, 86, 56, 61], [53, 83, 42, 41, 17], [32, 81, 76, 61, 46], [2, 44, 86, 104, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 60, 29, 67], [], [], []]
 b := ![[], [25, 84, 101, 66, 112], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [48, 56, 3, 52, 72, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28758839, 29653912, -42784512, 30628989, 19397580]
  a := ![-1, -5, 1, -6, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![254503, 262424, -378624, 271053, 171660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 18424351793 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-559, 307, 81, -88, -198]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-559, 307, 81, -88, -198]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![32, 19, 47, 1, 0], ![97, 24, 5, 0, 1]] where
  M :=![![![-559, 307, 81, -88, -198], ![330, -148, -111, 96, 66], ![90, 309, -142, 0, 378], ![-732, -519, 777, -379, -600], ![621, 401, -681, 355, 413]]]
  hmulB := by decide  
  f := ![![![377, 797, 105, -206, -342]], ![![408, 890, 183, -66, -210]], ![![432, 1023, 392, 378, 234]], ![![316, 714, 202, 85, -24]], ![![380, 813, 130, -153, -289]]]
  g := ![![![169, 53, 41, -88, -198], ![-72, -28, -39, 96, 66], ![-288, -69, -16, 0, 378], ![548, 166, 170, -379, -600], ![-400, -128, -153, 355, 413]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [122, 24, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 81, 21], [40, 45, 106], [0, 1]]
 g := ![![[32, 8, 81], [33, 65, 42], [58, 40, 37], [44, 73, 49], [40, 68, 122], [1]], ![[31, 77, 118, 52], [26, 2, 10, 70], [123, 7, 85, 94], [66, 48, 52, 103], [37, 31, 36, 120], [86, 45, 7, 117]], ![[23, 98, 12, 67], [103, 88, 81, 33], [49, 75, 93, 86], [14, 112, 32, 39], [56, 66, 80, 92], [115, 100, 67, 10]]]
 h' := ![![[33, 81, 21], [38, 67, 118], [36, 91, 114], [93, 66, 52], [73, 40, 7], [5, 103, 73], [0, 1]], ![[40, 45, 106], [17, 19, 113], [69, 11, 56], [54, 115, 43], [81, 52, 12], [45, 25, 114], [33, 81, 21]], ![[0, 1], [93, 41, 23], [96, 25, 84], [35, 73, 32], [74, 35, 108], [59, 126, 67], [40, 45, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 110], []]
 b := ![[], [61, 118, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [122, 24, 54, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![966049, 1204002, -5211, 2930634, 3734451]
  a := ![8, 26, -3, 25, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3583118, -1134684, -1231632, 2930634, 3734451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-377, -797, -105, 206, 342]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-377, -797, -105, 206, 342]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![36, 33, 1, 0, 0], ![41, 109, 0, 1, 0], ![100, 84, 0, 0, 1]] where
  M :=![![![-377, -797, -105, 206, 342], ![-408, -890, -183, 66, 210], ![-432, -1023, -392, -378, -234], ![-12, -183, -393, -875, -888], ![261, 533, 27, -245, -341]]]
  hmulB := by decide  
  f := ![![![559, -307, -81, 88, 198]], ![![-330, 148, 111, -96, -66]], ![![72, -51, 7, 0, 36]], ![![-97, 32, 63, -51, 12]], ![![217, -147, 15, 3, 109]]]
  g := ![![![-309, -382, -105, 206, 342], ![-138, -155, -183, 66, 210], ![414, 573, -392, -378, -234], ![1093, 1439, -393, -875, -888], ![342, 433, 27, -245, -341]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [20, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 126], [0, 1]]
 g := ![![[12, 73], [71, 88], [99, 81], [13, 68], [78, 115], [14, 1]], ![[18, 54], [33, 39], [90, 46], [76, 59], [37, 12], [28, 126]]]
 h' := ![![[14, 126], [104, 33], [52, 56], [121, 118], [91, 103], [101, 49], [0, 1]], ![[0, 1], [58, 94], [74, 71], [122, 9], [9, 24], [25, 78], [14, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [68, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [20, 113, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3712, -3212, 3546, -1688, -4584]
  a := ![-10, -8, 5, -6, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3120, 3534, 3546, -1688, -4584]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-559, 307, 81, -88, -198]] ![![-377, -797, -105, 206, 342]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![249, -146, -18, 28, 70]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![249, -146, -18, 28, 70]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![61, 42, 61, 1, 0], ![127, 41, 24, 0, 1]] where
  M :=![![![249, -146, -18, 28, 70], ![-126, 105, 8, -22, -42], ![60, -58, 23, -8, -6], ![60, -14, -34, 25, 6], ![-62, 22, 22, -18, 3]]]
  hmulB := by decide  
  f := ![![![3, -2, -18, -44, -46]], ![![6, -9, -52, -122, -126]], ![![12, -34, -143, -344, -354]], ![![9, -20, -93, -223, -230]], ![![7, -11, -60, -144, -149]]]
  g := ![![![-79, -32, -26, 28, 70], ![50, 21, 18, -22, -42], ![10, 4, 5, -8, -6], ![-17, -10, -13, 25, 6], ![5, 5, 8, -18, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [33, 96, 110, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 91, 109], [4, 39, 22], [0, 1]]
 g := ![![[63, 88, 89], [8, 124, 105], [19, 129], [29, 21], [118, 77], [21, 1], []], ![[77, 49, 19, 75], [72, 25], [9, 36], [58, 44], [52, 52], [69, 80], [3, 91]], ![[62, 97, 121, 51], [71, 11, 90, 83], [46, 108], [54, 25], [71, 75], [24, 28], [90, 91]]]
 h' := ![![[17, 91, 109], [129, 110, 58], [56, 107, 57], [40, 97, 28], [39, 113, 26], [93, 47, 83], [0, 0, 1], [0, 1]], ![[4, 39, 22], [50, 25, 104], [129, 80], [66, 36, 6], [88, 52, 100], [25, 109, 107], [59, 65, 39], [17, 91, 109]], ![[0, 1], [61, 127, 100], [48, 75, 74], [115, 129, 97], [60, 97, 5], [69, 106, 72], [59, 66, 91], [4, 39, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 88], []]
 b := ![[], [105, 1, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [33, 96, 110, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1601001, 1193664, -728928, -153432, 2940432]
  a := ![6, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2766981, -861984, -472824, -153432, 2940432]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42, 135, -127, 57, 64]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![42, 135, -127, 57, 64]] 
 ![![131, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![118, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![42, 135, -127, 57, 64], ![-21, -106, 213, -147, 150], ![-891, -699, 638, -165, -1332], ![1761, 1677, -2289, 1130, 1428], ![-1337, -1323, 1931, -1011, -849]]]
  hmulB := by decide  
  f := ![![![-19218, 66909, 260287, 610875, 629486]], ![![-6441, 22355, 87064, 204348, 210578]], ![![-4443, 15195, 59500, 139701, 143974]], ![![-18819, 65127, 253913, 596000, 614182]], ![![-5795, 20130, 78374, 183948, 189555]]]
  g := ![![![-91, 135, -127, 57, 64], ![85, -106, 213, -147, 150], ![650, -699, 638, -165, -1332], ![-1570, 1677, -2289, 1130, 1428], ![1243, -1323, 1931, -1011, -849]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1284, 417, -657, 217, 1430]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![1284, 417, -657, 217, 1430]] 
 ![![131, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![102, 0, 0, 0, 1]] where
  M :=![![![1284, 417, -657, 217, 1430], ![-3639, -3012, 4273, -2093, -2988], ![2685, 3319, -7790, 5255, -3594], ![15093, 12227, -11123, 2936, 22650], ![-15331, -12905, 13541, -4793, -20133]]]
  hmulB := by decide  
  f := ![![![-816240, -1779381, -362247, 140743, 429112]], ![![-623457, -1360323, -279664, 100780, 320910]], ![![-156147, -345109, -80942, 607, 55260]], ![![-43047, -100606, -35818, -30353, -15880]], ![![-631147, -1376671, -282049, 104429, 327321]]]
  g := ![![![-1310, 417, -657, 217, 1430], ![3904, -3012, 4273, -2093, -2988], ![1457, 3319, -7790, 5255, -3594], ![-24880, 12227, -11123, 2936, 22650], ![23087, -12905, 13541, -4793, -20133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![249, -146, -18, 28, 70]] ![![42, 135, -127, 57, 64]]
  ![![-14720, 16019, -3127, -505, -1434]] where
 M := ![![![-14720, 16019, -3127, -505, -1434]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-14720, 16019, -3127, -505, -1434]] ![![1284, 417, -657, 217, 1430]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-71226927, -52434846, 88678878, -47763910, -40243462]]]
 hmul := by decide  
 g := ![![![![-543717, -400266, 676938, -364610, -307202]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4186, -13166, -53218, -125201, -129102]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![4186, -13166, -53218, -125201, -129102]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![48, 51, 131, 1, 0], ![4, 84, 22, 0, 1]] where
  M :=![![![4186, -13166, -53218, -125201, -129102], ![11703, -37329, -150070, -352937, -363900], ![32889, -105478, -423155, -995051, -1025922], ![40455, -130162, -521536, -1226302, -1264320], ![1800, -6002, -23726, -55740, -57455]]]
  hmulB := by decide  
  f := ![![![4064, -2642, -284, 517, 1296]], ![![-2337, 1443, 212, -313, -786]], ![![1419, -706, -289, 271, 480]], ![![1917, -1067, -297, 324, 624]], ![![-1094, 698, 76, -134, -371]]]
  g := ![![![47666, 125669, 140061, -125201, -129102], ![134367, 354234, 394821, -352937, -363900], ![378825, 998683, 1113130, -995051, -1025922], ![466863, 1230760, 1371818, -1226302, -1264320], ![21220, 55934, 62352, -55740, -57455]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [135, 110, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 93, 5], [29, 43, 132], [0, 1]]
 g := ![![[101, 15, 100], [65, 107], [18, 8], [37, 10, 121], [132, 120], [94, 1], []], ![[49, 86, 24, 41], [21, 32], [82, 32], [129, 118, 89, 82], [40, 109], [109, 68], [129, 25]], ![[5, 136, 121, 106], [32, 65], [40, 72], [35, 11, 0, 127], [1, 19], [77, 18], [2, 25]]]
 h' := ![![[65, 93, 5], [58, 24, 127], [32, 6, 92], [74, 67, 62], [125, 118, 126], [51, 74, 95], [0, 0, 1], [0, 1]], ![[29, 43, 132], [80, 127, 101], [77, 59, 13], [18, 102, 124], [130, 96, 117], [18, 96, 71], [99, 5, 43], [65, 93, 5]], ![[0, 1], [113, 123, 46], [130, 72, 32], [18, 105, 88], [6, 60, 31], [135, 104, 108], [23, 132, 93], [29, 43, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 85], []]
 b := ![[], [85, 98, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [135, 110, 43, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85718, -38636, 130732, 169143, 34200]
  a := ![6, 6, 4, 7, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-60886, -84217, -166273, 169143, 34200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30, 29, 221, 535, 556]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-30, 29, 221, 535, 556]] 
 ![![137, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![123, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![-30, 29, 221, 535, 556], ![-63, 128, 627, 1491, 1542], ![-153, 411, 1772, 4185, 4320], ![-171, 543, 2187, 5144, 5304], ![1, 43, 101, 227, 231]]]
  hmulB := by decide  
  f := ![![![474, -355, 73, -17, 254]], ![![129, -103, 24, -6, 66]], ![![441, -306, 47, -6, 240]], ![![165, -129, 39, -16, 102]], ![![331, -252, 46, -6, 163]]]
  g := ![![![-788, 29, 221, 535, 556], ![-2214, 128, 627, 1491, 1542], ![-6234, 411, 1772, 4185, 4320], ![-7677, 543, 2187, 5144, 5304], ![-346, 43, 101, 227, 231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-215, 636, 2634, 6206, 6402]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-215, 636, 2634, 6206, 6402]] 
 ![![137, 0, 0, 0, 0], ![110, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-215, 636, 2634, 6206, 6402], ![-588, 1831, 7430, 17484, 18030], ![-1638, 5204, 20953, 49282, 50814], ![-2004, 6444, 25826, 60727, 62610], ![-84, 308, 1176, 2756, 2839]]]
  hmulB := by decide  
  f := ![![![93005, -60652, -6526, 11922, 29346]], ![![74294, -48449, -5214, 9524, 23442]], ![![63351, -41312, -4445, 8120, 19992]], ![![24564, -16028, -1718, 3147, 7746]], ![![35152, -22916, -2472, 4508, 11095]]]
  g := ![![![-6361, 636, 2634, 6206, 6402], ![-17956, 1831, 7430, 17484, 18030], ![-50651, 5204, 20953, 49282, 50814], ![-62442, 6444, 25826, 60727, 62610], ![-2848, 308, 1176, 2756, 2839]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![4186, -13166, -53218, -125201, -129102]] ![![-30, 29, 221, 535, 556]]
  ![![30126501, -96971981, -388486161, -913448424, -941764982]] where
 M := ![![![30126501, -96971981, -388486161, -913448424, -941764982]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![30126501, -96971981, -388486161, -913448424, -941764982]] ![![-215, 636, 2634, 6206, 6402]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![2596541559015, -8356402483131, -33479333763685, -78720354771640, -81160747353620]]]
 hmul := by decide  
 g := ![![![![18952858095, -60995638563, -244374699005, -574601129720, -592414214260]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![273, -6, 222, -240, 742]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![273, -6, 222, -240, 742]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![62, 130, 55, 57, 1]] where
  M :=![![![273, -6, 222, -240, 742], ![-2946, -2451, 2700, -1018, -3666], ![7944, 7698, -11413, 6012, 4890], ![3156, 1174, 3822, -4331, 12534], ![-6026, -4062, 730, 1818, -13773]]]
  hmulB := by decide  
  f := ![![![243, 522, 94, -72, -158]], ![![258, 595, 192, 130, 42]], ![![264, 714, 461, 732, 654]], ![![-12, 182, 510, 1167, 1194]], ![![448, 1144, 613, 859, 719]]]
  g := ![![![-329, -694, -292, -306, 742], ![1614, 3411, 1470, 1496, -3666], ![-2124, -4518, -2017, -1962, 4890], ![-5568, -11714, -4932, -5171, 12534], ![6100, 12852, 5455, 5661, -13773]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [100, 136, 116, 128, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 80, 71, 29], [57, 26, 32, 49], [40, 32, 36, 61], [0, 1]]
 g := ![![[37, 67, 42, 54], [20, 43, 31, 79], [28, 43, 66], [39, 42, 80, 69], [94, 30, 121], [1], []], ![[83, 103, 14, 26, 67, 137], [48, 20, 125, 106, 26, 34], [126, 83, 81], [10, 95, 90, 113, 30, 44], [21, 11, 78], [3, 10, 44], [109, 25, 7]], ![[114, 55, 83, 137, 55, 86], [128, 102, 8, 27, 23, 55], [26, 32, 7], [131, 48, 7, 71, 17, 41], [85, 49, 122], [8, 125, 124], [33, 79, 38]], ![[8, 132, 80, 127, 39, 84], [112, 88, 24, 136, 4, 70], [45, 10, 64], [107, 42, 46, 63, 16, 32], [109, 92, 55], [100, 115, 28], [115, 9, 107]]]
 h' := ![![[53, 80, 71, 29], [85, 59, 117, 101], [44, 112, 71, 45], [131, 77, 28, 30], [44, 18, 17, 25], [39, 3, 23, 11], [0, 0, 1], [0, 1]], ![[57, 26, 32, 49], [45, 38, 76, 62], [54, 52, 130, 11], [127, 50, 14, 130], [71, 50, 102, 120], [124, 24, 51, 83], [110, 52, 101, 105], [53, 80, 71, 29]], ![[40, 32, 36, 61], [13, 57, 108, 22], [50, 56, 20, 90], [3, 20, 123, 110], [15, 29, 49, 50], [133, 97, 8, 119], [88, 28, 130, 92], [57, 26, 32, 49]], ![[0, 1], [115, 124, 116, 93], [125, 58, 57, 132], [90, 131, 113, 8], [97, 42, 110, 83], [135, 15, 57, 65], [108, 59, 46, 81], [40, 32, 36, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 84, 61], []]
 b := ![[], [], [0, 119, 95, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [100, 136, 116, 128, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-972053, -1154732, 1937619, -1648398, -114375]
  a := ![2, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![44023, 98662, 59196, 35043, -114375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![243, 522, 94, -72, -158]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![243, 522, 94, -72, -158]] 
 ![![139, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![103, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![243, 522, 94, -72, -158], ![258, 595, 192, 130, 42], ![264, 714, 461, 732, 654], ![-12, 182, 510, 1167, 1194], ![-170, -342, -6, 186, 249]]]
  hmulB := by decide  
  f := ![![![273, -6, 222, -240, 742]], ![![132, -21, 144, -142, 390]], ![![120, 54, -31, -12, 206]], ![![225, 4, 192, -209, 640]], ![![-8, -30, 34, -18, -3]]]
  g := ![![![-239, 522, 94, -72, -158], ![-478, 595, 192, 130, 42], ![-1132, 714, 461, 732, 654], ![-1239, 182, 510, 1167, 1194], ![22, -342, -6, 186, 249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![273, -6, 222, -240, 742]] ![![243, 522, 94, -72, -158]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [22, 101, 131, 12, 72, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 65, 84, 139, 140], [91, 51, 134, 75, 73], [27, 17, 107, 43, 100], [75, 15, 122, 41, 134], [0, 1]]
 g := ![![[73, 34, 84, 112, 148], [80, 4, 34, 47], [110, 40, 131, 0, 86], [131, 83, 115, 29], [124, 104, 106, 77, 1], [], []], ![[147, 105, 13, 124, 40, 73, 99, 82], [78, 22, 141, 42], [109, 132, 10, 113, 95, 121], [63, 88, 122, 20], [20, 39, 89, 85, 69, 7, 125, 69], [87, 97, 131, 85], [115, 25, 10, 81]], ![[57, 102, 7, 84, 30, 115, 86, 125], [134, 6, 79, 81], [48, 79, 79, 94, 44, 126, 52, 95], [75, 3, 17, 29], [116, 140, 101, 110, 35, 37, 60, 29], [28, 82, 139, 125], [76, 131, 60, 114]], ![[109, 136, 100, 123, 61, 134, 54, 145], [113, 127, 79, 129], [97, 143, 26, 34, 27, 10, 147, 67], [59, 47, 3, 110], [30, 98, 32, 132, 53, 58, 36, 73], [133, 34, 79, 42], [22, 63, 75, 17]], ![[66, 13, 86, 112, 142, 112, 128, 115], [99, 113, 73, 145], [44, 63, 32, 135, 117, 142, 64, 146], [19, 96, 105, 127], [128, 113, 40, 5, 27, 121, 62, 105], [74, 142, 100, 96], [64, 22, 3, 76]]]
 h' := ![![[33, 65, 84, 139, 140], [132, 135, 97, 14, 44], [113, 73, 27, 5, 14], [128, 91, 148, 147, 91], [103, 88, 124, 53, 25], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[91, 51, 134, 75, 73], [89, 71, 71, 60, 89], [100, 104, 59, 124, 41], [100, 9, 59, 62], [61, 51, 138, 66, 136], [40, 26, 142, 0, 108], [49, 22, 5, 131, 54], [33, 65, 84, 139, 140]], ![[27, 17, 107, 43, 100], [127, 9, 22, 86, 145], [86, 18, 107, 138, 9], [119, 12, 85, 117, 143], [32, 80, 105, 92, 124], [107, 23, 52, 15, 26], [53, 65, 98, 81, 107], [91, 51, 134, 75, 73]], ![[75, 15, 122, 41, 134], [8, 52, 102, 63, 128], [109, 103, 79, 12, 24], [106, 124, 51, 55, 18], [19, 3, 41, 63, 109], [32, 77, 70, 23, 83], [96, 141, 89, 73, 108], [27, 17, 107, 43, 100]], ![[0, 1], [64, 31, 6, 75, 41], [93, 0, 26, 19, 61], [143, 62, 104, 66, 46], [73, 76, 39, 24, 53], [99, 23, 34, 111, 80], [45, 70, 105, 13, 29], [75, 15, 122, 41, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 0, 67, 13], [], [], []]
 b := ![[], [72, 90, 55, 108, 18], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [22, 101, 131, 12, 72, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24948370472, 23669109814, -32913894976, 16579835834, 19325830589]
  a := ![10, 6, 0, 2, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![167438728, 158853086, -220898624, 111274066, 129703561]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0, 0, 0]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]] where
  M :=![![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 5 2 7 [21, 17, 46, 98, 75, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 72, 118, 116, 102], [128, 68, 80, 41, 117], [148, 133, 7, 143, 15], [102, 28, 97, 2, 68], [0, 1]]
 g := ![![[0, 14, 128, 77, 32], [137, 91, 95, 67, 10], [13, 22, 69, 90, 10], [4, 108, 108, 69], [115, 26, 91, 76, 1], [], []], ![[73, 10, 79, 60, 83, 104, 31, 24], [39, 147, 98, 50, 142, 25, 110, 89], [102, 118, 98, 22, 135, 114, 149, 52], [86, 61, 83, 100], [18, 77, 119, 135, 87, 118, 105, 6], [1, 73, 126, 38], [51, 128, 25, 136]], ![[102, 49, 95, 75, 104, 1, 94, 28], [116, 88, 44, 56, 125, 46, 86, 77], [0, 93, 58, 25, 59, 55, 87, 129], [42, 59, 38, 4], [59, 74, 106, 35, 32, 107, 35, 143], [28, 65, 12, 100], [111, 81, 55, 99]], ![[51, 66, 122, 56, 28, 94, 83, 35], [34, 110, 28, 17, 47, 137, 63, 119], [112, 83, 68, 128, 72, 15, 146, 33], [52, 118, 50, 103], [66, 8, 131, 2, 40, 31, 84, 107], [70, 78, 99, 5], [105, 93, 99, 74]], ![[6, 144, 149, 143, 114, 67, 12, 44], [54, 9, 86, 39, 134, 114, 56, 69], [0, 39, 76, 128, 82, 146, 86, 55], [10, 119, 106, 5], [143, 136, 127, 124, 86, 144, 27, 47], [115, 140, 32, 55], [89, 142, 17, 94]]]
 h' := ![![[0, 72, 118, 116, 102], [143, 74, 86, 70, 118], [29, 15, 137, 142, 114], [68, 61, 33, 107, 114], [1, 66, 58, 95, 89], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[128, 68, 80, 41, 117], [87, 150, 5, 35, 138], [123, 35, 59, 149, 123], [44, 139, 12, 45, 103], [75, 138, 65, 130, 10], [24, 142, 12, 1, 69], [137, 69, 137, 107, 76], [0, 72, 118, 116, 102]], ![[148, 133, 7, 143, 15], [71, 46, 94, 3, 115], [58, 141, 143, 31, 53], [79, 40, 21, 124, 124], [31, 132, 101, 142, 149], [116, 41, 29, 30, 13], [10, 79, 101, 134, 10], [128, 68, 80, 41, 117]], ![[102, 28, 97, 2, 68], [45, 92, 141, 25, 109], [144, 56, 94, 109, 138], [136, 14, 15, 48, 24], [110, 73, 142, 89, 109], [120, 119, 2, 106, 17], [69, 145, 97, 111, 96], [148, 133, 7, 143, 15]], ![[0, 1], [64, 91, 127, 18, 124], [70, 55, 20, 22, 25], [85, 48, 70, 129, 88], [12, 44, 87, 148, 96], [51, 0, 108, 14, 51], [79, 9, 117, 101, 120], [102, 28, 97, 2, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 88, 105, 124], [], [], []]
 b := ![[], [144, 17, 72, 18, 58], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 5
  hpos := by decide
  P := [21, 17, 46, 98, 75, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-469930271, -455588744, 737911783, -307631545, -171495683]
  a := ![6, 6, -3, 5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3112121, -3017144, 4886833, -2037295, -1135733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 78502725751 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀



lemma PB402I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB402I3 : PrimesBelowBoundCertificateInterval O 103 151 402 where
  m := 9
  g := ![2, 2, 1, 2, 3, 3, 2, 1, 1]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB402I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
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
    · exact ![131079601, 107]
    · exact ![141158161, 109]
    · exact ![18424351793]
    · exact ![2048383, 16129]
    · exact ![2248091, 131, 131]
    · exact ![2571353, 137, 137]
    · exact ![373301041, 139]
    · exact ![73439775749]
    · exact ![78502725751]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
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
  β := ![I107N1, I109N1, I131N1, I131N2, I137N1, I137N2, I139N1]
  Il := ![[I107N1], [I109N1], [], [], [I131N1, I131N2], [I137N1, I137N2], [I139N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
