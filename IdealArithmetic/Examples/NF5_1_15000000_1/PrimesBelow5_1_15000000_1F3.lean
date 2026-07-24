
import IdealArithmetic.Examples.NF5_1_15000000_1.RI5_1_15000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, -15, -15, 5, 17]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![20, -15, -15, 5, 17]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![21, 92, 58, 1, 0], ![102, 35, 45, 0, 1]] where
  M :=![![![20, -15, -15, 5, 17], ![-153, -46, 1, -19, 15], ![-135, -197, 20, 87, -57], ![234, 124, -114, -105, 90], ![-159, -33, 21, -33, -64]]]
  hmulB := by decide  
  f := ![![![5536, -715, -871, -681, 1121]], ![![-10089, 1302, 1587, 1241, -2043]], ![![18387, -2373, -2894, -2263, 3723]], ![![2238, -289, -353, -276, 453]], ![![9759, -1260, -1536, -1201, 1976]]]
  g := ![![![-17, -10, -10, 5, 17], ![-12, 11, 4, -19, 15], ![36, -58, -23, 87, -57], ![-63, 62, 18, -105, 90], ![66, 49, 45, -33, -64]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [25, 60, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 95, 76], [3, 11, 31], [0, 1]]
 g := ![![[87, 3, 100], [72, 77, 53], [48, 49], [37, 104, 34], [69, 61], [1]], ![[68, 101, 100, 34], [96, 42, 66, 47], [101, 99], [15, 23, 99, 102], [15, 100], [22, 91, 14, 62]], ![[56, 26, 27, 97], [11, 35, 35, 93], [48, 29], [10, 21, 25, 95], [88, 56], [74, 17, 99, 45]]]
 h' := ![![[72, 95, 76], [19, 5, 10], [30, 36, 38], [38, 39, 7], [77, 10, 81], [82, 47, 75], [0, 1]], ![[3, 11, 31], [19, 83, 62], [77, 90, 51], [26, 28, 45], [21, 86, 46], [17, 27, 10], [72, 95, 76]], ![[0, 1], [18, 19, 35], [13, 88, 18], [101, 40, 55], [63, 11, 87], [103, 33, 22], [3, 11, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 75], []]
 b := ![[], [89, 96, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [25, 60, 32, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9530884, 5878418, -713377, -2498894, -3422862]
  a := ![0, -8, -7, -7, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3842426, 3323148, 2787395, -2498894, -3422862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5536, 715, 871, 681, -1121]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-5536, 715, 871, 681, -1121]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![93, 91, 1, 0, 0], ![58, 21, 0, 1, 0], ![25, 33, 0, 0, 1]] where
  M :=![![![-5536, 715, 871, 681, -1121], ![10089, -1302, -1587, -1241, 2043], ![-18387, 2373, 2894, 2263, -3723], ![15048, -1942, -2368, -1851, 3048], ![-5241, 675, 825, 645, -1060]]]
  hmulB := by decide  
  f := ![![![-20, 15, 15, -5, -17]], ![![153, 46, -1, 19, -15]], ![![114, 54, 12, 11, -27]], ![![17, 16, 9, 2, -13]], ![![44, 18, 3, 5, -8]]]
  g := ![![![-916, -522, 871, 681, -1121], ![1669, 951, -1587, -1241, 2043], ![-3044, -1735, 2894, 2263, -3723], ![2490, 1419, -2368, -1851, 3048], ![-868, -495, 825, 645, -1060]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [79, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 106], [0, 1]]
 g := ![![[61, 42], [94, 23], [37], [50, 29], [10], [103, 1]], ![[0, 65], [2, 84], [37], [41, 78], [10], [99, 106]]]
 h' := ![![[103, 106], [64, 16], [47, 68], [9, 12], [91, 55], [102, 44], [0, 1]], ![[0, 1], [0, 91], [96, 39], [68, 95], [85, 52], [33, 63], [103, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [10, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [79, 4, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1585910, -900121, 394765, 666420, 490907]
  a := ![3, -61, -63, -66, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-833870, -626341, 394765, 666420, 490907]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![20, -15, -15, 5, 17]] ![![-5536, 715, 871, 681, -1121]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [105, 6, 40, 42, 41, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 45, 71, 8, 48], [62, 101, 101, 93, 78], [4, 108, 65, 95, 9], [5, 72, 90, 22, 83], [0, 1]]
 g := ![![[81, 76, 15, 96, 108], [6, 70, 0, 20], [68, 61, 59, 104, 71], [16, 23, 38, 47, 16], [68, 1], []], ![[25, 74, 94, 100, 103, 52, 2, 31], [58, 43, 88, 84], [50, 73, 43, 73, 13, 27, 37, 66], [89, 2, 27, 89, 88, 86, 79, 9], [66, 8, 108, 48], [29, 96, 55, 12, 6, 95, 52, 66]], ![[31, 108, 69, 87, 22, 76, 11, 63], [18, 29, 33, 45], [16, 3, 7, 106, 55, 18, 94, 83], [61, 54, 5, 9, 20, 53, 52, 97], [106, 8, 7, 64], [75, 41, 16, 87, 96, 69, 65, 75]], ![[34, 83, 25, 31, 51, 4, 58, 78], [0, 20, 81, 45], [69, 22, 53, 33, 90, 105, 45, 9], [65, 68, 41, 43, 50, 57, 106, 88], [34, 38, 44, 12], [73, 66, 93, 42, 67, 94, 63, 75]], ![[93, 9, 35, 101, 58, 107, 74, 93], [41, 91, 67, 36], [2, 47, 108, 76, 61, 68, 78, 63], [5, 19, 17, 87, 25, 90, 26, 93], [83, 86, 87, 9], [14, 60, 35, 85, 84, 108, 52, 82]]]
 h' := ![![[106, 45, 71, 8, 48], [106, 18, 9, 90, 76], [54, 8, 49, 11, 67], [64, 78, 105, 47, 17], [54, 32, 108, 47, 4], [0, 0, 0, 1], [0, 1]], ![[62, 101, 101, 93, 78], [102, 71, 101, 84, 11], [57, 93, 0, 58, 53], [56, 106, 48, 62, 48], [10, 79, 88, 73, 94], [89, 8, 52, 42, 87], [106, 45, 71, 8, 48]], ![[4, 108, 65, 95, 9], [23, 70, 75, 63, 88], [96, 6, 74, 37, 46], [91, 70, 71, 13, 103], [63, 105, 12, 28, 104], [27, 108, 69, 35, 8], [62, 101, 101, 93, 78]], ![[5, 72, 90, 22, 83], [7, 68, 93, 95, 46], [94, 44, 21, 47, 46], [106, 16, 13, 61, 108], [105, 43, 25, 25, 19], [29, 105, 79, 64, 11], [4, 108, 65, 95, 9]], ![[0, 1], [10, 100, 49, 104, 106], [8, 67, 74, 65, 6], [0, 57, 90, 35, 51], [66, 68, 94, 45, 106], [72, 106, 18, 76, 3], [5, 72, 90, 22, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 51, 50, 94], [], [], []]
 b := ![[], [71, 67, 23, 56, 48], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [105, 6, 40, 42, 41, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22717698904, 25076054187, 11634917785, 4968371401, -2278845015]
  a := ![1, -6, -6, -7, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![208419256, 230055543, 106742365, 45581389, -20906835]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 15386239549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![920, 671, 21, -169, -239]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![920, 671, 21, -169, -239]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![90, 35, 84, 1, 0], ![37, 41, 19, 0, 1]] where
  M :=![![![920, 671, 21, -169, -239], ![2151, 1658, 165, -295, -507], ![4563, 3837, 762, -271, -885], ![-828, -338, 322, 443, 366], ![-129, 519, 789, 705, 392]]]
  hmulB := by decide  
  f := ![![![544, -55, -93, -69, 115]], ![![-1035, 106, 173, 111, -207]], ![![1863, -241, -280, -151, 333]], ![![1485, -188, -227, -132, 273]], ![![119, -21, -15, -8, 19]]]
  g := ![![![221, 145, 166, -169, -239], ![420, 290, 306, -295, -507], ![546, 439, 357, -271, -885], ![-480, -273, -388, 443, 366], ![-691, -356, -583, 705, 392]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [34, 65, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 87, 79], [44, 25, 34], [0, 1]]
 g := ![![[74, 60, 88], [74, 82], [56, 98], [41, 44], [79, 20, 83], [1]], ![[39, 53, 7, 24], [45, 18], [17, 77], [106, 14], [57, 111, 82, 40], [18, 3, 60, 20]], ![[45, 96, 103, 93], [68, 36], [106, 99], [2, 112], [17, 28, 42, 6], [73, 106, 88, 93]]]
 h' := ![![[83, 87, 79], [65, 50, 38], [35, 35, 46], [73, 24, 95], [26, 87, 48], [79, 48, 14], [0, 1]], ![[44, 25, 34], [52, 79, 41], [0, 4, 73], [76, 55, 90], [8, 33, 50], [73, 57, 74], [83, 87, 79]], ![[0, 1], [9, 97, 34], [93, 74, 107], [9, 34, 41], [23, 106, 15], [99, 8, 25], [44, 25, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 1], []]
 b := ![[], [79, 11, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [34, 65, 99, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-389687903, -234438504, 41785606, 110690819, 133502009]
  a := ![1, 26, 22, 17, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-135322442, -84798226, -104360897, 110690819, 133502009]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-164, -68, 72, 49, -71]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-164, -68, 72, 49, -71]] 
 ![![113, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![-164, -68, 72, 49, -71], ![639, 121, -186, -23, 147], ![-1323, 12, 213, -257, -69], ![657, -262, 62, 424, -195], ![582, 264, -270, -198, 271]]]
  hmulB := by decide  
  f := ![![![-3820, -2426, 312, 1029, 1135]], ![![-1375, -877, 110, 369, 409]], ![![-1091, -704, 77, 284, 320]], ![![-787, -506, 58, 207, 232]], ![![-3776, -2410, 294, 1005, 1116]]]
  g := ![![![64, -68, 72, 49, -71], ![-131, 121, -186, -23, 147], ![56, 12, 213, -257, -69], ![182, -262, 62, 424, -195], ![-245, 264, -270, -198, 271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-389, 49, 61, 48, -78]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-389, 49, 61, 48, -78]] 
 ![![113, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![100, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![-389, 49, 61, 48, -78], ![702, -94, -111, -86, 144], ![-1296, 159, 202, 160, -258], ![1053, -136, -166, -130, 213], ![-369, 45, 57, 45, -74]]]
  hmulB := by decide  
  f := ![![![-25, 65, -41, -84, 54]], ![![-22, 44, -27, -58, 36]], ![![11, 28, -21, -32, 24]], ![![-41, 56, -32, -76, 45]], ![![-17, 49, -31, -63, 40]]]
  g := ![![![-42, 49, 61, 48, -78], ![77, -94, -111, -86, 144], ![-138, 159, 202, 160, -258], ![115, -136, -166, -130, 213], ![-38, 45, 57, 45, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![920, 671, 21, -169, -239]] ![![-164, -68, 72, 49, -71]]
  ![![-25, 65, -41, -84, 54]] where
 M := ![![![-25, 65, -41, -84, 54]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-25, 65, -41, -84, 54]] ![![-389, 49, 61, 48, -78]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1871, 248, 296, 230, -382]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-1871, 248, 296, 230, -382]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![16, 63, 1, 0, 0], ![121, 60, 0, 1, 0], ![20, 69, 0, 0, 1]] where
  M :=![![![-1871, 248, 296, 230, -382], ![3438, -429, -536, -422, 690], ![-6210, 832, 991, 770, -1266], ![5094, -664, -800, -623, 1038], ![-1788, 228, 288, 228, -353]]]
  hmulB := by decide  
  f := ![![![-461, -64, 120, -10, -86]], ![![774, -83, -72, 242, -30]], ![![328, -43, -25, 112, -20]], ![![-89, -108, 88, 111, -104]], ![![362, -53, -24, 130, -27]]]
  g := ![![![-211, -46, 296, 230, -382], ![388, 87, -536, -422, 690], ![-708, -161, 991, 770, -1266], ![571, 122, -800, -623, 1038], ![-212, -57, 288, 228, -353]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [107, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [122, 126], [0, 1]]
 g := ![![[95, 19], [122, 30], [94, 121], [113, 37], [52, 120], [122, 1]], ![[0, 108], [99, 97], [124, 6], [55, 90], [87, 7], [117, 126]]]
 h' := ![![[122, 126], [27, 107], [102, 86], [101, 116], [24, 75], [27, 45], [0, 1]], ![[0, 1], [0, 20], [53, 41], [29, 11], [30, 52], [56, 82], [122, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [6, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [107, 5, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16097, -21301, 5995, 16832, 7164]
  a := ![-1, -6, 1, 10, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18047, -14986, 5995, 16832, 7164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1343, 830, -768, -714, 824]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![1343, 830, -768, -714, 824]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![45, 121, 1, 0, 0], ![45, 69, 0, 1, 0], ![26, 70, 0, 0, 1]] where
  M :=![![![1343, 830, -768, -714, 824], ![-7416, -1897, 2480, 828, -2142], ![19278, 1490, -4191, 1838, 2484], ![-13374, 1638, 1156, -4373, 672], ![-4506, -3156, 2820, 2826, -3097]]]
  hmulB := by decide  
  f := ![![![6677, -502, -1000, -874, 1132]], ![![-10188, 2281, 1768, 1144, -2622]], ![![-7155, 1991, 1305, 756, -2070]], ![![-3303, 1079, 628, 329, -1050]], ![![-4196, 1154, 764, 446, -1205]]]
  g := ![![![367, 672, -768, -714, 824], ![-792, -1647, 2480, 828, -2142], ![477, 1637, -4191, 1838, 2484], ![897, 917, 1156, -4373, 672], ![-1402, -2540, 2820, 2826, -3097]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [36, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 126], [0, 1]]
 g := ![![[26, 60], [38, 117], [112, 71], [116, 1], [64, 69], [80, 1]], ![[0, 67], [0, 10], [77, 56], [69, 126], [123, 58], [33, 126]]]
 h' := ![![[80, 126], [29, 106], [32, 25], [15, 43], [109, 126], [41, 14], [0, 1]], ![[0, 1], [0, 21], [0, 102], [26, 84], [29, 1], [18, 113], [80, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [64, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [36, 47, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42588, -2490, -7366, 5156, 5082]
  a := ![0, -2, -14, -36, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![78, 1396, -7366, 5156, 5082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 14, 0, -4, -6]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![17, 14, 0, -4, -6]] 
 ![![127, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![17, 14, 0, -4, -6], ![54, 35, 0, -10, -12], ![108, 90, 9, -16, -30], ![0, -2, 4, 5, 6], ![18, 24, 12, 6, -1]]]
  hmulB := by decide  
  f := ![![![-361, -14, 72, -36, -42]], ![![-196, -9, 40, -18, -24]], ![![-143, 0, 25, -20, -12]], ![![-324, -18, 68, -27, -42]], ![![-61, -2, 12, -6, -7]]]
  g := ![![![-3, 14, 0, -4, -6], ![-8, 35, 0, -10, -12], ![-33, 90, 9, -16, -30], ![-6, -2, 4, 5, 6], ![-23, 24, 12, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-1871, 248, 296, 230, -382]] ![![1343, 830, -768, -714, 824]]
  ![![-361, -14, 72, -36, -42]] where
 M := ![![![-361, -14, 72, -36, -42]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-361, -14, 72, -36, -42]] ![![17, 14, 0, -4, -6]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3398, -3964, 2032, 5225, -3351]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![3398, -3964, 2032, 5225, -3351]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![99, 126, 32, 1, 0], ![34, 79, 29, 0, 1]] where
  M :=![![![3398, -3964, 2032, 5225, -3351], ![30159, 15483, -15178, -12375, 15675], ![-141075, -32044, 44527, 11063, -37125], ![146529, 15858, -34826, 8714, 22941], ![-18162, 14184, -6270, -19806, 11633]]]
  hmulB := by decide  
  f := ![![![946, 870, -64, -321, -471]], ![![4239, 2295, -350, -1027, -963]], ![![8667, 6778, -267, -2235, -3081]], ![![6921, 4524, -450, -1777, -2034]], ![![4748, 3133, -285, -1202, -1393]]]
  g := ![![![-3053, -3035, -519, 5225, -3351], ![5514, 2568, -563, -12375, 15675], ![198, 11503, 5856, 11063, -37125], ![-11421, -22095, -7473, 8714, 22941], ![11810, 12143, 2215, -19806, 11633]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [46, 12, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 16, 49], [4, 114, 82], [0, 1]]
 g := ![![[62, 15, 28], [20, 89, 4], [89, 46], [9, 121], [70, 46], [34, 1], []], ![[67, 28, 26, 108], [38, 129, 64, 91], [37, 100], [82, 5], [81, 117], [22, 27], [17, 43]], ![[1, 16, 65, 47], [47, 46, 62, 14], [47, 60], [34, 13], [7, 63], [124, 125], [115, 43]]]
 h' := ![![[30, 16, 49], [128, 33, 91], [31, 110, 129], [123, 7, 35], [119, 129, 11], [8, 70, 96], [0, 0, 1], [0, 1]], ![[4, 114, 82], [66, 21, 70], [82, 12, 53], [9, 48, 10], [47, 19, 108], [74, 5, 95], [118, 88, 114], [30, 16, 49]], ![[0, 1], [48, 77, 101], [15, 9, 80], [9, 76, 86], [130, 114, 12], [37, 56, 71], [97, 43, 16], [4, 114, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 90], []]
 b := ![[], [119, 128, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [46, 12, 97, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5531739, 1382124, 221858, 798499, -1594589]
  a := ![13, -6, -1, 5, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-147356, 204151, 159641, 798499, -1594589]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811, -109, -129, -100, 166]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![811, -109, -129, -100, 166]] 
 ![![131, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![811, -109, -129, -100, 166], ![-1494, 184, 231, 182, -300], ![2700, -363, -436, -340, 546], ![-2205, 292, 346, 268, -453], ![789, -93, -129, -105, 148]]]
  hmulB := by decide  
  f := ![![![2933, 577, -869, -128, 694]], ![![624, 132, -191, -38, 156]], ![![407, 44, -97, 24, 64]], ![![1244, 279, -391, -94, 325]], ![![698, 136, -206, -29, 164]]]
  g := ![![![44, -109, -129, -100, 166], ![-77, 184, 231, 182, -300], ![152, -363, -436, -340, 546], ![-116, 292, 346, 268, -453], ![47, -93, -129, -105, 148]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74, 47, -7, -21, -23]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![74, 47, -7, -21, -23]] 
 ![![131, 0, 0, 0, 0], ![106, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![74, 47, -7, -21, -23], ![207, 136, -15, -55, -63], ![567, 381, -28, -139, -165], ![36, 34, 10, 1, -6], ![231, 171, 9, -39, -58]]]
  hmulB := by decide  
  f := ![![![670, 31, -151, -27, 133]], ![![533, 26, -121, -23, 107]], ![![159, 1, -32, -1, 27]], ![![84, 11, -23, -8, 21]], ![![61, 1, -13, -3, 12]]]
  g := ![![![-31, 47, -7, -21, -23], ![-92, 136, -15, -55, -63], ![-264, 381, -28, -139, -165], ![-29, 34, 10, 1, -6], ![-128, 171, 9, -39, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![3398, -3964, 2032, 5225, -3351]] ![![811, -109, -129, -100, 166]]
  ![![-670, -31, 151, 27, -133]] where
 M := ![![![-670, -31, 151, 27, -133]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-670, -31, 151, 27, -133]] ![![74, 47, -7, -21, -23]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0, 0, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] where
  M :=![![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 5 2 7 [30, 66, 133, 93, 70, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 111, 112, 100, 43], [62, 62, 52, 73, 105], [51, 11, 90, 39, 127], [21, 89, 20, 62, 136], [0, 1]]
 g := ![![[89, 22, 133, 59, 118], [91, 118, 81, 65], [61, 124, 16, 38], [21, 59, 78, 56, 99], [57, 12, 67, 1], [], []], ![[36, 72, 120, 8, 11, 21, 15, 70], [8, 1, 107, 72], [16, 78, 125, 100], [15, 123, 73, 32, 127, 35, 120, 96], [8, 76, 112, 109], [98, 130, 93, 34], [111, 13, 4, 68]], ![[25, 89, 67, 82, 108, 108, 5, 87], [16, 88, 96, 2], [77, 105, 89, 68], [66, 77, 84, 113, 112, 23, 28, 65], [17, 95, 6, 133], [70, 65, 90, 59], [118, 62, 94, 65]], ![[117, 125, 15, 78, 18, 118, 107, 92], [107, 95, 61, 4], [35, 66, 13, 9], [54, 91, 91, 117, 18, 95, 75, 29], [114, 112, 66, 133], [48, 70, 103, 25], [65, 36, 29, 100]], ![[89, 72, 79, 132, 110, 60, 131, 69], [30, 69, 41, 7], [86, 55, 38, 37], [40, 4, 97, 90, 83, 4, 29, 2], [85, 11, 111, 105], [1, 37, 68, 2], [97, 29, 80, 1]]]
 h' := ![![[70, 111, 112, 100, 43], [84, 13, 10, 23, 23], [99, 132, 49, 131, 105], [55, 104, 92, 101, 77], [71, 125, 29, 22, 28], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[62, 62, 52, 73, 105], [56, 12, 93, 125, 75], [61, 99, 93, 135, 49], [104, 28, 24, 48, 10], [2, 117, 49, 118, 85], [70, 16, 18, 123, 66], [63, 15, 67, 122, 50], [70, 111, 112, 100, 43]], ![[51, 11, 90, 39, 127], [112, 131, 22, 51, 104], [27, 114, 26, 89, 106], [62, 43, 121, 130, 94], [31, 121, 133, 45, 70], [33, 89, 124, 0, 63], [30, 95, 16, 45, 123], [62, 62, 52, 73, 105]], ![[21, 89, 20, 62, 136], [96, 62, 131, 52, 115], [44, 104, 123, 51, 2], [51, 78, 117, 7, 134], [105, 93, 83, 18, 40], [127, 6, 93, 130, 74], [103, 136, 13, 75, 132], [51, 11, 90, 39, 127]], ![[0, 1], [122, 56, 18, 23, 94], [101, 99, 120, 5, 12], [30, 21, 57, 125, 96], [83, 92, 117, 71, 51], [116, 26, 39, 21, 70], [134, 28, 40, 32, 106], [21, 89, 20, 62, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 110, 34, 26], [], [], []]
 b := ![[], [134, 3, 68, 119, 44], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 5
  hpos := by decide
  P := [30, 66, 133, 93, 70, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![67032730, -13339142, -1195188, 26359896, -12401514]
  a := ![-1, 0, -2, -5, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![489290, -97366, -8724, 192408, -90522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 48261724457 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀

instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-227, 63, 15, -104, 10]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-227, 63, 15, -104, 10]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![19, 48, 71, 73, 1]] where
  M :=![![![-227, 63, 15, -104, 10], ![-90, -242, 227, 298, -312], ![2808, 1073, -1022, -624, 894], ![-3393, -700, 1038, 198, -837], ![1185, -57, -93, 339, -62]]]
  hmulB := by decide  
  f := ![![![1075, -139, -169, -132, 218]], ![![-1962, 252, 309, 242, -396]], ![![3564, -465, -560, -436, 726]], ![![-2925, 376, 460, 360, -591]], ![![-239, 27, 38, 31, -45]]]
  g := ![![![-3, -3, -5, -6, 10], ![42, 106, 161, 166, -312], ![-102, -301, -464, -474, 894], ![90, 284, 435, 441, -837], ![17, 21, 31, 35, -62]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [119, 72, 126, 46, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 102, 87, 65], [81, 133, 25, 36], [29, 42, 27, 38], [0, 1]]
 g := ![![[20, 5, 127, 4], [121, 50, 38, 117], [96, 12, 67], [21, 41, 43, 67], [67, 19, 31], [1], []], ![[38, 123, 135, 26, 129, 6], [100, 25, 129, 1, 87, 29], [59, 2, 118], [50, 107, 76, 104, 116, 65], [102, 110, 137], [53, 58, 30], [53, 23, 55]], ![[104, 99, 11, 107, 98, 55], [119, 33, 109, 113], [22, 72, 64], [50, 85, 2, 83, 9, 1], [93, 54, 7], [90, 134, 91], [132, 8, 45]], ![[93, 69, 61, 111, 2, 29], [93, 93, 136, 116, 74, 28], [85, 77, 49], [106, 24, 86, 133, 112, 66], [28, 47, 116], [73, 117, 65], [31, 124, 54]]]
 h' := ![![[122, 102, 87, 65], [57, 83, 43, 2], [122, 125, 13, 16], [3, 44, 64, 22], [72, 43, 128, 117], [20, 67, 13, 93], [0, 0, 1], [0, 1]], ![[81, 133, 25, 36], [28, 77, 34, 36], [106, 120, 106, 136], [90, 92, 137, 102], [86, 31, 42, 138], [100, 78, 53, 50], [98, 126, 73, 126], [122, 102, 87, 65]], ![[29, 42, 27, 38], [3, 51, 121, 34], [53, 89, 29], [126, 114, 119, 8], [87, 137, 84, 116], [27, 1, 64, 29], [27, 109, 10, 77], [81, 133, 25, 36]], ![[0, 1], [102, 67, 80, 67], [131, 83, 130, 126], [51, 28, 97, 7], [55, 67, 24, 46], [107, 132, 9, 106], [71, 43, 55, 75], [29, 42, 27, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 75, 35], []]
 b := ![[], [], [14, 107, 46, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [119, 72, 126, 46, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9210558400, -7455329909, 62735513, 2675724210, 2883871005]
  a := ![3, 10, 6, -2, 63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-460461205, -1049504591, -1472605078, -1495301145, 2883871005]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1075, 139, 169, 132, -218]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-1075, 139, 169, 132, -218]] 
 ![![139, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![133, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-1075, 139, 169, 132, -218], ![1962, -252, -309, -242, 396], ![-3564, 465, 560, 436, -726], ![2925, -376, -460, -360, 591], ![-1011, 135, 159, 123, -208]]]
  hmulB := by decide  
  f := ![![![227, -63, -15, 104, -10]], ![![97, -25, -8, 42, -2]], ![![197, -68, -7, 104, -16]], ![![93, -14, -12, 30, 3]], ![![47, -15, -3, 23, -2]]]
  g := ![![![-215, 139, 169, 132, -218], ![393, -252, -309, -242, 396], ![-713, 465, 560, 436, -726], ![585, -376, -460, -360, 591], ![-203, 135, 159, 123, -208]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-227, 63, 15, -104, 10]] ![![-1075, 139, 169, 132, -218]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26491, -3420, -4168, -3258, 5364]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![26491, -3420, -4168, -3258, 5364]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![140, 127, 30, 1, 0], ![56, 28, 74, 0, 1]] where
  M :=![![![26491, -3420, -4168, -3258, 5364], ![-48276, 6231, 7594, 5936, -9774], ![87966, -11360, -13839, -10818, 17808], ![-71982, 9298, 11322, 8851, -14574], ![25056, -3234, -3942, -3084, 5071]]]
  hmulB := by decide  
  f := ![![![-37, -16, 4, 2, 0]], ![![0, -33, -10, 12, 6]], ![![-54, -28, -47, -46, 36]], ![![-46, -49, -14, 3, 12]], ![![-40, -26, -24, -20, 19]]]
  g := ![![![1223, 1746, -2036, -3258, 5364], ![-2228, -3181, 3710, 5936, -9774], ![4062, 5798, -6759, -10818, 17808], ![-3322, -4743, 5532, 8851, -14574], ![1160, 1654, -1924, -3084, 5071]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [22, 114, 127, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 101, 59], [128, 47, 90], [0, 1]]
 g := ![![[59, 3, 39], [5, 88], [87, 3, 113], [113, 42], [16, 48, 118], [22, 1], []], ![[45, 126, 25, 115], [47, 82], [111, 121, 133, 87], [120, 28], [7, 9, 17, 14], [143, 123], [143, 54]], ![[117, 82, 3, 2], [117, 5], [75, 70, 21, 78], [134, 124], [80, 132, 41, 72], [121, 69], [112, 54]]]
 h' := ![![[43, 101, 59], [121, 14, 28], [23, 139, 104], [132, 84, 34], [95, 128, 108], [112, 3, 72], [0, 0, 1], [0, 1]], ![[128, 47, 90], [18, 7, 56], [146, 22, 126], [25, 145, 147], [70, 51, 112], [131, 112, 134], [44, 136, 47], [43, 101, 59]], ![[0, 1], [101, 128, 65], [80, 137, 68], [63, 69, 117], [39, 119, 78], [115, 34, 92], [63, 13, 101], [128, 47, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 114], []]
 b := ![[], [146, 76, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [22, 114, 127, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3756078, -2261262, 523208, 1086976, 1137098]
  a := ![1, 4, 0, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1473894, -1155342, -780076, 1086976, 1137098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 16, -4, -2, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![37, 16, -4, -2, 0]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![146, 31, 1, 0, 0], ![62, 79, 0, 1, 0], ![20, 62, 0, 0, 1]] where
  M :=![![![37, 16, -4, -2, 0], ![0, 33, 10, -12, -6], ![54, 28, 47, 46, -36], ![54, 30, -34, -23, 54], ![-108, -18, 42, 24, 1]]]
  hmulB := by decide  
  f := ![![![-26491, 3420, 4168, 3258, -5364]], ![![48276, -6231, -7594, -5936, 9774]], ![![-16504, 2131, 2597, 2030, -3342]], ![![15056, -1943, -2368, -1851, 3048]], ![![16364, -2112, -2574, -2012, 3313]]]
  g := ![![![5, 2, -4, -2, 0], ![-4, 7, 10, -12, -6], ![-60, -19, 47, 46, -36], ![36, -3, -34, -23, 54], ![-52, -22, 42, 24, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [144, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 148], [0, 1]]
 g := ![![[113, 119], [142], [92, 25], [5], [94, 9], [67], [1]], ![[0, 30], [142], [62, 124], [5], [113, 140], [67], [1]]]
 h' := ![![[118, 148], [134, 62], [13, 80], [107, 144], [23, 81], [62, 146], [5, 118], [0, 1]], ![[0, 1], [0, 87], [66, 69], [113, 5], [45, 68], [6, 3], [72, 31], [118, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [75, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [144, 31, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94, -694, 158, 610, -84]
  a := ![4, -1, 0, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-398, -326, 158, 610, -84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![26491, -3420, -4168, -3258, 5364]] ![![37, 16, -4, -2, 0]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13487, 1712, 2124, 1670, -2706]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-13487, 1712, 2124, 1670, -2706]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![147, 42, 26, 114, 1]] where
  M :=![![![-13487, 1712, 2124, 1670, -2706], ![24354, -3245, -3828, -2962, 5010], ![-45090, 5496, 7091, 5642, -8886], ![36450, -4772, -5744, -4475, 7422], ![-12996, 1464, 2028, 1644, -2489]]]
  hmulB := by decide  
  f := ![![![-5, 8, -4, -10, 6]], ![![-54, -27, 28, 22, -30]], ![![270, 64, -83, -22, 66]], ![![-270, -28, 64, -17, -42]], ![![-177, -10, 38, -20, -23]]]
  g := ![![![2545, 764, 480, 2054, -2706], ![-4716, -1415, -888, -3802, 5010], ![8352, 2508, 1577, 6746, -8886], ![-6984, -2096, -1316, -5633, 7422], ![2337, 702, 442, 1890, -2489]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [82, 40, 85, 75, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 143, 89, 45], [117, 1, 67, 40], [75, 6, 146, 66], [0, 1]]
 g := ![![[134, 53, 19, 90], [124, 54, 54, 44], [31, 150, 29, 118], [36, 134, 55], [85, 147, 85, 38], [1], []], ![[46, 88, 21, 70, 31, 2], [126, 23, 74, 104, 21, 42], [144, 19, 2, 79, 33, 90], [56, 15, 43], [30, 37, 84, 76, 86, 105], [5, 110, 121], [138, 38, 62]], ![[109, 22, 124, 11, 116, 11], [76, 75, 149, 107, 32, 39], [75, 47, 148, 90, 12, 31], [84, 85, 59], [114, 110, 68, 40, 86, 72], [105, 18, 9], [150, 120, 90]], ![[90, 143, 43, 91, 43, 113], [11, 5, 7, 115, 116, 63], [5, 102, 107, 136, 18, 147], [123, 53, 38], [68, 44, 6, 113], [17, 48, 64], [58, 8, 128]]]
 h' := ![![[35, 143, 89, 45], [100, 146, 140, 111], [25, 140, 97, 78], [40, 120, 109, 119], [127, 28, 75, 120], [69, 111, 66, 76], [0, 0, 1], [0, 1]], ![[117, 1, 67, 40], [99, 111, 77, 68], [57, 56, 104, 112], [43, 139, 15, 105], [16, 42, 39, 88], [115, 16, 91, 42], [26, 15, 40, 11], [35, 143, 89, 45]], ![[75, 6, 146, 66], [70, 47, 59, 125], [111, 119, 48, 119], [89, 79, 140, 86], [129, 62, 71, 19], [142, 53, 143, 33], [30, 98, 111, 148], [117, 1, 67, 40]], ![[0, 1], [75, 149, 26, 149], [3, 138, 53, 144], [69, 115, 38, 143], [76, 19, 117, 75], [126, 122, 2], [114, 38, 150, 143], [75, 6, 146, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [127, 101, 47], []]
 b := ![[], [], [62, 91, 19, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [82, 40, 85, 75, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2645290899578, -1850441603714, 80085196737, 607176303403, 695081663600]
  a := ![7, -46, -47, -48, -205]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-694187387078, -205588552814, -119152569913, -520742604947, 695081663600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -8, 4, 10, -6]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![5, -8, 4, 10, -6]] 
 ![![151, 0, 0, 0, 0], ![111, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![5, -8, 4, 10, -6], ![54, 27, -28, -22, 30], ![-270, -64, 83, 22, -66], ![270, 28, -64, 17, 42], ![-36, 24, -12, -36, 23]]]
  hmulB := by decide  
  f := ![![![13487, -1712, -2124, -1670, 2706]], ![![9753, -1237, -1536, -1208, 1956]], ![![5747, -728, -905, -712, 1152]], ![![5207, -660, -820, -645, 1044]], ![![6249, -792, -984, -774, 1253]]]
  g := ![![![3, -8, 4, 10, -6], ![-13, 27, -28, -22, 30], ![33, -64, 83, 22, -66], ![-19, 28, -64, 17, 42], ![-9, 24, -12, -36, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-13487, 1712, 2124, 1670, -2706]] ![![5, -8, 4, 10, -6]]
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


lemma PB242I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB242I3 : PrimesBelowBoundCertificateInterval O 103 151 242 where
  m := 9
  g := ![2, 1, 3, 3, 3, 1, 2, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB242I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
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
    · exact ![1225043, 11449]
    · exact ![15386239549]
    · exact ![1442897, 113, 113]
    · exact ![16129, 16129, 127]
    · exact ![2248091, 131, 131]
    · exact ![48261724457]
    · exact ![373301041, 139]
    · exact ![3307949, 22201]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I113N1, I113N2, I127N2, I131N1, I131N2, I139N1, I151N1]
  Il := ![[], [], [I113N1, I113N2], [I127N2], [I131N1, I131N2], [], [I139N1], [], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
