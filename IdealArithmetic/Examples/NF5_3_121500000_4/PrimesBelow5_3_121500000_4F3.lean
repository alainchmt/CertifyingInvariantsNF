
import IdealArithmetic.Examples.NF5_3_121500000_4.RI5_3_121500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, 98, 30, -2, -42]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![95, 98, 30, -2, -42]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![42, 98, 23, 1, 0], ![90, 100, 95, 0, 1]] where
  M :=![![![95, 98, 30, -2, -42], ![510, 463, 102, -18, -150], ![1854, 1830, 499, -42, -666], ![3804, 3630, 906, -95, -1176], ![2526, 2460, 644, -54, -817]]]
  hmulB := by decide  
  f := ![![![241, 34, -42, -10, 30]], ![![-330, -31, 54, 6, -30]], ![![342, -42, -43, 30, -18]], ![![-132, -22, 23, 7, -18]], ![![198, -38, -23, 24, -19]]]
  g := ![![![37, 42, 38, -2, -42], ![138, 161, 138, -18, -150], ![594, 678, 605, -42, -666], ![1062, 1220, 1073, -95, -1176], ![732, 836, 743, -54, -817]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [46, 83, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 77, 33], [94, 29, 74], [0, 1]]
 g := ![![[87, 25, 27], [41, 83, 85], [4, 64], [60, 105, 81], [65, 33], [1]], ![[77, 83, 106, 75], [60, 105, 21, 81], [105, 99], [37, 2, 52, 53], [26, 41], [17, 82, 93, 92]], ![[90, 59, 45, 8], [47, 54, 44, 63], [50, 85], [78, 6, 76, 54], [84, 61], [44, 88, 64, 15]]]
 h' := ![![[64, 77, 33], [40, 68, 53], [86, 64, 37], [22, 37, 8], [89, 81, 98], [61, 24, 51], [0, 1]], ![[94, 29, 74], [63, 37, 36], [104, 67, 82], [71, 5, 62], [4, 74, 58], [68, 35, 24], [64, 77, 33]], ![[0, 1], [74, 2, 18], [16, 83, 95], [47, 65, 37], [45, 59, 58], [59, 48, 32], [94, 29, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 15], []]
 b := ![[], [44, 61, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [46, 83, 56, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![209862914, 234326756, 94924276, 15461584, -148499992]
  a := ![17, 4, 8, 14, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![120798838, 126813932, 129409412, 15461584, -148499992]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 106, 26, -4, -40]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![113, 106, 26, -4, -40]] 
 ![![107, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![113, 106, 26, -4, -40], ![492, 463, 114, -16, -168], ![2064, 1966, 495, -60, -696], ![4020, 3862, 986, -103, -1320], ![2764, 2664, 684, -68, -903]]]
  hmulB := by decide  
  f := ![![![-3405, -574, 634, 132, -424]], ![![-879, -151, 164, 36, -112]], ![![-513, -68, 93, 8, -48]], ![![-2907, -536, 548, 141, -400]], ![![-244, -32, 44, 4, -23]]]
  g := ![![![-25, 106, 26, -4, -40], ![-111, 463, 114, -16, -168], ![-481, 1966, 495, -60, -696], ![-963, 3862, 986, -103, -1320], ![-668, 2664, 684, -68, -903]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -13, -5, 0, 6]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-7, -13, -5, 0, 6]] 
 ![![107, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![104, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-7, -13, -5, 0, 6], ![-72, -60, -13, 2, 18], ![-222, -231, -64, 4, 78], ![-438, -427, -113, 7, 132], ![-288, -288, -78, 4, 89]]]
  hmulB := by decide  
  f := ![![![-119, -11, 35, -34, 30]], ![![-38, -6, 11, -8, 6]], ![![-22, 15, 8, -26, 30]], ![![-200, -61, 55, -7, -12]], ![![-41, 5, 13, -22, 23]]]
  g := ![![![3, -13, -5, 0, 6], ![12, -60, -13, 2, 18], ![52, -231, -64, 4, 78], ![100, -427, -113, 7, 132], ![69, -288, -78, 4, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![95, 98, 30, -2, -42]] ![![113, 106, 26, -4, -40]]
  ![![-3257, -5188, -2208, -686, -578]] where
 M := ![![![-3257, -5188, -2208, -686, -578]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-3257, -5188, -2208, -686, -578]] ![![-7, -13, -5, 0, 6]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![1353443, 1323055, 347643, -26322, -427144]]]
 hmul := by decide  
 g := ![![![![12649, 12365, 3249, -246, -3992]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-800, -918, -276, 19, 369]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-800, -918, -276, 19, 369]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![64, 56, 9, 29, 1]] where
  M :=![![![-800, -918, -276, 19, 369], ![-4485, -4047, -956, 129, 1335], ![-16407, -16250, -4305, 371, 5553], ![-31632, -30730, -8018, 627, 9888], ![-21261, -20906, -5536, 389, 6700]]]
  hmulB := by decide  
  f := ![![![202, 68, -50, -11, 33]], ![![-363, -101, 90, -1, -33]], ![![399, -8, -99, 117, -111]], ![![672, 586, -166, -385, 552]], ![![142, 142, -35, -99, 139]]]
  g := ![![![-224, -198, -33, -98, 369], ![-825, -723, -119, -354, 1335], ![-3411, -3002, -498, -1474, 5553], ![-6096, -5362, -890, -2625, 9888], ![-4129, -3634, -604, -1779, 6700]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [94, 27, 45, 104, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 25, 91, 56], [100, 17, 107, 73], [59, 66, 20, 89], [0, 1]]
 g := ![![[106, 102, 33, 84], [63, 72, 43], [53, 59, 25, 84], [84, 95, 95, 80], [89, 5, 1], []], ![[38, 38, 99, 7, 94, 47], [31, 37, 16], [14, 77, 10, 108, 84, 24], [90, 103, 57, 90, 46, 6], [45, 21, 36], [100, 73, 62, 107, 18, 17]], ![[58, 3, 20, 24, 73, 102], [65, 0, 83], [68, 2, 13, 82, 73, 31], [32, 73, 53, 96, 17, 26], [34, 82, 9], [14, 26, 10, 50, 52, 105]], ![[56, 93, 81, 27, 58, 25], [20, 3, 38], [40, 15, 89, 20, 45, 97], [48, 82, 48, 99, 12, 29], [69, 25, 64], [80, 101, 3, 25, 23, 66]]]
 h' := ![![[64, 25, 91, 56], [7, 57, 20, 53], [32, 14, 38, 77], [61, 104, 59, 53], [27, 70, 17, 84], [0, 0, 0, 1], [0, 1]], ![[100, 17, 107, 73], [17, 53, 12, 39], [73, 12, 90, 4], [67, 5, 21, 4], [96, 6, 58, 107], [82, 68, 95, 103], [64, 25, 91, 56]], ![[59, 66, 20, 89], [29, 54, 4, 52], [12, 89, 108, 44], [49, 99, 88, 86], [96, 37, 68, 29], [26, 1, 12, 106], [100, 17, 107, 73]], ![[0, 1], [70, 54, 73, 74], [36, 103, 91, 93], [42, 10, 50, 75], [85, 105, 75, 107], [24, 40, 2, 8], [59, 66, 20, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 33, 11], []]
 b := ![[], [], [53, 72, 86, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [94, 27, 45, 104, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1315763495493341, -1286181511661952, -346613685401041, 22044040510454, 458818089442263]
  a := ![113, -4, 57, 50, -449]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-281469002016497, -247522885508520, -41064004498912, -121868628929497, 458818089442263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![202, 68, -50, -11, 33]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![202, 68, -50, -11, 33]] 
 ![![109, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![100, 0, 0, 0, 1]] where
  M :=![![![202, 68, -50, -11, 33], ![-363, -101, 90, -1, -33], ![399, -8, -99, 117, -111], ![672, 586, -166, -385, 552], ![-201, -140, 50, 81, -122]]]
  hmulB := by decide  
  f := ![![![-800, -918, -276, 19, 369]], ![![-665, -753, -224, 16, 300]], ![![-723, -806, -237, 17, 315]], ![![-848, -922, -266, 19, 348]], ![![-929, -1034, -304, 21, 400]]]
  g := ![![![-38, 68, -50, -11, 33], ![42, -101, 90, -1, -33], ![101, -8, -99, 117, -111], ![-570, 586, -166, -385, 552], ![127, -140, 50, 81, -122]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-800, -918, -276, 19, 369]] ![![202, 68, -50, -11, 33]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5932, 1790, -1324, -471, 1113]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![5932, 1790, -1324, -471, 1113]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![10, 21, 38, 41, 1]] where
  M :=![![![5932, 1790, -1324, -471, 1113], ![-11943, -3825, 2732, 991, -2313], ![24783, 8302, -5807, -2135, 4953], ![-20544, -7344, 4920, 1853, -4224], ![3243, 1036, -762, -275, 652]]]
  hmulB := by decide  
  f := ![![![14, 12, 2, -1, -3]], ![![39, 41, 14, 1, -21]], ![![249, 220, 39, -17, -51]], ![![312, 336, 120, 13, -168]], ![![208, 207, 60, -1, -83]]]
  g := ![![![-46, -191, -386, -408, 1113], ![99, 396, 802, 848, -2313], ![-219, -847, -1717, -1816, 4953], ![192, 720, 1464, 1549, -4224], ![-29, -112, -226, -239, 652]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [38, 28, 39, 95, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 103, 106, 88], [84, 62, 23, 101], [26, 60, 97, 37], [0, 1]]
 g := ![![[50, 104, 75, 13], [97, 67, 49], [15, 66, 49], [22, 112, 57], [106, 59, 18, 1], []], ![[72, 77, 32, 21, 17, 53], [21, 41, 109], [97, 111, 36], [54, 9, 69], [54, 26, 29, 3, 44, 16], [15, 68, 47, 74, 103, 82]], ![[26, 2, 30, 16, 49, 29], [48, 4, 7], [33, 17, 109], [26, 78, 28], [104, 80, 22, 87, 13, 75], [54, 62, 112, 112, 76, 80]], ![[58, 110, 97, 10, 81, 84], [59, 68, 15], [8, 4, 50], [9, 84, 11], [57, 74, 50, 112, 3, 108], [78, 77, 33, 104, 11, 29]]]
 h' := ![![[21, 103, 106, 88], [12, 15, 22, 76], [46, 7, 79, 7], [86, 44, 26, 106], [40, 101, 84, 82], [0, 0, 0, 1], [0, 1]], ![[84, 62, 23, 101], [92, 17, 53, 108], [41, 25, 0, 30], [26, 23, 40, 6], [48, 89, 51, 71], [103, 38, 109, 101], [21, 103, 106, 88]], ![[26, 60, 97, 37], [2, 96, 110, 32], [40, 99, 44, 32], [27, 33, 90, 30], [87, 87, 51, 49], [1, 8, 37, 19], [84, 62, 23, 101]], ![[0, 1], [29, 98, 41, 10], [24, 95, 103, 44], [92, 13, 70, 84], [78, 62, 40, 24], [35, 67, 80, 105], [26, 60, 97, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [80, 24, 26], []]
 b := ![[], [], [97, 1, 88, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [38, 28, 39, 95, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41012888856, -41475413539, -12285900581, -48790578, 15876164649]
  a := ![10, 1, 5, 6, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1767916242, -3317476736, -5447612011, -5760810099, 15876164649]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 12, 2, -1, -3]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![14, 12, 2, -1, -3]] 
 ![![113, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![72, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![14, 12, 2, -1, -3], ![39, 41, 14, 1, -21], ![249, 220, 39, -17, -51], ![312, 336, 120, 13, -168], ![291, 274, 64, -11, -82]]]
  hmulB := by decide  
  f := ![![![5932, 1790, -1324, -471, 1113]], ![![3569, 1075, -796, -283, 669]], ![![3999, 1214, -895, -319, 753]], ![![2128, 632, -472, -167, 396]], ![![2391, 722, -534, -190, 449]]]
  g := ![![![-7, 12, 2, -1, -3], ![-26, 41, 14, 1, -21], ![-132, 220, 39, -17, -51], ![-220, 336, 120, 13, -168], ![-171, 274, 64, -11, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![5932, 1790, -1324, -471, 1113]] ![![14, 12, 2, -1, -3]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [33, 92, 101, 23, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 108, 29, 67, 117], [125, 18, 90, 12, 111], [46, 108, 21, 119, 21], [15, 19, 114, 56, 5], [0, 1]]
 g := ![![[118, 57, 112, 23, 30], [114, 83, 121, 52, 81], [49, 88, 6, 2, 84], [41, 56, 17, 27, 79], [94, 102, 1], []], ![[24, 94, 9, 74, 90, 126, 82, 104], [62, 63, 73, 6, 95, 43, 99, 34], [124, 55, 89, 122, 33, 94, 75, 26], [29, 62, 51, 63, 88, 98, 78, 52], [44, 23, 92, 48, 44, 69, 56, 87], [108, 34, 34, 121, 56, 33, 15, 16]], ![[44, 81, 52, 5, 39, 85, 62, 95], [122, 89, 83, 113, 117, 77, 57, 20], [102, 110, 111, 83, 40, 48, 28, 125], [105, 8, 54, 89, 70, 68, 103, 67], [63, 24, 33, 64, 15, 4, 20, 96], [18, 59, 25, 119, 50, 123, 110, 95]], ![[22, 42, 66, 25, 36, 72, 65, 113], [86, 31, 91, 62, 22, 19, 104, 42], [13, 28, 3, 50, 29, 99, 64, 22], [73, 116, 98, 60, 102, 86, 73, 25], [112, 61, 69, 21, 70, 70, 8, 37], [42, 0, 84, 63, 58, 73, 80, 117]], ![[102, 46, 105, 107, 11, 82, 22, 54], [11, 62, 62, 70, 6, 93, 43, 55], [13, 30, 56, 12, 40, 16, 119, 111], [59, 76, 18, 86, 112, 120, 7, 95], [79, 118, 71, 115, 112, 38, 5, 102], [16, 118, 19, 40, 44, 59, 59, 125]]]
 h' := ![![[43, 108, 29, 67, 117], [48, 121, 94, 107, 41], [34, 112, 11, 66, 9], [44, 90, 5, 125, 46], [73, 51, 12, 17, 29], [0, 0, 0, 1], [0, 1]], ![[125, 18, 90, 12, 111], [13, 75, 77, 41, 74], [55, 96, 87, 7, 99], [51, 0, 66, 124, 37], [78, 70, 60, 28, 43], [124, 8, 123, 43, 2], [43, 108, 29, 67, 117]], ![[46, 108, 21, 119, 21], [93, 126, 106, 0, 16], [121, 55, 3, 33, 100], [15, 55, 0, 87, 4], [61, 104, 69, 2, 90], [33, 42, 82, 98, 116], [125, 18, 90, 12, 111]], ![[15, 19, 114, 56, 5], [68, 3, 66, 99, 46], [107, 61, 6, 114, 16], [10, 62, 66, 46, 73], [27, 69, 17, 95, 72], [65, 111, 90, 22, 63], [46, 108, 21, 119, 21]], ![[0, 1], [31, 56, 38, 7, 77], [100, 57, 20, 34, 30], [22, 47, 117, 126, 94], [31, 87, 96, 112, 20], [53, 93, 86, 90, 73], [15, 19, 114, 56, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 111, 27, 115], [], [], []]
 b := ![[], [99, 16, 97, 18, 75], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [33, 92, 101, 23, 25, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-149661057552746371, -166476428087476902, -59086421070100330, -7427144791535420, 65415155475553626]
  a := ![-61, -8, -30, -43, 245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1178433524037373, -1310838016436826, -465247410000790, -58481455051460, 515079964374438]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [130, 65, 118, 126, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 20, 22, 128, 128], [66, 60, 105, 93, 46], [57, 35, 77, 10, 15], [33, 15, 58, 31, 73], [0, 1]]
 g := ![![[104, 123, 92, 34, 9], [32, 55, 15, 59, 43], [127, 42, 14, 43], [75, 78, 109, 125], [116, 9, 129, 1], [], []], ![[70, 60, 17, 78, 13, 7, 17, 82], [17, 76, 112, 7, 115, 43, 52, 120], [1, 6, 81, 27], [21, 74, 38, 35], [110, 116, 108, 33], [52, 71, 120, 41], [21, 53, 0, 9]], ![[7, 96, 58, 68, 74, 20, 47, 112], [95, 11, 9, 74, 31, 4, 56, 60], [45, 7, 16, 15], [84, 90, 73, 65], [71, 119, 96, 38], [51, 86, 49, 1], [29, 67, 1, 20]], ![[79, 75, 118, 14, 68, 30, 50, 35], [105, 130, 19, 110, 4, 50, 58, 114], [37, 20, 87, 27], [70, 78, 2, 5], [52, 28, 111, 46], [15, 31, 50, 99], [108, 36, 112, 94]], ![[40, 95, 104, 16, 80, 106, 11, 31], [24, 13, 91, 101, 35, 75, 51, 19], [100, 109, 4, 80], [113, 13, 103, 15], [112, 8, 104, 60], [55, 59, 53, 38], [127, 130, 25, 89]]]
 h' := ![![[104, 20, 22, 128, 128], [32, 72, 77, 96, 3], [130, 27, 34, 75, 49], [38, 5, 121, 124, 49], [116, 67, 4, 42, 115], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[66, 60, 105, 93, 46], [23, 77, 21, 4, 45], [78, 42, 73, 90, 22], [83, 74, 30, 23, 114], [113, 104, 40, 36, 67], [38, 56, 21, 43, 66], [95, 97, 101, 11, 33], [104, 20, 22, 128, 128]], ![[57, 35, 77, 10, 15], [121, 89, 7, 4, 21], [107, 126, 1, 30, 20], [18, 70, 60, 31, 43], [117, 49, 66, 40, 14], [96, 38, 51, 57, 13], [62, 76, 121, 40, 130], [66, 60, 105, 93, 46]], ![[33, 15, 58, 31, 73], [11, 116, 56, 92, 35], [117, 73, 68, 93, 86], [39, 8, 127, 8, 17], [10, 93, 70, 80, 23], [58, 76, 67, 115, 96], [82, 19, 9, 90, 112], [57, 35, 77, 10, 15]], ![[0, 1], [87, 39, 101, 66, 27], [120, 125, 86, 105, 85], [46, 105, 55, 76, 39], [8, 80, 82, 64, 43], [114, 92, 123, 47, 86], [37, 70, 30, 121, 118], [33, 15, 58, 31, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 86, 5, 114], [], [], []]
 b := ![[], [75, 58, 81, 127, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [130, 65, 118, 126, 2, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2408600828136971, -912183584459960, 1075596726719930, 875493323147037, -1635493234221453]
  a := ![29, 11, 15, 32, -117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18386265863641, -6963233469160, 8210662036030, 6683155138527, -12484681177263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 38579489651 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2910, -84, 394, 75, -269]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-2910, -84, 394, 75, -269]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![103, 38, 24, 15, 1]] where
  M :=![![![-2910, -84, 394, 75, -269], ![3003, -439, -234, 25, 93], ![-1191, 2000, -489, -357, 579], ![-4440, -2758, 1474, 613, -1320], ![-619, 168, 34, -13, -10]]]
  hmulB := by decide  
  f := ![![![-20, -18, -4, 1, 7]], ![![-87, -81, -20, 3, 33]], ![![-405, -374, -87, 17, 135]], ![![-792, -754, -194, 21, 288]], ![![-201, -188, -46, 7, 71]]]
  g := ![![![181, 74, 50, 30, -269], ![-48, -29, -18, -10, 93], ![-444, -146, -105, -66, 579], ![960, 346, 242, 149, -1320], ![3, 4, 2, 1, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [128, 81, 106, 21, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 75, 82, 126], [28, 110, 87, 12], [41, 88, 105, 136], [0, 1]]
 g := ![![[127, 82, 68, 129], [136, 47, 14], [28, 69, 19], [83, 19, 114, 74], [107, 123, 30], [1], []], ![[9, 43, 134, 125, 78, 25], [122, 65, 122], [48, 41, 4], [19, 15, 92, 26, 103, 14], [37, 125, 61], [70, 84, 18], [60, 39, 121]], ![[111, 20, 88, 34, 103, 43], [119, 18, 93], [46, 119, 2], [29, 17, 40, 0, 23, 53], [64, 84, 11], [93, 28, 56], [79, 23, 7]], ![[102, 6, 63, 107, 61, 18], [90, 50, 118], [101, 29, 76], [2, 27, 52, 128, 113, 100], [87, 4, 88], [82, 4, 88], [113, 43, 1]]]
 h' := ![![[47, 75, 82, 126], [50, 56, 116, 35], [123, 16, 29, 98], [62, 125, 112, 29], [85, 24, 58, 38], [9, 56, 31, 116], [0, 0, 1], [0, 1]], ![[28, 110, 87, 12], [101, 123, 75, 103], [28, 41, 10, 56], [125, 80, 3, 135], [50, 79, 1, 91], [26, 135, 83, 91], [9, 75, 108, 44], [47, 75, 82, 126]], ![[41, 88, 105, 136], [97, 42, 83, 120], [81, 41, 49, 97], [107, 19, 49, 31], [101, 125, 81, 104], [22, 63, 103, 82], [125, 105, 85, 78], [28, 110, 87, 12]], ![[0, 1], [136, 53, 0, 16], [55, 39, 49, 23], [70, 50, 110, 79], [24, 46, 134, 41], [36, 20, 57, 122], [95, 94, 80, 15], [41, 88, 105, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [30, 5, 97], []]
 b := ![[], [], [132, 130, 34, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [128, 81, 106, 21, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1964266918574, 1092343406672, -486816200696, -522238127494, 848266667016]
  a := ![-18, -16, -8, -38, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-623410217402, -227312335328, -152154862840, -96687869582, 848266667016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, -18, -4, 1, 7]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-20, -18, -4, 1, 7]] 
 ![![137, 0, 0, 0, 0], ![91, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![127, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-20, -18, -4, 1, 7], ![-87, -81, -20, 3, 33], ![-405, -374, -87, 17, 135], ![-792, -754, -194, 21, 288], ![-571, -538, -132, 19, 192]]]
  hmulB := by decide  
  f := ![![![-2910, -84, 394, 75, -269]], ![![-1911, -59, 260, 50, -178]], ![![-1623, -32, 215, 39, -145]], ![![-2730, -98, 376, 74, -259]], ![![-47, 0, 6, 1, -4]]]
  g := ![![![13, -18, -4, 1, 7], ![61, -81, -20, 3, 33], ![276, -374, -87, 17, 135], ![579, -754, -194, 21, 288], ![406, -538, -132, 19, 192]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-2910, -84, 394, 75, -269]] ![![-20, -18, -4, 1, 7]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163, -193, -65, -10, 26]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-163, -193, -65, -10, 26]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![106, 30, 67, 21, 1]] where
  M :=![![![-163, -193, -65, -10, 26], ![-282, -426, -173, -48, -42], ![648, -71, -330, -286, -702], ![4782, 3323, 337, -579, -2748], ![4132, 3042, 372, -456, -2067]]]
  hmulB := by decide  
  f := ![![![273, 33, -45, -12, 34]], ![![-372, -32, 57, 14, -42]], ![![462, 7, -60, -12, 42]], ![![-48, 55, -13, -7, 12]], ![![344, 30, -53, -13, 39]]]
  g := ![![![-21, -7, -13, -4, 26], ![30, 6, 19, 6, -42], ![540, 151, 336, 104, -702], ![2130, 617, 1327, 411, -2748], ![1606, 468, 999, 309, -2067]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [85, 106, 109, 124, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 29, 124, 23], [125, 110, 42, 5], [11, 138, 112, 111], [0, 1]]
 g := ![![[93, 73, 87, 28], [125, 78, 64, 42], [102, 94, 100], [113, 98, 118, 129], [68, 105, 86], [1], []], ![[133, 22, 17, 4, 63, 27], [100, 27, 38, 39, 33, 109], [131, 5, 113], [84, 12, 62, 97, 112, 72], [44, 78, 44], [26, 28, 96], [31, 17, 112]], ![[15, 90, 60, 67, 68, 13], [5, 88, 128, 75, 22, 34], [133, 111, 9], [9, 23, 52, 109, 94, 83], [82, 26, 46], [77, 111, 122], [110, 100, 25]], ![[12, 129, 136, 4, 66, 119], [18, 15, 66, 62, 122, 74], [23, 54, 89], [135, 68, 98, 111, 132, 18], [113, 69, 41], [98, 108, 67], [12, 67, 89]]]
 h' := ![![[18, 29, 124, 23], [78, 22, 52, 81], [5, 28, 71, 43], [125, 92, 112, 129], [55, 80, 22, 44], [54, 33, 30, 15], [0, 0, 1], [0, 1]], ![[125, 110, 42, 5], [94, 99, 113, 33], [103, 114, 11, 67], [37, 24, 95, 35], [104, 31, 122, 92], [77, 60, 110, 34], [52, 66, 56, 42], [18, 29, 124, 23]], ![[11, 138, 112, 111], [117, 52, 115, 15], [1, 133, 35, 102], [66, 114, 135, 3], [126, 118, 98, 10], [110, 88, 136, 18], [20, 112, 109, 119], [125, 110, 42, 5]], ![[0, 1], [37, 105, 137, 10], [38, 3, 22, 66], [66, 48, 75, 111], [41, 49, 36, 132], [65, 97, 2, 72], [74, 100, 112, 117], [11, 138, 112, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [74, 106, 130], []]
 b := ![[], [], [62, 98, 59, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [85, 106, 109, 124, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-370030673261, -350425490878, -87456650238, 11360159130, 126535482028]
  a := ![-3, 8, -1, 11, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-99156775311, -29830862962, -61621107526, -19035143622, 126535482028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-273, -33, 45, 12, -34]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-273, -33, 45, 12, -34]] 
 ![![139, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![95, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-273, -33, 45, 12, -34], ![372, 32, -57, -14, 42], ![-462, -7, 60, 12, -42], ![48, -55, 13, 7, -12], ![-92, -8, 14, 4, -11]]]
  hmulB := by decide  
  f := ![![![163, 193, 65, 10, -26]], ![![29, 35, 12, 2, -4]], ![![27, 38, 15, 4, 0]], ![![77, 108, 42, 11, 2]], ![![-18, -8, 2, 4, 13]]]
  g := ![![![-11, -33, 45, 12, -34], ![15, 32, -57, -14, 42], ![-19, -7, 60, 12, -42], ![3, -55, 13, 7, -12], ![-4, -8, 14, 4, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-163, -193, -65, -10, 26]] ![![-273, -33, 45, 12, -34]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-269, -72, 56, 22, -50]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-269, -72, 56, 22, -50]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![108, 144, 1, 0, 0], ![121, 42, 0, 1, 0], ![117, 62, 0, 0, 1]] where
  M :=![![![-269, -72, 56, 22, -50], ![534, 165, -116, -54, 114], ![-1206, -440, 273, 158, -306], ![1332, 596, -320, -243, 432], ![-262, -112, 60, 46, -81]]]
  hmulB := by decide  
  f := ![![![243, 240, 64, -6, -86]], ![![1050, 1001, 252, -26, -330]], ![![1218, 1168, 297, -30, -390]], ![![543, 526, 136, -13, -178]], ![![661, 638, 164, -16, -215]]]
  g := ![![![-21, -40, 56, 22, -50], ![42, 81, -116, -54, 114], ![-94, -184, 273, 158, -306], ![99, 202, -320, -243, 432], ![-19, -38, 60, 46, -81]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [114, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 148], [0, 1]]
 g := ![![[107, 17], [73], [136, 26], [114], [59, 20], [102], [1]], ![[0, 132], [73], [60, 123], [114], [12, 129], [102], [1]]]
 h' := ![![[20, 148], [86, 100], [141, 85], [110, 131], [128, 76], [27, 13], [35, 20], [0, 1]], ![[0, 1], [0, 49], [53, 64], [48, 18], [9, 73], [138, 136], [137, 129], [20, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [138, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [114, 129, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5131, 1394, -3278, -3713, 7647]
  a := ![-1, -4, 0, -7, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-579, 1042, -3278, -3713, 7647]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1293, 212, -242, -70, 194]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![1293, 212, -242, -70, 194]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![37, 15, 1, 0, 0], ![95, 130, 0, 1, 0], ![51, 79, 0, 0, 1]] where
  M :=![![![1293, 212, -242, -70, 194], ![-2118, -431, 352, 114, -258], ![2754, 184, -659, -154, 594], ![-2274, -1036, 70, 109, 96], ![-86, -468, -228, -6, 283]]]
  hmulB := by decide  
  f := ![![![1589, 748, -394, -290, 518]], ![![-5346, -2659, 1328, 1118, -1926]], ![![-11, -13, 3, 10, -14]], ![![-3895, -1974, 968, 851, -1450]], ![![-2245, -1129, 558, 482, -825]]]
  g := ![![![47, -16, -242, -70, 194], ![-86, -1, 352, 114, -258], ![77, -113, -659, -154, 594], ![-135, -160, 70, 109, 96], ![-37, -125, -228, -6, 283]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [128, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 148], [0, 1]]
 g := ![![[60, 68], [33], [17, 127], [7], [105, 19], [5], [1]], ![[65, 81], [33], [11, 22], [7], [56, 130], [5], [1]]]
 h' := ![![[68, 148], [2, 51], [59, 114], [4, 96], [119, 56], [99, 67], [21, 68], [0, 1]], ![[0, 1], [43, 98], [63, 35], [125, 53], [53, 93], [36, 82], [26, 81], [68, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [128, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [128, 81, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-77497, -121996, -89340, -34921, 171505]
  a := ![-19, -6, -10, -19, 77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14773, -52289, -89340, -34921, 171505]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -4, 2, 0, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-11, -4, 2, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![139, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-11, -4, 2, 0, 0], ![0, -9, -4, 4, 0], ![-12, -8, -17, -20, 48], ![-258, -192, 18, 59, -48], ![-36, -44, -24, -8, 43]]]
  hmulB := by decide  
  f := ![![![86825, 15084, -15790, -4696, 12384]], ![![80095, 13915, -14566, -4332, 11424]], ![![29953, 5204, -5447, -1620, 4272]], ![![58223, 10116, -10588, -3149, 8304]], ![![24702, 4292, -4492, -1336, 3523]]]
  g := ![![![3, -4, 2, 0, 0], ![7, -9, -4, 4, 0], ![13, -8, -17, -20, 48], ![145, -192, 18, 59, -48], ![42, -44, -24, -8, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-269, -72, 56, 22, -50]] ![![1293, 212, -242, -70, 194]]
  ![![-86825, -15084, 15790, 4696, -12384]] where
 M := ![![![-86825, -15084, 15790, 4696, -12384]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-86825, -15084, 15790, 4696, -12384]] ![![-11, -4, 2, 0, 0]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80, -12, 26, -3, -11]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-80, -12, 26, -3, -11]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![103, 15, 74, 1, 0], ![89, 148, 101, 0, 1]] where
  M :=![![![-80, -12, 26, -3, -11], ![141, 37, -6, 39, -69], ![711, 648, -41, -267, 261], ![-1236, -594, 594, 601, -1176], ![827, 640, -2, -139, 48]]]
  hmulB := by decide  
  f := ![![![12774, 2218, -2324, -691, 1823]], ![![-19803, -3443, 3600, 1071, -2823]], ![![30663, 5310, -5585, -1659, 4383]], ![![21681, 3757, -3948, -1173, 3098]], ![![8662, 1490, -1583, -469, 1244]]]
  g := ![![![8, 11, 9, -3, -11], ![15, 64, 27, 39, -69], ![33, -225, -44, -267, 261], ![275, 1089, 496, 601, -1176], ![72, -29, 36, -139, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [130, 36, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 150, 82], [59, 0, 69], [0, 1]]
 g := ![![[20, 138, 42], [13, 47, 94], [120, 71, 125], [8, 128], [43, 130, 88], [26, 1], []], ![[130, 62, 116, 56], [31, 134, 15, 133], [111, 7, 115, 133], [46, 95], [94, 72, 91, 142], [], [104, 80]], ![[75, 21, 5, 38], [80, 6, 111, 1], [9, 79, 107, 72], [43, 85], [31, 94, 64, 88], [107, 1], [117, 80]]]
 h' := ![![[118, 150, 82], [122, 10, 58], [104, 112, 83], [26, 39, 27], [148, 16, 85], [93, 142, 36], [0, 0, 1], [0, 1]], ![[59, 0, 69], [121, 74, 65], [42, 3, 124], [134, 73, 27], [136, 29, 104], [136, 108, 17], [102, 116], [118, 150, 82]], ![[0, 1], [81, 67, 28], [58, 36, 95], [26, 39, 97], [123, 106, 113], [118, 52, 98], [49, 35, 150], [59, 0, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 128], []]
 b := ![[], [81, 63, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [130, 36, 125, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65360630, -60191841, -14278929, 2638830, 23705988]
  a := ![-5, 2, -3, 1, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16205252, -23895765, -17244087, 2638830, 23705988]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1422, 562, -360, -139, 313]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![1422, 562, -360, -139, 313]] 
 ![![151, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![141, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![146, 0, 0, 0, 1]] where
  M :=![![![1422, 562, -360, -139, 313], ![-3339, -1303, 840, 323, -729], ![7779, 3010, -1949, -747, 1689], ![-7344, -2816, 1832, 699, -1584], ![947, 368, -238, -91, 206]]]
  hmulB := by decide  
  f := ![![![1196, 1196, 326, -15, -373]], ![![323, 323, 88, -4, -100]], ![![1221, 1224, 335, -14, -378]], ![![884, 892, 246, -8, -265]], ![![1259, 1266, 348, -13, -386]]]
  g := ![![![-11, 562, -360, -139, 313], ![23, -1303, 840, 323, -729], ![-49, 3010, -1949, -747, 1689], ![41, -2816, 1832, 699, -1584], ![-6, 368, -238, -91, 206]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-485, -186, 120, 46, -104]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-485, -186, 120, 46, -104]] 
 ![![151, 0, 0, 0, 0], ![117, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![146, 0, 0, 1, 0], ![116, 0, 0, 0, 1]] where
  M :=![![![-485, -186, 120, 46, -104], ![1110, 421, -278, -106, 240], ![-2562, -982, 633, 242, -552], ![2394, 912, -594, -229, 504], ![-304, -114, 78, 28, -75]]]
  hmulB := by decide  
  f := ![![![-2523, -1542, 648, 746, -1192]], ![![-1875, -1149, 482, 556, -888]], ![![-1230, -734, 313, 354, -568]], ![![-1680, -1068, 438, 519, -824]], ![![-2084, -1266, 534, 612, -979]]]
  g := ![![![135, -186, 120, 46, -104], ![-305, 421, -278, -106, 240], ![716, -982, 633, 242, -552], ![-652, 912, -594, -229, 504], ![90, -114, 78, 28, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-80, -12, 26, -3, -11]] ![![1422, 562, -360, -139, 313]]
  ![![140177, 53336, -34832, -13274, 30108]] where
 M := ![![![140177, 53336, -34832, -13274, 30108]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![140177, 53336, -34832, -13274, 30108]] ![![-485, -186, 120, 46, -104]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![39525911, 15048358, -9821644, -3752048, 8501300]]]
 hmul := by decide  
 g := ![![![![261761, 99658, -65044, -24848, 56300]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB539I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB539I3 : PrimesBelowBoundCertificateInterval O 103 151 539 where
  m := 9
  g := ![3, 2, 2, 1, 1, 2, 2, 3, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB539I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
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
    · exact ![141158161, 109]
    · exact ![163047361, 113]
    · exact ![33038369407]
    · exact ![38579489651]
    · exact ![352275361, 137]
    · exact ![373301041, 139]
    · exact ![22201, 22201, 149]
    · exact ![3442951, 151, 151]
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
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I107N1, I107N2, I109N1, I113N1, I137N1, I139N1, I149N2, I151N1, I151N2]
  Il := ![[I107N1, I107N2], [I109N1], [I113N1], [], [], [I137N1], [I139N1], [I149N2], [I151N1, I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
