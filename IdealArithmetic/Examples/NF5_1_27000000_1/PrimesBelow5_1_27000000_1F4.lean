
import IdealArithmetic.Examples.NF5_1_27000000_1.RI5_1_27000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, 3, 19, -24, -5]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-57, 3, 19, -24, -5]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![36, 134, 39, 1, 0], ![27, 47, 123, 0, 1]] where
  M :=![![![-57, 3, 19, -24, -5], ![40, 13, 44, 72, -48], ![172, -30, -129, 20, 96], ![-404, -20, 24, -271, 44], ![-166, 44, 222, 72, -201]]]
  hmulB := by decide  
  f := ![![![149, -97, 37, -28, 31]], ![![-248, 145, -76, 40, -56]], ![![348, -202, 87, -60, 68]], ![![-92, 52, -35, 13, -24]], ![![225, -132, 52, -40, 42]]]
  g := ![![![6, 22, 10, -24, -5], ![-8, -47, 20, 72, -48], ![-20, -46, -81, 20, 96], ![52, 218, 33, -271, 44], ![17, -1, 141, 72, -201]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [141, 22, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 150, 32], [100, 6, 125], [0, 1]]
 g := ![![[131, 121, 51], [50, 47], [63, 16, 1], [60, 17, 113], [100, 18, 10], [155, 1], []], ![[90, 102, 6, 62], [121, 33], [111, 11, 109, 83], [105, 35, 40, 134], [139, 75, 136, 96], [10, 36], [16, 82]], ![[12, 72], [128, 71], [65, 72, 48, 66], [78, 89, 81, 128], [140, 76, 33, 7], [50, 49], [80, 82]]]
 h' := ![![[55, 150, 32], [132, 20, 88], [66, 136, 19], [18, 9, 1], [30, 54, 120], [125, 60, 139], [0, 0, 1], [0, 1]], ![[100, 6, 125], [138, 95, 69], [20, 146, 70], [26, 127, 137], [138, 128, 93], [102, 85, 85], [141, 33, 6], [55, 150, 32]], ![[0, 1], [20, 42], [22, 32, 68], [109, 21, 19], [38, 132, 101], [120, 12, 90], [133, 124, 150], [100, 6, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 35], []]
 b := ![[], [130, 17, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [141, 22, 2, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2585673, -180276, -1000284, 1062984, 461712]
  a := ![0, 8, 5, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-306675, -1046628, -632148, 1062984, 461712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -13, -6, -3, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-9, -13, -6, -3, 0]] 
 ![![157, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![132, 0, 0, 0, 1]] where
  M :=![![![-9, -13, -6, -3, 0], ![0, -22, -20, -9, -6], ![24, -1, -9, -5, -6], ![24, 23, 8, 4, -2], ![44, 12, -8, -4, -9]]]
  hmulB := by decide  
  f := ![![![99, -23, -46, 9, 44]], ![![11, -3, -6, 0, 6]], ![![53, -12, -23, 6, 22]], ![![44, -9, -20, 6, 18]], ![![80, -20, -40, 4, 39]]]
  g := ![![![6, -13, -6, -3, 0], ![22, -22, -20, -9, -6], ![12, -1, -9, -5, -6], ![-7, 23, 8, 4, -2], ![12, 12, -8, -4, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63, 38, -17, 11, -13]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-63, 38, -17, 11, -13]] 
 ![![157, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![114, 0, 1, 0, 0], ![140, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-63, 38, -17, 11, -13], ![104, -64, 28, -19, 22], ![-140, 85, -37, 25, -30], ![68, -39, 16, -10, 14], ![-58, 34, -16, 8, -11]]]
  hmulB := by decide  
  f := ![![![-173, -44, 41, 27, 39]], ![![-67, -18, 15, 10, 15]], ![![-126, -33, 29, 19, 28]], ![![-152, -39, 36, 24, 34]], ![![-40, -12, 8, 6, 9]]]
  g := ![![![-9, 38, -17, 11, -13], ![16, -64, 28, -19, 22], ![-21, 85, -37, 25, -30], ![9, -39, 16, -10, 14], ![-6, 34, -16, 8, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-57, 3, 19, -24, -5]] ![![-9, -13, -6, -3, 0]]
  ![![173, 44, -41, -27, -39]] where
 M := ![![![173, 44, -41, -27, -39]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![173, 44, -41, -27, -39]] ![![-63, 38, -17, 11, -13]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29856471, 18066168, -7963717, 5195125, -6227121]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-29856471, 18066168, -7963717, 5195125, -6227121]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![18, 105, 11, 36, 1]] where
  M :=![![![-29856471, 18066168, -7963717, 5195125, -6227121], ![49816968, -30144270, 13287844, -8668317, 10390250], ![-66469484, 40220723, -17729625, 11565911, -13863442], ![30545284, -18482969, 8147448, -5314980, 6370786], ![-26863018, 16254830, -7165260, 4674256, -5602779]]]
  hmulB := by decide  
  f := ![![![37, 10, -13, 3, 13]], ![![-104, 28, 40, -55, 6]], ![![28, 23, 69, 89, -58]], ![![284, -43, -144, 110, 86]], ![![0, 11, -3, -6, 21]]]
  g := ![![![504489, 4122171, 371378, 1407187, -6227121], ![-841764, -6878040, -619662, -2347959, 10390250], ![1123144, 9177191, 826799, 3132821, -13863442], ![-516128, -4217273, -379946, -1439652, 6370786], ![453908, 3708875, 334143, 1266100, -5602779]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [102, 145, 8, 105, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 154, 27, 44], [0, 93, 42, 86], [144, 78, 94, 33], [0, 1]]
 g := ![![[36, 143, 51, 33], [160, 33, 147, 87], [10, 81, 61], [96, 138, 88], [79, 157, 88], [58, 1], []], ![[128, 107, 119, 54, 129, 63], [101, 24, 13, 42, 110, 147], [139, 58, 24], [82, 140, 83], [62, 85, 53], [9, 74, 75, 131, 2, 108], [46, 75, 143]], ![[152, 39, 145, 155, 122, 128], [2, 162, 5, 142, 60, 112], [67, 55, 119], [48, 154, 35], [162, 80, 91], [109, 39, 94, 126, 24, 76], [63, 4, 61]], ![[59, 6, 45, 99, 10, 60], [86, 76, 158, 18, 42, 41], [55, 27, 57], [111, 145, 121], [23, 70, 143], [43, 107, 63, 150, 90, 156], [118, 91, 111]]]
 h' := ![![[77, 154, 27, 44], [143, 12, 79, 14], [160, 63, 10, 24], [107, 83, 40, 77], [114, 111, 3, 96], [115, 127, 43, 96], [0, 0, 1], [0, 1]], ![[0, 93, 42, 86], [139, 139, 87, 100], [18, 99, 28, 123], [34, 102, 57, 137], [133, 62, 21, 75], [153, 43, 101, 78], [96, 105, 89, 11], [77, 154, 27, 44]], ![[144, 78, 94, 33], [122, 90, 29, 114], [93, 81, 37, 80], [154, 104, 158, 49], [117, 121, 118, 144], [129, 5, 68, 108], [94, 74, 39, 144], [0, 93, 42, 86]], ![[0, 1], [19, 85, 131, 98], [36, 83, 88, 99], [58, 37, 71, 63], [40, 32, 21, 11], [58, 151, 114, 44], [61, 147, 34, 8], [144, 78, 94, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 3, 112], []]
 b := ![[], [], [101, 106, 15, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [102, 145, 8, 105, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5164627805, 824782325, 1899587201, 5421432049, -2751255392]
  a := ![3, -5, -3, -1, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![335504447, 1777341095, 197321451, 640899547, -2751255392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 10, -13, 3, 13]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![37, 10, -13, 3, 13]] 
 ![![163, 0, 0, 0, 0], ![91, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![37, 10, -13, 3, 13], ![-104, 28, 40, -55, 6], ![28, 23, 69, 89, -58], ![284, -43, -144, 110, 86], ![-278, -32, -30, -196, 101]]]
  hmulB := by decide  
  f := ![![![-29856471, 18066168, -7963717, 5195125, -6227121]], ![![-16362711, 9901086, -4364481, 2847166, -3412747]], ![![-9932552, 6010193, -2649343, 1728297, -2071618]], ![![-20876987, 12632677, -5568589, 3632665, -4354283]], ![![-4011343, 2427266, -1069959, 697987, -836640]]]
  g := ![![![-5, 10, -13, 3, 13], ![9, 28, 40, -55, 6], ![-90, 23, 69, 89, -58], ![-17, -43, -144, 110, 86], ![151, -32, -30, -196, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-29856471, 18066168, -7963717, 5195125, -6227121]] ![![37, 10, -13, 3, 13]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![751, -146, -688, -36, 556]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![751, -146, -688, -36, 556]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![64, 6, 1, 0, 0], ![117, 83, 0, 1, 0], ![71, 66, 0, 0, 1]] where
  M :=![![![751, -146, -688, -36, 556], ![-4448, -11, 892, -2452, -72], ![2512, 674, 1923, 3416, -2416], ![11888, -856, -5604, 3857, 3452], ![-9800, -908, -1248, -8092, 3095]]]
  hmulB := by decide  
  f := ![![![-34455, 21018, -9128, 6044, -7188]], ![![57504, -34653, 15572, -9924, 12088]], ![![-11600, 7088, -3061, 2040, -2416]], ![![4651, -2627, 1400, -735, 1016]], ![![7889, -4648, 2224, -1320, 1683]]]
  g := ![![![57, -178, -688, -36, 556], ![1380, 1215, 892, -2452, -72], ![-2088, -808, 1923, 3416, -2416], ![-1951, -3085, -5604, 3857, 3452], ![4773, 2838, -1248, -8092, 3095]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [127, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 166], [0, 1]]
 g := ![![[115, 96], [20, 147], [115, 61], [12], [44], [166, 98], [1]], ![[0, 71], [37, 20], [155, 106], [12], [44], [66, 69], [1]]]
 h' := ![![[91, 166], [132, 116], [91, 67], [45, 140], [20, 43], [127, 85], [40, 91], [0, 1]], ![[0, 1], [0, 51], [9, 100], [93, 27], [92, 124], [13, 82], [138, 76], [91, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [1, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [127, 76, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1394, -247, -409, -1728, -468]
  a := ![1, 3, 2, -1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1558, 1057, -409, -1728, -468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![591, 781, 2715, 2698, -2859]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![591, 781, 2715, 2698, -2859]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![90, 56, 1, 0, 0], ![137, 27, 0, 1, 0], ![150, 58, 0, 0, 1]] where
  M :=![![![591, 781, 2715, 2698, -2859], ![22872, -1309, -9552, 8450, 5396], ![-33020, -1790, 413, -23398, 5752], ![-34444, 6854, 32136, 2135, -26096], ![77014, 466, -14448, 43284, 235]]]
  hmulB := by decide  
  f := ![![![7415, -4721, -7329, -3434, -3333]], ![![26664, 2233, -9240, -4558, -6868]], ![![13022, -1716, -7021, -3366, -4106]], ![![10341, -3436, -7419, -3513, -3811]], ![![16004, -3320, -9708, -4628, -5369]]]
  g := ![![![-1105, -349, 2715, 2698, -2859], ![-6494, -45, -9552, 8450, 5396], ![13608, 1636, 413, -23398, 5752], ![4163, -2017, 32136, 2135, -26096], ![-27472, -2232, -14448, 43284, 235]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [148, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 166], [0, 1]]
 g := ![![[136, 48], [125, 12], [56, 62], [31], [76], [51, 62], [1]], ![[87, 119], [71, 155], [111, 105], [31], [76], [106, 105], [1]]]
 h' := ![![[79, 166], [37, 86], [62, 124], [37, 79], [28, 71], [134, 57], [19, 79], [0, 1]], ![[0, 1], [151, 81], [5, 43], [99, 88], [126, 96], [128, 110], [81, 88], [79, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [147, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [148, 88, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26281, -6637, -4634, -22780, 9698]
  a := ![1, -11, -7, -1, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12317, 1829, -4634, -22780, 9698]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, -44, -7, -3, 9]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-69, -44, -7, -3, 9]] 
 ![![167, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![134, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-69, -44, -7, -3, 9], ![-72, -114, -64, -29, -6], ![60, -39, -59, -29, -26], ![140, 67, -4, -4, -26], ![162, -14, -80, -36, -49]]]
  hmulB := by decide  
  f := ![![![-50005, 30254, -13339, 8695, -10425]], ![![-12975, 7850, -3461, 2256, -2705]], ![![-40790, 24679, -10881, 7093, -8504]], ![![-15264, 9235, -4072, 2654, -3182]], ![![-11349, 6866, -3027, 1973, -2366]]]
  g := ![![![16, -44, -7, -3, 9], ![92, -114, -64, -29, -6], ![73, -39, -59, -29, -26], ![-7, 67, -4, -4, -26], ![91, -14, -80, -36, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![751, -146, -688, -36, 556]] ![![591, 781, 2715, 2698, -2859]]
  ![![63882057, 2021517, -6040571, 40879366, -5822185]] where
 M := ![![![63882057, 2021517, -6040571, 40879366, -5822185]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![63882057, 2021517, -6040571, 40879366, -5822185]] ![![-69, -44, -7, -3, 9]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-135928147, 14746935, 82099538, -29012409, -57712194]]]
 hmul := by decide  
 g := ![![![![-813941, 88305, 491614, -173727, -345582]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49480511, 29940684, -13198101, 8609773, -10320077]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-49480511, 29940684, -13198101, 8609773, -10320077]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![80, 36, 8, 1, 0], ![92, 137, 148, 0, 1]] where
  M :=![![![-49480511, 29940684, -13198101, 8609773, -10320077], ![82560616, -49957474, 22021668, -14365821, 17219546], ![-110158492, 66656963, -29382941, 19167943, -22975594], ![50622068, -30631441, 13502592, -8808408, 10558170], ![-44519522, 26938786, -11874840, 7746544, -9285371]]]
  hmulB := by decide  
  f := ![![![-109, -102, -27, -35, -41]], ![![328, -168, -216, 63, -70]], ![![116, -7, -193, -209, 98]], ![![20, -81, -64, -14, -30]], ![![306, -192, -350, -145, 5]]]
  g := ![![![1220721, 6553985, 8354307, 8609773, -10320077], ![-2036832, -10935640, -13939564, -14365821, 17219546], ![2717692, 14591141, 18599199, 19167943, -22975594], ![-1248884, -6705191, -8547048, -8808408, 10558170], ![1098330, 5896873, 7516692, 7746544, -9285371]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [171, 36, 159, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 80, 21], [155, 92, 152], [0, 1]]
 g := ![![[16, 2, 169], [36, 54], [10, 150, 64], [148, 166, 121], [9, 64], [160, 14, 1], []], ![[75, 16, 170, 117], [50, 29], [115, 54, 119, 49], [70, 68, 93, 9], [41, 172], [14, 119, 140, 73], [19, 95]], ![[55, 12, 49, 52], [123, 89], [72, 154, 16, 25], [67, 23, 47, 133], [23, 132], [115, 24, 31, 21], [61, 95]]]
 h' := ![![[32, 80, 21], [126, 51, 160], [20, 18, 153], [123, 25, 165], [2, 135, 11], [147, 150, 8], [0, 0, 1], [0, 1]], ![[155, 92, 152], [62, 167, 48], [116, 91, 95], [39, 111, 135], [88, 98, 41], [122, 49, 80], [24, 128, 92], [32, 80, 21]], ![[0, 1], [157, 128, 138], [118, 64, 98], [84, 37, 46], [56, 113, 121], [150, 147, 85], [100, 45, 80], [155, 92, 152]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 21], []]
 b := ![[], [4, 93, 172], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [171, 36, 159, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3217437, -640770, -2401298, 208964, 1556124]
  a := ![-1, 13, 9, 2, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-905567, -1279494, -1354794, 208964, 1556124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9817, -5941, 2624, -1707, 2044]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![9817, -5941, 2624, -1707, 2044]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![52, 166, 1, 0, 0], ![18, 147, 0, 1, 0], ![29, 139, 0, 0, 1]] where
  M :=![![![9817, -5941, 2624, -1707, 2044], ![-16352, 9914, -4380, 2867, -3414], ![21832, -13233, 5823, -3833, 4574], ![-10120, 6087, -2636, 1732, -2126], ![8924, -5342, 2354, -1476, 1829]]]
  hmulB := by decide  
  f := ![![![1149, -3119, -3096, -1463, -1064]], ![![8512, -2140, -5440, -2601, -2926]], ![![8556, -2967, -6149, -2935, -3134]], ![![7354, -2103, -4912, -2347, -2588]], ![![7089, -2189, -4870, -2326, -2533]]]
  g := ![![![-897, -2744, 2624, -1707, 2044], ![1496, 4567, -4380, 2867, -3414], ![-1992, -6082, 5823, -3833, 4574], ![910, 2801, -2636, 1732, -2126], ![-809, -2505, 2354, -1476, 1829]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [150, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 172], [0, 1]]
 g := ![![[162, 15], [124], [155, 49], [169, 160], [77], [33, 172], [1]], ![[0, 158], [124], [41, 124], [171, 13], [77], [113, 1], [1]]]
 h' := ![![[93, 172], [37, 154], [105, 132], [81, 7], [32, 81], [67, 115], [23, 93], [0, 1]], ![[0, 1], [0, 19], [98, 41], [40, 166], [126, 92], [36, 58], [22, 80], [93, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [136, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [150, 80, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1930, -728, 524, -1616, 152]
  a := ![0, -10, -6, -10, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26, 744, 524, -1616, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-49480511, 29940684, -13198101, 8609773, -10320077]] ![![9817, -5941, 2624, -1707, 2044]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-1442708452195, 872983667145, -384818421793, 251036054926, -300903571865]]]
 hmul := by decide  
 g := ![![![![-8339355215, 5046148365, -2224383941, 1451075462, -1739327005]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14837, -26, -3234, 7974, 494]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![14837, -26, -3234, 7974, 494]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![80, 110, 95, 1, 0], ![137, 39, 171, 0, 1]] where
  M :=![![![14837, -26, -3234, 7974, 494], ![-3952, -4371, -15012, -15430, 15948], ![-61816, 5948, 34513, -15530, -23404], ![95592, 7038, 5580, 73397, -23504], ![76044, -14196, -67572, -1876, 54189]]]
  hmulB := by decide  
  f := ![![![-19041, -6278, 2934, 1470, 3926]], ![![-31408, -25325, -7644, -3454, 2940]], ![![3944, -16072, -15109, -7130, -4924]], ![![-25520, -26864, -11461, -5277, 900]], ![![-17511, -25775, -13995, -6506, -1121]]]
  g := ![![![-3859, -5008, -4722, 7974, 494], ![-5332, 5983, -7130, -15430, 15948], ![24508, 14676, 30793, -15530, -23404], ![-14280, -39944, -16469, 73397, -23504], ![-40211, -10733, -51149, -1876, 54189]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [38, 98, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 69, 37], [146, 109, 142], [0, 1]]
 g := ![![[89, 77, 20], [48, 154, 45], [46, 107], [58, 36], [121, 154, 12], [98, 165, 1], []], ![[39, 71, 50, 53], [71, 146, 44, 34], [70, 147], [26, 5], [83, 150, 56, 118], [102, 17, 67, 152], [81, 116]], ![[37, 43, 103, 177], [174, 110, 35, 121], [13, 158], [57, 43], [71, 69, 29, 81], [124, 141, 61, 158], [155, 116]]]
 h' := ![![[19, 69, 37], [145, 88, 60], [158, 111, 89], [37, 173, 110], [56, 162, 173], [35, 57, 141], [0, 0, 1], [0, 1]], ![[146, 109, 142], [76, 86, 130], [135, 170, 25], [162, 8, 133], [104, 70, 149], [7, 51, 115], [147, 121, 109], [19, 69, 37]], ![[0, 1], [56, 5, 168], [59, 77, 65], [175, 177, 115], [67, 126, 36], [160, 71, 102], [32, 58, 69], [146, 109, 142]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 68], []]
 b := ![[], [97, 49, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [38, 98, 14, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2413597, -261708, -1248513, 678215, 691733]
  a := ![13, 10, 7, 1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-819056, -568955, -1027739, 678215, 691733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![955, 134, 287, 927, -469]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![955, 134, 287, 927, -469]] 
 ![![179, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![178, 0, 0, 1, 0], ![138, 0, 0, 0, 1]] where
  M :=![![![955, 134, 287, 927, -469], ![3752, -478, -2524, 585, 1854], ![-9292, 29, 2053, -4963, -342], ![-508, 1597, 5912, 4584, -5890], ![17766, -734, -6392, 7424, 3151]]]
  hmulB := by decide  
  f := ![![![-52153, 29744, -12517, 9017, -9767]], ![![-9761, 5520, -2325, 1682, -1809]], ![![-25678, 14651, -6189, 4435, -4824]], ![![-51554, 29405, -12382, 8912, -9660]], ![![-40448, 23064, -9736, 6986, -7589]]]
  g := ![![![-719, 134, 287, 927, -469], ![-684, -478, -2524, 585, 1854], ![4155, 29, 2053, -4963, -342], ![-3173, 1597, 5912, 4584, -5890], ![-6498, -734, -6392, 7424, 3151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![134239, -81228, 35806, -23358, 27998]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![134239, -81228, 35806, -23358, 27998]] 
 ![![179, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![134239, -81228, 35806, -23358, 27998], ![-223984, 135533, -59744, 38974, -46716], ![298856, -180838, 79715, -52002, 62332], ![-137336, 83102, -36632, 23897, -28644], ![120780, -73084, 32216, -21016, 25191]]]
  hmulB := by decide  
  f := ![![![757, 124, -242, -54, -74]], ![![570, 97, -180, -42, -56]], ![![356, 62, -109, -22, -36]], ![![143, 22, -46, -5, -10]], ![![338, 60, -108, -28, -29]]]
  g := ![![![36235, -81228, 35806, -23358, 27998], ![-60460, 135533, -59744, 38974, -46716], ![80670, -180838, 79715, -52002, 62332], ![-37071, 83102, -36632, 23897, -28644], ![32602, -73084, 32216, -21016, 25191]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![14837, -26, -3234, 7974, 494]] ![![955, 134, 287, 927, -469]]
  ![![48847723, 14278682, 41669081, 70009303, -51310995]] where
 M := ![![![48847723, 14278682, 41669081, 70009303, -51310995]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![48847723, 14278682, 41669081, 70009303, -51310995]] ![![134239, -81228, 35806, -23358, 27998]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-11562863, 2350270, 10981829, 872983, -8953043]]]
 hmul := by decide  
 g := ![![![![-64597, 13130, 61351, 4877, -50017]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 167, 598, 553, -618]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![77, 167, 598, 553, -618]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![174, 36, 69, 1, 0], ![27, 116, 105, 0, 1]] where
  M :=![![![77, 167, 598, 553, -618], ![4944, -264, -2008, 1879, 1106], ![-6896, -411, -33, -4993, 1326], ![-7776, 1455, 6912, 198, -5546], ![16344, 150, -2874, 9344, -143]]]
  hmulB := by decide  
  f := ![![![1065, 405, -110, -59, -202]], ![![1616, 1478, 524, 243, -118]], ![![-336, 827, 855, 399, 302]], ![![1206, 996, 327, 145, -100]], ![![991, 1492, 823, 382, 73]]]
  g := ![![![-439, 287, 151, 553, -618], ![-1944, -1084, -1369, 1879, 1106], ![4564, 141, 1134, -4993, 1326], ![594, 3523, 3180, 198, -5546], ![-8871, -1766, -3495, 9344, -143]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [48, 5, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 77, 19], [127, 103, 162], [0, 1]]
 g := ![![[135, 138, 81], [175, 168], [104, 55, 25], [140, 176], [142, 29, 138], [138, 163, 1], []], ![[121, 63, 65, 17], [167, 167], [69, 98, 113, 175], [84, 42], [20, 11, 75, 140], [77, 70, 143, 118], [48, 180]], ![[31, 111, 70, 118], [65, 156], [12, 98, 145, 107], [178, 138], [23, 116, 5, 85], [136, 129, 162, 112], [86, 180]]]
 h' := ![![[36, 77, 19], [91, 149, 9], [76, 136, 63], [20, 40, 176], [62, 150, 151], [73, 174, 92], [0, 0, 1], [0, 1]], ![[127, 103, 162], [3, 92, 138], [112, 128, 23], [165, 31, 64], [45, 134, 122], [119, 68, 112], [78, 103, 103], [36, 77, 19]], ![[0, 1], [142, 121, 34], [179, 98, 95], [119, 110, 122], [86, 78, 89], [81, 120, 158], [55, 78, 77], [127, 103, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 70], []]
 b := ![[], [170, 153, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [48, 5, 18, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-140582, 7361, 55252, -56763, -28296]
  a := ![-1, -5, -3, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![58012, 29465, 38359, -56763, -28296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 2, 1, 1, -1]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![3, 2, 1, 1, -1]] 
 ![![181, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![135, 0, 0, 0, 1]] where
  M :=![![![3, 2, 1, 1, -1], ![8, 4, 0, 3, 2], ![-12, 1, 3, -5, 2], ![-12, -1, 8, 2, -6], ![14, 0, -2, 12, 3]]]
  hmulB := by decide  
  f := ![![![-1799, 1100, -489, 313, -381]], ![![-500, 306, -136, 87, -106]], ![![-718, 439, -195, 125, -152]], ![![-1431, 875, -389, 249, -303]], ![![-1351, 826, -367, 235, -286]]]
  g := ![![![-1, 2, 1, 1, -1], ![-5, 4, 0, 3, 2], ![1, 1, 3, -5, 2], ![0, -1, 8, 2, -6], ![-11, 0, -2, 12, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, -163, 115, -14, 91]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![59, -163, 115, -14, 91]] 
 ![![181, 0, 0, 0, 0], ![173, 1, 0, 0, 0], ![153, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![59, -163, 115, -14, 91], ![-728, 39, -116, 62, -28], ![476, -484, 7, -150, 76], ![60, 130, -200, -25, -136], ![322, -360, -190, -152, -45]]]
  hmulB := by decide  
  f := ![![![20897, -867, -7531, 8722, 3719]], ![![19809, -856, -7263, 8164, 3651]], ![![17361, -675, -6092, 7384, 2923]], ![![9393, -333, -3179, 4093, 1463]], ![![2587, -217, -1331, 746, 864]]]
  g := ![![![54, -163, 115, -14, 91], ![35, 39, -116, 62, -28], ![511, -484, 7, -150, 76], ![71, 130, -200, -25, -136], ![573, -360, -190, -152, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![77, 167, 598, 553, -618]] ![![3, 2, 1, 1, -1]]
  ![![-20897, 867, 7531, -8722, -3719]] where
 M := ![![![-20897, 867, 7531, -8722, -3719]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-20897, 867, 7531, -8722, -3719]] ![![59, -163, 115, -14, 91]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-299, 180, -80, 52, -62]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-299, 180, -80, 52, -62]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![36, 145, 1, 0, 0], ![128, 76, 0, 1, 0], ![38, 151, 0, 0, 1]] where
  M :=![![![-299, 180, -80, 52, -62], ![496, -303, 132, -88, 104], ![-664, 402, -177, 116, -140], ![312, -184, 80, -51, 64], ![-268, 162, -74, 44, -55]]]
  hmulB := by decide  
  f := ![![![-37, -8, 12, 12, 10]], ![![-80, -57, -20, -8, 24]], ![![-68, -45, -13, -4, 20]], ![![-56, -28, 0, 5, 16]], ![![-70, -47, -14, -4, 21]]]
  g := ![![![-9, 90, -80, 52, -62], ![16, -149, 132, -88, 104], ![-20, 201, -177, 116, -140], ![8, -92, 80, -51, 64], ![-6, 83, -74, 44, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [48, 168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 190], [0, 1]]
 g := ![![[99, 4], [7, 8], [174, 117], [12, 108], [98, 75], [27, 147], [1]], ![[0, 187], [0, 183], [0, 74], [13, 83], [104, 116], [161, 44], [1]]]
 h' := ![![[23, 190], [46, 189], [52, 114], [188, 133], [71, 144], [41, 71], [143, 23], [0, 1]], ![[0, 1], [0, 2], [0, 77], [0, 58], [136, 47], [146, 120], [99, 168], [23, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [182, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [48, 168, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13495, -4798, -2315, -12690, 8238]
  a := ![3, -14, -7, -4, 34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7231, 269, -2315, -12690, 8238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1141, 1053, -126, 313, -218]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-1141, 1053, -126, 313, -218]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![48, 131, 1, 0, 0], ![15, 119, 0, 1, 0], ![169, 43, 0, 0, 1]] where
  M :=![![![-1141, 1053, -126, 313, -218], ![1744, -840, 1044, -129, 626], ![-3376, 1523, -607, 547, -442], ![896, -1357, 12, -374, 234], ![-2120, 154, -306, 196, -73]]]
  hmulB := by decide  
  f := ![![![4093, -855, -3966, -377, 3250]], ![![-26000, 26, 5544, -14055, -754]], ![![-16720, -177, 2861, -9628, 228]], ![![-15523, -78, 2970, -8676, -106]], ![![-2541, -777, -2292, -3746, 2795]]]
  g := ![![![194, -54, -126, 313, -218], ![-797, -781, 1044, -129, 626], ![483, 183, -607, 547, -442], ![-176, 165, 12, -374, 234], ![115, 105, -306, 196, -73]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [69, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 190], [0, 1]]
 g := ![![[93, 36], [15, 15], [102, 81], [46, 118], [180, 163], [113, 8], [1]], ![[0, 155], [24, 176], [36, 110], [155, 73], [125, 28], [156, 183], [1]]]
 h' := ![![[77, 190], [111, 6], [29, 145], [73, 9], [186, 140], [34, 113], [122, 77], [0, 1]], ![[0, 1], [0, 185], [116, 46], [2, 182], [79, 51], [140, 78], [130, 114], [77, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [190, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [69, 114, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3118, -1399, -1176, -3226, 2808]
  a := ![1, -7, -5, -1, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1952, 2177, -1176, -3226, 2808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5469, -3292, 1468, -946, 1142]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![5469, -3292, 1468, -946, 1142]] 
 ![![191, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![5469, -3292, 1468, -946, 1142], ![-9136, 5537, -2408, 1598, -1892], ![12136, -7370, 3251, -2114, 2544], ![-5608, 3354, -1508, 965, -1168], ![4868, -3002, 1310, -856, 1033]]]
  hmulB := by decide  
  f := ![![![12131, -604, -4736, 4758, 2526]], ![![1355, -87, -600, 472, 354]], ![![6586, -302, -2477, 2662, 1276]], ![![1255, -30, -372, 591, 142]], ![![548, -90, -442, 24, 345]]]
  g := ![![![-383, -3292, 1468, -946, 1142], ![609, 5537, -2408, 1598, -1892], ![-838, -7370, 3251, -2114, 2544], ![397, 3354, -1508, 965, -1168], ![-334, -3002, 1310, -856, 1033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-299, 180, -80, 52, -62]] ![![-1141, 1053, -126, 313, -218]]
  ![![1103191, -667999, 293750, -192167, 229916]] where
 M := ![![![1103191, -667999, 293750, -192167, 229916]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![1103191, -667999, 293750, -192167, 229916]] ![![5469, -3292, 1468, -946, 1142]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![17898044067, -10830088685, 4773985026, -3114317839, 3732952514]]]
 hmul := by decide  
 g := ![![![![93707037, -56702035, 24994686, -16305329, 19544254]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 7, -13, 2, -7]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-17, 7, -13, 2, -7]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![35, 94, 151, 1, 0], ![40, 81, 45, 0, 1]] where
  M :=![![![-17, 7, -13, 2, -7], ![56, -27, -4, -14, 4], ![-44, 40, -7, 6, -16], ![36, 2, 20, 13, 4], ![14, 30, -8, 8, 3]]]
  hmulB := by decide  
  f := ![![![1, 3, 1, 2, 1]], ![![-8, 1, 4, -2, 4]], ![![-12, 0, 5, 2, -4]], ![![-13, 1, 6, 1, -1]], ![![-6, 1, 3, 0, 1]]]
  g := ![![![1, 2, 0, 2, -7], ![2, 5, 10, -14, 4], ![2, 4, -1, 6, -16], ![-3, -8, -11, 13, 4], ![-2, -5, -7, 8, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [47, 17, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 190, 167], [176, 2, 26], [0, 1]]
 g := ![![[0, 16, 95], [91, 69], [171, 3], [34, 186], [56, 189], [104, 96], [1]], ![[25, 186, 46, 141], [86, 145], [139, 75], [51, 48], [135, 121], [50, 98], [99, 181, 120, 180]], ![[109, 78, 129, 103], [92, 50], [112, 108], [17, 100], [61, 27], [181, 25], [172, 8, 168, 13]]]
 h' := ![![[0, 190, 167], [154, 46, 45], [125, 95, 29], [153, 132, 14], [20, 24, 147], [23, 143, 31], [146, 176, 176], [0, 1]], ![[176, 2, 26], [176, 30, 52], [92, 42, 97], [177, 68, 70], [79, 168, 56], [21, 47, 11], [172, 39, 22], [0, 190, 167]], ![[0, 1], [17, 117, 96], [148, 56, 67], [104, 186, 109], [175, 1, 183], [95, 3, 151], [127, 171, 188], [176, 2, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 192], []]
 b := ![[], [91, 86, 141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [47, 17, 17, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1971, -1468, -5093, -3549, 3724]
  a := ![4, 2, 1, 1, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-118, 158, 1882, -3549, 3724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4721, -2859, 1259, -822, 985]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![4721, -2859, 1259, -822, 985]] 
 ![![193, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![140, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![4721, -2859, 1259, -822, 985], ![-7880, 4765, -2104, 1370, -1644], ![10516, -6362, 2803, -1830, 2192], ![-4828, 2926, -1288, 841, -1008], ![4254, -2570, 1132, -740, 885]]]
  hmulB := by decide  
  f := ![![![751, 73, 109, 642, -239]], ![![543, 50, 69, 456, -163]], ![![-16, 2, 11, -2, -8]], ![![552, 58, 96, 485, -192]], ![![360, 26, 20, 280, -83]]]
  g := ![![![2226, -2859, 1259, -822, 985], ![-3709, 4765, -2104, 1370, -1644], ![4954, -6362, 2803, -1830, 2192], ![-2278, 2926, -1288, 841, -1008], ![2002, -2570, 1132, -740, 885]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, -2, 6, -48, 8]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-73, -2, 6, -48, 8]] 
 ![![193, 0, 0, 0, 0], ![141, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![131, 0, 0, 0, 1]] where
  M :=![![![-73, -2, 6, -48, 8], ![-64, 27, 108, 44, -96], ![416, -22, -167, 160, 92], ![-336, -60, -144, -361, 208], ![-648, 66, 378, -148, -261]]]
  hmulB := by decide  
  f := ![![![311559, -188506, 83070, -54216, 64960]], ![![224923, -136087, 59970, -39140, 46896]], ![![43951, -26592, 11719, -7648, 9164]], ![![154935, -93742, 41310, -26961, 32304]], ![![212925, -128828, 56772, -37052, 44395]]]
  g := ![![![19, -2, 6, -48, 8], ![9, 27, 108, 44, -96], ![-103, -22, -167, 160, 92], ![101, -60, -144, -361, 208], ![151, 66, 378, -148, -261]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-17, 7, -13, 2, -7]] ![![4721, -2859, 1259, -822, 985]]
  ![![-311559, 188506, -83070, 54216, -64960]] where
 M := ![![![-311559, 188506, -83070, 54216, -64960]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-311559, 188506, -83070, 54216, -64960]] ![![-73, -2, 6, -48, 8]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16901, 1444, 8410, 4050, 5118]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-16901, 1444, 8410, 4050, 5118]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![83, 119, 20, 1, 0], ![56, 55, 122, 0, 1]] where
  M :=![![![-16901, 1444, 8410, 4050, 5118], ![-40944, -15147, 5024, 2534, 8100], ![-11928, -20494, -12093, -5610, -1516], ![26536, -9074, -18912, -9039, -9660], ![-964, -31864, -26220, -12328, -7285]]]
  hmulB := by decide  
  f := ![![![-4777, 356, 2294, -1514, -1430]], ![![11440, 901, 880, 8962, -3028]], ![![6392, -2802, -11529, -5054, 10476]], ![![5305, 413, 390, 4141, -1386]], ![![5836, -1357, -6158, -958, 5143]]]
  g := ![![![-3247, -3868, -3538, 4050, 5118], ![-3578, -3869, -5248, 2534, 8100], ![2734, 3708, 1447, -5610, -1516], ![6689, 8111, 6804, -9039, -9660], ![7260, 9319, 5630, -12328, -7285]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [36, 190, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [136, 89, 172], [179, 107, 25], [0, 1]]
 g := ![![[40, 187, 135], [75, 16], [112, 21, 92], [157, 172], [18, 61], [128, 134], [1]], ![[105, 78, 88, 4], [40, 65], [30, 19, 127, 93], [42, 25], [92, 116], [131, 24], [3, 3, 186, 135]], ![[38, 153, 45, 83], [150, 171], [24, 114, 77, 134], [165, 109], [71, 65], [94, 142], [1, 26, 106, 62]]]
 h' := ![![[136, 89, 172], [51, 81, 174], [105, 192, 4], [19, 0, 180], [130, 134, 127], [37, 99, 109], [161, 7, 118], [0, 1]], ![[179, 107, 25], [160, 28, 45], [157, 33, 159], [60, 37, 151], [28, 15, 192], [155, 68, 126], [52, 146, 40], [136, 89, 172]], ![[0, 1], [186, 88, 175], [55, 169, 34], [23, 160, 63], [168, 48, 75], [153, 30, 159], [42, 44, 39], [179, 107, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 151], []]
 b := ![[], [146, 73, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [36, 190, 79, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![400000324, -38912518, -184626698, 139998258, 97663534]
  a := ![7, 47, 23, 0, -140]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-84715802, -112031470, -75632198, 139998258, 97663534]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4777, -356, -2294, 1514, 1430]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![4777, -356, -2294, 1514, 1430]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![152, 178, 1, 0, 0], ![130, 100, 0, 1, 0], ![186, 75, 0, 0, 1]] where
  M :=![![![4777, -356, -2294, 1514, 1430], ![-11440, -901, -880, -8962, 3028], ![-6392, 2802, 11529, 5054, -10476], ![47624, -634, -12288, 23959, 3540], ![-8180, -5024, -16548, -19736, 18281]]]
  hmulB := by decide  
  f := ![![![16901, -1444, -8410, -4050, -5118]], ![![40944, 15147, -5024, -2534, -8100]], ![![50096, 12676, -10967, -5386, -11260]], ![![31802, 6782, -8004, -3913, -7440]], ![![31550, 4565, -9720, -4726, -7879]]]
  g := ![![![-555, 758, -2294, 1514, 1430], ![3676, 4187, -880, -8962, 3028], ![-2372, -8980, 11529, 5054, -10476], ![-9430, -2410, -12288, 23959, 3540], ![8490, 17985, -16548, -19736, 18281]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [7, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 196], [0, 1]]
 g := ![![[155, 169], [156], [171, 135], [116], [64], [158], [97, 1]], ![[0, 28], [156], [67, 62], [116], [64], [158], [194, 196]]]
 h' := ![![[97, 196], [118, 13], [182, 64], [173, 23], [0, 126], [137, 8], [109, 143], [0, 1]], ![[0, 1], [0, 184], [86, 133], [40, 174], [8, 71], [125, 189], [190, 54], [97, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [67, 155]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [7, 100, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17042, -3103, -4573, -18156, 1128]
  a := ![1, 15, 8, -1, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14358, 12903, -4573, -18156, 1128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-16901, 1444, 8410, 4050, 5118]] ![![4777, -356, -2294, 1514, 1430]]
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


lemma PB324I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB324I4 : PrimesBelowBoundCertificateInterval O 151 197 324 where
  m := 9
  g := ![3, 2, 3, 2, 3, 3, 3, 3, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB324I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![705911761, 163]
    · exact ![27889, 27889, 167]
    · exact ![5177717, 29929]
    · exact ![5735339, 179, 179]
    · exact ![5929741, 181, 181]
    · exact ![36481, 36481, 191]
    · exact ![7189057, 193, 193]
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
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
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
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I157N2, I163N1, I167N2, I179N1, I179N2, I181N1, I181N2, I191N2, I193N1, I193N2]
  Il := ![[I157N1, I157N2], [I163N1], [I167N2], [], [I179N1, I179N2], [I181N1, I181N2], [I191N2], [I193N1, I193N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
