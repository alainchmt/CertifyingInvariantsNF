
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, -19, 77, 15, -28]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![39, -19, 77, 15, -28]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![152, 48, 97, 1, 0], ![52, 32, 38, 0, 1]] where
  M :=![![![39, -19, 77, 15, -28], ![-64, -180, -121, 19, 64], ![-52, 134, -123, -36, 68], ![216, 459, 339, 0, -20], ![204, 147, 357, 47, -61]]]
  hmulB := by decide  
  f := ![![![311, 13, 79, 9, -44]], ![![-44, 8, -35, 17, -16]], ![![-140, -20, -1, -30, 52]], ![![200, 3, 64, -4, -16]], ![![60, 1, 19, -1, -5]]]
  g := ![![![-5, 1, -2, 15, -28], ![-40, -20, -28, 19, 64], ![12, -2, 5, -36, 68], ![8, 7, 7, 0, -20], ![-24, -1, -12, 47, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [36, 56, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 11, 144], [98, 145, 13], [0, 1]]
 g := ![![[113, 80, 120], [19, 14], [75, 85, 99], [14, 137, 17], [14, 129, 3], [112, 1], []], ![[9, 26, 63, 14], [110, 127], [130, 96, 114, 58], [93, 3, 112, 40], [46, 15, 60, 13], [110, 144], [116, 12]], ![[116, 142, 87, 82], [8, 3], [59, 123, 39, 13], [49, 11, 13, 67], [41, 83, 91, 4], [151, 121], [90, 12]]]
 h' := ![![[14, 11, 144], [120, 152, 80], [126, 109, 93], [124, 83, 16], [124, 55, 71], [50, 129, 85], [0, 0, 1], [0, 1]], ![[98, 145, 13], [46, 63, 47], [148, 37, 136], [92, 26, 142], [129, 15, 3], [7, 151, 129], [102, 131, 145], [14, 11, 144]], ![[0, 1], [70, 99, 30], [94, 11, 85], [25, 48, 156], [17, 87, 83], [50, 34, 100], [84, 26, 11], [98, 145, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 41], []]
 b := ![[], [65, 151, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [36, 56, 45, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-177372348, -204367551, -289618341, 5513537, -204839708]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![61377292, 38763397, 44327882, 5513537, -204839708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-311, -13, -79, -9, 44]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-311, -13, -79, -9, 44]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![127, 133, 1, 0, 0], ![25, 129, 0, 1, 0], ![144, 140, 0, 0, 1]] where
  M :=![![![-311, -13, -79, -9, 44], ![44, -8, 35, -17, 16], ![140, 20, 1, 30, -52], ![180, -51, 183, -98, 100], ![24, 15, -33, 29, -39]]]
  hmulB := by decide  
  f := ![![![-39, 19, -77, -15, 28]], ![![64, 180, 121, -19, -64]], ![![23, 167, 41, -28, -32]], ![![45, 148, 85, -18, -48]], ![![20, 177, 35, -31, -31]]]
  g := ![![![23, 35, -79, -9, 44], ![-40, -30, 35, -17, 16], ![43, 21, 1, 30, -52], ![-223, -164, 183, -98, 100], ![58, 39, -33, 29, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [35, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 156], [0, 1]]
 g := ![![[24, 9], [48], [83, 89], [116, 40], [54, 115], [42], [1]], ![[0, 148], [48], [55, 68], [114, 117], [9, 42], [42], [1]]]
 h' := ![![[102, 156], [8, 3], [78, 26], [22, 106], [151, 121], [69, 127], [122, 102], [0, 1]], ![[0, 1], [0, 154], [61, 131], [1, 51], [90, 36], [149, 30], [7, 55], [102, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125]]
 b := ![[], [31, 141]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [35, 55, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![171313, 189266, 303874, -29173, 224623]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-446096, -432547, 303874, -29173, 224623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![39, -19, 77, 15, -28]] ![![-311, -13, -79, -9, 44]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![321, 446, 396, 102, 250]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![321, 446, 396, 102, 250]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![45, 25, 17, 1, 0], ![24, 62, 142, 0, 1]] where
  M :=![![![321, 446, 396, 102, 250], ![1596, 2177, 2046, 442, 1316], ![1408, 1970, 1727, 458, 1088], ![10036, 13700, 12846, 2799, 8244], ![7312, 10106, 9156, 2216, 5821]]]
  hmulB := by decide  
  f := ![![![435, 50, 108, 14, -70]], ![![-12, -1, 78, 10, -28]], ![![-224, -82, -91, -2, 48]], ![![93, 5, 31, 5, -18]], ![![-136, -64, -34, 4, 21]]]
  g := ![![![-63, -108, -226, 102, 250], ![-306, -555, -1180, 442, 1316], ![-278, -472, -985, 458, 1088], ![-1925, -3481, -7395, 2799, 8244], ![-1424, -2492, -5246, 2216, 5821]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [132, 69, 138, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 159, 160], [94, 3, 3], [0, 1]]
 g := ![![[145, 75, 16], [101, 31, 69], [118, 96], [1, 119], [73, 35], [67, 25, 1], []], ![[96, 143, 143, 25], [23, 134, 31, 140], [135, 49], [145, 60], [6, 61], [36, 130, 26, 136], [86, 9]], ![[12, 30, 105, 139], [148, 122, 60, 92], [0, 69], [107, 35], [63, 104], [0, 124, 48, 48], [80, 9]]]
 h' := ![![[94, 159, 160], [34, 61, 159], [110, 50, 45], [53, 0, 52], [115, 126, 49], [121, 64, 144], [0, 0, 1], [0, 1]], ![[94, 3, 3], [21, 119, 131], [148, 158, 148], [110, 8, 156], [4, 143, 95], [151, 42, 77], [92, 113, 3], [94, 159, 160]], ![[0, 1], [113, 146, 36], [91, 118, 133], [55, 155, 118], [18, 57, 19], [99, 57, 105], [69, 50, 159], [94, 3, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 94], []]
 b := ![[], [40, 0, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [132, 69, 138, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2116554, -2480426, -3322968, -76990, -2227056]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![336180, 843692, 1927778, -76990, -2227056]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-435, -50, -108, -14, 70]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-435, -50, -108, -14, 70]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![48, 159, 1, 0, 0], ![156, 138, 0, 1, 0], ![120, 44, 0, 0, 1]] where
  M :=![![![-435, -50, -108, -14, 70], ![12, 1, -78, -10, 28], ![224, 82, 91, 2, -48], ![308, 16, 210, 31, -100], ![56, -74, 48, 20, -23]]]
  hmulB := by decide  
  f := ![![![-321, -446, -396, -102, -250]], ![![-1596, -2177, -2046, -442, -1316]], ![![-1660, -2267, -2123, -464, -1364]], ![![-1720, -2354, -2190, -489, -1404]], ![![-712, -978, -900, -208, -575]]]
  g := ![![![-9, 98, -108, -14, 70], ![12, 77, -78, -10, 28], ![8, -77, 91, 2, -48], ![-16, -204, 210, 31, -100], ![-16, -58, 48, 20, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [59, 156, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 162], [0, 1]]
 g := ![![[80, 132], [34, 57], [40], [64], [74], [6, 49], [1]], ![[26, 31], [107, 106], [40], [64], [74], [23, 114], [1]]]
 h' := ![![[7, 162], [113, 28], [43, 100], [152, 23], [4, 8], [135, 143], [104, 7], [0, 1]], ![[0, 1], [146, 135], [91, 63], [150, 140], [60, 155], [158, 20], [153, 156], [7, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [88, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [59, 156, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![431297, 485675, 775778, -96687, 636944]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-602185, -843839, 775778, -96687, 636944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![321, 446, 396, 102, 250]] ![![-435, -50, -108, -14, 70]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1169, 753, 2279, 189, -914]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![1169, 753, 2279, 189, -914]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![147, 1, 104, 1, 0], ![5, 14, 165, 0, 1]] where
  M :=![![![1169, 753, 2279, 189, -914], ![56, -5274, 575, 987, -316], ![-2900, -240, -5793, -770, 2352], ![-160, 8941, -1113, -1684, 580], ![3056, 5185, 5673, -99, -2223]]]
  hmulB := by decide  
  f := ![![![-181, 247, 155, 41, 214]], ![![1004, 1318, 1211, 287, 756]], ![![1020, 1174, 1111, 256, 656]], ![![519, 1006, 881, 208, 630]], ![![1113, 1314, 1237, 286, 739]]]
  g := ![![![-132, 80, 799, 189, -914], ![-859, -11, -299, 987, -316], ![590, -194, -1879, -770, 2352], ![1464, 15, 469, -1684, 580], ![172, 218, 2292, -99, -2223]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [159, 79, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 64, 10], [18, 102, 157], [0, 1]]
 g := ![![[77, 159, 36], [90, 28, 127], [20, 83, 107], [113, 19], [43, 28], [75, 133, 1], []], ![[35, 158, 163, 41], [18, 43, 22, 159], [166, 135, 130, 123], [68, 1], [140, 107], [151, 74, 78, 166], [51, 100]], ![[163, 140, 25, 116], [153, 120, 29, 112], [110, 160, 71, 108], [161, 130], [90, 99], [138, 89, 107, 122], [71, 100]]]
 h' := ![![[115, 64, 10], [52, 10, 161], [160, 102, 131], [163, 21, 21], [125, 110, 112], [99, 149, 144], [0, 0, 1], [0, 1]], ![[18, 102, 157], [65, 164, 156], [58, 165, 20], [128, 4, 14], [98, 116, 166], [100, 85, 146], [106, 135, 102], [115, 64, 10]], ![[0, 1], [57, 160, 17], [111, 67, 16], [68, 142, 132], [139, 108, 56], [134, 100, 44], [57, 32, 64], [18, 102, 157]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 95], []]
 b := ![[], [79, 141, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [159, 79, 34, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-516564589, -572412728, -882501220, 50568240, -633562846]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28636417, 49382628, 589199230, 50568240, -633562846]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -2, 18, 3, -7]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![9, -2, 18, 3, -7]] 
 ![![167, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![9, -2, 18, 3, -7], ![-12, -44, -21, 5, 10], ![-16, 22, -35, -8, 16], ![32, 91, 51, -6, -6], ![38, 31, 69, 7, -19]]]
  hmulB := by decide  
  f := ![![![54873, 2660, 12942, 2309, -8647]], ![![26571, 1288, 6267, 1118, -4187]], ![![3134, 152, 739, 132, -494]], ![![37940, 1839, 8949, 1596, -5978]], ![![16727, 811, 3945, 704, -2636]]]
  g := ![![![0, -2, 18, 3, -7], ![16, -44, -21, 5, 10], ![-8, 22, -35, -8, 16], ![-41, 91, 51, -6, -6], ![-18, 31, 69, 7, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1747, -2433, -3289, -42, 1299]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-1747, -2433, -3289, -42, 1299]] 
 ![![167, 0, 0, 0, 0], ![149, 1, 0, 0, 0], ![91, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-1747, -2433, -3289, -42, 1299], ![-2352, 6777, -5312, -1906, 2262], ![5028, 3920, 9737, 688, -3896], ![4100, -11404, 9224, 3247, -3922], ![-3190, -10534, -5470, 1044, 2061]]]
  hmulB := by decide  
  f := ![![![50489, 5963, 14587, 2812, -5441]], ![![45087, 5426, 13105, 2530, -4785]], ![![27449, 3339, 8004, 1548, -2889]], ![![12735, 2133, 4169, 827, -913]], ![![19682, 2780, 6036, 1184, -1793]]]
  g := ![![![3465, -2433, -3289, -42, 1299], ![-3565, 6777, -5312, -1906, 2262], ![-7449, 3920, 9737, 688, -3896], ![5879, -11404, 9224, 3247, -3922], ![11314, -10534, -5470, 1044, 2061]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![1169, 753, 2279, 189, -914]] ![![9, -2, 18, 3, -7]]
  ![![-63663, 3533, -127963, -18492, 52043]] where
 M := ![![![-63663, 3533, -127963, -18492, 52043]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-63663, 3533, -127963, -18492, 52043]] ![![-1747, -2433, -3289, -42, 1299]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-782322689, -660117934, -1510600838, -97809228, 603623504]]]
 hmul := by decide  
 g := ![![![![-4684567, -3952802, -9045514, -585684, 3614512]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0, 0, 0]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]] where
  M :=![![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 5 2 7 [40, 110, 171, 87, 101, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 4, 12, 22, 87], [131, 106, 142, 13, 66], [135, 135, 136, 23, 35], [53, 100, 56, 115, 158], [0, 1]]
 g := ![![[97, 25, 118, 100, 84], [116, 67, 78, 157], [154, 101, 0, 49, 37], [132, 148, 14, 42, 57], [88, 117, 15, 167], [1], []], ![[161, 82, 23, 84, 14, 53, 75, 30], [88, 153, 51, 149], [154, 81, 24, 78, 38, 99, 108, 99], [95, 104, 161, 27, 13, 154, 45, 146], [71, 140, 108, 10], [104, 44, 14, 115, 125, 122, 162, 102], [78, 24, 40, 130]], ![[28, 161, 170, 124, 80, 123, 91, 99], [90, 128, 147, 29], [70, 51, 30, 139, 92, 139, 58, 65], [129, 81, 66, 149, 82, 139, 142, 75], [111, 93, 14, 122], [78, 66, 111, 122, 156, 78, 20, 93], [17, 144, 142, 31]], ![[141, 74, 125, 92, 110, 14, 98, 89], [11, 169, 28, 160], [144, 9, 171, 144, 119, 154, 113, 64], [72, 62, 29, 128, 122, 169, 41, 14], [171, 19, 112, 56], [70, 74, 133, 24, 120, 5, 76, 117], [158, 107, 23, 14]], ![[93, 117, 25, 71, 120, 115, 91, 73], [78, 84, 28, 36], [55, 156, 145, 122, 133, 18, 51, 169], [2, 68, 133, 12, 163, 134, 18, 78], [15, 166, 17, 31], [124, 136, 63, 144, 73, 122, 31, 13], [121, 163, 121, 52]]]
 h' := ![![[99, 4, 12, 22, 87], [157, 75, 150, 139, 118], [68, 95, 159, 156, 147], [83, 90, 156, 26, 146], [156, 149, 30, 110, 24], [133, 63, 2, 86, 72], [0, 0, 1], [0, 1]], ![[131, 106, 142, 13, 66], [49, 30, 159, 6, 38], [121, 84, 8, 147, 29], [168, 2, 64, 130, 168], [142, 12, 13, 79, 130], [120, 17, 128, 81, 150], [107, 75, 38, 51, 107], [99, 4, 12, 22, 87]], ![[135, 135, 136, 23, 35], [100, 134, 82, 51, 61], [97, 112, 159, 69, 95], [131, 41, 48, 116, 115], [91, 32, 51, 21, 170], [44, 146, 77, 59, 128], [46, 74, 139, 62, 5], [131, 106, 142, 13, 66]], ![[53, 100, 56, 115, 158], [39, 87, 7, 48, 84], [126, 56, 168, 164, 81], [170, 47, 37, 10, 81], [95, 142, 34, 128, 30], [154, 64, 116, 28, 103], [141, 85, 13, 12, 129], [135, 135, 136, 23, 35]], ![[0, 1], [83, 20, 121, 102, 45], [75, 172, 25, 156, 167], [139, 166, 41, 64, 9], [98, 11, 45, 8, 165], [122, 56, 23, 92, 66], [45, 112, 155, 48, 105], [53, 100, 56, 115, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 5, 6, 167], [], [], []]
 b := ![[], [101, 111, 68, 153, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 5
  hpos := by decide
  P := [40, 110, 171, 87, 101, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![701923119456, -2165380542036, 5943044712876, -4188930864292, 5191379305472]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4057359072, -12516650532, 34352859612, -24213473204, 30007972864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 154963892093 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1385, -4536, 3176, 1225, -1363]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![1385, -4536, 3176, 1225, -1363]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![142, 51, 59, 176, 1]] where
  M :=![![![1385, -4536, 3176, 1225, -1363], ![-9348, -10830, -17783, -637, 7074], ![-552, 14510, -2395, -2812, 1176], ![15848, 18653, 30185, 956, -11894], ![9326, -5419, 19163, 3625, -7891]]]
  hmulB := by decide  
  f := ![![![-67, 194, 136, 35, 153]], ![![764, 1014, 933, 219, 586]], ![![752, 904, 845, 198, 508]], ![![4736, 6371, 5849, 1374, 3694]], ![![5088, 7031, 6427, 1512, 4103]]]
  g := ![![![1089, 363, 467, 1347, -1363], ![-5664, -2076, -2431, -6959, 7074], ![-936, -254, -401, -1172, 1176], ![9524, 3493, 4089, 11700, -11894], ![6312, 2218, 2708, 7779, -7891]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 4 2 7 [89, 51, 162, 178, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 2, 136, 62], [32, 44, 28, 139], [86, 132, 15, 157], [0, 1]]
 g := ![![[124, 158, 35, 15], [110, 162, 57, 43], [38, 39, 129], [134, 119, 121], [97, 8, 174, 145], [1, 1], []], ![[70, 2, 152, 170, 23, 10], [54, 94, 153, 26, 126, 84], [172, 128, 52], [165, 13, 67], [66, 135, 79, 174, 15, 33], [48, 136, 63, 167, 168, 96], [85, 123, 85]], ![[169, 32, 172, 14, 149, 48], [102, 82, 166, 65, 108, 13], [117, 112, 177], [138, 47, 169], [67, 68, 27, 175, 131, 45], [96, 157, 99, 143, 139, 142], [17, 76, 168]], ![[163, 23, 38, 25, 137, 165], [125, 21, 62, 133, 8, 143], [69, 76, 64], [133, 41, 147], [39, 79, 87, 75, 47, 8], [119, 66, 17, 142, 27, 114], [142, 3, 126]]]
 h' := ![![[62, 2, 136, 62], [55, 69, 157, 146], [172, 116, 35, 36], [137, 77, 7, 147], [138, 114, 114, 168], [90, 39, 145, 18], [0, 0, 1], [0, 1]], ![[32, 44, 28, 139], [82, 102, 177, 9], [101, 98, 44, 6], [146, 51, 112, 125], [137, 41, 84, 70], [52, 87, 123, 121], [38, 2, 0, 166], [62, 2, 136, 62]], ![[86, 132, 15, 157], [20, 149, 94, 58], [122, 71, 145, 116], [137, 95, 104, 78], [151, 92, 46, 166], [28, 152, 125, 31], [48, 18, 46, 163], [32, 44, 28, 139]], ![[0, 1], [10, 38, 109, 145], [146, 73, 134, 21], [102, 135, 135, 8], [150, 111, 114, 133], [85, 80, 144, 9], [128, 159, 132, 29], [86, 132, 15, 157]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [119, 50, 78], []]
 b := ![[], [], [83, 52, 66, 172], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 4
  hpos := by decide
  P := [89, 51, 162, 178, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17872451099847, 22581138650202, 25822804235710, 2415733472091, 17406488277379]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13708652984849, -4833238902213, -5593072648769, -17101263705847, 17406488277379]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 1026625681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 194, 136, 35, 153]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-67, 194, 136, 35, 153]] 
 ![![179, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![162, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-67, 194, 136, 35, 153], ![764, 1014, 933, 219, 586], ![752, 904, 845, 198, 508], ![4736, 6371, 5849, 1374, 3694], ![3398, 4655, 4259, 1003, 2709]]]
  hmulB := by decide  
  f := ![![![1385, -4536, 3176, 1225, -1363]], ![![118, -618, 291, 147, -128]], ![![407, -1262, 927, 347, -397]], ![![1342, -4001, 3043, 1114, -1300]], ![![114, -233, 249, 75, -105]]]
  g := ![![![-103, 194, 136, 35, 153], ![-621, 1014, 933, 219, 586], ![-559, 904, 845, 198, 508], ![-3897, 6371, 5849, 1374, 3694], ![-2843, 4655, 4259, 1003, 2709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![1385, -4536, 3176, 1225, -1363]] ![![-67, 194, 136, 35, 153]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
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


def P181P0 : CertificateIrreducibleZModOfList' 181 5 2 7 [178, 146, 20, 129, 57, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 76, 127, 130, 90], [23, 4, 173, 80, 11], [162, 60, 178, 68, 118], [26, 40, 65, 84, 143], [0, 1]]
 g := ![![[152, 144, 126, 99, 75], [12, 106, 74, 62], [2, 106, 121, 136, 133], [116, 116, 146, 37], [0, 155, 41, 15, 172], [1], []], ![[77, 43, 169, 118, 145, 61, 144, 35], [119, 73, 109, 56], [43, 119, 89, 38, 128, 120, 142, 97], [0, 177, 113, 1], [17, 142, 157, 106, 47, 168, 112, 179], [50, 67, 158, 33, 82, 99, 138, 22], [48, 166, 82, 136]], ![[72, 65, 151, 51, 50, 156, 173, 75], [12, 0, 115, 136], [9, 157, 146, 161, 83, 169, 15, 56], [141, 84, 62, 43], [86, 133, 174, 101, 164, 150, 174, 42], [158, 110, 32, 36, 67, 164, 69, 145], [27, 159, 112, 121]], ![[137, 87, 97, 149, 149, 65, 30, 24], [97, 15, 31, 101], [142, 177, 142, 38, 18, 106, 5, 113], [109, 88, 79, 122], [172, 27, 50, 168, 62, 4, 139, 173], [88, 165, 9, 179, 77, 145, 6, 134], [114, 137, 137, 168]], ![[149, 128, 49, 146, 167, 81, 164, 114], [175, 9, 6, 16], [44, 71, 89, 36, 94, 30, 169, 166], [149, 157, 170, 156], [51, 120, 64, 149, 146, 114, 45, 80], [178, 135, 11, 13, 34, 157, 131, 39], [116, 31, 179, 177]]]
 h' := ![![[94, 76, 127, 130, 90], [72, 144, 47, 148, 16], [6, 41, 69, 128, 65], [167, 64, 61, 50, 155], [0, 112, 147, 28, 134], [3, 35, 161, 52, 124], [0, 0, 1], [0, 1]], ![[23, 4, 173, 80, 11], [15, 43, 32, 100, 103], [54, 176, 101, 119, 150], [25, 113, 166, 113, 63], [176, 78, 123, 85, 1], [105, 140, 164, 101, 179], [111, 176, 177, 43, 104], [94, 76, 127, 130, 90]], ![[162, 60, 178, 68, 118], [47, 45, 114, 179, 22], [98, 156, 152, 97, 90], [126, 166, 77, 93, 161], [101, 166, 168, 133, 119], [8, 171, 75, 58, 32], [67, 158, 122, 150, 160], [23, 4, 173, 80, 11]], ![[26, 40, 65, 84, 143], [123, 97, 127, 34, 124], [70, 161, 151, 178, 61], [64, 19, 40, 99, 109], [68, 50, 92, 57, 22], [30, 16, 134, 113, 33], [160, 130, 124, 113, 30], [162, 60, 178, 68, 118]], ![[0, 1], [126, 33, 42, 82, 97], [12, 9, 70, 21, 177], [80, 0, 18, 7, 55], [151, 137, 13, 59, 86], [23, 0, 9, 38, 175], [119, 79, 119, 56, 68], [26, 40, 65, 84, 143]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139, 85, 168, 140], [], [], []]
 b := ![[], [16, 34, 80, 44, 99], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 5
  hpos := by decide
  P := [178, 146, 20, 129, 57, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![974415310, -1277687507, 5466015742, -3395979739, 4658149754]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5383510, -7059047, 30198982, -18762319, 25735634]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153, -159, 257, 63, -108]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![153, -159, 257, 63, -108]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![110, 28, 10, 79, 1]] where
  M :=![![![153, -159, 257, 63, -108], ![-408, -722, -749, 23, 288], ![-180, 614, -381, -164, 172], ![656, 1247, 1223, -22, -508], ![548, 11, 1109, 147, -443]]]
  hmulB := by decide  
  f := ![![![3, -5, -3, -1, -4]], ![![-20, -26, -25, -5, -16]], ![![-20, -24, -21, -6, -12]], ![![-124, -163, -157, -32, -100]], ![![-54, -76, -72, -15, -47]]]
  g := ![![![63, 15, 7, 45, -108], ![-168, -46, -19, -119, 288], ![-100, -22, -11, -72, 172], ![296, 81, 33, 210, -508], ![258, 65, 29, 184, -443]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [185, 158, 139, 182, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 118, 129, 87], [100, 190], [154, 73, 62, 104], [0, 1]]
 g := ![![[182, 159, 164, 2], [98, 9, 135, 144], [88, 95, 58, 8], [62, 47, 133, 98], [148, 27, 46, 117], [9, 1], []], ![[43, 119, 130, 178, 109, 137], [46, 41, 124, 146, 44, 111], [83, 105, 26, 7, 188, 66], [27, 56, 90, 4, 105, 56], [76, 142, 92, 63, 128, 126], [174, 23, 149, 180, 131, 164], [162, 33, 120]], ![[151, 58, 0, 189], [189, 151, 169, 47], [127, 43, 166, 183], [55, 156, 119, 93], [140, 139, 2, 74], [109, 190], []], ![[176, 32, 185, 9, 40, 54], [111, 154, 54, 173, 154, 80], [86, 165, 20, 52, 145, 125], [129, 129, 42, 136, 28, 135], [187, 81, 95, 4, 98, 65], [70, 73, 147, 160, 1, 27], [162, 33, 120]]]
 h' := ![![[137, 118, 129, 87], [15, 156, 75, 57], [146, 136, 71, 12], [181, 132, 52, 77], [124, 131, 140, 174], [54, 112, 119, 133], [0, 0, 1], [0, 1]], ![[100, 190], [34, 6, 111, 64], [93, 76, 13, 18], [26, 111, 112, 118], [179, 55, 13, 58], [30, 73, 48, 104], [68, 58, 102, 105], [137, 118, 129, 87]], ![[154, 73, 62, 104], [148, 147, 176, 134], [90, 24, 42, 179], [178, 118, 41, 114], [161, 167, 6, 17], [70, 144, 100, 58], [68, 182, 1], [100, 190]], ![[0, 1], [71, 73, 20, 127], [142, 146, 65, 173], [33, 21, 177, 73], [54, 29, 32, 133], [16, 53, 115, 87], [49, 142, 87, 86], [154, 73, 62, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [37], []]
 b := ![[], [], [92, 100, 90, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [185, 158, 139, 182, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7480557559107, 8678374079256, 12066026103264, -83890482494, 8437665900496]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4820223515683, -1191498801752, -378589701056, -3490363856658, 8437665900496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 5, 3, 1, 4]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-3, 5, 3, 1, 4]] 
 ![![191, 0, 0, 0, 0], ![130, 1, 0, 0, 0], ![136, 0, 1, 0, 0], ![158, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![-3, 5, 3, 1, 4], ![20, 26, 25, 5, 16], ![20, 24, 21, 6, 12], ![124, 163, 157, 32, 100], ![88, 121, 109, 27, 69]]]
  hmulB := by decide  
  f := ![![![-153, 159, -257, -63, 108]], ![![-102, 112, -171, -43, 72]], ![![-108, 110, -181, -44, 76]], ![![-130, 125, -219, -52, 92]], ![![-103, 104, -174, -42, 73]]]
  g := ![![![-9, 5, 3, 1, 4], ![-50, 26, 25, 5, 16], ![-44, 24, 21, 6, 12], ![-314, 163, 157, 32, 100], ![-227, 121, 109, 27, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![153, -159, 257, 63, -108]] ![![-3, 5, 3, 1, 4]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25069, -1214, -5942, -1057, 3959]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-25069, -1214, -5942, -1057, 3959]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![53, 162, 14, 1, 0], ![106, 72, 107, 0, 1]] where
  M :=![![![-25069, -1214, -5942, -1057, 3959], ![3376, 242, 817, 131, -538], ![11608, 538, 2801, 500, -1852], ![13356, 513, 3117, 580, -2094], ![2286, 63, 453, 93, -329]]]
  hmulB := by decide  
  f := ![![![-27, -52, -10, -29, 1]], ![![-160, -150, -313, 49, -230]], ![![-112, -244, 3, -158, 40]], ![![-155, -163, -275, 23, -197]], ![![-140, -225, -124, -87, -65]]]
  g := ![![![-2014, -596, -2149, -1057, 3959], ![277, 92, 293, 131, -538], ![940, 274, 1005, 500, -1852], ![1060, 297, 1135, 580, -2094], ![167, 45, 178, 93, -329]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [89, 178, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 17, 95], [75, 175, 98], [0, 1]]
 g := ![![[36, 114, 100], [51, 185], [79, 49], [10, 121], [11, 124], [101, 137], [1]], ![[139, 122, 28, 65], [131, 72], [65, 72], [131, 43], [21, 172], [38, 56], [36, 81, 36, 69]], ![[77, 23, 77, 161], [11, 92], [49, 50], [52, 28], [161, 59], [54, 1], [159, 173, 102, 124]]]
 h' := ![![[77, 17, 95], [121, 37, 10], [118, 164, 68], [89, 99, 186], [173, 147, 11], [90, 162, 33], [104, 15, 152], [0, 1]], ![[75, 175, 98], [130, 38, 54], [189, 43, 74], [50, 186, 74], [69, 54, 64], [104, 51, 128], [165, 34, 40], [77, 17, 95]], ![[0, 1], [72, 118, 129], [47, 179, 51], [111, 101, 126], [140, 185, 118], [103, 173, 32], [108, 144, 1], [75, 175, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 96], []]
 b := ![[], [172, 92, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [89, 178, 41, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148971615, 167327580, 251212724, -11890994, 180358178]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-95019547, -56435856, -97827142, -11890994, 180358178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -52, -10, -29, 1]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-27, -52, -10, -29, 1]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![80, 45, 1, 0, 0], ![52, 175, 0, 1, 0], ![158, 69, 0, 0, 1]] where
  M :=![![![-27, -52, -10, -29, 1], ![-160, -150, -313, 49, -230], ![-112, -244, 3, -158, 40], ![-996, -987, -1881, 250, -1374], ![-654, -1005, -657, -339, -371]]]
  hmulB := by decide  
  f := ![![![-25069, -1214, -5942, -1057, 3959]], ![![3376, 242, 817, 131, -538]], ![![-9544, -444, -2258, -405, 1506]], ![![-3624, -105, -844, -163, 568]], ![![-19304, -907, -4570, -818, 3047]]]
  g := ![![![11, 28, -10, -29, 1], ![304, 110, -313, 49, -230], ![8, 127, 3, -158, 40], ![1832, 698, -1881, 250, -1374], ![664, 588, -657, -339, -371]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [128, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 192], [0, 1]]
 g := ![![[127, 95], [6], [62], [95], [147], [23], [149, 1]], ![[0, 98], [6], [62], [95], [147], [23], [105, 192]]]
 h' := ![![[149, 192], [50, 45], [25, 149], [137, 107], [36, 148], [18, 98], [35, 71], [0, 1]], ![[0, 1], [0, 148], [31, 44], [61, 86], [86, 45], [145, 95], [192, 122], [149, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148]]
 b := ![[], [84, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [128, 44, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86113, 100458, 143292, -8364, 115320]
  a := ![21, 37, 37, -19, 92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-151103, -66534, 143292, -8364, 115320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-25069, -1214, -5942, -1057, 3959]] ![![-27, -52, -10, -29, 1]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, -79, -73, -17, -46]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-57, -79, -73, -17, -46]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![5, 149, 1, 0, 0], ![81, 148, 0, 1, 0], ![79, 96, 0, 0, 1]] where
  M :=![![![-57, -79, -73, -17, -46], ![-284, -390, -357, -85, -228], ![-252, -348, -317, -74, -204], ![-1788, -2467, -2249, -532, -1432], ![-1308, -1801, -1649, -387, -1049]]]
  hmulB := by decide  
  f := ![![![311, 5, 49, 13, -42]], ![![-48, 54, -19, -19, 20]], ![![-29, 41, -13, -14, 14]], ![![91, 42, 6, -9, -2]], ![![101, 28, 10, -4, -7]]]
  g := ![![![27, 90, -73, -17, -46], ![134, 443, -357, -85, -228], ![119, 393, -317, -74, -204], ![841, 2786, -2249, -532, -1432], ![615, 2040, -1649, -387, -1049]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [160, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 196], [0, 1]]
 g := ![![[190, 181], [135], [127, 181], [15], [178], [132], [135, 1]], ![[0, 16], [135], [134, 16], [15], [178], [132], [73, 196]]]
 h' := ![![[135, 196], [123, 56], [168, 174], [184, 56], [107, 58], [131, 104], [70, 138], [0, 1]], ![[0, 1], [0, 141], [18, 23], [61, 141], [57, 139], [184, 93], [182, 59], [135, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [67, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [160, 62, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1193971, 1278979, 2217994, -311938, 1759874]
  a := ![-75, -156, -157, 98, -371]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-627711, -2294331, 2217994, -311938, 1759874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-293, -45, 7, -69, 116]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-293, -45, 7, -69, 116]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![192, 144, 1, 0, 0], ![11, 78, 0, 1, 0], ![23, 56, 0, 0, 1]] where
  M :=![![![-293, -45, 7, -69, 116], ![4, 144, -347, 261, -320], ![188, -174, 495, -328, 384], ![-44, 809, -1971, 1468, -1792], ![88, -205, 549, -387, 471]]]
  hmulB := by decide  
  f := ![![![91, -517, 229, 121, -100]], ![![-992, -892, -1913, -113, 768]], ![![-636, -1148, -1175, 34, 464]], ![![-379, -374, -728, -37, 292]], ![![-267, -318, -508, -16, 203]]]
  g := ![![![-18, -11, 7, -69, 116], ![361, 242, -347, 261, -320], ![-508, -342, 495, -328, 384], ![2048, 1373, -1971, 1468, -1792], ![-568, -383, 549, -387, 471]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [18, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 196], [0, 1]]
 g := ![![[136, 135], [105], [86, 175], [25], [181], [158], [113, 1]], ![[25, 62], [105], [161, 22], [25], [181], [158], [29, 196]]]
 h' := ![![[113, 196], [76, 174], [28, 41], [163, 136], [66, 5], [70, 141], [133, 143], [0, 1]], ![[0, 1], [38, 23], [130, 156], [165, 61], [40, 192], [46, 56], [138, 54], [113, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [154, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [18, 84, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![184945, 201829, 332462, -37079, 258030]
  a := ![-29, -59, -58, 36, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-351140, -300661, 332462, -37079, 258030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, 176, -156, -52, 66]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-69, 176, -156, -52, 66]] 
 ![![197, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![140, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-69, 176, -156, -52, 66], ![380, 503, 718, 14, -284], ![56, -588, 165, 124, -76], ![-644, -866, -1214, -21, 480], ![-416, 160, -848, -146, 347]]]
  hmulB := by decide  
  f := ![![![639, 432, 868, -104, 566]], ![![48, 43, 58, 2, 36]], ![![204, 140, 285, -36, 188]], ![![512, 410, 654, -25, 416]], ![![167, 140, 232, -14, 153]]]
  g := ![![![61, 176, -156, -52, 66], ![-204, 503, 718, 14, -284], ![-88, -588, 165, 124, -76], ![344, -866, -1214, -21, 480], ![285, 160, -848, -146, 347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-57, -79, -73, -17, -46]] ![![-293, -45, 7, -69, 116]]
  ![![-639, -432, -868, 104, -566]] where
 M := ![![![-639, -432, -868, 104, -566]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-639, -432, -868, 104, -566]] ![![-69, 176, -156, -52, 66]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![-197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)


lemma PB853I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB853I4 : PrimesBelowBoundCertificateInterval O 151 197 853 where
  m := 9
  g := ![2, 2, 3, 1, 2, 1, 2, 2, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB853I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1, I197N2]
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
    · exact ![4330747, 26569]
    · exact ![4657463, 167, 167]
    · exact ![154963892093]
    · exact ![1026625681, 179]
    · exact ![194264244901]
    · exact ![1330863361, 191]
    · exact ![7189057, 37249]
    · exact ![38809, 38809, 197]
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
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I167N1, I167N2, I179N1, I191N1, I197N2]
  Il := ![[], [], [I167N1, I167N2], [], [I179N1], [], [I191N1], [], [I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
