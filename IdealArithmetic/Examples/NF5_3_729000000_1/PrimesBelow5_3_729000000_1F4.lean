
import IdealArithmetic.Examples.NF5_3_729000000_1.RI5_3_729000000_1
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


def P157P0 : CertificateIrreducibleZModOfList' 157 5 2 7 [62, 91, 9, 144, 87, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 104, 32, 19, 76], [132, 8, 132, 101, 11], [94, 101, 103, 60, 103], [95, 100, 47, 134, 124], [0, 1]]
 g := ![![[118, 25, 67, 19, 17], [61, 88, 117, 39], [12, 147, 148, 131, 68], [56, 144, 11, 10, 9], [95, 39, 46, 70, 1], [], []], ![[18, 46, 124, 10, 80, 28, 66, 33], [92, 108, 93, 143], [148, 154, 70, 11, 25, 106, 42, 10], [152, 82, 139, 79, 133, 65, 92, 117], [149, 64, 61, 85, 16, 147, 67, 51], [23, 70, 31, 35], [3, 40, 107, 124]], ![[99, 110, 64, 47, 139, 51, 149, 12], [90, 152, 148, 58], [145, 129, 7, 65, 110, 46, 128, 27], [33, 109, 99, 35, 156, 88, 75, 17], [27, 117, 141, 25, 137, 2, 93, 17], [18, 71, 130, 120], [6, 98, 16, 121]], ![[12, 39, 39, 25, 91, 25, 2, 26], [19, 43, 42, 86], [9, 118, 57, 6, 139, 65, 25, 92], [48, 155, 75, 45, 82, 4, 68, 135], [114, 39, 72, 92, 139, 6, 54, 150], [3, 136, 107, 147], [56, 43, 134, 90]], ![[58, 121, 20, 146, 124, 28, 49, 138], [49, 76, 53, 130], [41, 20, 38, 129, 10, 27, 109, 19], [83, 125, 68, 67, 148, 76, 56, 121], [141, 108, 109, 144, 14, 145, 147, 10], [46, 120, 151, 67], [43, 78, 33, 147]]]
 h' := ![![[63, 104, 32, 19, 76], [97, 93, 85, 58, 86], [41, 9, 145, 155, 143], [139, 73, 48, 13, 142], [76, 84, 123, 51, 154], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[132, 8, 132, 101, 11], [66, 121, 18, 105, 9], [79, 117, 82, 63, 92], [91, 152, 89, 91, 101], [2, 79, 2, 98, 153], [55, 145, 77, 45, 110], [15, 146, 151, 96, 52], [63, 104, 32, 19, 76]], ![[94, 101, 103, 60, 103], [89, 140, 137, 71, 27], [86, 116, 51, 126, 134], [149, 83, 42, 98, 38], [17, 116, 60, 28, 75], [93, 18, 143, 40, 75], [96, 43, 142, 17, 80], [132, 8, 132, 101, 11]], ![[95, 100, 47, 134, 124], [94, 94, 102, 147, 96], [153, 8, 62, 141, 20], [29, 59, 42, 25, 14], [19, 108, 125, 149, 62], [19, 113, 12, 136, 58], [26, 79, 41, 52, 124], [94, 101, 103, 60, 103]], ![[0, 1], [16, 23, 129, 90, 96], [89, 64, 131, 143, 82], [119, 104, 93, 87, 19], [133, 84, 4, 145, 27], [92, 38, 82, 93, 70], [79, 46, 136, 149, 58], [95, 100, 47, 134, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153, 130, 90, 58], [], [], []]
 b := ![[], [146, 155, 72, 39, 86], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 5
  hpos := by decide
  P := [62, 91, 9, 144, 87, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12321110201068, -17453245874161, -1345257360697, -5735668567170, -6862533948612]
  a := ![0, -9, 16, 2, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78478408924, -111167171173, -8568518221, -36532920810, -43710407316]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1183, -999, -95, -323, -221]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-1183, -999, -95, -323, -221]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![153, 114, 0, 1, 0], ![107, 99, 100, 0, 1]] where
  M :=![![![-1183, -999, -95, -323, -221], ![-2210, -4412, -251, -1511, -2159], ![-21590, -28725, -2038, -9635, -11225], ![-10120, -14283, -979, -4809, -5824], ![-21820, -29989, -2087, -10080, -12003]]]
  hmulB := by decide  
  f := ![![![-141, -61, 1, -9, 17]], ![![170, 42, -17, 87, -37]], ![![-370, -235, -256, -405, 485]], ![![-11, -26, -10, 52, -11]], ![![-219, -160, -167, -202, 287]]]
  g := ![![![441, 354, 135, -323, -221], ![2822, 2341, 1323, -1511, -2159], ![16280, 13380, 6874, -9635, -11225], ![8275, 6813, 3567, -4809, -5824], ![17207, 14156, 7351, -10080, -12003]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [153, 18, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 45, 41], [135, 117, 122], [0, 1]]
 g := ![![[98, 137, 104], [154, 55, 36], [91, 104], [6, 115], [83, 16], [6, 137, 1], []], ![[83, 42, 51, 21], [92, 115, 47, 145], [67, 97], [116, 152], [77, 151], [43, 11, 114, 40], [82, 51]], ![[31, 128, 19, 79], [18, 161, 145, 11], [110, 93], [132, 53], [69, 83], [128, 104, 46, 105], [1, 51]]]
 h' := ![![[2, 45, 41], [73, 109, 105], [156, 69, 6], [86, 56, 105], [29, 146, 142], [60, 121, 159], [0, 0, 1], [0, 1]], ![[135, 117, 122], [95, 126, 128], [22, 19, 108], [2, 23, 74], [132, 93, 106], [103, 113, 92], [9, 29, 117], [2, 45, 41]], ![[0, 1], [32, 91, 93], [54, 75, 49], [62, 84, 147], [131, 87, 78], [16, 92, 75], [142, 134, 45], [135, 117, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146, 86], []]
 b := ![[], [160, 160, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [153, 18, 26, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15798287272, -21978117058, -638192298, -6895582081, -10365650596]
  a := ![3, -125, 119, -69, -298]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13180063711, 10983543860, 6355379554, -6895582081, -10365650596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-141, -61, 1, -9, 17]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-141, -61, 1, -9, 17]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 50, 0, 1, 0], ![116, 90, 0, 0, 1]] where
  M :=![![![-141, -61, 1, -9, 17], ![170, 42, -17, 87, -37], ![-370, -235, -256, -405, 485], ![400, 307, 155, -65, -176], ![-440, -211, -45, -76, 125]]]
  hmulB := by decide  
  f := ![![![-1183, -999, -95, -323, -221]], ![![-2210, -4412, -251, -1511, -2159]], ![![-176, -213, -16, -71, -77]], ![![-740, -1441, -83, -493, -698]], ![![-2196, -3331, -219, -1126, -1423]]]
  g := ![![![-13, -7, 1, -9, 17], ![28, -6, -17, 87, -37], ![-338, -145, -256, -405, 485], ![122, 119, 155, -65, -176], ![-90, -47, -45, -76, 125]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [149, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 162], [0, 1]]
 g := ![![[19, 156], [27, 95], [58], [54], [4], [88, 14], [1]], ![[113, 7], [32, 68], [58], [54], [4], [63, 149], [1]]]
 h' := ![![[103, 162], [52, 51], [129, 62], [28, 104], [24, 124], [91, 2], [14, 103], [0, 1]], ![[0, 1], [89, 112], [158, 101], [145, 59], [82, 39], [134, 161], [28, 60], [103, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [69, 149]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [149, 60, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12990, 15622, -744, 3614, 8826]
  a := ![1, -9, 11, -3, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6174, -5886, -744, 3614, 8826]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-1183, -999, -95, -323, -221]] ![![-141, -61, 1, -9, 17]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-789, -209, -59, -51, 337]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-789, -209, -59, -51, 337]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![71, 153, 36, 150, 1]] where
  M :=![![![-789, -209, -59, -51, 337], ![3370, 2572, 281, 809, 31], ![310, 5925, 176, 2125, 4885], ![3200, 4419, 303, 1513, 1748], ![3040, 7513, 363, 2598, 4533]]]
  hmulB := by decide  
  f := ![![![2117, 657, 137, 175, -377]], ![![-3770, -1170, -245, -313, 673]], ![![6730, 2095, 442, 555, -1205]], ![![680, 209, 45, 61, -124]], ![![-469, -146, -29, -36, 81]]]
  g := ![![![-148, -310, -73, -303, 337], ![7, -13, -5, -23, 31], ![-2075, -4440, -1052, -4375, 4885], ![-724, -1575, -375, -1561, 1748], ![-1909, -4108, -975, -4056, 4533]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [107, 81, 21, 121, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [165, 100, 91, 39], [43, 17, 53, 56], [5, 49, 23, 72], [0, 1]]
 g := ![![[128, 136, 42, 130], [115, 45, 98, 72], [83, 17, 139, 77], [119, 148, 130], [53, 159, 98], [46, 1], []], ![[10, 14, 125, 82, 79, 74], [117, 139, 154, 95, 13, 79], [83, 135, 18, 67, 124, 163], [146, 156, 121], [74, 97, 72], [128, 5, 45, 165, 7, 101], [40, 77, 18]], ![[97, 122, 112, 68, 127, 6], [36, 5, 18, 143, 143, 21], [137, 107, 131, 109, 96, 141], [155, 148, 32], [25, 12, 54], [86, 86, 73, 122, 72, 89], [21, 59, 130]], ![[125, 132, 123, 148, 93, 122], [126, 18, 49, 51, 24, 25], [145, 66, 109, 83, 92, 12], [84, 155, 49], [46, 58, 147], [61, 14, 36, 28, 166, 97], [87, 127, 7]]]
 h' := ![![[165, 100, 91, 39], [53, 130, 56, 111], [137, 74, 57, 89], [44, 133, 98, 113], [69, 142, 64, 111], [88, 8, 122, 91], [0, 0, 1], [0, 1]], ![[43, 17, 53, 56], [144, 62, 20, 7], [76, 64, 97, 52], [92, 35, 141, 61], [163, 84, 164, 11], [137, 146, 148, 89], [66, 145, 132, 109], [165, 100, 91, 39]], ![[5, 49, 23, 72], [109, 84, 36, 128], [116, 82, 124, 118], [56, 153, 39, 16], [129, 143, 135, 52], [93, 85, 124, 87], [103, 128, 79, 157], [43, 17, 53, 56]], ![[0, 1], [62, 58, 55, 88], [53, 114, 56, 75], [59, 13, 56, 144], [14, 132, 138, 160], [60, 95, 107, 67], [68, 61, 122, 68], [5, 49, 23, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 128, 81], []]
 b := ![[], [], [121, 126, 166, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [107, 81, 21, 121, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4503393586171, 6192149825375, 387085955071, 1895392897610, 2543122008210]
  a := ![1, 45, -57, 10, 141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1054241131717, -2292847409765, -545900037967, -2272891666670, 2543122008210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2117, 657, 137, 175, -377]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![2117, 657, 137, 175, -377]] 
 ![![167, 0, 0, 0, 0], ![101, 1, 0, 0, 0], ![153, 0, 1, 0, 0], ![141, 0, 0, 1, 0], ![159, 0, 0, 0, 1]] where
  M :=![![![2117, 657, 137, 175, -377], ![-3770, -1170, -245, -313, 673], ![6730, 2095, 442, 555, -1205], ![680, 209, 45, 61, -124], ![3900, 1211, 253, 322, -695]]]
  hmulB := by decide  
  f := ![![![-789, -209, -59, -51, 337]], ![![-457, -111, -34, -26, 204]], ![![-721, -156, -53, -34, 338]], ![![-647, -150, -48, -34, 295]], ![![-733, -154, -54, -33, 348]]]
  g := ![![![-299, 657, 137, 175, -377], ![533, -1170, -245, -313, 673], ![-953, 2095, 442, 555, -1205], ![-97, 209, 45, 61, -124], ![-551, 1211, 253, 322, -695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-789, -209, -59, -51, 337]] ![![2117, 657, 137, 175, -377]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37633, -27075, -3105, -8562, 1104]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-37633, -27075, -3105, -8562, 1104]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![84, 1, 77, 1, 0], ![133, 152, 136, 0, 1]] where
  M :=![![![-37633, -27075, -3105, -8562, 1104], ![11040, -49576, -285, -18072, -50268], ![-502680, -561405, -45628, -185850, -158700], ![-164220, -241449, -16113, -81487, -102246], ![-450960, -554511, -41991, -184932, -186541]]]
  hmulB := by decide  
  f := ![![![-2021, -615, -9, -12, 168]], ![![1680, -230, -411, 594, 96]], ![![960, 1275, -1916, -4320, 3660]], ![![-528, 284, -848, -1927, 1698]], ![![659, 322, -1876, -2886, 3095]]]
  g := ![![![3091, -1077, 2925, -8562, 1104], ![47484, 43984, 47559, -18072, -50268], ![209340, 137265, 207214, -185850, -158700], ![117222, 88910, 116554, -81487, -102246], ![230597, 161761, 228713, -184932, -186541]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [100, 92, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 101, 133], [134, 71, 40], [0, 1]]
 g := ![![[80, 150, 41], [24, 13], [120, 91, 117], [3, 18, 57], [71, 21], [68, 92, 1], []], ![[101, 55, 131, 9], [23, 16], [151, 52, 93, 159], [103, 31, 98, 52], [118, 113], [105, 117, 120, 78], [28, 43]], ![[146, 148, 159, 142], [30, 142], [107, 95, 67, 60], [10, 124, 6, 47], [89, 52], [48, 138, 141, 106], [121, 43]]]
 h' := ![![[131, 101, 133], [12, 5, 53], [110, 141, 94], [46, 118, 64], [34, 44, 149], [120, 114, 114], [0, 0, 1], [0, 1]], ![[134, 71, 40], [81, 44, 103], [85, 73, 169], [62, 100, 170], [41, 96, 169], [58, 162, 74], [2, 37, 71], [131, 101, 133]], ![[0, 1], [169, 124, 17], [125, 132, 83], [8, 128, 112], [153, 33, 28], [149, 70, 158], [147, 136, 101], [134, 71, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 100], []]
 b := ![[], [62, 63, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [100, 92, 81, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27526752, -31266134, -4678014, -4754798, -6393448]
  a := ![-1, -6, 21, 13, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7064768, 5464120, 7115320, -4754798, -6393448]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 31, 3, 10, 6]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![37, 31, 3, 10, 6]] 
 ![![173, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![159, 0, 1, 0, 0], ![118, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![37, 31, 3, 10, 6], ![60, 128, 7, 44, 66], ![660, 865, 62, 290, 330], ![300, 425, 29, 143, 174], ![660, 899, 63, 302, 355]]]
  hmulB := by decide  
  f := ![![![209, 115, 75, 64, -126]], ![![35, 19, 14, 14, -24]], ![![207, 110, 63, 52, -108]], ![![154, 87, 55, 41, -90]], ![![121, 66, 42, 36, -71]]]
  g := ![![![-19, 31, 3, 10, 6], ![-99, 128, 7, 44, 66], ![-611, 865, 62, 290, 330], ![-306, 425, 29, 143, 174], ![-641, 899, 63, 302, 355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36233, 17136, 2804, 5047, -8819]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![36233, 17136, 2804, 5047, -8819]] 
 ![![173, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![118, 0, 0, 1, 0], ![86, 0, 0, 0, 1]] where
  M :=![![![36233, 17136, 2804, 5047, -8819], ![-88190, -41709, -6824, -12283, 21463], ![214630, 101500, 16603, 29895, -52235], ![-8140, -3850, -630, -1139, 1982], ![123960, 58622, 9592, 17266, -30173]]]
  hmulB := by decide  
  f := ![![![5452221, 1693012, 353374, 450393, -971459]], ![![1834790, 569735, 118918, 151567, -326917]], ![![1140071, 354012, 73891, 94178, -203134]], ![![3729106, 1157954, 241694, 308051, -664440]], ![![2768402, 859638, 179428, 228690, -493265]]]
  g := ![![![-5327, 17136, 2804, 5047, -8819], ![12966, -41709, -6824, -12283, 21463], ![-31553, 101500, 16603, 29895, -52235], ![1200, -3850, -630, -1139, 1982], ![-18222, 58622, 9592, 17266, -30173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-37633, -27075, -3105, -8562, 1104]] ![![37, 31, 3, 10, 6]]
  ![![-6906181, -9964402, -673680, -3359038, -4135266]] where
 M := ![![![-6906181, -9964402, -673680, -3359038, -4135266]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![-6906181, -9964402, -673680, -3359038, -4135266]] ![![36233, 17136, 2804, 5047, -8819]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-1327986233, -602861750, -102238848, -175967815, 345092615]]]
 hmul := by decide  
 g := ![![![![-7676221, -3484750, -590976, -1017155, 1994755]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![589, 593, 399, -89, -447]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![589, 593, 399, -89, -447]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![68, 1, 24, 1, 0], ![36, 111, 58, 0, 1]] where
  M :=![![![589, 593, 399, -89, -447], ![-4470, -2422, 413, 2291, -981], ![-9810, -10905, -10276, -2085, 12765], ![15000, 8925, 605, -6107, 516], ![-800, -629, -479, -72, 611]]]
  hmulB := by decide  
  f := ![![![-152089, -71933, -11769, -21187, 37011]], ![![370110, 175000, 28639, 51541, -90111]], ![![-901110, -426375, -69734, -125595, 219135]], ![![-176338, -83427, -13646, -24574, 42891]], ![![-95966, -45479, -7428, -13401, 23276]]]
  g := ![![![127, 281, 159, -89, -447], ![-698, 582, 13, 2291, -981], ![-1830, -7965, -3914, -2085, 12765], ![2300, -236, 655, -6107, 516], ![-100, -382, -191, -72, 611]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [72, 93, 158, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 175, 34], [12, 3, 145], [0, 1]]
 g := ![![[67, 116, 172], [58, 105, 138], [145, 117], [92, 93], [32, 130, 51], [169, 21, 1], []], ![[101, 16, 47, 84], [10, 26, 84, 131], [35, 82], [115, 81], [70, 110, 170, 34], [140, 103, 47, 127], [18, 82]], ![[30, 139, 168, 64], [176, 95, 60, 46], [173, 158], [129, 108], [51, 126, 77, 13], [120, 135, 5, 172], [86, 82]]]
 h' := ![![[9, 175, 34], [120, 105, 72], [23, 166, 73], [170, 136, 81], [23, 31, 123], [4, 134, 92], [0, 0, 1], [0, 1]], ![[12, 3, 145], [42, 100, 27], [174, 82, 135], [176, 41, 34], [143, 108, 170], [52, 29, 178], [38, 47, 3], [9, 175, 34]], ![[0, 1], [178, 153, 80], [135, 110, 150], [47, 2, 64], [57, 40, 65], [96, 16, 88], [38, 132, 175], [12, 3, 145]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 14], []]
 b := ![[], [122, 3, 147], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [72, 93, 158, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12021992, 13947518, 6665806, 1890990, -4822036]
  a := ![0, -2, -18, -26, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![318592, 3057556, 1346146, 1890990, -4822036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-152089, -71933, -11769, -21187, 37011]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-152089, -71933, -11769, -21187, 37011]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![136, 118, 1, 0, 0], ![42, 0, 0, 1, 0], ![75, 96, 0, 0, 1]] where
  M :=![![![-152089, -71933, -11769, -21187, 37011], ![370110, 175000, 28639, 51541, -90111], ![-901110, -426375, -69734, -125595, 219135], ![34080, 16011, 2635, 4709, -8388], ![-520540, -246403, -40285, -72588, 126499]]]
  hmulB := by decide  
  f := ![![![589, 593, 399, -89, -447]], ![![-4470, -2422, 413, 2291, -981]], ![![-2554, -1207, 518, 1431, -915]], ![![222, 189, 97, -55, -102]], ![![-2155, -1054, 386, 1191, -710]]]
  g := ![![![-2444, -12493, -11769, -21187, 37011], ![5971, 30426, 28639, 51541, -90111], ![-14399, -73937, -69734, -125595, 219135], ![598, 2851, 2635, 4709, -8388], ![-8271, -42663, -40285, -72588, 126499]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [31, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 178], [0, 1]]
 g := ![![[8, 52], [74, 5], [51], [12], [30, 61], [117, 107], [1]], ![[0, 127], [87, 174], [51], [12], [117, 118], [73, 72], [1]]]
 h' := ![![[110, 178], [33, 125], [4, 30], [137, 92], [144, 38], [132, 132], [148, 110], [0, 1]], ![[0, 1], [0, 54], [82, 149], [54, 87], [28, 141], [153, 47], [76, 69], [110, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [162, 137]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [31, 69, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32137, 30175, 311, 525, 11375]
  a := ![13, -7, 18, 8, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4946, -6137, 311, 525, 11375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![589, 593, 399, -89, -447]] ![![-152089, -71933, -11769, -21187, 37011]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12909, -6113, -999, -1801, 3133]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-12909, -6113, -999, -1801, 3133]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![163, 77, 1, 0, 0], ![30, 166, 0, 1, 0], ![132, 113, 0, 0, 1]] where
  M :=![![![-12909, -6113, -999, -1801, 3133], ![31330, 14758, 2423, 4343, -7673], ![-76730, -36615, -5944, -10805, 18385], ![2720, 1119, 207, 319, -808], ![-44480, -21383, -3449, -6320, 10521]]]
  hmulB := by decide  
  f := ![![![-569, -309, -49, 147, 41]], ![![410, -216, -709, -473, 923]], ![![-287, -334, -334, -85, 419]], ![![270, -251, -649, -399, 840]], ![![-158, -359, -478, -189, 606]]]
  g := ![![![-1158, 87, -999, -1801, 3133], ![2867, -142, 2423, 4343, -7673], ![-6688, 758, -5944, -10805, 18385], ![365, 130, 207, 319, -808], ![-3765, 577, -3449, -6320, 10521]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [127, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 180], [0, 1]]
 g := ![![[65, 34], [73], [78, 169], [52], [23, 25], [140, 154], [1]], ![[126, 147], [73], [131, 12], [52], [169, 156], [33, 27], [1]]]
 h' := ![![[71, 180], [8, 136], [49, 39], [175, 13], [156, 41], [139, 176], [54, 71], [0, 1]], ![[0, 1], [71, 45], [103, 142], [12, 168], [171, 140], [146, 5], [27, 110], [71, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [122, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [127, 110, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![798, 396, 140, -1093, 290]
  a := ![-1, -3, -3, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-152, 764, 140, -1093, 290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![201, 308, 20, 104, 136]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![201, 308, 20, 104, 136]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![118, 26, 1, 0, 0], ![19, 180, 0, 1, 0], ![112, 111, 0, 0, 1]] where
  M :=![![![201, 308, 20, 104, 136], ![1360, 1901, 132, 640, 760], ![7600, 11020, 741, 3720, 4600], ![3920, 5612, 380, 1889, 2312], ![8080, 11652, 788, 3928, 4833]]]
  hmulB := by decide  
  f := ![![![14221, 4412, 924, 1176, -2536]], ![![-25360, -7879, -1652, -2080, 4520]], ![![5878, 1822, 381, 488, -1048]], ![![-23701, -7364, -1544, -1943, 4224]], ![![-6608, -2057, -432, -536, 1177]]]
  g := ![![![-107, -188, 20, 104, 136], ![-616, -1111, 132, 640, 760], ![-3678, -6566, 741, 3720, 4600], ![-1855, -3320, 380, 1889, 2312], ![-3872, -6919, 788, 3928, 4833]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [57, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 180], [0, 1]]
 g := ![![[145, 101], [5], [63, 154], [100], [115, 38], [112, 101], [1]], ![[152, 80], [5], [45, 27], [100], [80, 143], [119, 80], [1]]]
 h' := ![![[61, 180], [13, 61], [29, 27], [165, 71], [142, 10], [132, 161], [124, 61], [0, 1]], ![[0, 1], [114, 120], [47, 154], [152, 110], [28, 171], [179, 20], [44, 120], [61, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [38, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [57, 120, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81626, 83850, -4928, -1355, 47110]
  a := ![3, 10, -28, -15, 70]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25345, -26372, -4928, -1355, 47110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16811, 7957, 1301, 2344, -4086]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![16811, 7957, 1301, 2344, -4086]] 
 ![![181, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![16811, 7957, 1301, 2344, -4086], ![-40860, -19286, -3161, -5678, 9978], ![99780, 47415, 7726, 13980, -24090], ![-3660, -1617, -281, -469, 990], ![57740, 27545, 4473, 8128, -13847]]]
  hmulB := by decide  
  f := ![![![-472009, -146591, -30587, -38946, 84078]], ![![-198762, -61730, -12881, -16400, 35406]], ![![-190810, -59255, -12364, -15750, 33990]], ![![-363331, -112838, -23542, -29977, 64716]], ![![-51742, -16069, -3353, -4270, 9217]]]
  g := ![![![-5233, 7957, 1301, 2344, -4086], ![12676, -19286, -3161, -5678, 9978], ![-31210, 47415, 7726, 13980, -24090], ![1047, -1617, -281, -469, 990], ![-18146, 27545, 4473, 8128, -13847]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-12909, -6113, -999, -1801, 3133]] ![![201, 308, 20, 104, 136]]
  ![![-246069, -207261, -20931, -66801, -19027]] where
 M := ![![![-246069, -207261, -20931, -66801, -19027]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-246069, -207261, -20931, -66801, -19027]] ![![16811, 7957, 1301, 2344, -4086]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![1389396001, 630739750, 106966656, 184105055, -361050655]]]
 hmul := by decide  
 g := ![![![![7676221, 3484750, 590976, 1017155, -1994755]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 22, 12, 19, -27]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![109, 22, 12, 19, -27]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![106, 31, 171, 1, 0], ![113, 21, 35, 0, 1]] where
  M :=![![![109, 22, 12, 19, -27], ![-270, -109, -62, -7, 87], ![870, 370, -1, -265, 45], ![180, 164, 152, 47, -198], ![180, 32, 6, -10, -11]]]
  hmulB := by decide  
  f := ![![![-61, -86, -6, -29, -33]], ![![-330, -483, -32, -163, -207]], ![![-2070, -2930, -201, -985, -1185]], ![![-1946, -2757, -189, -927, -1116]], ![![-463, -657, -45, -221, -266]]]
  g := ![![![6, 0, -12, 19, -27], ![-49, -9, -10, -7, 87], ![125, 40, 229, -265, 45], ![92, 15, -5, 47, -198], ![13, 3, 11, -10, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [146, 142, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 177, 89], [121, 13, 102], [0, 1]]
 g := ![![[98, 130, 48], [71, 61, 108], [22, 85, 90], [89, 18, 154], [19, 61, 97], [184, 138, 1], []], ![[131, 47, 1, 179], [35, 98, 84, 185], [39, 114, 68, 188], [57, 173, 127, 76], [96, 102, 6, 14], [23, 1, 4, 143], [187, 90]], ![[161, 72, 31, 32], [162, 88, 186, 67], [108, 182, 140, 3], [155, 168, 84, 125], [184, 74, 134, 67], [112, 116, 124, 128], [174, 90]]]
 h' := ![![[17, 177, 89], [139, 0, 95], [35, 164, 144], [185, 82, 89], [91, 143, 66], [67, 137, 111], [0, 0, 1], [0, 1]], ![[121, 13, 102], [180, 30, 89], [183, 142, 42], [11, 6, 51], [166, 150, 24], [170, 17, 75], [109, 131, 13], [17, 177, 89]], ![[0, 1], [77, 161, 7], [108, 76, 5], [133, 103, 51], [175, 89, 101], [39, 37, 5], [124, 60, 177], [121, 13, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155, 48], []]
 b := ![[], [107, 84, 169], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [146, 142, 53, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9241222, 10431570, 894718, 1460709, 3275351]
  a := ![1, 5, -13, -6, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2700045, -542580, -1903266, 1460709, 3275351]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -86, -6, -29, -33]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-61, -86, -6, -29, -33]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![158, 9, 1, 0, 0], ![87, 161, 0, 1, 0], ![24, 91, 0, 0, 1]] where
  M :=![![![-61, -86, -6, -29, -33], ![-330, -483, -32, -163, -207], ![-2070, -2930, -201, -985, -1185], ![-1020, -1468, -100, -495, -606], ![-2160, -3076, -210, -1036, -1255]]]
  hmulB := by decide  
  f := ![![![109, 22, 12, 19, -27]], ![![-270, -109, -62, -7, 87]], ![![82, 15, 7, 14, -18]], ![![-177, -81, -46, 3, 60]], ![![-114, -49, -28, -1, 38]]]
  g := ![![![22, 40, -6, -29, -33], ![125, 235, -32, -163, -207], ![753, 1389, -201, -985, -1185], ![379, 703, -100, -495, -606], ![792, 1465, -210, -1036, -1255]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [159, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 190], [0, 1]]
 g := ![![[184, 64], [97, 109], [35, 149], [63, 108], [8, 135], [151, 134], [1]], ![[173, 127], [129, 82], [84, 42], [128, 83], [137, 56], [122, 57], [1]]]
 h' := ![![[158, 190], [48, 8], [165, 142], [106, 63], [65, 47], [57, 138], [32, 158], [0, 1]], ![[0, 1], [166, 183], [63, 49], [128, 128], [42, 144], [87, 53], [166, 33], [158, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [91, 156]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [159, 33, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1947, 1543, 195, 28, 200]
  a := ![4, -1, 4, 3, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-189, -120, 195, 28, 200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![109, 22, 12, 19, -27]] ![![-61, -86, -6, -29, -33]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15027, 13441, 1653, 4304, -6200]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![15027, 13441, 1653, 4304, -6200]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![114, 147, 110, 1, 0], ![156, 141, 12, 0, 1]] where
  M :=![![![15027, 13441, 1653, 4304, -6200], ![-62000, -40604, -5671, -12574, 19624], ![196240, 112935, 16742, 34360, -55820], ![-24820, -9669, -1761, -2735, 5222], ![113020, 65137, 9649, 19822, -32175]]]
  hmulB := by decide  
  f := ![![![739, 369, -103, -378, 200]], ![![2000, 2046, 1703, 148, -2068]], ![![-20680, -12085, -466, 8610, -1180]], ![![-9838, -5131, 946, 4787, -2098]], ![![768, 1039, 1132, 340, -1423]]]
  g := ![![![2547, 1321, -2059, 4304, -6200], ![-8756, -4970, 5917, -12574, 19624], ![25840, 15195, -16026, 34360, -55820], ![-2734, -1782, 1225, -2735, 5222], ![14884, 8746, -9247, 19822, -32175]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [145, 27, 143, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 53, 26], [49, 139, 167], [0, 1]]
 g := ![![[189, 164, 8], [59, 2], [40, 1], [123, 145], [164, 128], [131, 184], [1]], ![[52, 98, 107, 74], [166, 185], [89, 81], [152, 85], [34, 175], [0, 166], [3, 178, 54, 13]], ![[56, 53, 4, 105], [165, 63], [70, 100], [150, 181], [55, 166], [34, 23], [116, 161, 41, 180]]]
 h' := ![![[1, 53, 26], [76, 183, 89], [116, 147, 141], [60, 5, 192], [116, 179, 96], [100, 1, 163], [48, 166, 50], [0, 1]], ![[49, 139, 167], [86, 114, 145], [80, 7, 68], [132, 145, 184], [39, 163, 49], [181, 120, 102], [145, 130, 72], [1, 53, 26]], ![[0, 1], [135, 89, 152], [163, 39, 177], [108, 43, 10], [7, 44, 48], [29, 72, 121], [83, 90, 71], [49, 139, 167]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 138], []]
 b := ![[], [144, 105, 158], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [145, 27, 143, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3763875176, -4640750652, -329073861, -1019532211, -1698445872]
  a := ![7, -44, 91, 25, -228]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1955545870, 1993323069, 684978341, -1019532211, -1698445872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10487, -4966, -812, -1463, 2555]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-10487, -4966, -812, -1463, 2555]] 
 ![![193, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![116, 0, 0, 0, 1]] where
  M :=![![![-10487, -4966, -812, -1463, 2555], ![25550, 12095, 1978, 3563, -6223], ![-62230, -29450, -4817, -8675, 15155], ![2380, 1124, 184, 331, -578], ![-35940, -17008, -2782, -5010, 8753]]]
  hmulB := by decide  
  f := ![![![-519, -358, -98, 187, 79]], ![![-47, -35, -14, 14, 14]], ![![-5, 0, 7, 10, -10]], ![![-388, -260, -60, 147, 42]], ![![-308, -212, -58, 112, 47]]]
  g := ![![![35, -4966, -812, -1463, 2555], ![-85, 12095, 1978, 3563, -6223], ![205, -29450, -4817, -8675, 15155], ![-8, 1124, 184, 331, -578], ![118, -17008, -2782, -5010, 8753]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1203, -349, -65, -120, 208]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-1203, -349, -65, -120, 208]] 
 ![![193, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![161, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![-1203, -349, -65, -120, 208], ![2080, 640, 219, 302, -512], ![-5120, -2155, -778, -160, 1300], ![260, 193, -147, -393, 290], ![-2380, -765, -173, -182, 439]]]
  hmulB := by decide  
  f := ![![![68989, 21875, 5115, 5762, -26128]], ![![12587, 3451, 922, 858, -5236]], ![![8659, 870, 603, 52, -4908]], ![![56433, 16736, 4160, 4299, -22378]], ![![27527, 6568, 1996, 1526, -12301]]]
  g := ![![![87, -349, -65, -120, 208], ![-187, 640, 219, 302, -512], ![103, -2155, -778, -160, 1300], ![189, 193, -147, -393, 290], ![135, -765, -173, -182, 439]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![15027, 13441, 1653, 4304, -6200]] ![![-10487, -4966, -812, -1463, 2555]]
  ![![316034731, 149551259, 24462209, 44052631, -76954455]] where
 M := ![![![316034731, 149551259, 24462209, 44052631, -76954455]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![316034731, 149551259, 24462209, 44052631, -76954455]] ![![-1203, -349, -65, -120, 208]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![235614207, 72940104, 15253562, 19385885, -41891615]]]
 hmul := by decide  
 g := ![![![![1220799, 377928, 79034, 100445, -217055]]]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0, 0, 0]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]] where
  M :=![![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 5 2 7 [134, 188, 125, 127, 35, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 106, 30, 173, 149], [185, 42, 75, 177, 26], [160, 82, 182, 158, 72], [172, 163, 107, 83, 147], [0, 1]]
 g := ![![[10, 31, 62, 58, 114], [97, 92, 57, 4], [162, 71, 148, 52, 161], [6, 71, 32, 39], [153, 165, 66, 161], [162, 1], []], ![[61, 157, 141, 73, 1, 168, 114, 192], [189, 188, 11, 97], [144, 132, 149, 55, 116, 88, 98, 89], [70, 49, 41, 172], [34, 16, 43, 97], [40, 153, 106, 155], [37, 104, 85, 153, 41, 4, 50, 122]], ![[137, 13, 176, 65, 57, 157, 170, 36], [112, 196, 144, 101], [115, 79, 98, 76, 178, 39, 160, 109], [74, 97, 30, 190], [38, 187, 70, 164], [149, 22, 139, 59], [164, 38, 39, 163, 47, 42, 93, 43]], ![[15, 180, 144, 178, 172, 31, 83, 108], [8, 119, 24, 85], [101, 95, 151, 25, 0, 67, 38, 27], [122, 161, 102, 43], [147, 30, 185, 133], [149, 65, 106, 138], [69, 48, 102, 156, 86, 174, 16, 130]], ![[178, 53, 148, 21, 26, 161, 31, 68], [16, 37, 177, 53], [188, 174, 113, 78, 25, 177, 144, 80], [104, 148, 71, 41], [28, 43, 170, 137], [150, 92, 140, 83], [106, 37, 109, 143, 38, 43, 4, 95]]]
 h' := ![![[39, 106, 30, 173, 149], [69, 106, 155, 97, 161], [159, 6, 107, 0, 2], [24, 77, 0, 101, 113], [51, 192, 124, 129, 165], [159, 142, 50, 183, 113], [0, 0, 0, 1], [0, 1]], ![[185, 42, 75, 177, 26], [87, 149, 112, 85, 28], [0, 154, 174, 99, 57], [192, 125, 4, 162, 100], [71, 8, 51, 25, 70], [80, 14, 62, 115, 140], [186, 33, 96, 19, 130], [39, 106, 30, 173, 149]], ![[160, 82, 182, 158, 72], [0, 141, 186, 88, 125], [6, 130, 20, 45, 135], [95, 183, 146, 58, 112], [113, 187, 103, 135, 105], [87, 65, 92, 13, 178], [133, 147, 51, 5, 181], [185, 42, 75, 177, 26]], ![[172, 163, 107, 83, 147], [101, 172, 163, 11, 10], [155, 142, 135, 181, 171], [146, 153, 68, 174, 5], [145, 46, 106, 8, 162], [52, 51, 146, 99, 112], [186, 3, 131, 91, 170], [160, 82, 182, 158, 72]], ![[0, 1], [74, 23, 172, 113, 70], [53, 159, 155, 69, 29], [60, 53, 176, 96, 64], [194, 158, 10, 97, 89], [20, 122, 44, 181, 48], [115, 14, 116, 81, 110], [172, 163, 107, 83, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 135, 40, 108], [], [], []]
 b := ![[], [81, 26, 126, 21, 150], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 5
  hpos := by decide
  P := [134, 188, 125, 127, 35, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53980207024490, -77436199313178, -6648374390738, -26179411777458, -29519114407374]
  a := ![1, -9, 23, 9, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-274011203170, -393077153874, -33748093354, -132890415114, -149843220342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 296709280757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀



lemma PB1321I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB1321I4 : PrimesBelowBoundCertificateInterval O 151 197 1321 where
  m := 9
  g := ![1, 2, 2, 3, 2, 3, 2, 3, 1]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1321I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
    · exact ![I197N0]
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
    · exact ![4330747, 26569]
    · exact ![777796321, 167]
    · exact ![5177717, 173, 173]
    · exact ![5735339, 32041]
    · exact ![32761, 32761, 181]
    · exact ![6967871, 36481]
    · exact ![7189057, 193, 193]
    · exact ![296709280757]
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
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
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
  β := ![I167N1, I173N1, I173N2, I181N2, I193N1, I193N2]
  Il := ![[], [], [I167N1], [I173N1, I173N2], [], [I181N2], [], [I193N1, I193N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
