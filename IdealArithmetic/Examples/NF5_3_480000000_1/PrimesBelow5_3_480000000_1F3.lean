
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9613, -1106, 7166, 1008, -1648]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-9613, -1106, 7166, 1008, -1648]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![23, 65, 57, 1, 0], ![61, 39, 0, 0, 1]] where
  M :=![![![-9613, -1106, 7166, 1008, -1648], ![-13184, -11695, -4228, 1788, 1376], ![5504, -6160, -13483, -306, 3370], ![20072, 10436, -3740, -2429, 538], ![7400, 2624, -3068, -846, 635]]]
  hmulB := by decide  
  f := ![![![-23, -142, 82, -84, -116]], ![![-928, -437, -116, -564, -368]], ![![-1472, -1160, 127, -1122, -1030]], ![![-1387, -937, 15, -983, -816]], ![![-425, -291, 6, -306, -245]]]
  g := ![![![633, -22, -470, 1008, -1648], ![-1292, -1697, -992, 1788, 1376], ![-1804, -1100, 37, -306, 3370], ![403, 1377, 1259, -2429, 538], ![-111, 307, 422, -846, 635]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [11, 17, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 100, 104], [53, 6, 3], [0, 1]]
 g := ![![[11, 25, 42], [73, 96, 44], [52, 40], [32, 55, 12], [106, 23], [1]], ![[43, 74, 47, 66], [95, 103, 70, 7], [14, 34], [64, 94, 38, 103], [16, 12], [24, 101, 42, 80]], ![[57, 78, 13, 39], [106, 85, 74, 25], [21, 49], [15, 87, 94, 16], [37, 9], [26, 103, 38, 27]]]
 h' := ![![[93, 100, 104], [53, 80, 16], [68, 27, 77], [76, 11, 19], [25, 31, 71], [96, 90, 39], [0, 1]], ![[53, 6, 3], [97, 26, 70], [22, 23, 60], [47, 17, 81], [75, 16, 12], [95, 36, 71], [93, 100, 104]], ![[0, 1], [64, 1, 21], [106, 57, 77], [4, 79, 7], [82, 60, 24], [75, 88, 104], [53, 6, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 17], []]
 b := ![[], [62, 28, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [11, 17, 68, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-565125, -397661, 35907, -366121, -477386]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![345572, 392694, 195372, -366121, -477386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -142, 82, -84, -116]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-23, -142, 82, -84, -116]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![46, 50, 1, 0, 0], ![54, 38, 0, 1, 0], ![96, 81, 0, 0, 1]] where
  M :=![![![-23, -142, 82, -84, -116], ![-928, -437, -116, -564, -368], ![-1472, -1160, 127, -1122, -1030], ![-3656, -2468, 20, -2635, -2014], ![-7880, -5432, 164, -5622, -4787]]]
  hmulB := by decide  
  f := ![![![-9613, -1106, 7166, 1008, -1648]], ![![-13184, -11695, -4228, 1788, 1376]], ![![-10242, -5998, 979, 1266, -34]], ![![-9346, -4614, 2080, 1121, -338]], ![![-18536, -9821, 3200, 2250, -431]]]
  g := ![![![111, 78, 82, -84, -116], ![656, 529, -116, -564, -368], ![1422, 1108, 127, -1122, -1030], ![3094, 2428, 20, -2635, -2014], ![6988, 5493, 164, -5622, -4787]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [69, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 106], [0, 1]]
 g := ![![[51, 76], [49, 92], [11], [3, 100], [61], [12, 1]], ![[0, 31], [83, 15], [11], [26, 7], [61], [24, 106]]]
 h' := ![![[12, 106], [43, 41], [39, 29], [7, 92], [106, 10], [28, 75], [0, 1]], ![[0, 1], [0, 66], [66, 78], [41, 15], [12, 97], [72, 32], [12, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [68, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [69, 95, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![136027, 99844, -17532, 72971, 159781]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-171373, -137745, -17532, 72971, 159781]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-9613, -1106, 7166, 1008, -1648]] ![![-23, -142, 82, -84, -116]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17971, 5508, -8645, -2021, 1852]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![17971, 5508, -8645, -2021, 1852]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![103, 76, 38, 1, 0], ![41, 36, 81, 0, 1]] where
  M :=![![![17971, 5508, -8645, -2021, 1852], ![14816, 20607, 15058, -2305, -4211], ![-16844, 5562, 22912, 1472, -5563], ![-29660, -21913, -3439, 3858, 1532], ![-12092, -6493, 1967, 1495, -233]]]
  hmulB := by decide  
  f := ![![![59047, -19199, 37321, 9635, -11390]], ![![-91120, 29783, -57668, -14723, 17515]], ![![70060, -23245, 44506, 10996, -13327]], ![![16617, -5447, 10524, 2670, -3187]], ![![44331, -14722, 28168, 6945, -8427]]]
  g := ![![![1378, 848, -751, -2021, 1852], ![3898, 3187, 4071, -2305, -4211], ![547, 862, 3831, 1472, -5563], ![-4494, -3397, -2515, 3858, 1532], ![-1436, -1025, -330, 1495, -233]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [7, 31, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 64, 58], [73, 44, 51], [0, 1]]
 g := ![![[2, 71, 63], [33, 22], [50, 51, 63], [71, 40, 61], [71, 102], [1]], ![[31, 95, 15, 24], [25, 21], [73, 34, 3, 52], [97, 33, 44, 42], [28, 26], [16, 82, 72, 2]], ![[97, 90, 69, 54], [25, 4], [50, 8, 40, 53], [71, 82, 91, 2], [42, 7], [47, 35, 82, 107]]]
 h' := ![![[95, 64, 58], [80, 72, 64], [86, 70, 26], [48, 61, 45], [97, 26, 72], [102, 78, 59], [0, 1]], ![[73, 44, 51], [74, 103, 16], [24, 10, 81], [45, 16, 68], [70, 43, 98], [87, 47, 35], [95, 64, 58]], ![[0, 1], [27, 43, 29], [86, 29, 2], [0, 32, 105], [69, 40, 48], [103, 93, 15], [73, 44, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 9], []]
 b := ![[], [40, 75, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [7, 31, 50, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-531463, -366961, 18182, -366678, -365514]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![479105, 373019, 399620, -366678, -365514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59047, -19199, 37321, 9635, -11390]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![59047, -19199, 37321, 9635, -11390]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![2, 71, 1, 0, 0], ![76, 29, 0, 1, 0], ![97, 90, 0, 0, 1]] where
  M :=![![![59047, -19199, 37321, 9635, -11390], ![-91120, 29783, -57668, -14723, 17515], ![70060, -23245, 44506, 10996, -13327], ![-7748, 3576, -5407, -275, 1073], ![16612, -6882, 11213, 1322, -2606]]]
  hmulB := by decide  
  f := ![![![17971, 5508, -8645, -2021, 1852]], ![![14816, 20607, 15058, -2305, -4211]], ![![9826, 13575, 9860, -1525, -2760]], ![![16200, 9122, -2053, -1987, 185]], ![![28115, 21857, 4758, -3688, -1831]]]
  g := ![![![3275, -17645, 37321, 9635, -11390], ![-5099, 27292, -57668, -14723, 17515], ![4019, -21125, 44506, 10996, -13327], ![-735, 2742, -5407, -275, 1073], ![1344, -5567, 11213, 1322, -2606]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [68, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 108], [0, 1]]
 g := ![![[97, 43], [9], [97, 75], [27, 45], [38], [53, 1]], ![[87, 66], [9], [39, 34], [14, 64], [38], [106, 108]]]
 h' := ![![[53, 108], [17, 32], [53, 3], [17, 27], [81, 46], [102, 16], [0, 1]], ![[0, 1], [78, 77], [103, 106], [31, 82], [12, 63], [78, 93], [53, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [49, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [68, 56, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12013, 10010, -4729, 1514, 33696]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30845, -25053, -4729, 1514, 33696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![17971, 5508, -8645, -2021, 1852]] ![![59047, -19199, 37321, 9635, -11390]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [27, 74, 32, 43, 68, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 97, 42, 111, 72], [25, 75, 45, 35, 81], [77, 64, 71, 60, 103], [102, 102, 68, 20, 83], [0, 1]]
 g := ![![[31, 112, 55, 12, 97], [56, 38, 15, 77], [54, 43, 99, 36], [0, 37, 20, 56], [61, 45, 1], []], ![[80, 75, 11, 44, 70, 36, 8, 109], [65, 68, 11, 91], [2, 34, 92, 100], [71, 35, 7, 11], [12, 55, 40, 111, 28, 6, 17, 56], [23, 85, 18, 73, 73, 39, 37, 9]], ![[36, 111, 61, 94, 56, 48, 40, 16], [41, 100, 79, 60], [10, 80, 32, 31], [21, 36, 87, 8], [90, 46, 32, 22, 90, 111, 95, 1], [49, 56, 37, 110, 30, 49, 34, 2]], ![[39, 93, 108, 5, 22, 75, 110, 80], [96, 99, 88, 72], [79, 89, 106, 51], [41, 74, 40, 91], [19, 64, 110, 93, 104, 109, 47, 37], [18, 5, 13, 31, 88, 7, 7, 17]], ![[80, 31, 75, 82, 22, 10, 102, 32], [26, 53, 101, 106], [58, 106, 19, 1], [73, 99, 100, 91], [112, 17, 112, 19, 72, 94, 9, 11], [65, 71, 33, 63, 112, 45, 75, 7]]]
 h' := ![![[67, 97, 42, 111, 72], [68, 67, 72, 40, 60], [26, 29, 12, 38, 23], [44, 5, 104, 71, 6], [48, 34, 2, 44, 100], [0, 0, 0, 1], [0, 1]], ![[25, 75, 45, 35, 81], [110, 100, 21, 40, 42], [31, 76, 85, 71, 54], [56, 101, 80, 96, 10], [39, 46, 43, 84, 24], [14, 90, 36, 78, 27], [67, 97, 42, 111, 72]], ![[77, 64, 71, 60, 103], [86, 53, 73, 1, 13], [17, 14, 96, 14, 88], [93, 91, 92, 108, 12], [78, 74, 7, 110, 102], [64, 0, 79, 26, 25], [25, 75, 45, 35, 81]], ![[102, 102, 68, 20, 83], [69, 33, 102, 46, 61], [66, 100, 80, 31, 33], [39, 94, 21, 51, 86], [109, 9, 41, 93, 59], [92, 8, 75, 25, 95], [77, 64, 71, 60, 103]], ![[0, 1], [104, 86, 71, 99, 50], [44, 7, 66, 72, 28], [64, 48, 42, 13, 112], [112, 63, 20, 8, 54], [78, 15, 36, 96, 79], [102, 102, 68, 20, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 112, 12, 7], [], [], []]
 b := ![[], [49, 86, 31, 57, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [27, 74, 32, 43, 68, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1117872466761, 610740810316, 308609377946, 1270538396060, -1135634985012]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9892676697, 5404785932, 2731056442, 11243702620, -10049867124]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24825, 8062, -15687, -4062, 4799]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-24825, 8062, -15687, -4062, 4799]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![101, 73, 73, 94, 1]] where
  M :=![![![-24825, 8062, -15687, -4062, 4799], ![38392, -12455, 24248, 6281, -7387], ![-29548, 9712, -18736, -4747, 5728], ![3716, -1221, 2335, 545, -563], ![-7164, 2813, -4807, -828, 1526]]]
  hmulB := by decide  
  f := ![![![-87, 119, 243, 4, -61]], ![![-488, -153, 230, 55, -49]], ![![-196, -279, -208, 31, 58]], ![![476, 4, -425, -48, 100]], ![![-109, -151, -110, 17, 31]]]
  g := ![![![-4012, -2695, -2882, -3584, 4799], ![6177, 4148, 4437, 5517, -7387], ![-4788, -3216, -3440, -4277, 5728], ![477, 314, 342, 421, -563], ![-1270, -855, -915, -1136, 1526]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [52, 37, 30, 91, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 44, 18, 114], [125, 18, 17, 13], [88, 64, 92], [0, 1]]
 g := ![![[84, 101, 59, 87], [19, 37], [99, 121, 49, 99], [123, 17, 98, 61], [9, 123, 36, 1], []], ![[0, 59, 104, 97, 90, 56], [118, 78, 31, 106, 19, 96], [83, 66, 86, 99, 121, 111], [96, 82, 39, 15, 63, 83], [32, 91, 57, 38, 107, 24], [60, 48, 55, 32, 11, 89]], ![[47, 50, 11, 58, 21, 26], [123, 95, 81, 80, 119, 71], [2, 26, 49, 30, 57, 38], [74, 10, 70, 119, 120, 16], [42, 85, 119, 14, 124, 19], [121, 72, 88, 75, 81, 38]], ![[72, 50, 87, 44, 67], [34, 47, 123, 75, 108], [86, 41, 46, 59, 48], [106, 68, 18, 82, 27], [38, 97, 92, 59, 125], [33, 54, 51]]]
 h' := ![![[77, 44, 18, 114], [28, 92, 32, 77], [59, 35, 52], [81, 102, 16, 37], [40, 2, 38, 76], [0, 0, 0, 1], [0, 1]], ![[125, 18, 17, 13], [76, 109, 30, 5], [79, 98, 12, 76], [1, 50, 64, 30], [80, 78, 57, 58], [23, 37, 89, 89], [77, 44, 18, 114]], ![[88, 64, 92], [2, 46, 38, 111], [22, 70, 62, 5], [8, 21, 74, 114], [55, 75, 71, 97], [50, 123, 90, 23], [125, 18, 17, 13]], ![[0, 1], [44, 7, 27, 61], [76, 51, 1, 46], [113, 81, 100, 73], [10, 99, 88, 23], [52, 94, 75, 14], [88, 64, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [105, 22, 65], []]
 b := ![[], [], [126, 93, 9, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [52, 37, 30, 91, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6096166604, -3564290284, -1186254400, -6210456126, 3457227918]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2797450286, -2015290774, -1996566082, -2607794334, 3457227918]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, -119, -243, -4, 61]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![87, -119, -243, -4, 61]] 
 ![![127, 0, 0, 0, 0], ![98, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![87, -119, -243, -4, 61], ![488, 153, -230, -55, 49], ![196, 279, 208, -31, -58], ![-476, -4, 425, 48, -100], ![-132, 36, 169, 11, -41]]]
  hmulB := by decide  
  f := ![![![24825, -8062, 15687, 4062, -4799]], ![![18854, -6123, 11914, 3085, -3645]], ![![4924, -1600, 3112, 805, -952]], ![![8767, -2847, 5540, 1435, -1696]], ![![6507, -2117, 4114, 1062, -1259]]]
  g := ![![![124, -119, -243, -4, 61], ![-64, 153, -230, -55, 49], ![-227, 279, 208, -31, -58], ![-72, -4, 425, 48, -100], ![-54, 36, 169, 11, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-24825, 8062, -15687, -4062, 4799]] ![![87, -119, -243, -4, 61]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [60, 1, 21, 102, 89, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 64, 78, 93, 62], [69, 62, 121, 7, 128], [129, 97, 74, 68, 108], [45, 38, 120, 94, 95], [0, 1]]
 g := ![![[23, 76, 81, 113, 25], [92, 103, 42, 108, 45], [90, 60, 65, 61], [51, 48, 35, 62], [130, 90, 42, 1], [], []], ![[97, 122, 8, 101, 24, 75, 25, 13], [75, 42, 93, 78, 115, 14, 17, 3], [82, 11, 31, 125], [43, 3, 2, 33], [69, 106, 3, 74], [128, 50, 103, 123], [84, 7, 60, 45]], ![[105, 97, 34, 101, 63, 118, 49, 127], [105, 14, 48, 45, 9, 19, 41, 88], [89, 75, 75, 105], [1, 107, 108, 28], [82, 34, 33, 117], [19, 36, 71, 36], [15, 72, 74, 9]], ![[76, 34, 115, 33, 70, 75, 90, 121], [3, 28, 110, 43, 90, 72, 108, 94], [109, 78, 64, 80], [126, 9, 106, 112], [59, 31, 17, 27], [123, 16, 40, 43], [113, 115, 95, 5]], ![[41, 31, 96, 122, 8, 15, 112, 106], [95, 36, 94, 49, 110, 107, 110, 119], [128, 63, 56, 53], [108, 92, 89, 15], [12, 25, 104, 49], [89, 76, 111, 107], [66, 129, 111, 117]]]
 h' := ![![[61, 64, 78, 93, 62], [113, 62, 37, 129, 5], [96, 13, 40, 30, 62], [16, 128, 106, 50, 89], [60, 103, 31, 75, 113], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[69, 62, 121, 7, 128], [62, 15, 47, 76, 43], [99, 99, 122, 85, 104], [98, 21, 2, 103, 16], [53, 116, 36, 57, 66], [130, 68, 51, 123, 104], [122, 99, 119, 30, 75], [61, 64, 78, 93, 62]], ![[129, 97, 74, 68, 108], [94, 2, 94, 92, 69], [7, 91, 82, 0, 53], [99, 107, 124, 124, 57], [40, 3, 30, 33, 91], [84, 107, 111, 25, 36], [62, 29, 126, 0, 6], [69, 62, 121, 7, 128]], ![[45, 38, 120, 94, 95], [120, 71, 93, 62, 35], [51, 123, 40, 19, 12], [98, 1, 84, 35, 39], [86, 61, 112, 117, 80], [73, 1, 64, 29, 114], [36, 66, 8, 10, 82], [129, 97, 74, 68, 108]], ![[0, 1], [50, 112, 122, 34, 110], [102, 67, 109, 128, 31], [70, 5, 77, 81, 61], [0, 110, 53, 111, 43], [14, 86, 36, 85, 7], [30, 68, 8, 91, 99], [45, 38, 120, 94, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113, 75, 62, 26], [], [], []]
 b := ![[], [80, 20, 68, 125, 101], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [60, 1, 21, 102, 89, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![92268407690, 24191387611, 81252816548, 185737353483, -401302015091]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![704338990, 184667081, 620250508, 1417842393, -3063374161]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -12, 4, 2, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-23, -12, 4, 2, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![10, 10, 1, 0, 0], ![37, 111, 0, 1, 0], ![101, 92, 0, 0, 1]] where
  M :=![![![-23, -12, 4, 2, 0], ![0, -21, -28, 6, 6], ![24, -2, -27, -10, 12], ![48, 44, 22, 17, -12], ![0, 4, -2, -18, 19]]]
  hmulB := by decide  
  f := ![![![1985, -644, 1256, 326, -384]], ![![-3072, 995, -1940, -502, 594]], ![![-62, 20, -39, -10, 12]], ![![-1955, 633, -1234, -319, 378]], ![![-595, 192, -374, -96, 115]]]
  g := ![![![-1, -2, 4, 2, 0], ![-4, -7, -28, 6, 6], ![-4, 2, -27, -10, 12], ![3, -7, 22, 17, -12], ![-9, 2, -2, -18, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [41, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 136], [0, 1]]
 g := ![![[116, 74], [98], [73], [25, 135], [72], [14], [1]], ![[125, 63], [98], [73], [84, 2], [72], [14], [1]]]
 h' := ![![[39, 136], [4, 99], [130, 80], [71, 22], [46, 86], [11, 88], [96, 39], [0, 1]], ![[0, 1], [29, 38], [99, 57], [107, 115], [112, 51], [18, 49], [110, 98], [39, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [134, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [41, 98, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56, -186, -25, -336, 144]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14, 176, -25, -336, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11015, 6498, 2102, 11240, -6166]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![11015, 6498, 2102, 11240, -6166]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![94, 11, 1, 0, 0], ![62, 132, 0, 1, 0], ![77, 17, 0, 0, 1]] where
  M :=![![![11015, 6498, 2102, 11240, -6166], ![-49328, -28953, -9484, -50198, 27554], ![110216, 64578, 21245, 112054, -61520], ![-221416, -129620, -42734, -225003, 123544], ![312680, 183052, 60346, 317750, -174469]]]
  hmulB := by decide  
  f := ![![![-1457, -182, 1066, 140, -254]], ![![-2032, -1801, -644, 214, 166]], ![![-1158, -277, 665, 112, -158]], ![![-2598, -1808, -142, 265, 44]], ![![-1069, -327, 516, 100, -125]]]
  g := ![![![-2983, -10186, 2102, 11240, -6166], ![13378, 45497, -9484, -50198, 27554], ![-29906, -101565, 21245, 112054, -61520], ![60094, 203946, -42734, -225003, 123544], ![-84863, -288013, 60346, 317750, -174469]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [49, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 136], [0, 1]]
 g := ![![[64, 14], [39], [36], [118, 28], [32], [88], [1]], ![[0, 123], [39], [36], [127, 109], [32], [88], [1]]]
 h' := ![![[15, 136], [37, 98], [116, 54], [109, 131], [125, 24], [7, 124], [88, 15], [0, 1]], ![[0, 1], [0, 39], [104, 83], [19, 6], [74, 113], [86, 13], [39, 122], [15, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [95, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [49, 122, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-920, -1337, 687, -2513, 1107]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![37, 2219, 687, -2513, 1107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-801, -547, 11, -572, -467]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-801, -547, 11, -572, -467]] 
 ![![137, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![134, 0, 0, 0, 1]] where
  M :=![![![-801, -547, 11, -572, -467], ![-3736, -2553, 50, -2675, -2183], ![-8732, -5963, 122, -6253, -5104], ![-18548, -12662, 265, -13278, -10840], ![-42156, -28782, 597, -30177, -24635]]]
  hmulB := by decide  
  f := ![![![-2169, -704, -665, -1672, 977]], ![![-1447, -461, -447, -1107, 648]], ![![-1337, -460, -399, -1055, 613]], ![![-1847, -541, -592, -1369, 808]], ![![-2442, -875, -713, -1960, 1134]]]
  g := ![![![1371, -547, 11, -572, -467], ![6408, -2553, 50, -2675, -2183], ![14974, -5963, 122, -6253, -5104], ![31795, -12662, 265, -13278, -10840], ![72266, -28782, 597, -30177, -24635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-23, -12, 4, 2, 0]] ![![11015, 6498, 2102, 11240, -6166]]
  ![![336623, 197054, 64974, 342066, -187822]] where
 M := ![![![336623, 197054, 64974, 342066, -187822]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![336623, 197054, 64974, 342066, -187822]] ![![-801, -547, 11, -572, -467]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![2329, 1507, 137, 1918, 411]]]
 hmul := by decide  
 g := ![![![![17, 11, 1, 14, 3]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29075, 16855, 49567, 2243, -12200]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-29075, 16855, 49567, 2243, -12200]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![83, 94, 105, 1, 0], ![102, 93, 114, 0, 1]] where
  M :=![![![-29075, 16855, 49567, 2243, -12200], ![-97600, -42751, 29224, 11491, -5471], ![-21884, -53611, -54242, 4330, 14501], ![106804, 17400, -72553, -11399, 16481], ![32428, -1506, -31405, -3196, 7432]]]
  hmulB := by decide  
  f := ![![![30415, -9744, 19135, 5053, -5786]], ![![-46288, 15567, -29594, -7285, 9373]], ![![37492, -10866, 22852, 6854, -6241]], ![![15167, -3475, 8654, 3277, -1813]], ![![22210, -5638, 13025, 4498, -3080]]]
  g := ![![![7404, 6767, 8668, 2243, -12200], ![-3549, -4418, -3983, 11491, -5471], ![-13384, -13016, -15554, 4330, 14501], ![-4519, -3193, -5428, -11399, 16481], ![-3312, -2822, -3907, -3196, 7432]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [36, 96, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 92, 37], [129, 46, 102], [0, 1]]
 g := ![![[9, 133, 57], [1, 82, 41], [78, 106], [80, 95, 79], [62, 46], [83, 1], []], ![[1, 45, 39, 37], [115, 88, 119, 107], [129, 20], [118, 35, 38, 51], [13, 41], [125, 31], [61, 118]], ![[83, 50, 83, 2], [61, 14, 60, 73], [95, 127], [102, 103, 111, 95], [83, 38], [37, 124], [135, 118]]]
 h' := ![![[93, 92, 37], [103, 55, 125], [103, 136, 67], [39, 54, 84], [27, 95, 45], [70, 58, 121], [0, 0, 1], [0, 1]], ![[129, 46, 102], [83, 78, 1], [24, 135, 52], [9, 110, 24], [119, 91, 25], [93, 122, 67], [59, 58, 46], [93, 92, 37]], ![[0, 1], [29, 6, 13], [79, 7, 20], [118, 114, 31], [49, 92, 69], [102, 98, 90], [105, 81, 92], [129, 46, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 58], []]
 b := ![[], [118, 100, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [36, 96, 56, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-559279, -235187, -308051, -858160, 1416170]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-530801, -368863, -515429, -858160, 1416170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30415, -9744, 19135, 5053, -5786]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![30415, -9744, 19135, 5053, -5786]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![30, 34, 1, 0, 0], ![92, 41, 0, 1, 0], ![111, 64, 0, 0, 1]] where
  M :=![![![30415, -9744, 19135, 5053, -5786], ![-46288, 15567, -29594, -7285, 9373], ![37492, -10866, 22852, 6854, -6241], ![-1820, 3359, -2923, 1224, 2474], ![15556, 1199, 5819, 5965, 1837]]]
  hmulB := by decide  
  f := ![![![-29075, 16855, 49567, 2243, -12200]], ![![-97600, -42751, 29224, 11491, -5471]], ![![-30306, -7205, 17456, 3326, -3867]], ![![-47264, -1329, 40905, 4792, -9570]], ![![-67923, -6235, 52812, 7059, -12208]]]
  g := ![![![-2635, -3577, 19135, 5053, -5786], ![3391, 5184, -29594, -7285, 9373], ![-4215, -4816, 22852, 6854, -6241], ![-2168, -761, -2923, 1224, 2474], ![-6559, -4020, 5819, 5965, 1837]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [66, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 138], [0, 1]]
 g := ![![[53, 99], [62, 45], [49], [106, 124], [42], [112], [1]], ![[0, 40], [0, 94], [49], [34, 15], [42], [112], [1]]]
 h' := ![![[116, 138], [78, 88], [133, 36], [93, 7], [75, 92], [22, 43], [73, 116], [0, 1]], ![[0, 1], [0, 51], [0, 103], [71, 132], [44, 47], [6, 96], [46, 23], [116, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [98, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [66, 23, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![126, 4, -42, 1, 63]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41, -19, -42, 1, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-29075, 16855, 49567, 2243, -12200]] ![![30415, -9744, 19135, 5053, -5786]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -12, 28, 22, 2]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![51, -12, 28, 22, 2]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![134, 143, 27, 1, 0], ![116, 60, 15, 0, 1]] where
  M :=![![![51, -12, 28, 22, 2], ![16, 67, -68, 48, 68], ![272, 120, 19, 146, 106], ![416, 304, 8, 293, 238], ![960, 644, 0, 674, 545]]]
  hmulB := by decide  
  f := ![![![87, 52, 20, 90, -50]], ![![-400, -233, -76, -400, 220]], ![![880, 512, 167, 894, -490]], ![![-158, -91, -27, -153, 84]], ![![12, 8, 5, 16, -9]]]
  g := ![![![-21, -22, -4, 22, 2], ![-96, -73, -16, 48, 68], ![-212, -182, -37, 146, 106], ![-446, -375, -77, 293, 238], ![-1024, -862, -177, 674, 545]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [60, 43, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 48, 43], [12, 100, 106], [0, 1]]
 g := ![![[29, 43, 116], [45, 129], [56, 92, 85], [118, 123], [36, 98, 63], [60, 1], []], ![[77, 16, 18, 77], [32, 132], [51, 6, 54, 90], [9, 26], [89, 63, 106, 147], [90, 17], [40, 61]], ![[49, 46, 34, 74], [104, 30], [141, 140, 64, 12], [99, 53], [32, 119, 61, 147], [27, 69], [126, 61]]]
 h' := ![![[48, 48, 43], [1, 129, 50], [67, 2, 125], [35, 64, 54], [75, 2, 47], [125, 42, 130], [0, 0, 1], [0, 1]], ![[12, 100, 106], [52, 74, 117], [83, 148, 70], [9, 124, 106], [129, 19, 18], [91, 145, 55], [53, 122, 100], [48, 48, 43]], ![[0, 1], [120, 95, 131], [20, 148, 103], [106, 110, 138], [58, 128, 84], [132, 111, 113], [34, 27, 48], [12, 100, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 120], []]
 b := ![[], [16, 104, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [60, 43, 89, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23879, -85886, -70960, 9930, 19910]
  a := ![7, -1, -26, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24591, -18124, -4280, 9930, 19910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 30, 17, -4, -5]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![27, 30, 17, -4, -5]] 
 ![![149, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![27, 30, 17, -4, -5], ![-40, 23, 68, 3, -17], ![-68, -30, 20, 7, -4], ![4, -49, -71, 1, 17], ![-12, -23, -21, -2, 4]]]
  hmulB := by decide  
  f := ![![![-13185, 4271, -8327, -2166, 2549]], ![![-1102, 357, -696, -181, 213]], ![![-4619, 1496, -2917, -759, 893]], ![![-7331, 2375, -4630, -1204, 1417]], ![![-11178, 3620, -7059, -1837, 2161]]]
  g := ![![![-2, 30, 17, -4, -5], ![-13, 23, 68, 3, -17], ![-5, -30, 20, 7, -4], ![14, -49, -71, 1, 17], ![7, -23, -21, -2, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, -85, 69, -52, 15]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![59, -85, 69, -52, 15]] 
 ![![149, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![72, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![59, -85, 69, -52, 15], ![120, 255, -66, 295, -141], ![-564, -473, -40, -707, 372], ![1428, 854, 267, 1468, -804], ![-2004, -1210, -369, -2071, 1133]]]
  hmulB := by decide  
  f := ![![![-17, 710, 993, 26, -219]], ![![-21, 385, 549, 17, -120]], ![![-12, 338, 476, 17, -102]], ![![10, 471, 639, 23, -135]], ![![14, 461, 621, 32, -124]]]
  g := ![![![38, -85, 69, -52, 15], ![-211, 255, -66, 295, -141], ![503, -473, -40, -707, 372], ![-1042, 854, 267, 1468, -804], ![1470, -1210, -369, -2071, 1133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![51, -12, 28, 22, 2]] ![![27, 30, 17, -4, -5]]
  ![![17, -710, -993, -26, 219]] where
 M := ![![![17, -710, -993, -26, 219]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![17, -710, -993, -26, 219]] ![![59, -85, 69, -52, 15]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181199, 59084, -114609, -29411, 34888]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-181199, 59084, -114609, -29411, 34888]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![32, 66, 58, 1, 0], ![82, 117, 85, 0, 1]] where
  M :=![![![-181199, 59084, -114609, -29411, 34888], ![279104, -91957, 176990, 44409, -53345], ![-213380, 72480, -136366, -31922, 39941], ![20212, -13081, 15907, -2816, -1240], ![-45788, 24219, -33455, 1233, 5203]]]
  hmulB := by decide  
  f := ![![![-28481, -16989, 2295, 3533, 16]], ![![128, -29639, -41044, 1169, 10615]], ![![42460, 5495, -30808, -4476, 7061]], ![![10516, -14176, -29085, -489, 7299]], ![![8634, -29004, -47859, 291, 12196]]]
  g := ![![![-13913, -13786, -9101, -29411, 34888], ![21406, 21314, 14143, 44409, -53345], ![-16338, -16515, -11125, -31922, 39941], ![1404, 2105, 1885, -2816, -1240], ![-3390, -4410, -3624, 1233, 5203]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [106, 123, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 28, 48], [0, 122, 103], [0, 1]]
 g := ![![[62, 131, 121], [34, 16, 5], [134, 1, 47], [94, 19], [39, 34, 44], [72, 1], []], ![[108, 80, 24, 134], [85, 40, 108, 48], [44, 144, 5, 57], [55, 55], [6, 32, 13, 134], [134, 86], [60, 39]], ![[0, 96, 114, 124], [89, 124, 3, 19], [10, 130, 117, 148], [40, 32], [21, 5, 61, 121], [92, 29], [5, 39]]]
 h' := ![![[72, 28, 48], [20, 111, 11], [141, 80, 96], [80, 26, 54], [94, 135, 87], [69, 98, 78], [0, 0, 1], [0, 1]], ![[0, 122, 103], [59, 81, 26], [64, 10, 150], [56, 21, 135], [65, 32, 31], [108, 45, 26], [32, 68, 122], [72, 28, 48]], ![[0, 1], [79, 110, 114], [148, 61, 56], [150, 104, 113], [39, 135, 33], [103, 8, 47], [74, 83, 28], [0, 122, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 134], []]
 b := ![[], [77, 121, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [106, 123, 79, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1581, -2106, -3518, -1093, 1431]
  a := ![1, 0, -5, -1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-535, -645, -409, -1093, 1431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, -31, -259, -23, 62]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![239, -31, -259, -23, 62]] 
 ![![151, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![109, 0, 0, 1, 0], ![150, 0, 0, 0, 1]] where
  M :=![![![239, -31, -259, -23, 62], ![496, 313, -16, -61, -7], ![-28, 253, 374, -10, -95], ![-628, -216, 271, 77, -59], ![-220, -42, 139, 16, -28]]]
  hmulB := by decide  
  f := ![![![69905, -22722, 44189, 11435, -13552]], ![![16874, -5487, 10668, 2759, -3273]], ![![15827, -5148, 10007, 2587, -3071]], ![![50383, -16385, 31854, 8237, -9774]], ![![69566, -22631, 43987, 11369, -13501]]]
  g := ![![![21, -31, -259, -23, 62], ![-21, 313, -16, -61, -7], ![-44, 253, 374, -10, -95], ![-6, -216, 271, 77, -59], ![-5, -42, 139, 16, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 36, 22, -4, -6]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![31, 36, 22, -4, -6]] 
 ![![151, 0, 0, 0, 0], ![148, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![140, 0, 0, 0, 1]] where
  M :=![![![31, 36, 22, -4, -6], ![-48, 27, 80, 6, -18], ![-72, -32, 21, 14, 0], ![24, -46, -86, 11, 30], ![24, -2, -26, 24, 25]]]
  hmulB := by decide  
  f := ![![![-2903, -1864, -482, -3104, 1686]], ![![-2756, -1773, -456, -2950, 1602]], ![![-1567, -996, -265, -1666, 906]], ![![-1668, -1094, -266, -1805, 978]], ![![-3268, -2066, -558, -3464, 1885]]]
  g := ![![![-37, 36, 22, -4, -6], ![-52, 27, 80, 6, -18], ![11, -32, 21, 14, 0], ![50, -46, -86, 11, 30], ![-26, -2, -26, 24, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-181199, 59084, -114609, -29411, 34888]] ![![239, -31, -259, -23, 62]]
  ![![2903, 1864, 482, 3104, -1686]] where
 M := ![![![2903, 1864, 482, 3104, -1686]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![2903, 1864, 482, 3104, -1686]] ![![31, 36, 22, -4, -6]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1072I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1072I3 : PrimesBelowBoundCertificateInterval O 103 151 1072 where
  m := 9
  g := ![2, 2, 1, 2, 1, 3, 2, 3, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1072I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![1225043, 11449]
    · exact ![1295029, 11881]
    · exact ![18424351793]
    · exact ![260144641, 127]
    · exact ![38579489651]
    · exact ![18769, 18769, 137]
    · exact ![2685619, 19321]
    · exact ![3307949, 149, 149]
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
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I127N1, I137N2, I149N1, I149N2, I151N1, I151N2]
  Il := ![[], [], [], [I127N1], [], [I137N2], [], [I149N1, I149N2], [I151N1, I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
