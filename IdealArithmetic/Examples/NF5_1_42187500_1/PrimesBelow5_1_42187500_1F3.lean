
import IdealArithmetic.Examples.NF5_1_42187500_1.RI5_1_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0, 0, 0]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]] where
  M :=![![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 5 2 6 [33, 87, 14, 57, 43, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 0, 83, 49, 65], [24, 50, 78, 79, 95], [87, 29, 14, 86, 4], [15, 27, 39, 0, 50], [0, 1]]
 g := ![![[57, 84, 44, 41, 86], [60, 56, 43, 92, 47], [72, 69, 38, 76], [75, 64, 75, 16, 87], [64, 1], []], ![[60, 79, 10, 101, 59, 28, 90, 45], [11, 0, 94, 27, 70, 47, 38, 60], [82, 84, 99, 89], [77, 102, 69, 88, 76, 30, 76, 82], [25, 98, 1, 13], [29, 78, 80, 6, 24, 94, 13, 63]], ![[35, 64, 28, 29, 87, 37, 42, 95], [31, 67, 24, 79, 2, 40, 36, 97], [12, 58, 30, 30], [86, 29, 11, 64, 0, 5, 32, 73], [3, 65, 46, 3], [37, 35, 45, 67, 57, 20, 41, 91]], ![[95, 1, 15, 14, 1, 51, 71, 42], [82, 35, 103, 18, 71, 81, 17, 102], [88, 58, 74, 30], [84, 16, 54, 103, 30, 66, 33, 85], [77, 63, 101, 53], [11, 26, 60, 69, 21, 72, 92, 64]], ![[91, 81, 74, 37, 84, 46, 47, 43], [52, 36, 7, 69, 94, 87, 55, 8], [4, 6, 63, 87], [47, 6, 75, 49, 16, 106, 83, 95], [33, 95, 30, 76], [70, 41, 93, 25, 88, 63, 38, 24]]]
 h' := ![![[45, 0, 83, 49, 65], [53, 96, 96, 41, 73], [67, 18, 99, 104, 58], [93, 65, 70, 9, 41], [28, 70, 87, 83, 80], [0, 0, 0, 1], [0, 1]], ![[24, 50, 78, 79, 95], [103, 23, 96, 26, 61], [54, 105, 73, 90, 90], [70, 31, 43, 5, 93], [50, 42, 28, 48, 7], [74, 39, 53, 49, 21], [45, 0, 83, 49, 65]], ![[87, 29, 14, 86, 4], [102, 5, 95, 26, 106], [27, 38, 77, 71, 25], [40, 0, 21, 90, 43], [2, 0, 34, 62, 29], [84, 64, 78, 10, 89], [24, 50, 78, 79, 95]], ![[15, 27, 39, 0, 50], [89, 48, 8, 55, 99], [84, 31, 40, 74, 20], [45, 8, 99, 14, 64], [102, 80, 104, 78, 72], [90, 29, 36, 82, 38], [87, 29, 14, 86, 4]], ![[0, 1], [55, 42, 26, 66, 89], [32, 22, 32, 89, 21], [59, 3, 88, 96, 80], [6, 22, 68, 50, 26], [102, 82, 47, 72, 66], [15, 27, 39, 0, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 82, 78, 17], [], [], []]
 b := ![[], [11, 70, 61, 83, 59], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 5
  hpos := by decide
  P := [33, 87, 14, 57, 43, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71312431989, 144172417283, 231976695821, -165213030070, -463231557444]
  a := ![-5, 3, 27, -28, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-666471327, 1347405769, 2168006503, -1544047010, -4329266892]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 14025517307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-959945, -660804, -110676, -460426, -778086]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-959945, -660804, -110676, -460426, -778086]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![46, 59, 74, 1, 0], ![4, 57, 51, 0, 1]] where
  M :=![![![-959945, -660804, -110676, -460426, -778086], ![-2016598, -1388281, -232506, -967310, -1634682], ![-4236674, -2916476, -488467, -2032198, -3434310], ![-3442110, -2369486, -396856, -1650997, -2790072], ![-1374774, -946412, -158506, -659470, -1114475]]]
  hmulB := by decide  
  f := ![![![-1173, 120, 160, 254, -486]], ![![-718, -1753, -2862, 2562, 5478]], ![![13518, -664, -691, -3870, 3354]], ![![8310, -1249, -1788, -1271, 4722]], ![![5898, -1269, -1889, -398, 4561]]]
  g := ![![![214055, 650048, 675626, -460426, -778086], ![449710, 1365687, 1419424, -967310, -1634682], ![944786, 2869164, 2982055, -2032198, -3434310], ![767560, 2330949, 2422666, -1650997, -2790072], ![306594, 931077, 967711, -659470, -1114475]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [31, 94, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 54, 97], [44, 54, 12], [0, 1]]
 g := ![![[34, 98, 80], [4, 28], [34, 24, 29], [69, 77, 45], [29, 78], [1]], ![[3, 96, 20, 84], [95, 106], [43, 104, 80, 93], [101, 73, 49, 108], [3, 4], [69, 78, 83, 16]], ![[53, 99, 2, 88], [49, 15], [59, 59, 46, 43], [20, 103, 101, 27], [23, 89], [57, 31, 30, 93]]]
 h' := ![![[36, 54, 97], [82, 44, 25], [36, 30, 79], [41, 94, 62], [62, 30, 63], [78, 15, 80], [0, 1]], ![[44, 54, 12], [104, 0, 59], [91, 24, 91], [57, 25, 40], [79, 23, 99], [45, 52, 107], [36, 54, 97]], ![[0, 1], [67, 65, 25], [13, 55, 48], [71, 99, 7], [93, 56, 56], [32, 42, 31], [44, 54, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 74], []]
 b := ![[], [91, 47, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [31, 94, 29, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-166850909, 36816491, 59889571, 2651326, -144576660]
  a := ![6, -68, -31, -33, 69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2655915, 74506953, 66395423, 2651326, -144576660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![675, 1128, 1842, -1720, -3496]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![675, 1128, 1842, -1720, -3496]] 
 ![![109, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![675, 1128, 1842, -1720, -3496], ![-8712, 741, 960, 2076, -3160], ![-4244, -12988, -21195, 18620, 40712], ![54378, -2044, -1766, -16395, 11520], ![-25008, 1036, 972, 7412, -5611]]]
  hmulB := by decide  
  f := ![![![-6704693849, -4615504224, -773018726, -3215994864, -5434823768]], ![![-5173124202, -3561173283, -596436164, -2481357276, -4193333656]], ![![-2362858662, -1626589428, -272426159, -1133376332, -1915332856]], ![![-5818061373, -4005147356, -670794296, -2790709899, -4716119624]], ![![-88098792, -60647116, -10157364, -42257748, -71412867]]]
  g := ![![![19, 1128, 1842, -1720, -3496], ![-2670, 741, 960, 2076, -3160], ![798, -12988, -21195, 18620, 40712], ![16275, -2044, -1766, -16395, 11520], ![-7500, 1036, 972, 7412, -5611]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1197, -824, -138, -574, -970]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-1197, -824, -138, -574, -970]] 
 ![![109, 0, 0, 0, 0], ![97, 1, 0, 0, 0], ![74, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-1197, -824, -138, -574, -970], ![-2514, -1731, -290, -1206, -2038], ![-5282, -3636, -609, -2534, -4282], ![-4292, -2954, -494, -2059, -3480], ![-1714, -1180, -198, -822, -1389]]]
  hmulB := by decide  
  f := ![![![-177, 188, -14, -14, -74]], ![![-159, 165, -12, -12, -64]], ![![-116, 128, -9, -10, -54]], ![![-26, 26, -6, 1, -4]], ![![-23, 28, 0, -4, -15]]]
  g := ![![![1041, -824, -138, -574, -970], ![2187, -1731, -290, -1206, -2038], ![4594, -3636, -609, -2534, -4282], ![3732, -2954, -494, -2059, -3480], ![1491, -1180, -198, -822, -1389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-959945, -660804, -110676, -460426, -778086]] ![![675, 1128, 1842, -1720, -3496]]
  ![![177, -188, 14, 14, 74]] where
 M := ![![![177, -188, 14, 14, 74]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![177, -188, 14, 14, 74]] ![![-1197, -824, -138, -574, -970]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14351, -24826, -40702, 37782, 77272]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-14351, -24826, -40702, 37782, 77272]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 100, 35, 111, 1]] where
  M :=![![![-14351, -24826, -40702, 37782, 77272], ![192326, -15563, -19702, -47038, 67024], ![87010, 286686, 467737, -408642, -899576], ![-1200060, 39688, 29756, 369227, -236424], ![552118, -20418, -17192, -167026, 115605]]]
  hmulB := by decide  
  f := ![![![-32095, -22154, -3702, -15386, -25976]], ![![-67338, -46387, -7766, -32382, -54752]], ![![-141886, -97474, -16351, -67938, -114824]], ![![-115124, -79368, -13276, -55181, -93192]], ![![-217032, -149484, -25025, -104099, -175891]]]
  g := ![![![-127, -68602, -24294, -75570, 77272], ![1702, -59451, -20934, -66254, 67024], ![770, 798622, 282769, 880038, -899576], ![-10620, 209576, 73492, 235507, -236424], ![4886, -102486, -35959, -115037, 115605]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [93, 40, 87, 80, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 3, 48, 52], [107, 111, 74, 55], [93, 111, 104, 6], [0, 1]]
 g := ![![[99, 78, 25, 105], [66, 38, 36], [73, 16, 61], [66, 62, 69], [97, 98, 33, 1], []], ![[72, 97, 84, 30, 49, 50], [29, 69, 100], [37, 22, 81], [21, 109, 60], [93, 95, 20, 110, 101, 28], [96, 111, 9, 102, 36, 36]], ![[84, 48, 3, 99, 8, 80], [44, 71, 1], [73, 39, 102], [28, 67, 82], [69, 25, 83, 41, 29, 90], [94, 111, 99, 57, 35, 39]], ![[91, 59, 10, 83, 91, 45], [90, 0, 25], [84, 5, 64], [67, 22, 14], [37, 86, 4, 71, 89, 110], [30, 31, 36, 52, 54, 103]]]
 h' := ![![[59, 3, 48, 52], [16, 10, 7, 61], [74, 54, 36, 6], [99, 107, 32, 20], [19, 1, 53, 42], [0, 0, 0, 1], [0, 1]], ![[107, 111, 74, 55], [23, 71, 63, 63], [11, 60, 9, 103], [66, 46, 85, 9], [95, 105, 112, 88], [57, 103, 51, 48], [59, 3, 48, 52]], ![[93, 111, 104, 6], [78, 18, 68, 94], [21, 100, 94, 112], [97, 43, 55, 92], [21, 20, 88, 46], [82, 52, 107, 77], [107, 111, 74, 55]], ![[0, 1], [54, 14, 88, 8], [47, 12, 87, 5], [47, 30, 54, 105], [17, 100, 86, 50], [58, 71, 68, 100], [93, 111, 104, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 70, 97], []]
 b := ![[], [], [106, 104, 111, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [93, 40, 87, 80, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![314931, 1812010, 3170884, -2867410, -6331316]
  a := ![-1, -2, 6, -9, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2787, 5618970, 1989088, 6193882, -6331316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32095, -22154, -3702, -15386, -25976]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-32095, -22154, -3702, -15386, -25976]] 
 ![![113, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![102, 0, 0, 0, 1]] where
  M :=![![![-32095, -22154, -3702, -15386, -25976], ![-67338, -46387, -7766, -32382, -54752], ![-141886, -97474, -16351, -67938, -114824], ![-115124, -79368, -13276, -55181, -93192], ![-46042, -31554, -5304, -22066, -37331]]]
  hmulB := by decide  
  f := ![![![-14351, -24826, -40702, 37782, 77272]], ![![-1981, -6509, -10620, 9280, 20424]], ![![-7231, -11304, -18553, 17448, 35120]], ![![-21923, -19202, -31794, 33025, 58768]], ![![-8068, -22590, -36892, 32626, 70773]]]
  g := ![![![43031, -22154, -3702, -15386, -25976], ![90565, -46387, -7766, -32382, -54752], ![190031, -97474, -16351, -67938, -114824], ![154333, -79368, -13276, -55181, -93192], ![61724, -31554, -5304, -22066, -37331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-14351, -24826, -40702, 37782, 77272]] ![![-32095, -22154, -3702, -15386, -25976]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-649855187, -447359608, -74925154, -311711566, -526772414]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-649855187, -447359608, -74925154, -311711566, -526772414]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![90, 3, 38, 1, 0], ![17, 75, 29, 0, 1]] where
  M :=![![![-649855187, -447359608, -74925154, -311711566, -526772414], ![-1365256394, -939841189, -157407454, -654863310, -1106676722], ![-2868216754, -1974477260, -330691495, -1375778014, -2324976110], ![-2330236920, -1604132578, -268665026, -1117728765, -1888889448], ![-930752066, -640728740, -107311206, -446447582, -754467639]]]
  hmulB := by decide  
  f := ![![![10347, -27092, -43666, 32094, 86726]], ![![205546, 21313, 40522, -100314, -48502]], ![![-197318, 297880, 477691, -323522, -961258]], ![![-56504, 68943, 110246, -71071, -223478]], ![![82171, 77649, 128379, -131268, -238241]]]
  g := ![![![286293833, 314926820, 212964680, -311711566, -526772414], ![601464140, 661618133, 447409632, -654863310, -1106676722], ![1263593688, 1389969016, 939946301, -1375778014, -2324976110], ![1026586398, 1129257971, 763644268, -1117728765, -1888889448], ![410043151, 451052653, 305017783, -446447582, -754467639]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [116, 124, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 64, 104], [110, 62, 23], [0, 1]]
 g := ![![[29, 24, 81], [14, 64, 36], [79, 51, 73], [74, 92, 32], [27, 9, 18], [1]], ![[98, 33, 69, 52], [86, 75, 72, 9], [0, 9, 124, 76], [30, 92, 26, 122], [25, 0, 11, 64], [83, 114, 25, 25]], ![[70, 114, 38, 23], [7, 103, 52, 5], [83, 113, 46, 118], [108, 74, 96, 28], [125, 57, 95, 45], [17, 24, 39, 102]]]
 h' := ![![[65, 64, 104], [27, 3, 118], [107, 73, 6], [52, 35, 94], [43, 47, 63], [11, 3, 48], [0, 1]], ![[110, 62, 23], [64, 16, 8], [89, 48, 90], [12, 113, 70], [13, 49, 31], [75, 30, 113], [65, 64, 104]], ![[0, 1], [45, 108, 1], [90, 6, 31], [91, 106, 90], [31, 31, 33], [100, 94, 93], [110, 62, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 83], []]
 b := ![[], [4, 126, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [116, 124, 79, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22741862, -4593881, -9760827, 16769340, 17070264]
  a := ![8, 11, -43, 58, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14347850, -10513163, -8992389, 16769340, 17070264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10347, -27092, -43666, 32094, 86726]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![10347, -27092, -43666, 32094, 86726]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![66, 51, 1, 0, 0], ![95, 3, 0, 1, 0], ![104, 104, 0, 0, 1]] where
  M :=![![![10347, -27092, -43666, 32094, 86726], ![205546, 21313, 40522, -100314, -48502], ![-197318, 297880, 477691, -323522, -961258], ![-1225792, -189338, -342642, 680301, 486264], ![566090, 84992, 154266, -310946, -216817]]]
  hmulB := by decide  
  f := ![![![-649855187, -447359608, -74925154, -311711566, -526772414]], ![![-1365256394, -939841189, -157407454, -654863310, -1106676722]], ![![-908556970, -625449701, -104752219, -435801340, -736476128]], ![![-536710621, -369471015, -61880134, -257440295, -435057472]], ![![-1657498870, -1141020564, -191101594, -795041218, -1343568329]]]
  g := ![![![-72253, -54456, -43666, 32094, 86726], ![95316, 25983, 40522, -100314, -48502], ![779374, 605331, 477691, -323522, -961258], ![-738673, -278165, -342642, 680301, 486264], ![334436, 123616, 154266, -310946, -216817]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [89, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 126], [0, 1]]
 g := ![![[28, 16], [36, 35], [110, 11], [15, 30], [105, 88], [48, 1]], ![[34, 111], [65, 92], [3, 116], [58, 97], [11, 39], [96, 126]]]
 h' := ![![[48, 126], [98, 4], [116, 17], [62, 97], [53, 86], [46, 56], [0, 1]], ![[0, 1], [36, 123], [43, 110], [19, 30], [117, 41], [67, 71], [48, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [72, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [89, 79, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26633, -18382, -26370, 13520, 56082]
  a := ![-10, 11, 55, -47, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42125, -35800, -26370, 13520, 56082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-649855187, -447359608, -74925154, -311711566, -526772414]] ![![10347, -27092, -43666, 32094, 86726]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43417, -8097, -14393, 25930, 21626]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-43417, -8097, -14393, 25930, 21626]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![72, 103, 1, 0, 0], ![91, 103, 0, 1, 0], ![57, 49, 0, 0, 1]] where
  M :=![![![-43417, -8097, -14393, 25930, 21626], ![69182, -62114, -98799, 57612, 203030], ![463672, 115801, 201304, -315598, -323806], ![-516196, 359441, 568385, -292691, -1185588], ![234312, -166427, -263307, 137170, 548513]]]
  hmulB := by decide  
  f := ![![![145643, 100521, 16835, 72052, 122726]], ![![317504, 213152, 36387, 148478, 250994]], ![![334654, 226325, 38437, 158734, 268820]], ![![354817, 240192, 40767, 168757, 285932]], ![![183775, 124612, 21125, 87654, 148561]]]
  g := ![![![-19843, -17222, -14393, 25930, 21626], ![-73532, -44033, -98799, 57612, 203030], ![253024, 211867, 201304, -315598, -323806], ![402851, 229441, 568385, -292691, -1185588], ![-187445, -107263, -263307, 137170, 548513]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [18, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 130], [0, 1]]
 g := ![![[76, 5], [121, 105], [114], [46], [53], [89], [1]], ![[48, 126], [57, 26], [114], [46], [53], [89], [1]]]
 h' := ![![[73, 130], [49, 108], [34, 74], [11, 30], [70, 96], [32, 70], [113, 73], [0, 1]], ![[0, 1], [73, 23], [65, 57], [105, 101], [4, 35], [33, 61], [71, 58], [73, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [12, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [18, 58, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37978, 4380, 8468, -19496, -10800]
  a := ![6, -16, -32, 10, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13878, 12744, 8468, -19496, -10800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99, 21, -9, 16, 26]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-99, 21, -9, 16, 26]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![27, 19, 1, 0, 0], ![71, 30, 0, 1, 0], ![113, 130, 0, 0, 1]] where
  M :=![![![-99, 21, -9, 16, 26], ![68, -98, 3, 10, 62], ![134, 123, 28, -68, -190], ![-258, 69, -21, 43, 36], ![198, -1, 17, -44, -79]]]
  hmulB := by decide  
  f := ![![![3537, 2435, 407, 1698, 2870]], ![![7438, 5116, 857, 3564, 6026]], ![![1927, 1326, 222, 924, 1562]], ![![3717, 2558, 428, 1783, 3014]], ![![10471, 7204, 1206, 5020, 8487]]]
  g := ![![![-30, -28, -9, 16, 26], ![-59, -65, 3, 10, 62], ![196, 201, 28, -68, -190], ![-52, -42, -21, 43, 36], ![90, 86, 17, -44, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [4, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 130], [0, 1]]
 g := ![![[80, 33], [40, 91], [27], [94], [62], [89], [1]], ![[0, 98], [2, 40], [27], [94], [62], [89], [1]]]
 h' := ![![[73, 130], [102, 65], [103, 22], [92, 114], [72, 15], [53, 18], [127, 73], [0, 1]], ![[0, 1], [0, 66], [6, 109], [30, 17], [119, 116], [57, 113], [85, 58], [73, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [1, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [4, 58, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21568, 1766, -4513, 15510, 8891]
  a := ![6, 7, -26, 44, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15310, -11707, -4513, 15510, 8891]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23368979, 16087186, 2694330, 11209224, 18942856]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![23368979, 16087186, 2694330, 11209224, 18942856]] 
 ![![131, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![108, 0, 0, 0, 1]] where
  M :=![![![23368979, 16087186, 2694330, 11209224, 18942856], ![49094936, 33796941, 5660410, 23549068, 39796408], ![103141884, 71002686, 11891757, 49473344, 83606776], ![83795980, 57685066, 9661270, 40193807, 67924920], ![33470084, 23040742, 3858938, 16054384, 27130891]]]
  hmulB := by decide  
  f := ![![![-588967, -121046, -213430, 366528, 328840]], ![![-32645, -14729, -24844, 30892, 43616]], ![![-177038, -33250, -59067, 106040, 88920]], ![![-498030, -53638, -101418, 245687, 123832]], ![![-459464, -116894, -202954, 315560, 327651]]]
  g := ![![![-25957745, 16087186, 2694330, 11209224, 18942856], ![-54533731, 33796941, 5660410, 23549068, 39796408], ![-114567860, 71002686, 11891757, 49473344, 83606776], ![-93078760, 57685066, 9661270, 40193807, 67924920], ![-37177934, 23040742, 3858938, 16054384, 27130891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-43417, -8097, -14393, 25930, 21626]] ![![-99, 21, -9, 16, 26]]
  ![![-588967, -121046, -213430, 366528, 328840]] where
 M := ![![![-588967, -121046, -213430, 366528, 328840]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-588967, -121046, -213430, 366528, 328840]] ![![23368979, 16087186, 2694330, 11209224, 18942856]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-697, -460, -80, -350, -606]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-697, -460, -80, -350, -606]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![99, 24, 18, 1, 0], ![50, 19, 77, 0, 1]] where
  M :=![![![-697, -460, -80, -350, -606], ![-1562, -1033, -178, -698, -1170], ![-3038, -2212, -355, -1506, -2526], ![-2498, -1690, -288, -1245, -2136], ![-1010, -756, -118, -474, -775]]]
  hmulB := by decide  
  f := ![![![-1, 16, 28, -22, -54]], ![![-130, -5, -14, 54, 6]], ![![66, -192, -311, 230, 618]], ![![-9, -14, -22, 21, 42]], ![![16, -103, -167, 130, 329]]]
  g := ![![![469, 142, 386, -350, -606], ![920, 277, 748, -698, -1170], ![1988, 598, 1615, -1506, -2526], ![1661, 502, 1362, -1245, -2136], ![618, 185, 497, -474, -775]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [135, 63, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 58, 71], [77, 78, 66], [0, 1]]
 g := ![![[47, 12, 15], [19, 68], [100, 72], [135, 110, 50], [131, 9], [34, 1], []], ![[27, 74, 35, 40], [70, 65], [128, 16], [71, 110, 67, 82], [37, 130], [56, 56], [23, 109]], ![[73, 126, 115, 62], [15, 8], [47, 107], [112, 33, 19, 26], [131, 78], [80, 76], [28, 109]]]
 h' := ![![[94, 58, 71], [114, 74, 17], [79, 41, 94], [133, 133, 88], [91, 70, 18], [68, 52, 134], [0, 0, 1], [0, 1]], ![[77, 78, 66], [103, 86, 4], [127, 42, 105], [62, 85, 4], [92, 74, 72], [93, 27, 33], [114, 83, 78], [94, 58, 71]], ![[0, 1], [12, 114, 116], [16, 54, 75], [14, 56, 45], [49, 130, 47], [91, 58, 107], [94, 54, 58], [77, 78, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 29], []]
 b := ![[], [30, 117, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [135, 63, 103, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![675077, 329120, 553140, -665958, -983851]
  a := ![2, -7, -11, 4, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![845237, 255513, 644503, -665958, -983851]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -16, -28, 22, 54]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![1, -16, -28, 22, 54]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![26, 101, 1, 0, 0], ![57, 119, 0, 1, 0], ![74, 100, 0, 0, 1]] where
  M :=![![![1, -16, -28, 22, 54], ![130, 5, 14, -54, -6], ![-66, 192, 311, -230, -618], ![-798, -74, -148, 381, 168], ![370, 32, 66, -174, -73]]]
  hmulB := by decide  
  f := ![![![697, 460, 80, 350, 606]], ![![1562, 1033, 178, 698, 1170]], ![![1306, 865, 149, 592, 996]], ![![1665, 1101, 190, 761, 1284]], ![![1524, 1008, 174, 702, 1187]]]
  g := ![![![-33, -38, -28, 22, 54], ![24, 41, 14, -54, -6], ![370, 423, 311, -230, -618], ![-227, -345, -148, 381, 168], ![102, 156, 66, -174, -73]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [19, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 136], [0, 1]]
 g := ![![[88, 101], [44], [9], [20, 1], [123], [99], [1]], ![[0, 36], [44], [9], [129, 136], [123], [99], [1]]]
 h' := ![![[109, 136], [51, 85], [105, 110], [31, 134], [24, 1], [124, 73], [118, 109], [0, 1]], ![[0, 1], [0, 52], [39, 27], [115, 3], [133, 136], [135, 64], [80, 28], [109, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [106, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [19, 28, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28601, -15003, -25234, 12989, 55473]
  a := ![10, -11, -50, 45, 117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30370, -33280, -25234, 12989, 55473]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-697, -460, -80, -350, -606]] ![![1, -16, -28, 22, 54]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -5, 1, -2, 2]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![17, -5, 1, -2, 2]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![39, 89, 90, 1, 0], ![117, 17, 21, 0, 1]] where
  M :=![![![17, -5, 1, -2, 2], ![2, 22, 13, -12, -34], ![-80, -7, -8, 34, 26], ![42, -59, -73, 57, 156], ![-28, 29, 33, -22, -63]]]
  hmulB := by decide  
  f := ![![![9, 5, 1, 0, -2]], ![![-4, 8, -1, 6, 10]], ![![26, -1, 2, 8, 22]], ![![17, 6, 1, 9, 20]], ![![11, 5, 1, 2, 3]]]
  g := ![![![-1, 1, 1, -2, 2], ![32, 12, 13, -12, -34], ![-32, -25, -26, 34, 26], ![-147, -56, -61, 57, 156], ![59, 22, 24, -22, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [109, 90, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 33, 41], [67, 105, 98], [0, 1]]
 g := ![![[40, 54, 4], [129, 68, 89], [117, 67], [69, 121, 137], [20, 34], [16, 1], []], ![[8, 70, 30, 129], [114, 110, 46, 64], [20, 64], [93, 109, 35, 11], [61, 35], [112, 44], [134, 13]], ![[60, 79, 135, 8], [93, 11, 7, 32], [45, 66], [116, 118, 43, 12], [66, 42], [104, 116], [77, 13]]]
 h' := ![![[88, 33, 41], [117, 67, 2], [121, 85, 28], [124, 107, 117], [121, 36, 89], [63, 119, 27], [0, 0, 1], [0, 1]], ![[67, 105, 98], [73, 78, 38], [57, 48, 31], [98, 28, 131], [1, 25, 118], [123, 82, 69], [88, 115, 105], [88, 33, 41]], ![[0, 1], [134, 133, 99], [59, 6, 80], [51, 4, 30], [75, 78, 71], [67, 77, 43], [127, 24, 33], [67, 105, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 50], []]
 b := ![[], [35, 81, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [109, 90, 123, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4586683, -3467571, -5576281, 3131072, 11676894]
  a := ![6, -5, -33, 30, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10674257, -3457843, -3831565, 3131072, 11676894]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 5, 1, 0, -2]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![9, 5, 1, 0, -2]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![124, 98, 1, 0, 0], ![40, 56, 0, 1, 0], ![127, 116, 0, 0, 1]] where
  M :=![![![9, 5, 1, 0, -2], ![-4, 8, -1, 6, 10], ![26, -1, 2, 8, 22], ![28, 17, 9, -3, -12], ![-2, -5, -3, 8, 19]]]
  hmulB := by decide  
  f := ![![![17, -5, 1, -2, 2]], ![![2, 22, 13, -12, -34]], ![![16, 11, 10, -10, -22]], ![![6, 7, 5, -5, -12]], ![![17, 14, 12, -12, -27]]]
  g := ![![![1, 1, 1, 0, -2], ![-10, -10, -1, 6, 10], ![-24, -23, 2, 8, 22], ![4, 5, 9, -3, -12], ![-17, -17, -3, 8, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [39, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 138], [0, 1]]
 g := ![![[126, 16], [84, 5], [80], [60, 116], [57], [38], [1]], ![[37, 123], [117, 134], [80], [75, 23], [57], [38], [1]]]
 h' := ![![[90, 138], [60, 135], [50, 127], [23, 91], [132, 106], [39, 14], [100, 90], [0, 1]], ![[0, 1], [117, 4], [82, 12], [12, 48], [81, 33], [48, 125], [138, 49], [90, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [44, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [39, 49, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4379, -689, -2985, 4922, 5792]
  a := ![3, 2, -15, 21, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4077, -4717, -2985, 4922, 5792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![17, -5, 1, -2, 2]] ![![9, 5, 1, 0, -2]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![472347, 504556, 832412, -831328, -1553746]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![472347, 504556, 832412, -831328, -1553746]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![121, 36, 84, 15, 1]] where
  M :=![![![472347, 504556, 832412, -831328, -1553746], ![-3938820, 582341, 831286, 615676, -2207206], ![-3798736, -5930416, -9733333, 9155364, 18424142], ![24971234, -2422816, -3210730, -5576903, 9975432], ![-11473816, 1160184, 1551452, 2500572, -4732147]]]
  hmulB := by decide  
  f := ![![![2457087, 1691308, 283284, 1178456, 1991510]], ![![5161476, 3553425, 595102, 2475828, 4183922]], ![![10843672, 7464672, 1250223, 5201500, 8790326]], ![![8810338, 6064648, 1015774, 4225733, 7141224]], ![![10266193, 7067088, 1183638, 4924315, 8321827]]]
  g := ![![![1264937, 378788, 881524, 150838, -1553746], ![1765994, 537193, 1249910, 226334, -2207206], ![-14987382, -4491272, -10452089, -1793334, 18424142], ![-7933262, -2426432, -5645282, -1041667, 9975432], ![3765879, 1151124, 2678200, 493173, -4732147]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [43, 73, 59, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 124, 4, 43], [2, 130, 33, 75], [31, 43, 112, 31], [0, 1]]
 g := ![![[32, 123, 38, 63], [34, 116, 69], [16, 130, 128, 132], [76, 75, 113], [55, 101, 79, 4], [1], []], ![[56, 56, 84, 77, 141, 56], [60, 38, 100], [112, 63, 120, 77], [93, 59, 42], [129, 74, 81, 108, 124, 59], [10, 118, 95], [81, 73, 61]], ![[134, 21, 83, 16, 85, 62], [42, 69, 17], [119, 114, 112, 21, 89, 10], [133, 30, 26], [39, 8, 1, 58, 99, 41], [32, 17, 53], [59, 107, 112]], ![[128, 93, 53, 18, 118, 6], [116, 86, 81], [45, 85, 61, 110, 115, 42], [105, 124, 121], [131, 94, 132, 100, 122, 42], [109, 69, 143], [21, 105, 67]]]
 h' := ![![[114, 124, 4, 43], [148, 80, 129, 130], [57, 61, 106, 101], [73, 16, 27, 79], [19, 47, 11, 34], [106, 76, 90, 147], [0, 0, 1], [0, 1]], ![[2, 130, 33, 75], [137, 70, 126, 9], [66, 19, 3, 139], [148, 5, 32], [78, 141, 120, 108], [99, 53, 102, 45], [126, 148, 130, 86], [114, 124, 4, 43]], ![[31, 43, 112, 31], [132, 31, 40, 78], [1, 52, 109, 49], [131, 141, 8, 136], [28, 18, 143, 18], [114, 62, 104, 23], [0, 105, 30, 84], [2, 130, 33, 75]], ![[0, 1], [31, 117, 3, 81], [129, 17, 80, 9], [9, 136, 82, 83], [90, 92, 24, 138], [18, 107, 2, 83], [58, 45, 137, 128], [31, 43, 112, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 29, 18], []]
 b := ![[], [], [62, 42, 11, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [43, 73, 59, 2, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![103422300731, 12193150463, 22678262401, -52243756761, -28790270369]
  a := ![-16, 25, 79, -71, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24074127620, 7037871703, 16382959553, 2547720126, -28790270369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2457087, -1691308, -283284, -1178456, -1991510]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-2457087, -1691308, -283284, -1178456, -1991510]] 
 ![![149, 0, 0, 0, 0], ![123, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-2457087, -1691308, -283284, -1178456, -1991510], ![-5161476, -3553425, -595102, -2475828, -4183922], ![-10843672, -7464672, -1250223, -5201500, -8790326], ![-8810338, -6064648, -1015774, -4225733, -7141224], ![-3518576, -2422376, -405684, -1687956, -2852577]]]
  hmulB := by decide  
  f := ![![![-472347, -504556, -832412, 831328, 1553746]], ![![-363489, -420421, -692738, 682132, 1297436]], ![![-193243, -193852, -320155, 323532, 595868]], ![![-218314, -37920, -67838, 126699, 99896]], ![![-75160, -170328, -278572, 251028, 532295]]]
  g := ![![![2278981, -1691308, -283284, -1178456, -1991510], ![4788009, -3553425, -595102, -2475828, -4183922], ![10058631, -7464672, -1250223, -5201500, -8790326], ![8171948, -6064648, -1015774, -4225733, -7141224], ![3264140, -2422376, -405684, -1687956, -2852577]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![472347, 504556, 832412, -831328, -1553746]] ![![-2457087, -1691308, -283284, -1178456, -1991510]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -50, -8, -18, -22]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-71, -50, -8, -18, -22]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![3, 78, 19, 1, 0], ![90, 62, 26, 0, 1]] where
  M :=![![![-71, -50, -8, -18, -22], ![-62, -83, -8, -62, -106], ![-274, -114, -29, -114, -214], ![-240, -160, -32, -69, -96], ![-58, -18, -4, -50, -103]]]
  hmulB := by decide  
  f := ![![![-9, 2, 0, 2, -2]], ![![-2, -13, -16, 14, 34]], ![![82, 2, 5, -30, -2]], ![![9, -6, -7, 3, 16]], ![![8, -4, -6, 2, 13]]]
  g := ![![![13, 18, 6, -18, -22], ![64, 75, 26, -62, -106], ![128, 146, 51, -114, -214], ![57, 74, 25, -69, -96], ![62, 68, 24, -50, -103]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [12, 116, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 98, 27], [95, 52, 124], [0, 1]]
 g := ![![[79, 132, 49], [40, 74, 11], [16, 35, 43], [15, 43], [67, 16, 21], [53, 1], []], ![[139, 42, 105, 93], [13, 62, 60, 106], [129, 112, 89, 106], [86, 17], [118, 32, 11, 133], [148, 137], [139, 125]], ![[65, 62, 55, 148], [116, 118, 28, 20], [107, 85, 13, 90], [109, 29], [150, 90, 7, 145], [56, 91], [42, 125]]]
 h' := ![![[109, 98, 27], [124, 79, 144], [110, 113, 112], [107, 25, 88], [102, 6, 63], [119, 31, 126], [0, 0, 1], [0, 1]], ![[95, 52, 124], [60, 135, 108], [76, 57, 117], [106, 125, 117], [9, 44, 116], [41, 138, 141], [96, 116, 52], [109, 98, 27]], ![[0, 1], [77, 88, 50], [5, 132, 73], [48, 1, 97], [86, 101, 123], [80, 133, 35], [65, 35, 98], [95, 52, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 59], []]
 b := ![[], [57, 43, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [12, 116, 98, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6254361, 1680942, 2557964, 4045, -5899929]
  a := ![-7, 10, 36, -33, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3475014, 2431530, 1032313, 4045, -5899929]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 2, 0, 2, -2]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-9, 2, 0, 2, -2]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![91, 113, 1, 0, 0], ![68, 79, 0, 1, 0], ![148, 78, 0, 0, 1]] where
  M :=![![![-9, 2, 0, 2, -2], ![-2, -13, -16, 14, 34], ![82, 2, 5, -30, -2], ![-16, 64, 96, -75, -192], ![10, -30, -44, 34, 87]]]
  hmulB := by decide  
  f := ![![![-71, -50, -8, -18, -22]], ![![-62, -83, -8, -62, -106]], ![![-91, -93, -11, -58, -94]], ![![-66, -67, -8, -41, -66]], ![![-102, -92, -12, -50, -77]]]
  g := ![![![1, 0, 0, 2, -2], ![-30, -13, -16, 14, 34], ![13, 13, 5, -30, -2], ![164, 67, 96, -75, -192], ![-74, -30, -44, 34, 87]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [84, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 150], [0, 1]]
 g := ![![[147, 9], [139, 69], [120, 40], [80], [15, 68], [99], [1]], ![[0, 142], [69, 82], [121, 111], [80], [62, 83], [99], [1]]]
 h' := ![![[34, 150], [102, 148], [37, 62], [61, 74], [99, 69], [99, 70], [67, 34], [0, 1]], ![[0, 1], [0, 3], [31, 89], [10, 77], [29, 82], [63, 81], [15, 117], [34, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [119, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [84, 117, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15802, -3819, -13921, 21226, 27930]
  a := ![6, 2, -31, 43, 69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28649, -15140, -13921, 21226, 27930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-71, -50, -8, -18, -22]] ![![-9, 2, 0, 2, -2]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB405I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB405I3 : PrimesBelowBoundCertificateInterval O 103 151 405 where
  m := 9
  g := ![1, 3, 2, 2, 3, 2, 2, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB405I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1]
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
    · exact ![14025517307]
    · exact ![1295029, 109, 109]
    · exact ![163047361, 113]
    · exact ![2048383, 16129]
    · exact ![17161, 17161, 131]
    · exact ![2571353, 18769]
    · exact ![2685619, 19321]
    · exact ![492884401, 149]
    · exact ![3442951, 22801]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
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
  β := ![I109N1, I109N2, I113N1, I131N2, I149N1]
  Il := ![[], [I109N1, I109N2], [I113N1], [], [I131N2], [], [], [I149N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
