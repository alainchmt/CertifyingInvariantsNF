
import IdealArithmetic.Examples.NF5_3_1687500000_3.RI5_3_1687500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-182, 228, 76, 119, -267]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-182, 228, 76, 119, -267]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![8, 62, 45, 1, 0], ![36, 65, 38, 0, 1]] where
  M :=![![![-182, 228, 76, 119, -267], ![-342, 399, 126, 198, -446], ![-604, 626, 259, 360, -812], ![-389, 394, 132, 268, -537], ![-352, 356, 128, 216, -459]]]
  hmulB := by decide  
  f := ![![![-56, 42, 24, 43, -101]], ![![-214, 155, 82, 146, -342]], ![![-708, 502, 275, 480, -1124]], ![![-297, 212, 115, 202, -473]], ![![-278, 199, 108, 190, -445]]]
  g := ![![![54, 65, 31, 119, -267], ![90, 109, 52, 198, -446], ![164, 198, 95, 360, -812], ![107, 119, 54, 268, -537], ![92, 107, 50, 216, -459]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [122, 119, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 11, 50], [155, 145, 107], [0, 1]]
 g := ![![[8, 150, 138], [141, 93], [88, 146, 12], [30, 147, 44], [119, 68, 118], [121, 1], []], ![[69, 19, 73, 97], [148, 86], [99, 4, 67, 65], [103, 121, 60, 53], [109, 23, 145, 77], [42, 144], [119, 145]], ![[20, 146, 23, 62], [149, 11], [95, 88, 29, 104], [78, 37, 84, 41], [126, 5, 146, 114], [42, 121], [62, 145]]]
 h' := ![![[123, 11, 50], [57, 7, 74], [97, 22, 90], [108, 143, 13], [83, 10, 63], [153, 80, 78], [0, 0, 1], [0, 1]], ![[155, 145, 107], [131, 56, 90], [17, 34, 20], [49, 116, 86], [85, 90, 58], [32, 145, 81], [140, 57, 145], [123, 11, 50]], ![[0, 1], [151, 94, 150], [91, 101, 47], [138, 55, 58], [121, 57, 36], [5, 89, 155], [133, 100, 11], [155, 145, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141, 19], []]
 b := ![[], [58, 20, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [122, 119, 36, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2113191509, 1168758261, -2826995623, -2262490183, 4907678881]
  a := ![-189, -11, 173, 177, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-996581699, -1130929794, -557367738, -2262490183, 4907678881]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-405607, 455013, 149845, 232834, -521552]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-405607, 455013, 149845, 232834, -521552]] 
 ![![157, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![-405607, 455013, 149845, 232834, -521552], ![-652012, 731458, 240871, 374266, -838356], ![-1047948, 1175747, 387136, 601510, -1347364], ![-515924, 579057, 190587, 296079, -663172], ![-511576, 574104, 188982, 293600, -657631]]]
  hmulB := by decide  
  f := ![![![-2003, 4195, -1847, 2238, -2232]], ![![123, 419, -464, -124, 444]], ![![-2179, 1072, 973, 2376, -4028]], ![![-5934, 5907, 87, 6475, -9532]], ![![-2893, 2735, 167, 3158, -4719]]]
  g := ![![![-71559, 455013, 149845, 232834, -521552], ![-115037, 731458, 240871, 374266, -838356], ![-184917, 1175747, 387136, 601510, -1347364], ![-91084, 579057, 190587, 296079, -663172], ![-90301, 574104, 188982, 293600, -657631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-328155, 192628, 53388, 81602, -176934]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-328155, 192628, 53388, 81602, -176934]] 
 ![![157, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![122, 0, 1, 0, 0], ![99, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![-328155, 192628, 53388, 81602, -176934], ![-111396, 65371, 18028, 27508, -59588], ![-36424, 21236, 5555, 8320, -17832], ![52098, -30884, -9064, -14111, 30914], ![170864, -100516, -28260, -43400, 94355]]]
  hmulB := by decide  
  f := ![![![16397, -12940, -3116, -17786, 27814]], ![![4216, -4605, 292, -4588, 6556]], ![![14338, -4684, -8397, -15476, 27412]], ![![34177, -14744, -16956, -36929, 63672]], ![![17270, -7380, -8628, -18660, 32207]]]
  g := ![![![-79945, 192628, 53388, 81602, -176934], ![-27148, 65371, 18028, 27508, -59588], ![-8878, 21236, 5555, 8320, -17832], ![12719, -30884, -9064, -14111, 30914], ![41638, -100516, -28260, -43400, 94355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-182, 228, 76, 119, -267]] ![![-405607, 455013, 149845, 232834, -521552]]
  ![![-79286474, 88938845, 29290793, 45513821, -101952359]] where
 M := ![![![-79286474, 88938845, 29290793, 45513821, -101952359]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-79286474, 88938845, 29290793, 45513821, -101952359]] ![![-328155, 192628, 53388, 81602, -176934]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-4875368100, 5440072451, 1789970659, 2781147141, -6228896971]]]
 hmul := by decide  
 g := ![![![![-31053300, 34650143, 11401087, 17714313, -39674503]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -15, -7, -4, 24]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![17, -15, -7, -4, 24]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![57, 2, 1, 0, 0], ![106, 27, 0, 1, 0], ![35, 52, 0, 0, 1]] where
  M :=![![![17, -15, -7, -4, 24], ![312, -22, -267, -286, 616], ![308, -1143, 660, -182, 44], ![-3538, 291, 2737, 4047, -7254], ![-1232, -206, 1184, 1508, -2707]]]
  hmulB := by decide  
  f := ![![![568183, -637595, -209997, -326308, 730948]], ![![914024, -1025378, -337699, -524738, 1175432]], ![![218921, -245658, -80909, -125722, 281624]], ![![525340, -589465, -194142, -301671, 675758]], ![![417999, -468963, -154451, -239996, 537601]]]
  g := ![![![0, -7, -7, -4, 24], ![149, -146, -267, -286, 616], ![-120, 1, 660, -182, 44], ![-2053, 1612, 2737, 4047, -7254], ![-821, 598, 1184, 1508, -2707]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [69, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 162], [0, 1]]
 g := ![![[21, 26], [43, 61], [34], [15], [65], [88, 161], [1]], ![[0, 137], [0, 102], [34], [15], [65], [52, 2], [1]]]
 h' := ![![[18, 162], [130, 29], [81, 77], [54, 69], [130, 129], [122, 126], [94, 18], [0, 1]], ![[0, 1], [0, 134], [0, 86], [155, 94], [7, 34], [108, 37], [92, 145], [18, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [143, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [69, 145, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3654147, -1167178, 4130480, 4009562, -8117406]
  a := ![171, -54, -156, -226, 350]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2331263, 1867600, 4130480, 4009562, -8117406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1199, 19, -1053, -1290, 2484]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![1199, 19, -1053, -1290, 2484]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![26, 112, 1, 0, 0], ![11, 17, 0, 1, 0], ![35, 122, 0, 0, 1]] where
  M :=![![![1199, 19, -1053, -1290, 2484], ![-4500, -4918, 8101, 4782, -11580], ![-30756, 24745, 5444, 33362, -51948], ![183372, 49139, -200679, -196655, 401396], ![68168, 24740, -80138, -73032, 152235]]]
  hmulB := by decide  
  f := ![![![5459637, -3204461, -888567, -1358394, 2945612]], ![![1859692, -1091330, -302499, -462390, 1002596]], ![![2152562, -1263283, -350214, -535350, 1160828]], ![![557333, -327096, -90685, -138627, 300596]], ![![2546989, -1494775, -414397, -633466, 1373583]]]
  g := ![![![-271, -1001, -1053, -1290, 2484], ![844, 2572, 8101, 4782, -11580], ![7846, 31813, 5444, 33362, -51948], ![-39783, -141730, -200679, -196655, 401396], ![-14559, -51110, -80138, -73032, 152235]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [2, 144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 162], [0, 1]]
 g := ![![[72, 58], [61, 160], [57], [145], [51], [100, 35], [1]], ![[33, 105], [4, 3], [57], [145], [51], [113, 128], [1]]]
 h' := ![![[19, 162], [41, 59], [144, 117], [101, 63], [126, 54], [126, 41], [161, 19], [0, 1]], ![[0, 1], [21, 104], [85, 46], [157, 100], [11, 109], [90, 122], [33, 144], [19, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [49, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [2, 144, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51327, -13018, -34355, -54150, 99384]
  a := ![-62, -6, 57, 55, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11891, -45212, -34355, -54150, 99384]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48, 23, 13, 15, -33]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-48, 23, 13, 15, -33]] 
 ![![163, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![147, 0, 0, 0, 1]] where
  M :=![![![-48, 23, 13, 15, -33], ![-30, 28, -1, 20, -30], ![240, 39, -242, -262, 520], ![-287, -537, 709, 308, -851], ![-48, -222, 236, 68, -231]]]
  hmulB := by decide  
  f := ![![![-15318, 15381, 5711, 9241, -20997]], ![![-4800, 4807, 1790, 2899, -6589]], ![![-4592, 4549, 1714, 2786, -6340]], ![![-11779, 11717, 4395, 7134, -16227]], ![![-14222, 14197, 5305, 8601, -19556]]]
  g := ![![![8, 23, 13, 15, -33], ![4, 28, -1, 20, -30], ![-221, 39, -242, -262, 520], ![509, -537, 709, 308, -851], ![161, -222, 236, 68, -231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![17, -15, -7, -4, 24]] ![![1199, 19, -1053, -1290, 2484]]
  ![![1205719, 298082, -1298120, -1293342, 2627620]] where
 M := ![![![1205719, 298082, -1298120, -1293342, 2627620]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![1205719, 298082, -1298120, -1293342, 2627620]] ![![-48, 23, 13, 15, -33]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-133302378, 96644167, 32660147, 144483689, -230099765]]]
 hmul := by decide  
 g := ![![![![-817806, 592909, 200369, 886403, -1411655]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-376, 414, 138, 213, -477]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-376, 414, 138, 213, -477]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![143, 62, 41, 1, 0], ![86, 135, 122, 0, 1]] where
  M :=![![![-376, 414, 138, 213, -477], ![-594, 665, 216, 342, -762], ![-876, 1068, 281, 468, -1068], ![-555, 372, 378, 362, -855], ![-480, 456, 240, 288, -667]]]
  hmulB := by decide  
  f := ![![![-110, 72, 30, 51, -117]], ![![-198, 139, 72, 126, -294]], ![![-588, 420, 223, 396, -924]], ![![-317, 220, 109, 191, -444]], ![![-650, 459, 238, 420, -979]]]
  g := ![![![61, 309, 297, 213, -477], ![96, 493, 474, 342, -762], ![144, 696, 667, 468, -1068], ![127, 559, 538, 362, -855], ![94, 435, 418, 288, -667]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [80, 82, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 31, 151], [65, 135, 16], [0, 1]]
 g := ![![[49, 144, 114], [82, 56, 18], [39, 77, 8], [139, 36], [73, 61], [114, 153, 1], []], ![[165, 23, 75, 146], [30, 144, 71, 160], [68, 64, 78, 164], [145, 88], [142, 48], [6, 131, 24, 149], [100, 89]], ![[148, 125, 80, 121], [32, 78, 130, 42], [6, 165, 134, 1], [112, 57], [60, 77], [82, 22, 32, 12], [68, 89]]]
 h' := ![![[88, 31, 151], [120, 122, 92], [53, 56, 128], [88, 161, 26], [55, 151, 6], [65, 122, 140], [0, 0, 1], [0, 1]], ![[65, 135, 16], [163, 98, 114], [102, 161, 18], [85, 29, 99], [117, 106, 64], [11, 71, 81], [78, 156, 135], [88, 31, 151]], ![[0, 1], [144, 114, 128], [143, 117, 21], [5, 144, 42], [75, 77, 97], [52, 141, 113], [121, 11, 31], [65, 135, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 29], []]
 b := ![[], [10, 29, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [80, 82, 14, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-822997424, -5594451603, 5481700316, 871294158, -4324651231]
  a := ![295, 33, -270, -263, 604]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1476059544, 3139001358, 2978240060, 871294158, -4324651231]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44041, 31480, 16796, 29752, -69602]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-44041, 31480, 16796, 29752, -69602]] 
 ![![167, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![136, 0, 1, 0, 0], ![104, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![-44041, 31480, 16796, 29752, -69602], ![-142456, 101861, 54386, 96348, -225408], ![-461544, 330034, 176225, 312196, -730392], ![-676576, 483802, 258334, 457659, -1070708], ![-524664, 375178, 200338, 354916, -830339]]]
  hmulB := by decide  
  f := ![![![641, -860, 136, -656, 906]], ![![312, -503, 134, -316, 400]], ![![672, -458, -227, -692, 1160]], ![![1336, -994, -334, -1421, 2284]], ![![662, -478, -182, -700, 1137]]]
  g := ![![![-23059, 31480, 16796, 29752, -69602], ![-74616, 101861, 54386, 96348, -225408], ![-241760, 330034, 176225, 312196, -730392], ![-354400, 483802, 258334, 457659, -1070708], ![-274830, 375178, 200338, 354916, -830339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26, -4, 26, 29, -57]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-26, -4, 26, 29, -57]] 
 ![![167, 0, 0, 0, 0], ![156, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-26, -4, 26, 29, -57], ![78, 115, -166, -82, 214], ![836, -466, -325, -904, 1508], ![-3943, -1460, 4660, 4224, -8819], ![-1432, -682, 1822, 1532, -3273]]]
  hmulB := by decide  
  f := ![![![43600, -31414, -16526, -29197, 68243]], ![![41558, -29941, -15754, -27834, 65058]], ![![14684, -10570, -5573, -9850, 23026]], ![![5997, -4302, -2284, -4042, 9453]], ![![12952, -9318, -4918, -8694, 20325]]]
  g := ![![![8, -4, 26, 29, -57], ![-106, 115, -166, -82, 214], ![230, -466, -325, -904, 1508], ![1861, -1460, 4660, 4224, -8819], ![798, -682, 1822, 1532, -3273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-376, 414, 138, 213, -477]] ![![-44041, 31480, 16796, 29752, -69602]]
  ![![43600, -31414, -16526, -29197, 68243]] where
 M := ![![![43600, -31414, -16526, -29197, 68243]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![43600, -31414, -16526, -29197, 68243]] ![![-26, -4, 26, 29, -57]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-283, 169, 51, 80, -176]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-283, 169, 51, 80, -176]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![44, 26, 1, 0, 0], ![120, 117, 0, 1, 0], ![121, 161, 0, 0, 1]] where
  M :=![![![-283, 169, 51, 80, -176], ![-160, 104, 41, 70, -160], ![-260, 181, 94, 162, -380], ![-318, 217, 141, 239, -554], ![-136, 108, 86, 152, -359]]]
  hmulB := by decide  
  f := ![![![-1019, 1143, 375, 584, -1308]], ![![-1632, 1832, 603, 934, -2096]], ![![-520, 583, 192, 298, -668]], ![![-1818, 2041, 670, 1041, -2334]], ![![-2239, 2513, 826, 1282, -2875]]]
  g := ![![![53, 103, 51, 80, -176], ![52, 96, 41, 70, -160], ![128, 231, 94, 162, -380], ![184, 334, 141, 239, -554], ![123, 219, 86, 152, -359]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [151, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 172], [0, 1]]
 g := ![![[108, 55], [47], [122, 34], [70, 133], [41], [115, 40], [1]], ![[0, 118], [47], [115, 139], [7, 40], [41], [5, 133], [1]]]
 h' := ![![[127, 172], [132, 48], [89, 96], [156, 42], [110, 47], [108, 53], [22, 127], [0, 1]], ![[0, 1], [0, 125], [171, 77], [127, 131], [24, 126], [92, 120], [62, 46], [127, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [51, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [151, 46, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![838202, -1908752, 898125, -893624, 829292]
  a := ![-421, -19, 386, 404, -862]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-183750, -313422, 898125, -893624, 829292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, -66, -20, -32, 72]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![57, -66, -20, -32, 72]] 
 ![![173, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![122, 0, 1, 0, 0], ![133, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![57, -66, -20, -32, 72], ![96, -99, -42, -56, 128], ![208, -186, -91, -148, 304], ![-116, -192, 230, 161, -348], ![8, -130, 70, 28, -63]]]
  hmulB := by decide  
  f := ![![![-13483, 7794, 1992, 2960, -6312]], ![![-2583, 1491, 378, 560, -1192]], ![![-9462, 5462, 1385, 2052, -4368]], ![![-10271, 5926, 1498, 2217, -4716]], ![![-6752, 3894, 982, 1452, -3087]]]
  g := ![![![15, -66, -20, -32, 72], ![27, -99, -42, -56, 128], ![60, -186, -91, -148, 304], ![-73, -192, 230, 161, -348], ![-14, -130, 70, 28, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9857, 5785, 1603, 2450, -5312]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![-9857, 5785, 1603, 2450, -5312]] 
 ![![173, 0, 0, 0, 0], ![125, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![-9857, 5785, 1603, 2450, -5312], ![-3340, 1958, 539, 822, -1780], ![-1076, 623, 160, 238, -508], ![1588, -945, -281, -439, 964], ![5152, -3034, -856, -1316, 2863]]]
  hmulB := by decide  
  f := ![![![-629, 695, 223, 382, -824]], ![![-457, 509, 160, 276, -596]], ![![-442, 471, 170, 270, -588]], ![![-380, 375, 149, 257, -532]], ![![-453, 479, 169, 286, -609]]]
  g := ![![![-2984, 5785, 1603, 2450, -5312], ![-1016, 1958, 539, 822, -1780], ![-343, 623, 160, 238, -508], ![455, -945, -281, -439, 964], ![1539, -3034, -856, -1316, 2863]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2

def I173N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, -66, -22, -34, 76]] i)))

def SI173N3: IdealEqSpanCertificate' Table ![![59, -66, -22, -34, 76]] 
 ![![173, 0, 0, 0, 0], ![162, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![164, 0, 0, 0, 1]] where
  M :=![![![59, -66, -22, -34, 76], ![92, -107, -32, -52, 116], ![136, -160, -51, -72, 168], ![122, -60, -88, -97, 206], ![88, -70, -50, -60, 131]]]
  hmulB := by decide  
  f := ![![![-30893, 18134, 5034, 7698, -16696]], ![![-28990, 17017, 4724, 7224, -15668]], ![![-9308, 5464, 1517, 2320, -5032]], ![![-5690, 3340, 928, 1419, -3078]], ![![-29196, 17138, 4758, 7276, -15781]]]
  g := ![![![3, -66, -22, -34, 76], ![10, -107, -32, -52, 116], ![20, -160, -51, -72, 168], ![-94, -60, -88, -97, 206], ![-32, -70, -50, -60, 131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N3 : Nat.card (O ⧸ I173N3) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N3)

lemma isPrimeI173N3 : Ideal.IsPrime I173N3 := prime_ideal_of_norm_prime hp173.out _ NI173N3
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-283, 169, 51, 80, -176]] ![![57, -66, -20, -32, 72]]
  ![![13, -19, 1, -4, 8]] where
 M := ![![![13, -19, 1, -4, 8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![13, -19, 1, -4, 8]] ![![-9857, 5785, 1603, 2450, -5312]]
  ![![-30893, 18134, 5034, 7698, -16696]] where
 M := ![![![-30893, 18134, 5034, 7698, -16696]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N2 : IdealMulLeCertificate' Table 
  ![![-30893, 18134, 5034, 7698, -16696]] ![![59, -66, -22, -34, 76]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2, I173N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
    exact isPrimeI173N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1 ⊙ MulI173N2)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35516, -39763, -13123, -20407, 45725]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![35516, -39763, -13123, -20407, 45725]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![98, 151, 1, 0, 0], ![119, 105, 0, 1, 0], ![118, 53, 0, 0, 1]] where
  M :=![![![35516, -39763, -13123, -20407, 45725], ![57406, -64146, -21215, -33016, 73998], ![93288, -103839, -34488, -53754, 120544], ![47903, -52553, -17733, -27796, 62459], ![46856, -51644, -17338, -27128, 60919]]]
  hmulB := by decide  
  f := ![![![-6686, 3907, 1103, 1663, -3615]], ![![-2454, 1358, 505, 756, -1582]], ![![-5730, 3291, 1023, 1544, -3304]], ![![-5869, 3378, 1031, 1537, -3314]], ![![-5110, 2962, 873, 1310, -2833]]]
  g := ![![![-9193, 9280, -13123, -20407, 45725], ![-14896, 14995, -21215, -33016, 73998], ![-24326, 24353, -34488, -53754, 120544], ![-12719, 12477, -17733, -27796, 62459], ![-12370, 12213, -17338, -27128, 60919]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [4, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 178], [0, 1]]
 g := ![![[102, 45], [128, 67], [65], [60], [125, 161], [163, 173], [1]], ![[0, 134], [0, 112], [65], [60], [130, 18], [105, 6], [1]]]
 h' := ![![[129, 178], [25, 90], [80, 109], [55, 94], [37, 66], [64, 124], [175, 129], [0, 1]], ![[0, 1], [0, 89], [0, 70], [9, 85], [138, 113], [129, 55], [169, 50], [129, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [165, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [4, 50, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-674900, -850924, 1311412, 716480, -1789832]
  a := ![210, 0, -192, -220, 430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18180, -1001360, 1311412, 716480, -1789832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-402, 348, 106, 259, -603]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-402, 348, 106, 259, -603]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![7, 85, 1, 0, 0], ![150, 61, 0, 1, 0], ![31, 75, 0, 0, 1]] where
  M :=![![![-402, 348, 106, 259, -603], ![-1182, 825, 498, 706, -1846], ![-7268, 2574, 4673, 5984, -13124], ![-4985, 10836, -4096, 2756, -4245], ![-5032, 6026, -134, 3364, -6807]]]
  hmulB := by decide  
  f := ![![![87236, -10626, 1482, 2969, -9555]], ![![-66402, 104211, 36018, 56194, -126866]], ![![-29110, 50237, 17549, 27403, -61969]], ![![49797, 27295, 13738, 21982, -52009]], ![![-13718, 42699, 15622, 24483, -55752]]]
  g := ![![![-119, 116, 106, 259, -603], ![-298, 301, 498, 706, -1846], ![-2965, 1255, 4673, 5984, -13124], ![-1442, 2845, -4096, 2756, -4245], ![-1663, 1803, -134, 3364, -6807]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [72, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 178], [0, 1]]
 g := ![![[118, 43], [92, 64], [141], [27], [61, 61], [77, 87], [1]], ![[129, 136], [150, 115], [141], [27], [10, 118], [16, 92], [1]]]
 h' := ![![[96, 178], [178, 36], [65, 171], [112, 61], [83, 57], [5, 47], [107, 96], [0, 1]], ![[0, 1], [54, 143], [13, 8], [61, 118], [6, 122], [42, 132], [15, 83], [96, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [77, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [72, 83, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-142813, -47050, 163756, 159593, -319237]
  a := ![-29, 11, 29, 41, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-85652, 1348, 163756, 159593, -319237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2343, -1420, -384, -580, 1252]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![2343, -1420, -384, -580, 1252]] 
 ![![179, 0, 0, 0, 0], ![122, 1, 0, 0, 0], ![152, 0, 1, 0, 0], ![154, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![2343, -1420, -384, -580, 1252], ![680, -453, -84, -104, 200], ![-368, 188, 203, 392, -944], ![-1548, 1008, 516, 911, -2124], ![-2096, 1292, 540, 920, -2109]]]
  hmulB := by decide  
  f := ![![![-1819, 548, 1104, 1964, -3500]], ![![-1170, 411, 660, 1264, -2224]], ![![-1448, 132, 1139, 1560, -2928]], ![![-3422, 472, 2556, 3687, -6844]], ![![-763, -56, 708, 820, -1601]]]
  g := ![![![1785, -1420, -384, -580, 1252], ![470, -453, -84, -104, 200], ![-624, 188, 203, 392, -944], ![-1882, 1008, 516, 911, -2124], ![-2107, 1292, 540, 920, -2109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![35516, -39763, -13123, -20407, 45725]] ![![-402, 348, 106, 259, -603]]
  ![![-258907, 185089, 98865, 175142, -409758]] where
 M := ![![![-258907, 185089, 98865, 175142, -409758]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-258907, 185089, 98865, 175142, -409758]] ![![2343, -1420, -384, -580, 1252]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![70592051, -50474957, -26953641, -47751114, 111715690]]]
 hmul := by decide  
 g := ![![![![394369, -281983, -150579, -266766, 624110]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87015, -51073, -14161, -21648, 46942]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![87015, -51073, -14161, -21648, 46942]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![135, 16, 1, 0, 0], ![6, 121, 0, 1, 0], ![165, 79, 0, 0, 1]] where
  M :=![![![87015, -51073, -14161, -21648, 46942], ![29624, -17384, -4815, -7358, 15952], ![10004, -5859, -1606, -2446, 5292], ![-13258, 7799, 2193, 3365, -7314], ![-44872, 26352, 7330, 11216, -24335]]]
  hmulB := by decide  
  f := ![![![2503, -2795, -933, -1440, 3226]], ![![4040, -4536, -1477, -2334, 5200]], ![![2257, -2526, -837, -1298, 2906]], ![![2804, -3139, -1032, -1621, 3614]], ![![4063, -4545, -1504, -2342, 5235]]]
  g := ![![![-31032, -5047, -14161, -21648, 46942], ![-10543, -1714, -4815, -7358, 15952], ![-3490, -565, -1606, -2446, 5292], ![4847, 792, 2193, 3365, -7314], ![16097, 2621, 7330, 11216, -24335]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [25, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 180], [0, 1]]
 g := ![![[3, 29], [137], [107, 116], [49], [74, 132], [166, 14], [1]], ![[0, 152], [137], [95, 65], [49], [129, 49], [21, 167], [1]]]
 h' := ![![[106, 180], [166, 36], [40, 104], [13, 109], [141, 7], [13, 133], [156, 106], [0, 1]], ![[0, 1], [0, 145], [23, 77], [164, 72], [159, 174], [174, 48], [170, 75], [106, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [104, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [25, 75, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56472, -116470, 148168, 59699, -170943]
  a := ![83, -1, -76, -85, 170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![43029, 20960, 148168, 59699, -170943]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-387, 230, 60, 94, -204]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-387, 230, 60, 94, -204]] 
 ![![181, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![-387, 230, 60, 94, -204], ![-132, 65, 32, 32, -76], ![-176, 40, 109, 152, -288], ![378, 230, -512, -355, 814], ![304, -8, -216, -160, 373]]]
  hmulB := by decide  
  f := ![![![-39539, 42598, 14660, 23138, -52120]], ![![-2793, 2995, 1036, 1638, -3692]], ![![-13860, 14864, 5141, 8128, -18320]], ![![-26173, 28076, 9708, 15347, -34590]], ![![-15603, 16718, 5788, 9154, -20635]]]
  g := ![![![-19, 230, 60, 94, -204], ![-7, 65, 32, 32, -76], ![-28, 40, 109, 152, -288], ![77, 230, -512, -355, 814], ![35, -8, -216, -160, 373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-527, 610, 202, 314, -704]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-527, 610, 202, 314, -704]] 
 ![![181, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![137, 0, 0, 1, 0], ![171, 0, 0, 0, 1]] where
  M :=![![![-527, 610, 202, 314, -704], ![-892, 1007, 332, 516, -1156], ![-1448, 1628, 535, 832, -1864], ![-722, 804, 268, 413, -926], ![-728, 806, 266, 412, -923]]]
  hmulB := by decide  
  f := ![![![2009, -1430, -766, -1354, 3164]], ![![546, -389, -208, -368, 860]], ![![736, -524, -281, -496, 1160]], ![![1695, -1202, -650, -1145, 2674]], ![![2031, -1444, -776, -1370, 3201]]]
  g := ![![![207, 610, 202, 314, -704], ![338, 1007, 332, 516, -1156], ![544, 1628, 535, 832, -1864], ![271, 804, 268, 413, -926], ![269, 806, 266, 412, -923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2

def I181N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -38, 10, -6, 8]] i)))

def SI181N3: IdealEqSpanCertificate' Table ![![15, -38, 10, -6, 8]] 
 ![![181, 0, 0, 0, 0], ![108, 1, 0, 0, 0], ![101, 0, 1, 0, 0], ![103, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![15, -38, 10, -6, 8], ![-92, 5, 60, 116, -196], ![952, 396, -1187, -992, 2136], ![574, -2180, 1356, -629, 162], ![424, -810, 314, -452, 491]]]
  hmulB := by decide  
  f := ![![![251783, -148390, -42006, -64650, 140732]], ![![150784, -88875, -25172, -38748, 84356]], ![![140927, -83090, -23569, -36298, 79044]], ![![143471, -84606, -24022, -37007, 80602]], ![![49684, -29322, -8358, -12892, 28099]]]
  g := ![![![19, -38, 10, -6, 8], ![-64, 5, 60, 116, -196], ![571, 396, -1187, -992, 2136], ![873, -2180, 1356, -629, 162], ![470, -810, 314, -452, 491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N3 : Nat.card (O ⧸ I181N3) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N3)

lemma isPrimeI181N3 : Ideal.IsPrime I181N3 := prime_ideal_of_norm_prime hp181.out _ NI181N3
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![87015, -51073, -14161, -21648, 46942]] ![![-387, 230, 60, 94, -204]]
  ![![-18353409, 10772689, 2987319, 4566922, -9903250]] where
 M := ![![![-18353409, 10772689, 2987319, 4566922, -9903250]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-18353409, 10772689, 2987319, 4566922, -9903250]] ![![-527, 610, 202, 314, -704]]
  ![![-350381641, 205659453, 57030391, 87186292, -189061186]] where
 M := ![![![-350381641, 205659453, 57030391, 87186292, -189061186]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N2 : IdealMulLeCertificate' Table 
  ![![-350381641, 205659453, 57030391, 87186292, -189061186]] ![![15, -38, 10, -6, 8]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-473315, 278559, 76201, 116926, -253762]]]
 hmul := by decide  
 g := ![![![![-2615, 1539, 421, 646, -1402]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2, I181N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
    exact isPrimeI181N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1 ⊙ MulI181N2)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2773, 1952, 1060, 1884, -4412]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-2773, 1952, 1060, 1884, -4412]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![123, 88, 36, 1, 0], ![48, 189, 96, 0, 1]] where
  M :=![![![-2773, 1952, 1060, 1884, -4412], ![-9112, 6467, 3480, 6176, -14456], ![-29728, 21176, 11355, 20128, -47104], ![-43796, 31260, 16736, 29643, -69348], ![-33936, 24220, 12964, 22968, -53737]]]
  hmulB := by decide  
  f := ![![![653, -384, -108, -164, 356]], ![![232, -139, -40, -64, 136]], ![![32, -72, 45, 32, -64]], ![![533, -324, -80, -129, 280]], ![![408, -269, -44, -88, 191]]]
  g := ![![![-119, 3508, 1868, 1884, -4412], ![-392, 11493, 6120, 6176, -14456], ![-1280, 37448, 19941, 20128, -47104], ![-1891, 55128, 29356, 29643, -69348], ![-1464, 42719, 22748, 22968, -53737]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [189, 160, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 178, 134], [92, 12, 57], [0, 1]]
 g := ![![[4, 89, 68], [55, 62, 97], [152, 11, 162], [144, 156, 160], [127, 161, 5], [99, 100, 1], []], ![[99, 103, 120, 45], [85, 18, 89, 26], [168, 70, 62, 134], [17, 188, 21, 3], [138, 135, 109, 125], [99, 142, 17, 5], [154, 2]], ![[179, 156, 131, 70], [106, 98, 179, 91], [36, 174, 41, 87], [74, 185, 181, 116], [3, 86, 166, 38], [101, 137, 85, 83], [40, 2]]]
 h' := ![![[8, 178, 134], [110, 82, 100], [113, 9, 80], [97, 150, 60], [63, 106, 55], [7, 22, 14], [0, 0, 1], [0, 1]], ![[92, 12, 57], [148, 17, 155], [149, 100, 65], [124, 75, 1], [170, 144, 157], [43, 91, 60], [181, 177, 12], [8, 178, 134]], ![[0, 1], [71, 92, 127], [108, 82, 46], [141, 157, 130], [134, 132, 170], [171, 78, 117], [140, 14, 178], [92, 12, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 75], []]
 b := ![[], [51, 49, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [189, 160, 91, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4759817187, -290009633, 4365504733, 5117838100, -9960443244]
  a := ![213, 9, -193, -208, 436]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-817553025, 7496670213, 4064533427, 5117838100, -9960443244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, -384, -108, -164, 356]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![653, -384, -108, -164, 356]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![68, 119, 1, 0, 0], ![156, 21, 0, 1, 0], ![185, 152, 0, 0, 1]] where
  M :=![![![653, -384, -108, -164, 356], ![232, -139, -40, -64, 136], ![32, -72, 45, 32, -64], ![-84, 172, -96, 13, 28], ![-336, 236, 20, 88, -167]]]
  hmulB := by decide  
  f := ![![![-2773, 1952, 1060, 1884, -4412]], ![![-9112, 6467, 3480, 6176, -14456]], ![![-6820, 4835, 2605, 4624, -10824]], ![![-3496, 2469, 1336, 2373, -5556]], ![![-10115, 7164, 3864, 6860, -16059]]]
  g := ![![![-169, -200, -108, -164, 356], ![-64, -77, -40, -64, 136], ![20, 19, 45, 32, -64], ![-4, 37, -96, 13, 28], ![81, 112, 20, 88, -167]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [96, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 190], [0, 1]]
 g := ![![[41, 2], [146, 77], [43, 23], [20, 6], [57, 2], [72, 86], [1]], ![[0, 189], [0, 114], [49, 168], [88, 185], [16, 189], [28, 105], [1]]]
 h' := ![![[75, 190], [118, 57], [74, 162], [181, 65], [67, 31], [155, 57], [95, 75], [0, 1]], ![[0, 1], [0, 134], [0, 29], [90, 126], [100, 160], [37, 134], [181, 116], [75, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [35, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [96, 116, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![420866, -642871, 181368, -442310, 562587]
  a := ![253, 13, -232, -241, 518]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-246023, -515447, 181368, -442310, 562587]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-2773, 1952, 1060, 1884, -4412]] ![![653, -384, -108, -164, 356]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-458, -803, 1085, 477, -1317]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-458, -803, 1085, 477, -1317]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![66, 141, 83, 190, 1]] where
  M :=![![![-458, -803, 1085, 477, -1317], ![-6306, 2898, 2983, 6796, -11658], ![52272, 21927, -63960, -56030, 118136], ![7883, -122391, 97901, -9982, -40741], ![13392, -45186, 27088, -14996, 6607]]]
  hmulB := by decide  
  f := ![![![-4452, 3897, 1221, 1889, -4195]], ![![-4562, 4742, 1541, 2392, -5346]], ![![-6456, 7109, 2336, 3630, -8128]], ![![-2769, 3263, 1087, 1692, -3797]], ![![-10368, 11081, 3623, 5628, -12591]]]
  g := ![![![448, 958, 572, 1299, -1317], ![3954, 8532, 5029, 11512, -11658], ![-40128, -86193, -51136, -116590, 118136], ![13973, 29130, 18028, 40056, -40741], ![-2190, -5061, -2701, -6582, 6607]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [169, 37, 109, 148, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 97, 162, 138], [180, 117, 79, 56], [5, 171, 145, 192], [0, 1]]
 g := ![![[155, 0, 181, 185], [159, 157, 50], [90, 21, 83], [45, 109, 184], [97, 180, 46], [179, 45, 1], []], ![[30, 90, 121, 96, 43, 16], [38, 101, 18], [50, 131, 6], [7, 191, 59], [87, 174, 27], [147, 51, 55], [129, 11, 82, 33, 50, 184]], ![[11, 80, 44, 10, 79, 118], [154, 54, 16], [48, 123, 187], [67, 112, 18], [153, 55, 54], [13, 77, 169], [1, 147, 142, 63, 131, 179]], ![[105, 8, 95, 82, 74, 128], [162, 119, 97], [123, 31, 1], [163, 3, 168], [36, 145, 36], [72, 13, 81], [165, 159, 107, 66, 4, 192]]]
 h' := ![![[53, 97, 162, 138], [106, 19, 65, 68], [166, 82, 78, 67], [124, 102, 151, 58], [3, 148, 184, 143], [50, 54, 78, 25], [0, 0, 0, 1], [0, 1]], ![[180, 117, 79, 56], [32, 100, 131, 43], [49, 160, 80, 156], [59, 46, 5, 44], [108, 158, 58, 32], [23, 12, 91, 42], [82, 187, 25, 21], [53, 97, 162, 138]], ![[5, 171, 145, 192], [130, 41, 142, 3], [78, 99, 35, 189], [85, 72, 44, 90], [139, 121, 1, 37], [110, 8, 78, 132], [143, 85, 52, 180], [180, 117, 79, 56]], ![[0, 1], [70, 33, 48, 79], [106, 45, 0, 167], [186, 166, 186, 1], [83, 152, 143, 174], [50, 119, 139, 187], [32, 114, 116, 184], [5, 171, 145, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 3, 79], []]
 b := ![[], [], [180, 32, 24, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [169, 37, 109, 148, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86488998098, -96844183056, 157563742343, 92232518730, -223776946433]
  a := ![67, 8, -61, -58, 137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![76076629360, 162982928829, 97052074074, 220776437000, -223776946433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4452, 3897, 1221, 1889, -4195]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-4452, 3897, 1221, 1889, -4195]] 
 ![![193, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![147, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![186, 0, 0, 0, 1]] where
  M :=![![![-4452, 3897, 1221, 1889, -4195], ![-4562, 4742, 1541, 2392, -5346], ![-6456, 7109, 2336, 3630, -8128], ![-2769, 3263, 1087, 1692, -3797], ![-1992, 2792, 954, 1488, -3353]]]
  hmulB := by decide  
  f := ![![![-458, -803, 1085, 477, -1317]], ![![-92, -89, 156, 97, -231]], ![![-78, -498, 495, 73, -391]], ![![-149, -967, 957, 146, -757]], ![![-372, -1008, 1186, 382, -1235]]]
  g := ![![![1802, 3897, 1221, 1889, -4195], ![2349, 4742, 1541, 2392, -5346], ![3595, 7109, 2336, 3630, -8128], ![1693, 3263, 1087, 1692, -3797], ![1516, 2792, 954, 1488, -3353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-458, -803, 1085, 477, -1317]] ![![-4452, 3897, 1221, 1889, -4195]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1648366, 967221, 268183, 409985, -889019]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-1648366, 967221, 268183, 409985, -889019]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![164, 167, 149, 1, 0], ![72, 183, 118, 0, 1]] where
  M :=![![![-1648366, 967221, 268183, 409985, -889019], ![-561010, 328806, 91129, 139308, -302050], ![-190064, 110785, 30644, 46838, -101512], ![248983, -146519, -40661, -62162, 134819], ![848672, -498510, -138272, -211388, 458413]]]
  hmulB := by decide  
  f := ![![![-136, 41, 83, 145, -261]], ![![870, 498, -1177, -936, 2030]], ![![1288, -4209, 2492, -1454, 704]], ![![1477, -2728, 1062, -1642, 1785]], ![![1482, -2048, 475, -1636, 2111]]]
  g := ![![![-24754, 483199, 223780, 409985, -889019], ![-8426, 164160, 76021, 139308, -302050], ![-2856, 55155, 25534, 46838, -101512], ![3739, -73286, -33945, -62162, 134819], ![12744, -249169, -115402, -211388, 458413]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [159, 160, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 97, 125], [196, 99, 72], [0, 1]]
 g := ![![[116, 41, 174], [81, 22], [0, 10, 105], [146, 60], [48, 136], [25, 10], [1]], ![[79, 10, 189, 115], [119, 105], [139, 106, 41, 180], [57, 49], [85, 107], [109, 39], [80, 0, 81, 67]], ![[184, 58, 186, 56], [149, 23], [113, 177, 39, 5], [140, 61], [175, 175], [11, 190], [25, 159, 127, 130]]]
 h' := ![![[74, 97, 125], [123, 90, 119], [0, 22, 131], [6, 58, 41], [163, 31, 116], [30, 177, 50], [38, 37, 73], [0, 1]], ![[196, 99, 72], [124, 56, 179], [85, 68, 156], [42, 98, 80], [35, 167, 190], [101, 49, 86], [80, 185, 32], [74, 97, 125]], ![[0, 1], [140, 51, 96], [114, 107, 107], [162, 41, 76], [84, 196, 88], [138, 168, 61], [161, 172, 92], [196, 99, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 59], []]
 b := ![[], [175, 193, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [159, 160, 124, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11536758792, -369414530, -9664742825, -12413712760, 23640981360]
  a := ![-287, -5, 258, 282, -588]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1752461896, -11439487170, -4820595645, -12413712760, 23640981360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-136, 41, 83, 145, -261]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-136, 41, 83, 145, -261]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![43, 96, 1, 0, 0], ![103, 142, 0, 1, 0], ![45, 147, 0, 0, 1]] where
  M :=![![![-136, 41, 83, 145, -261], ![870, 498, -1177, -936, 2030], ![1288, -4209, 2492, -1454, 704], ![-23929, -165, 20853, 25704, -49457], ![-9448, -880, 8934, 10128, -19903]]]
  hmulB := by decide  
  f := ![![![-1648366, 967221, 268183, 409985, -889019]], ![![-561010, 328806, 91129, 139308, -302050]], ![![-634146, 371912, 103101, 157613, -341757]], ![![-1264955, 741968, 205698, 314457, -681854]], ![![-790844, 463761, 128558, 196529, -426136]]]
  g := ![![![-35, 50, 83, 145, -261], ![287, -264, -1177, -936, 2030], ![62, -713, 2492, -1454, 704], ![-6815, 8214, 20853, 25704, -49457], ![-2747, 3193, 8934, 10128, -19903]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [11, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 196], [0, 1]]
 g := ![![[68, 136], [187], [165, 54], [121], [137], [169], [40, 1]], ![[189, 61], [187], [158, 143], [121], [137], [169], [80, 196]]]
 h' := ![![[40, 196], [101, 147], [155, 160], [8, 60], [123, 11], [60, 48], [151, 13], [0, 1]], ![[0, 1], [71, 50], [54, 37], [44, 137], [169, 186], [10, 149], [80, 184], [40, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [195, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [11, 157, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![108352, -387016, 235888, -118025, 41879]
  a := ![-188, -6, 171, 181, -385]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1204, -63091, 235888, -118025, 41879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-1648366, 967221, 268183, 409985, -889019]] ![![-136, 41, 83, 145, -261]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB2009I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB2009I4 : PrimesBelowBoundCertificateInterval O 151 197 2009 where
  m := 9
  g := ![3, 3, 3, 4, 3, 4, 2, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB2009I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1, I173N2, I173N3]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1, I181N2, I181N3]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact ![26569, 26569, 163]
    · exact ![4657463, 167, 167]
    · exact ![29929, 173, 173, 173]
    · exact ![32041, 32041, 179]
    · exact ![32761, 181, 181, 181]
    · exact ![6967871, 36481]
    · exact ![1387488001, 193]
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
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
      exact NI173N3
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
      exact NI181N3
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
  β := ![I157N1, I157N2, I163N2, I167N1, I167N2, I173N1, I173N2, I173N3, I179N2, I181N1, I181N2, I181N3, I193N1]
  Il := ![[I157N1, I157N2], [I163N2], [I167N1, I167N2], [I173N1, I173N2, I173N3], [I179N2], [I181N1, I181N2, I181N3], [], [I193N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
