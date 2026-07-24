
import IdealArithmetic.Examples.NF5_3_1822500000_3.RI5_3_1822500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![693, 1830, 10, -568, -1944]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![693, 1830, 10, -568, -1944]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![44, 46, 57, 32, 1]] where
  M :=![![![693, 1830, 10, -568, -1944], ![6640, 4341, 1512, -2212, 2904], ![-16040, 10372, -5899, 224, -41064], ![30124, 2330, 8722, -5787, 41512], ![-17952, -2956, -5032, 3828, -22183]]]
  hmulB := by decide  
  f := ![![![-761, 214, 34, -64, -88]], ![![224, -481, 80, -52, -328]], ![![1208, 708, -281, 272, 1016]], ![![-788, -222, 130, -145, -472]], ![![308, 302, -99, 84, 353]]]
  g := ![![![1287, 1362, 1654, 920, -1944], ![-1808, -1929, -2448, -1420, 2904], ![26728, 28348, 34847, 19616, -41064], ![-26812, -28466, -35186, -19913, 41512], ![14300, 15186, 18797, 10652, -22183]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [8, 56, 56, 50, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 14, 56, 9], [39, 11, 20, 17], [28, 41, 58, 41], [0, 1]]
 g := ![![[23, 38, 27, 6], [31, 42, 41, 62], [42, 27, 60], [21, 61, 21], [1], []], ![[44, 58, 63, 24, 1, 59], [36, 13, 62, 43, 46, 23], [51, 36, 24], [22, 45, 35], [13, 65, 36], [1, 40, 14]], ![[9, 19, 5, 58, 9, 29], [27, 43, 7, 45, 57, 40], [36, 62, 6], [28, 64, 35], [48, 62, 36], [8, 32, 21]], ![[22, 32, 54, 62, 1, 31], [44, 12, 42, 6, 5, 58], [36, 10, 9], [41, 24, 21], [48, 10, 10], [0, 34, 6]]]
 h' := ![![[17, 14, 56, 9], [20, 52, 5, 26], [28, 61, 38, 14], [30, 36, 9, 23], [59, 11, 11, 17], [0, 0, 1], [0, 1]], ![[39, 11, 20, 17], [36, 30, 8, 9], [31, 25, 38, 55], [29, 35, 1, 15], [65, 12, 16, 54], [13, 33, 27, 6], [17, 14, 56, 9]], ![[28, 41, 58, 41], [41, 58, 22, 7], [20, 49, 56, 19], [24, 38, 25, 26], [39, 22, 44, 13], [50, 20, 10, 6], [39, 11, 20, 17]], ![[0, 1], [13, 61, 32, 25], [5, 66, 2, 46], [62, 25, 32, 3], [16, 22, 63, 50], [47, 14, 29, 55], [28, 41, 58, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17, 2, 49], []]
 b := ![[], [], [12, 58, 43, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [8, 56, 56, 50, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16690650585351, -65809081773775, 55190109453030, 88923977114885, 176133245463160]
  a := ![-55, 82, -115, -139, -330]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-115420479847667, -121909527956405, -149020968387270, -82796117577705, 176133245463160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-761, 214, 34, -64, -88]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-761, 214, 34, -64, -88]] 
 ![![67, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![-761, 214, 34, -64, -88], ![224, -481, 80, -52, -328], ![1208, 708, -281, 272, 1016], ![-788, -222, 130, -145, -472], ![176, -308, 48, -28, -197]]]
  hmulB := by decide  
  f := ![![![693, 1830, 10, -568, -1944]], ![![337, 693, 26, -228, -624]], ![![-167, 346, -87, -56, -816]], ![![853, 1100, 136, -417, -512]], ![![363, 1622, -66, -460, -2101]]]
  g := ![![![29, 214, 34, -64, -88], ![489, -481, 80, -52, -328], ![-1279, 708, -281, 272, 1016], ![565, -222, 130, -145, -472], ![299, -308, 48, -28, -197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![693, 1830, 10, -568, -1944]] ![![-761, 214, 34, -64, -88]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4567, 6400, 674, -2356, -3574]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![4567, 6400, 674, -2356, -3574]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![2, 41, 37, 39, 1]] where
  M :=![![![4567, 6400, 674, -2356, -3574], ![9584, 15209, 1224, -5380, -10402], ![30848, 36126, 5315, -14176, -12550], ![-1500, 8300, -1338, -1773, -15802], ![-3176, -10438, 174, 3104, 12257]]]
  hmulB := by decide  
  f := ![![![-207, -40, 30, -36, -110]], ![![368, 11, -44, 36, 118]], ![![-400, 142, -7, -120, -158]], ![![132, -4, -30, -67, -82]], ![![74, 77, -45, -79, -61]]]
  g := ![![![165, 2154, 1872, 1930, -3574], ![428, 6221, 5438, 5638, -10402], ![788, 7756, 6615, 6694, -12550], ![424, 9242, 8216, 8655, -15802], ![-390, -7225, -6385, -6689, 12257]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [42, 20, 48, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 23, 32, 53], [53, 15, 67, 29], [50, 32, 43, 60], [0, 1]]
 g := ![![[1, 55, 59, 6], [15, 9, 12, 6], [57, 50, 34, 19], [8, 31, 29], [1], []], ![[14, 63, 35, 6, 67, 67], [44, 69, 40, 60, 9, 17], [24, 29, 12, 7, 7, 26], [15, 34, 48], [1, 53, 49], [22, 10, 40]], ![[68, 29, 59, 66, 14, 58], [4, 58, 48, 65, 34, 29], [45, 39, 53, 0, 26, 45], [45], [41, 61, 54], [7, 20, 60]], ![[21, 6, 55, 64, 42, 18], [3, 43, 40, 27, 0, 6], [13, 41, 21, 19, 38, 30], [46, 13, 38], [47, 27, 49], [70, 45, 50]]]
 h' := ![![[29, 23, 32, 53], [9, 6, 66, 52], [20, 19, 28, 52], [8, 5, 9, 44], [29, 51, 23, 61], [0, 0, 1], [0, 1]], ![[53, 15, 67, 29], [13, 14, 6, 67], [5, 51, 60, 28], [47, 28, 20, 31], [31, 10, 8, 41], [59, 48, 17, 64], [29, 23, 32, 53]], ![[50, 32, 43, 60], [37, 44, 28, 12], [23, 63, 58, 70], [4, 62, 63, 2], [30, 61, 20], [30, 42, 24, 14], [53, 15, 67, 29]], ![[0, 1], [61, 7, 42, 11], [47, 9, 67, 63], [65, 47, 50, 65], [68, 20, 20, 40], [57, 52, 29, 64], [50, 32, 43, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [48, 64, 9], []]
 b := ![[], [], [37, 50, 22, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [42, 20, 48, 10, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![358055163657160621, -1671893207626142602, 1382526166177107514, 2270661465791291748, 4375518706659530382]
  a := ![-689, 1003, -1441, -1754, -4137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-118211017600871833, -2550255777192491384, -2260727689862331220, -2371472790055357650, 4375518706659530382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![207, 40, -30, 36, 110]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![207, 40, -30, 36, 110]] 
 ![![71, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![207, 40, -30, 36, 110], ![-368, -11, 44, -36, -118], ![400, -142, 7, 120, 158], ![-132, 4, 30, 67, 82], ![-232, 2, 22, -40, -95]]]
  hmulB := by decide  
  f := ![![![-4567, -6400, -674, 2356, 3574]], ![![-2322, -3279, -340, 1204, 1858]], ![![-3715, -5106, -559, 1892, 2744]], ![![-1394, -2100, -190, 755, 1330]], ![![-4072, -5622, -610, 2080, 3049]]]
  g := ![![![-105, 40, -30, 36, 110], ![86, -11, 44, -36, -118], ![-111, -142, 7, 120, 158], ![-120, 4, 30, 67, 82], ![78, 2, 22, -40, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![4567, 6400, 674, -2356, -3574]] ![![207, 40, -30, 36, 110]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, 123, -101, -224, -228]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![55, 123, -101, -224, -228]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![7, 14, 1, 0, 0], ![19, 27, 0, 1, 0], ![67, 17, 0, 0, 1]] where
  M :=![![![55, 123, -101, -224, -228], ![464, 955, -646, -1502, -1548], ![3188, 6518, -4151, -9884, -10284], ![3030, 6101, -3789, -9093, -9484], ![-320, -672, 454, 1062, 1099]]]
  hmulB := by decide  
  f := ![![![-10257, 17, -3065, 1774, -15476]], ![![65452, -103, 19524, -11294, 98668]], ![![5853, -9, 1746, -1010, 8824]], ![![28563, -45, 8518, -4927, 43052]], ![![1909, -2, 565, -326, 2867]]]
  g := ![![![278, 157, -101, -224, -228], ![1880, 1053, -646, -1502, -1548], ![12453, 6936, -4151, -9884, -10284], ![11476, 6382, -3789, -9093, -9484], ![-1333, -745, 454, 1062, 1099]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [52, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 72], [0, 1]]
 g := ![![[36, 71], [9], [50], [14, 35], [19], [1]], ![[57, 2], [9], [50], [48, 38], [19], [1]]]
 h' := ![![[26, 72], [45, 61], [32, 3], [2, 59], [37, 53], [21, 26], [0, 1]], ![[0, 1], [25, 12], [37, 70], [3, 14], [28, 20], [40, 47], [26, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [69, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [52, 47, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![382270, -940725, 833243, 1251022, 2734007]
  a := ![-54, 80, -113, -137, -325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2909566, -1272080, 833243, 1251022, 2734007]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12315, -5870, 4300, -692, 28107]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![12315, -5870, 4300, -692, 28107]] 
 ![![73, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![12315, -5870, 4300, -692, 28107], ![-113812, -13716, -32445, 23032, -148839], ![641420, -34069, 194806, -102542, 1020579], ![-821470, -6244, -244136, 143535, -1225663], ![461988, 8786, 136734, -82014, 680695]]]
  hmulB := by decide  
  f := ![![![-20077, -30614, 8808, -7322, -32255]], ![![-6409, -11694, 3241, -2586, -11808]], ![![-13003, -15085, 4718, -3768, -16620]], ![![-10854, -18626, 5262, -4047, -18801]], ![![-9731, -16016, 4522, -3752, -16636]]]
  g := ![![![-14160, -5870, 4300, -692, 28107], ![85080, -13716, -32445, 23032, -148839], ![-554514, -34069, 194806, -102542, 1020579], ![676571, -6244, -244136, 143535, -1225663], ![-376945, 8786, 136734, -82014, 680695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, -133, -13, 48, 80]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-91, -133, -13, 48, 80]] 
 ![![73, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-91, -133, -13, 48, 80], ![-224, -315, -34, 114, 176], ![-476, -742, -69, 252, 488], ![-162, -163, -37, 57, 16], ![176, 216, 30, -82, -87]]]
  hmulB := by decide  
  f := ![![![2589, 2189, -745, 706, 2760]], ![![1535, 1378, -459, 432, 1704]], ![![2162, 1628, -579, 556, 2136]], ![![120, 187, -53, 47, 200]], ![![307, 309, -99, 92, 369]]]
  g := ![![![78, -133, -13, 48, 80], ![189, -315, -34, 114, 176], ![428, -742, -69, 252, 488], ![123, -163, -37, 57, 16], ![-139, 216, 30, -82, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2

def I73N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 22, -8, 8, 30]] i)))

def SI73N3: IdealEqSpanCertificate' Table ![![29, 22, -8, 8, 30]] 
 ![![73, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![29, 22, -8, 8, 30], ![-104, -25, 16, -16, -54], ![184, -2, -19, 32, 78], ![-72, 2, 8, -3, -14], ![-64, -14, 10, -12, -37]]]
  hmulB := by decide  
  f := ![![![-1011, -6, -300, 176, -1510]], ![![-688, -5, -204, 120, -1026]], ![![-601, 0, -179, 104, -904]], ![![576, -2, 172, -99, 870]], ![![-854, -2, -254, 148, -1281]]]
  g := ![![![-31, 22, -8, 8, 30], ![44, -25, 16, -16, -54], ![-35, -2, -19, 32, 78], ![4, 2, 8, -3, -14], ![28, -14, 10, -12, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N3 : Nat.card (O ⧸ I73N3) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N3)

lemma isPrimeI73N3 : Ideal.IsPrime I73N3 := prime_ideal_of_norm_prime hp73.out _ NI73N3
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![55, 123, -101, -224, -228]] ![![12315, -5870, 4300, -692, 28107]]
  ![![571045, 826499, 81471, -301030, -489739]] where
 M := ![![![571045, 826499, 81471, -301030, -489739]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![571045, 826499, 81471, -301030, -489739]] ![![-91, -133, -13, 48, 80]]
  ![![-313308271, -453463386, -44700110, 165161626, 268696085]] where
 M := ![![![-313308271, -453463386, -44700110, 165161626, 268696085]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N2 : IdealMulLeCertificate' Table 
  ![![-313308271, -453463386, -44700110, 165161626, 268696085]] ![![29, 22, -8, 8, 30]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![761245533, 1101780970, 108607940, -401293410, -652851775]]]
 hmul := by decide  
 g := ![![![![10428021, 15092890, 1487780, -5497170, -8943175]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2, I73N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
    exact isPrimeI73N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1 ⊙ MulI73N2)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 2, -4, 12, 25]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![43, 2, -4, 12, 25]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![46, 59, 46, 1, 0], ![46, 16, 22, 0, 1]] where
  M :=![![![43, 2, -4, 12, 25], ![-76, -18, 21, 24, 19], ![-28, -167, 80, 222, 193], ![-50, -120, 88, 191, 251], ![-52, 18, -10, -26, -61]]]
  hmulB := by decide  
  f := ![![![-339, -490, -48, 178, 289]], ![![-800, -1162, -115, 424, 691]], ![![-1916, -2763, -272, 1006, 1633]], ![![-1916, -2770, -273, 1009, 1640]], ![![-886, -1280, -126, 466, 757]]]
  g := ![![![-21, -14, -14, 12, 25], ![-26, -22, -19, 24, 19], ![-242, -207, -182, 222, 193], ![-258, -195, -180, 191, 251], ![50, 32, 32, -26, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [51, 56, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 73, 32], [21, 5, 47], [0, 1]]
 g := ![![[54, 30, 19], [43, 57, 2], [43, 65, 49], [18, 68, 5], [32, 1], []], ![[48, 52, 48, 25], [2, 29, 61, 11], [62, 1, 72, 65], [9, 78, 32, 50], [25, 25], [73, 76]], ![[4, 41, 27, 6], [58, 25, 56, 54], [53, 7, 70, 61], [55, 31, 57, 47], [64, 36], [58, 76]]]
 h' := ![![[11, 73, 32], [19, 23, 63], [19, 75, 70], [30, 45, 7], [27, 53, 20], [0, 0, 1], [0, 1]], ![[21, 5, 47], [76, 75, 24], [3, 50, 64], [38, 17, 53], [65, 28, 58], [32, 41, 5], [11, 73, 32]], ![[0, 1], [10, 60, 71], [73, 33, 24], [25, 17, 19], [17, 77, 1], [11, 38, 73], [21, 5, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 37], []]
 b := ![[], [10, 52, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [51, 56, 47, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![220804448095, -729122399761, 622183790099, 979050932438, 2005445958281]
  a := ![246, -359, 514, 624, 1475]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1735013323101, -1146585604381, -1120683166889, 979050932438, 2005445958281]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-339, -490, -48, 178, 289]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-339, -490, -48, 178, 289]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![18, 41, 1, 0, 0], ![32, 32, 0, 1, 0], ![54, 7, 0, 0, 1]] where
  M :=![![![-339, -490, -48, 178, 289], ![-800, -1162, -115, 424, 691], ![-1916, -2763, -272, 1006, 1633], ![-434, -634, -62, 231, 379], ![552, 798, 78, -290, -473]]]
  hmulB := by decide  
  f := ![![![43, 2, -4, 12, 25]], ![![-76, -18, 21, 24, 19]], ![![-30, -11, 11, 18, 18]], ![![-14, -8, 8, 17, 21]], ![![22, 0, -1, 10, 18]]]
  g := ![![![-263, -79, -48, 178, 289], ![-628, -188, -115, 424, 691], ![-1486, -446, -272, 1006, 1633], ![-344, -103, -62, 231, 379], ![430, 129, 78, -290, -473]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [66, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 78], [0, 1]]
 g := ![![[48, 36], [69, 18], [50, 2], [57, 2], [64], [1]], ![[76, 43], [4, 61], [34, 77], [41, 77], [64], [1]]]
 h' := ![![[71, 78], [28, 6], [18, 52], [30, 9], [53, 70], [13, 71], [0, 1]], ![[0, 1], [59, 73], [76, 27], [37, 70], [46, 9], [77, 8], [71, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [19, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [66, 8, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142295, -293608, 267156, 386678, 888364]
  a := ![-31, 46, -64, -76, -185]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-822935, -377712, 267156, 386678, 888364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![43, 2, -4, 12, 25]] ![![-339, -490, -48, 178, 289]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![162715, 234132, 23362, -85440, -137307]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![162715, 234132, 23362, -85440, -137307]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![51, 23, 21, 1, 0], ![1, 73, 67, 0, 1]] where
  M :=![![![162715, 234132, 23362, -85440, -137307], ![378348, 556342, 53041, -201588, -338745], ![951804, 1321857, 141776, -488106, -725331], ![162218, 303266, 15794, -102277, -250881], ![-237292, -381650, -29754, 134442, 265859]]]
  hmulB := by decide  
  f := ![![![-1615, -1284, 890, 1758, 1617]], ![![-2952, -8506, 5021, 12372, 13011]], ![![-27300, -53079, 32992, 79614, 83409]], ![![-9013, -17171, 10651, 25529, 26616]], ![![-24609, -50275, 31015, 75066, 78686]]]
  g := ![![![56114, 147261, 132737, -85440, -137307], ![132507, 360497, 325088, -201588, -338745], ![320127, 789126, 710713, -488106, -725331], ![67822, 252650, 228586, -102277, -250881], ![-88671, -275681, -248983, 134442, 265859]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [27, 31, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 73, 45], [10, 9, 38], [0, 1]]
 g := ![![[71, 24, 44], [15, 1, 49], [27, 33], [58, 31], [56, 2, 1], []], ![[7, 28, 31, 55], [57, 4, 15, 55], [34, 61], [78, 1], [14, 77, 28, 76], [79, 33]], ![[9, 46, 37, 44], [32, 29, 68, 12], [38, 12], [56, 78], [28, 48, 28, 65], [3, 33]]]
 h' := ![![[75, 73, 45], [10, 71, 58], [27, 1, 76], [3, 53, 38], [65, 36, 23], [0, 0, 1], [0, 1]], ![[10, 9, 38], [39, 23, 65], [60, 6, 65], [56, 59, 71], [81, 38, 1], [6, 57, 9], [75, 73, 45]], ![[0, 1], [79, 72, 43], [70, 76, 25], [10, 54, 57], [32, 9, 59], [19, 26, 73], [10, 9, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 5], []]
 b := ![[], [28, 66, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [27, 31, 81, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1179274525, 9560396544, -7648307090, -13136700774, -23715774048]
  a := ![-56, 84, -118, -150, -336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8343472759, 24613927950, 22375653860, -13136700774, -23715774048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1615, 1284, -890, -1758, -1617]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![1615, 1284, -890, -1758, -1617]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![4, 41, 1, 0, 0], ![55, 18, 0, 1, 0], ![16, 20, 0, 0, 1]] where
  M :=![![![1615, 1284, -890, -1758, -1617], ![2952, 8506, -5021, -12372, -13011], ![27300, 53079, -32992, -79614, -83409], ![24518, 49412, -30328, -72799, -75819], ![-3664, -5690, 3642, 8574, 8885]]]
  hmulB := by decide  
  f := ![![![-162715, -234132, -23362, 85440, 137307]], ![![-378348, -556342, -53041, 201588, 338745]], ![![-206204, -302029, -29035, 109578, 182688]], ![![-191829, -279454, -27174, 101567, 167472]], ![![-119676, -174594, -16926, 63426, 104891]]]
  g := ![![![1539, 1226, -890, -1758, -1617], ![10984, 8401, -5021, -12372, -13011], ![70754, 54301, -32992, -79614, -83409], ![64613, 49634, -30328, -72799, -75819], ![-7614, -5868, 3642, 8574, 8885]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [71, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 82], [0, 1]]
 g := ![![[36, 27], [61, 1], [77], [70], [9, 40], [1]], ![[80, 56], [78, 82], [77], [70], [25, 43], [1]]]
 h' := ![![[17, 82], [68, 39], [22, 1], [54, 34], [25, 30], [12, 17], [0, 1]], ![[0, 1], [67, 44], [39, 82], [51, 49], [37, 53], [52, 66], [17, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [20, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [71, 66, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![207967, -176156, 195442, 209996, 715272]
  a := ![-26, 45, -55, -58, -169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-283951, -316562, 195442, 209996, 715272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![162715, 234132, 23362, -85440, -137307]] ![![1615, 1284, -890, -1758, -1617]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![231, 483, -297, -720, -755]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![231, 483, -297, -720, -755]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![72, 6, 1, 0, 0], ![5, 5, 0, 1, 0], ![78, 83, 0, 0, 1]] where
  M :=![![![231, 483, -297, -720, -755], ![1580, 3146, -1939, -4662, -4865], ![10136, 20431, -12576, -30282, -31619], ![9296, 18695, -11513, -27717, -28945], ![-1092, -2220, 1366, 3292, 3441]]]
  hmulB := by decide  
  f := ![![![9175, 13273, 1307, -4832, -7857]], ![![21764, 31528, 3109, -11486, -18699]], ![![9472, 13705, 1350, -4990, -8115]], ![![1871, 2710, 267, -987, -1607]], ![![28170, 40792, 4021, -14858, -24180]]]
  g := ![![![945, 770, -297, -720, -755], ![6112, 4965, -1939, -4662, -4865], ![39700, 32266, -12576, -30282, -31619], ![36343, 29537, -11513, -27717, -28945], ![-4318, -3511, 1366, 3292, 3441]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [19, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 88], [0, 1]]
 g := ![![[29, 9], [9], [68], [53, 50], [5, 22], [1]], ![[54, 80], [9], [68], [4, 39], [76, 67], [1]]]
 h' := ![![[72, 88], [60, 3], [26, 3], [61, 54], [83, 36], [70, 72], [0, 1]], ![[0, 1], [9, 86], [64, 86], [33, 35], [5, 53], [3, 17], [72, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [58, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [19, 17, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44229, -165607, 140001, 224456, 446749]
  a := ![-22, 31, -46, -58, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-516905, -440540, 140001, 224456, 446749]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4099, -8308, 5116, 12338, 12898]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-4099, -8308, 5116, 12338, 12898]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![46, 71, 1, 0, 0], ![71, 16, 0, 1, 0], ![63, 60, 0, 0, 1]] where
  M :=![![![-4099, -8308, 5116, 12338, 12898], ![-26916, -54011, 33262, 80048, 83566], ![-174168, -350626, 215877, 519764, 542746], ![-159548, -320930, 197614, 475759, 496782], ![18892, 38100, -23456, -56492, -59001]]]
  hmulB := by decide  
  f := ![![![-3203, -2848, -648, 1250, -170]], ![![3180, -6783, 1674, 1112, 15850]], ![![194, -7063, 815, 1696, 11816]], ![![-1321, -3534, -14, 1093, 3780]], ![![-473, -6536, 560, 1682, 9953]]]
  g := ![![![-21663, -15088, 5116, 12338, 12898], ![-140506, -97869, 33262, 80048, 83566], ![-912368, -635493, 215877, 519764, 542746], ![-835123, -581692, 197614, 475759, 496782], ![99167, 69072, -23456, -56492, -59001]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [13, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 88], [0, 1]]
 g := ![![[82, 85], [40], [53], [59, 40], [45, 4], [1]], ![[74, 4], [40], [53], [50, 49], [53, 85], [1]]]
 h' := ![![[2, 88], [53, 21], [22, 29], [34, 63], [38, 29], [76, 2], [0, 1]], ![[0, 1], [6, 68], [80, 60], [71, 26], [7, 60], [80, 87], [2, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [63, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [13, 87, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![166325, -339252, 311692, 448696, 1033187]
  a := ![33, -48, 69, 80, 195]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1248536, -1029660, 311692, 448696, 1033187]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8335, -16770, 10326, 24860, 25959]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-8335, -16770, 10326, 24860, 25959]] 
 ![![89, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-8335, -16770, 10326, 24860, 25959], ![-54116, -108874, 67037, 161396, 168525], ![-351308, -706829, 435222, 1047806, 1094127], ![-321598, -647004, 398378, 959125, 1001485], ![38188, 76816, -47296, -113874, -118893]]]
  hmulB := by decide  
  f := ![![![969, 9298, -2086, 1650, 8093]], ![![-196, 1118, -217, 156, 859]], ![![1166, 3657, -902, 750, 3455]], ![![155, 4696, -1018, 789, 3968]], ![![-138, 536, -100, 70, 399]]]
  g := ![![![-16097, -16770, 10326, 24860, 25959], ![-104504, -108874, 67037, 161396, 168525], ![-678460, -706829, 435222, 1047806, 1094127], ![-621033, -647004, 398378, 959125, 1001485], ![73732, 76816, -47296, -113874, -118893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![231, 483, -297, -720, -755]] ![![-4099, -8308, 5116, 12338, 12898]]
  ![![138391699, 278433561, -171440927, -412751666, -430991031]] where
 M := ![![![138391699, 278433561, -171440927, -412751666, -430991031]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![138391699, 278433561, -171440927, -412751666, -430991031]] ![![-8335, -16770, 10326, 24860, 25959]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![160288788574715, 322489386549307, -198567511213735, -478060120296022, -499185406729190]]]
 hmul := by decide  
 g := ![![![![1800997624435, 3623476253363, -2231095631615, -5371462025798, -5608824794710]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2355, -2983, 1021, 324, 8410]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![2355, -2983, 1021, 324, 8410]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![76, 46, 25, 39, 1]] where
  M :=![![![2355, -2983, 1021, 324, 8410], ![-32992, -7027, -9076, 7422, -38162], ![167492, -17096, 51747, -24768, 279874], ![-222754, -3497, -66007, 39363, -329410], ![126144, 4652, 37094, -22946, 182187]]]
  hmulB := by decide  
  f := ![![![-181, -309, 189, 434, 438]], ![![-884, -1921, 1178, 2870, 3018]], ![![-6332, -12512, 7719, 18548, 19350]], ![![-5662, -11469, 7055, 16993, 17746]], ![![-4462, -8975, 5524, 13293, 13875]]]
  g := ![![![-6565, -4019, -2157, -3378, 8410], ![29560, 18025, 9742, 15420, -38162], ![-217556, -132900, -71599, -112782, 279874], ![255798, 156179, 84219, 132849, -329410], ![-141444, -86350, -46573, -73487, 182187]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [65, 29, 6, 48, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 53, 55, 2], [54, 31, 46, 38], [83, 12, 93, 57], [0, 1]]
 g := ![![[70, 64, 24, 22], [0, 27, 49], [93, 90, 65], [86, 48, 75], [67, 49, 1], []], ![[41, 58, 95, 35, 67, 72], [57, 88, 43], [12, 34, 70], [12, 81, 6], [34, 34, 36], [24, 89, 75, 58, 82, 8]], ![[43, 56, 75, 27, 4, 71], [18, 87, 9], [21, 66, 24], [69, 58, 22], [36, 63, 11], [27, 5, 58, 73, 19, 67]], ![[80, 79, 8, 2, 88, 87], [47, 51, 61], [64, 51, 86], [0, 33, 94], [29, 8, 54], [50, 24, 76, 84, 16, 20]]]
 h' := ![![[9, 53, 55, 2], [61, 47, 34, 33], [35, 59, 31, 90], [39, 78, 52, 29], [10, 13, 52, 50], [0, 0, 0, 1], [0, 1]], ![[54, 31, 46, 38], [29, 47, 36, 6], [57, 77, 85, 72], [62, 94, 74, 19], [39, 57, 60, 54], [42, 93, 31, 91], [9, 53, 55, 2]], ![[83, 12, 93, 57], [10, 19, 73, 9], [93, 50, 59, 94], [10, 68, 73, 11], [79, 83, 86, 64], [24, 32, 46, 37], [54, 31, 46, 38]], ![[0, 1], [84, 81, 51, 49], [61, 8, 19, 35], [27, 51, 92, 38], [67, 41, 93, 26], [20, 69, 20, 65], [83, 12, 93, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [61, 45, 10], []]
 b := ![[], [], [20, 78, 17, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [65, 29, 6, 48, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1178430962945, -4316970526911, 3645198290925, 5818680494100, 11679672147075]
  a := ![28, -41, 58, 70, 167]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9138934558915, -5583318446313, -2972645416350, -4635964260225, 11679672147075]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181, -309, 189, 434, 438]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-181, -309, 189, 434, 438]] 
 ![![97, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-181, -309, 189, 434, 438], ![-884, -1921, 1178, 2870, 3018], ![-6332, -12512, 7719, 18548, 19350], ![-5662, -11469, 7055, 16993, 17746], ![724, 1366, -844, -2010, -2085]]]
  hmulB := by decide  
  f := ![![![2355, -2983, 1021, 324, 8410]], ![![194, -749, 138, 150, 1514]], ![![1751, -207, 544, -252, 2972]], ![![-427, -2404, 130, 663, 3280]], ![![3267, -2443, 1235, 34, 8901]]]
  g := ![![![-644, -309, 189, 434, 438], ![-4384, -1921, 1178, 2870, 3018], ![-28189, -12512, 7719, 18548, 19350], ![-25838, -11469, 7055, 16993, 17746], ![3043, 1366, -844, -2010, -2085]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![2355, -2983, 1021, 324, 8410]] ![![-181, -309, 189, 434, 438]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22209, -1850, -6420, 4292, -30393]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-22209, -1850, -6420, 4292, -30393]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![16, 72, 8, 1, 0], ![15, 51, 6, 0, 1]] where
  M :=![![![-22209, -1850, -6420, 4292, -30393], ![130156, -4692, 39291, -21352, 203469], ![-856580, -9257, -254278, 150338, -1273569], ![1041922, -4128, 310944, -179109, 1574245], ![-580140, 4014, -173318, 99306, -879337]]]
  hmulB := by decide  
  f := ![![![26003, -2874, -2120, 2926, 6745]], ![![-21128, 10480, -35, -1016, 1387]], ![![-7580, -19467, 4994, -4274, -19127]], ![![-11418, 5546, 6, -571, 647]], ![![-7399, 3774, -35, -340, 571]]]
  g := ![![![3614, 12269, 1402, 4292, -30393], ![-25547, -87567, -10007, -21352, 203469], ![156847, 535826, 61232, 150338, -1273569], ![-195109, -667275, -76254, -179109, 1574245], ![109119, 373269, 42656, 99306, -879337]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [95, 55, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 84, 34], [83, 16, 67], [0, 1]]
 g := ![![[48, 80, 16], [83, 37], [52, 27, 37], [0, 71], [13, 79], [1]], ![[43, 24, 15, 94], [21, 14], [65, 34, 78, 67], [59, 20], [41, 70], [9, 23, 38, 15]], ![[69, 77, 96, 44], [18, 20], [44, 66, 26, 27], [50, 13], [70, 49], [31, 10, 29, 86]]]
 h' := ![![[86, 84, 34], [74, 25, 97], [9, 7, 21], [68, 28, 80], [13, 8, 77], [6, 46, 68], [0, 1]], ![[83, 16, 67], [68, 23, 79], [12, 54, 69], [45, 58, 10], [87, 27, 90], [12, 86, 26], [86, 84, 34]], ![[0, 1], [86, 53, 26], [33, 40, 11], [20, 15, 11], [15, 66, 35], [10, 70, 7], [83, 16, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 84], []]
 b := ![[], [34, 97, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [95, 55, 33, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2543807, -5765365, 3650911, 8499877, 9413588]
  a := ![4, -4, 8, 13, 20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2769759, -10869797, -1196333, 8499877, 9413588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26003, -2874, -2120, 2926, 6745]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![26003, -2874, -2120, 2926, 6745]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![15, 54, 1, 0, 0], ![14, 63, 0, 1, 0], ![38, 74, 0, 0, 1]] where
  M :=![![![26003, -2874, -2120, 2926, 6745], ![-21128, 10480, -35, -1016, 1387], ![-7580, -19467, 4994, -4274, -19127], ![12590, 7306, -2906, 2857, 10579], ![-14336, 6606, 86, -770, 521]]]
  hmulB := by decide  
  f := ![![![-22209, -1850, -6420, 4292, -30393]], ![![130156, -4692, 39291, -21352, 203469]], ![![57809, -2875, 17536, -9290, 91662]], ![![88424, -3224, 26697, -14497, 138290]], ![![81262, -4094, 24656, -13046, 128935]]]
  g := ![![![-2371, -5662, -2120, 2926, 6745], ![-585, -260, -35, -1016, 1387], ![6972, 13817, 4994, -4274, -19127], ![-3820, -7907, -2906, 2857, 10579], ![-244, 118, 86, -770, 521]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [55, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 100], [0, 1]]
 g := ![![[20, 92], [24], [34, 22], [77], [13], [11, 1]], ![[22, 9], [24], [74, 79], [77], [13], [22, 100]]]
 h' := ![![[11, 100], [71, 30], [49, 78], [56, 27], [94, 73], [1, 66], [0, 1]], ![[0, 1], [98, 71], [99, 23], [50, 74], [89, 28], [20, 35], [11, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [56, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [55, 90, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6711026, -13739576, 12515464, 18084450, 41652666]
  a := ![-209, 318, -440, -518, -1261]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19970342, -48625666, 12515464, 18084450, 41652666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-22209, -1850, -6420, 4292, -30393]] ![![26003, -2874, -2120, 2926, 6745]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [43, 84, 75, 30, 15, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 52, 101, 93, 29], [56, 92, 37, 52, 100], [42, 96, 69, 24, 13], [25, 68, 102, 37, 64], [0, 1]]
 g := ![![[8, 70, 101, 93, 46], [97, 71, 90, 19, 76], [2, 91, 17], [48, 49, 29, 18], [88, 1], []], ![[52, 93, 15, 34, 76, 18, 23, 34], [15, 33, 37, 62, 37, 51, 55, 98], [84, 2, 53, 31, 41, 55, 75, 83], [70, 10, 102, 30], [22, 67, 83, 63], [40, 10, 50, 66, 84, 10, 26, 81]], ![[42, 84, 26, 46, 67, 73, 88, 33], [1, 65, 4, 30, 26, 29, 31, 4], [34, 50, 58, 7, 42, 51, 75, 15], [77, 2, 91, 56], [18, 30, 42, 36], [86, 42, 52, 91, 11, 87, 58, 76]], ![[37, 23, 0, 19, 96, 81, 96, 46], [91, 52, 11, 76, 67, 76, 73, 16], [3, 81, 45, 70, 53, 41, 84, 19], [31, 21, 39, 13], [52, 10, 25, 4], [85, 15, 69, 66, 52, 7, 19, 34]], ![[27, 23, 57, 74, 38, 6, 9, 81], [97, 85, 5, 94, 41, 27, 33, 14], [85, 4, 58, 14, 33, 64, 81, 52], [81, 72, 43, 59], [35, 28, 33, 91], [6, 50, 29, 65, 69, 64, 85, 9]]]
 h' := ![![[68, 52, 101, 93, 29], [52, 6, 5, 87, 56], [17, 55, 75, 100, 30], [4, 45, 26, 74], [27, 84, 11, 66, 92], [0, 0, 0, 1], [0, 1]], ![[56, 92, 37, 52, 100], [95, 98, 13, 59, 26], [34, 81, 32, 95, 47], [89, 12, 7, 93, 94], [100, 45, 101, 51, 66], [4, 56, 101, 11, 28], [68, 52, 101, 93, 29]], ![[42, 96, 69, 24, 13], [62, 33, 28, 57, 68], [35, 36, 71, 2, 41], [77, 62, 87, 13, 43], [68, 85, 73, 94, 57], [11, 61, 36, 3, 97], [56, 92, 37, 52, 100]], ![[25, 68, 102, 37, 64], [28, 32, 32, 67, 70], [27, 40, 30, 3, 98], [35, 55, 88, 98, 7], [82, 28, 100, 34, 61], [84, 79, 14, 56, 101], [42, 96, 69, 24, 13]], ![[0, 1], [10, 37, 25, 39, 89], [57, 97, 101, 6, 93], [82, 32, 101, 31, 62], [28, 67, 24, 64, 33], [20, 10, 55, 32, 83], [25, 68, 102, 37, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 19, 9, 87], [], [], []]
 b := ![[], [57, 76, 34, 46, 100], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [43, 84, 75, 30, 15, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-87524078104649609, 259549356001083791, -224110901537116764, -346922402207004481, -727282741420937186]
  a := ![-48, 74, -101, -119, -289]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-849748331113103, 2519896660204697, -2175833995505988, -3368178662203927, -7060997489523662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB2088I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB2088I2 : PrimesBelowBoundCertificateInterval O 61 103 2088 where
  m := 9
  g := ![2, 2, 4, 2, 2, 3, 2, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB2088I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2, I73N3]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20151121, 67]
    · exact ![25411681, 71]
    · exact ![5329, 73, 73, 73]
    · exact ![493039, 6241]
    · exact ![571787, 6889]
    · exact ![7921, 7921, 89]
    · exact ![88529281, 97]
    · exact ![1030301, 10201]
    · exact ![11592740743]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
      exact NI73N3
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I67N1, I71N1, I73N1, I73N2, I73N3, I89N2, I97N1]
  Il := ![[I67N1], [I71N1], [I73N1, I73N2, I73N3], [], [], [I89N2], [I97N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
