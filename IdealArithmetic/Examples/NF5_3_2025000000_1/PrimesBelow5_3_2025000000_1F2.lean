
import IdealArithmetic.Examples.NF5_3_2025000000_1.RI5_3_2025000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-563361399, -597362073, -99778435, 23999756, 212358500]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-563361399, -597362073, -99778435, 23999756, 212358500]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![12, 51, 20, 1, 0], ![66, 39, 11, 0, 1]] where
  M :=![![![-563361399, -597362073, -99778435, 23999756, 212358500], ![88720416, 94074553, 15713671, -3779411, -33442296], ![-13972838, -14813480, -2472924, 596027, 5269210], ![2194042, 2335786, 398123, -88816, -811922], ![-211777226, -224558010, -37507803, 9022219, 79830161]]]
  hmulB := by decide  
  f := ![![![-331067, -749875, -538833, 77434, 602898]], ![![121720, 1461053, 981385, -229097, 221164]], ![![3649686, 2839152, 2353642, 64997, -8673954]], ![![850310, 1354211, 1006116, -102107, -1762078]], ![![392322, 682717, 502470, -56911, -791369]]]
  g := ![![![-221895813, -150795987, -43518165, 23999756, 212358500], ![34944252, 23747374, 6853241, -3779411, -33442296], ![-5505866, -3741941, -1079922, 596027, 5269210], ![848458, 575080, 165755, -88816, -811922], ![-83415440, -56687574, -16359462, 9022219, 79830161]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [45, 32, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 17, 43], [57, 49, 24], [0, 1]]
 g := ![![[28, 8, 25], [0, 63, 54], [16, 55], [33, 60], [3, 1], []], ![[0, 53, 42, 34], [58, 22, 50, 34], [45, 64], [35, 39], [9, 56], [41, 40]], ![[14, 8, 24, 4], [62, 30, 50, 39], [25, 40], [18, 60], [58, 21], [60, 40]]]
 h' := ![![[13, 17, 43], [0, 0, 62], [50, 29, 11], [57, 10, 16], [66, 60, 44], [0, 0, 1], [0, 1]], ![[57, 49, 24], [5, 17, 23], [14, 0, 44], [37, 62, 8], [65, 53, 46], [66, 10, 49], [13, 17, 43]], ![[0, 1], [2, 50, 49], [37, 38, 12], [31, 62, 43], [38, 21, 44], [13, 57, 17], [57, 49, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 52], []]
 b := ![[], [17, 27, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [45, 32, 64, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111036856, -63618583, -150053005, -88403740, -313046993]
  a := ![35, 19, 2, -11, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![325865422, 248564252, 75545354, -88403740, -313046993]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331067, 749875, 538833, -77434, -602898]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![331067, 749875, 538833, -77434, -602898]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![66, 47, 1, 0, 0], ![47, 1, 0, 1, 0], ![65, 3, 0, 0, 1]] where
  M :=![![![331067, 749875, 538833, -77434, -602898], ![-121720, -1461053, -981385, 229097, -221164], ![-3649686, -2839152, -2353642, -64997, 8673954], ![18257866, 31566106, 23247707, -2613630, -36905714], ![-3242370, -7022050, -5064391, 703865, 6024893]]]
  hmulB := by decide  
  f := ![![![563361399, 597362073, 99778435, -23999756, -212358500]], ![![-88720416, -94074553, -15713671, 3779411, 33442296]], ![![492924860, 522674721, 87303091, -20999218, -185808094]], ![![393836885, 417606076, 69753353, -16777915, -148456646]], ![![545732939, 578669688, 96656195, -23248778, -205713519]]]
  g := ![![![113371, -338644, 538833, -77434, -602898], ![1018773, 673111, -981385, 229097, -221164], ![-6105395, 1221271, -2353642, -64997, 8673954], ![15009272, -14145453, 23247707, -2613630, -36905714], ![-1398392, 3167549, -5064391, 703865, 6024893]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [66, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 66], [0, 1]]
 g := ![![[56, 6], [26, 4], [36], [35], [54], [1]], ![[57, 61], [49, 63], [36], [35], [54], [1]]]
 h' := ![![[56, 66], [26, 41], [51, 2], [45, 61], [55, 54], [1, 56], [0, 1]], ![[0, 1], [44, 26], [29, 65], [44, 6], [64, 13], [55, 11], [56, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [31, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [66, 11, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17100, -923, 17771, 12306, 44808]
  a := ![-27, -79, -1, 8, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-69864, -14670, 17771, 12306, 44808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-563361399, -597362073, -99778435, 23999756, 212358500]] ![![331067, 749875, 538833, -77434, -602898]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![429, 707, 698, -85, -892]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![429, 707, 698, -85, -892]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![23, 48, 50, 11, 1]] where
  M :=![![![429, 707, 698, -85, -892], ![-594, -2459, -1884, 358, 678], ![-3656, -746, -783, -452, 9460], ![25248, 37800, 28086, -2591, -53208], ![-5104, -9664, -6990, 862, 9999]]]
  hmulB := by decide  
  f := ![![![-6411, -6803, -1140, 271, 2410]], ![![1026, 1061, 156, -56, -426]], ![![-68, -230, -161, -68, -200]], ![![552, -324, -762, -433, -1512]], ![![-1379, -1735, -502, -64, 129]]]
  g := ![![![295, 613, 638, 137, -892], ![-228, -493, -504, -100, 678], ![-3116, -6406, -6673, -1472, 9460], ![17592, 36504, 37866, 8207, -53208], ![-3311, -6896, -7140, -1537, 9999]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [57, 47, 55, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 41, 43], [34, 12, 0, 17], [47, 17, 28, 54], [0, 1]]
 g := ![![[22, 39, 48, 64], [27, 61, 51, 1], [3, 55, 31, 12], [53, 64, 20], [1], []], ![[45, 56, 48, 7, 3], [11, 16, 31, 21, 27], [0, 48, 25, 55, 25], [35, 11, 49], [64, 27, 49], [3]], ![[44, 57, 11, 70, 22, 39], [63, 38, 12, 37, 19, 69], [21, 54, 2, 61, 22, 52], [36, 19, 40], [57, 12, 29], [20, 28, 5]], ![[21, 17, 41, 29, 26, 40], [67, 14, 19, 38, 11, 49], [41, 59, 31, 9, 13, 29], [57, 42, 32], [0, 55, 9], [39, 70, 5]]]
 h' := ![![[24, 41, 43], [23, 0, 9, 8], [42, 2, 27, 70], [15, 0, 67, 56], [14, 24, 16, 34], [0, 0, 1], [0, 1]], ![[34, 12, 0, 17], [22, 44, 32, 55], [32, 48, 56, 48], [66, 19, 60, 58], [59, 14, 39, 7], [50, 52, 30, 7], [24, 41, 43]], ![[47, 17, 28, 54], [30, 56, 62, 27], [0, 64, 44, 60], [57, 44, 4, 7], [60, 30, 55, 53], [16, 55, 70, 61], [34, 12, 0, 17]], ![[0, 1], [32, 42, 39, 52], [34, 28, 15, 35], [22, 8, 11, 21], [54, 3, 32, 48], [57, 35, 41, 3], [47, 17, 28, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 58, 48], []]
 b := ![[], [], [61, 32, 55, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [57, 47, 55, 37, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5198988835, 3510149820, 7606711837, 4266373931, 14843165484]
  a := ![12, 4, 1, -4, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4881574577, -9985377372, -10345796653, -2239555583, 14843165484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6411, 6803, 1140, -271, -2410]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![6411, 6803, 1140, -271, -2410]] 
 ![![71, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![6411, 6803, 1140, -271, -2410], ![-1026, -1061, -156, 56, 426], ![68, 230, 161, 68, 200], ![-552, 324, 762, 433, 1512], ![2376, 2580, 478, -74, -809]]]
  hmulB := by decide  
  f := ![![![-429, -707, -698, 85, 892]], ![![-330, -523, -524, 62, 694]], ![![-305, -577, -569, 77, 608]], ![![-555, -861, -720, 76, 1164]], ![![-55, -73, -108, 13, 123]]]
  g := ![![![-5384, 6803, 1140, -271, -2410], ![800, -1061, -156, 56, 426], ![-405, 230, 161, 68, 200], ![-1545, 324, 762, 433, 1512], ![-2125, 2580, 478, -74, -809]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![429, 707, 698, -85, -892]] ![![6411, 6803, 1140, -271, -2410]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-615, -4969, -3393, 754, -214]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-615, -4969, -3393, 754, -214]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![32, 24, 1, 0, 0], ![35, 40, 0, 1, 0], ![6, 48, 0, 0, 1]] where
  M :=![![![-615, -4969, -3393, 754, -214], ![-10984, -7503, -6365, -377, 26492], ![58262, 98000, 72350, -7873, -118786], ![-127350, -353898, -250485, 40858, 207462], ![9238, 51754, 35397, -7377, -5305]]]
  hmulB := by decide  
  f := ![![![-146267145, -155095057, -25905805, 6231132, 55135340]], ![![23034832, 24425159, 4079831, -981277, -8682872]], ![![-56593706, -60009376, -10023452, 2410963, 21333014]], ![![-57498449, -60968685, -10183656, 2449524, 21674114]], ![![2371024, 2514172, 419983, -100987, -893689]]]
  g := ![![![1135, 775, -3393, 754, -214], ![643, -15223, -6365, -377, 26492], ![-17379, 59976, 72350, -7873, -118786], ![71416, -81298, -250485, 40858, 207462], ![-11417, -3398, 35397, -7377, -5305]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [63, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 72], [0, 1]]
 g := ![![[29, 71], [16], [12], [56, 41], [4], [1]], ![[33, 2], [16], [12], [47, 32], [4], [1]]]
 h' := ![![[71, 72], [2, 61], [39, 4], [49, 42], [67, 25], [10, 71], [0, 1]], ![[0, 1], [26, 12], [31, 69], [38, 31], [17, 48], [14, 2], [71, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [63, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [63, 2, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38788, 86040, 129331, 52748, 131418]
  a := ![-51, -10, -3, 14, 124]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-93316, -156656, 129331, 52748, 131418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5937049, -19479851, -3472864, 694731, 7946254]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-5937049, -19479851, -3472864, 694731, 7946254]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![14, 21, 1, 0, 0], ![71, 11, 0, 1, 0], ![0, 18, 0, 0, 1]] where
  M :=![![![-5937049, -19479851, -3472864, 694731, 7946254], ![6166274, 20290119, 3664180, -693940, -8164162], ![-6613164, -20938854, -3508427, 888420, 9062688], ![5687496, 22530228, 5360790, 45253, -6044472], ![-2231592, -7067916, -1173726, 306586, 3085039]]]
  hmulB := by decide  
  f := ![![![-8487927, 25890533, 15997774, -5650851, 32311580]], ![![143735074, 165965201, 128476124, -6605630, -321375254]], ![![32182656, 37791997, 29183733, -1585980, -71720666]], ![![22897421, 89599766, 62203200, -11742642, -27600294]], ![![36057012, 36796434, 29032806, -838354, -82426445]]]
  g := ![![![-90998, -1331840, -3472864, 694731, 7946254], ![56678, 1341515, 3664180, -693940, -8164162], ![-281822, -1646067, -3508427, 888420, 9062688], ![-994199, 250087, 5360790, 45253, -6044472], ![-103658, -566066, -1173726, 306586, 3085039]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [63, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 72], [0, 1]]
 g := ![![[26, 65], [49], [9], [11, 19], [2], [1]], ![[63, 8], [49], [9], [60, 54], [2], [1]]]
 h' := ![![[41, 72], [53, 24], [72, 7], [37, 3], [47, 26], [10, 41], [0, 1]], ![[0, 1], [15, 49], [67, 66], [14, 70], [18, 47], [12, 32], [41, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [34, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [63, 32, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53636, 116602, 178847, 75196, 180676]
  a := ![65, 37, 5, -17, -158]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-108170, -105733, 178847, 75196, 180676]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 11, -1, -14]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![5, 0, 11, -1, -14]] 
 ![![73, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![5, 0, 11, -1, -14], ![-14, -43, -41, 7, 22], ![-54, 18, 16, -13, 150], ![482, 650, 481, -36, -1042], ![-106, -186, -133, 15, 213]]]
  hmulB := by decide  
  f := ![![![7529, 8012, 1365, -305, -2786]], ![![2870, 3057, 523, -115, -1058]], ![![1953, 2094, 369, -72, -700]], ![![5310, 5742, 1049, -174, -1834]], ![![6533, 6958, 1190, -262, -2409]]]
  g := ![![![10, 0, 11, -1, -14], ![3, -43, -41, 7, 22], ![-132, 18, 16, -13, 150], ![557, 650, 481, -36, -1042], ![-90, -186, -133, 15, 213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-615, -4969, -3393, 754, -214]] ![![-5937049, -19479851, -3472864, 694731, 7946254]]
  ![![215467753, 704364612, 125806775, -24969407, -286655850]] where
 M := ![![![215467753, 704364612, 125806775, -24969407, -286655850]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![215467753, 704364612, 125806775, -24969407, -286655850]] ![![5, 0, 11, -1, -14]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![2772934273, 9064717184, 1619047874, -321342642, -3689084784]]]
 hmul := by decide  
 g := ![![![![37985401, 124174208, 22178738, -4401954, -50535408]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24685, -26385, -20665, 776, 55984]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-24685, -26385, -20665, 776, 55984]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![36, 62, 1, 0, 0], ![59, 63, 0, 1, 0], ![6, 46, 0, 0, 1]] where
  M :=![![![-24685, -26385, -20665, 776, 55984], ![101104, 193043, 140791, -17561, -197552], ![-149250, -548616, -382052, 70547, 193134], ![-601390, 58910, -39761, -99864, 1626062], ![216758, 208602, 166205, -2907, -500217]]]
  hmulB := by decide  
  f := ![![![-396685, -1249879, -222987, 44410, 507490]], ![![393240, 1277995, 228181, -45347, -520020]], ![![122722, 416658, 74468, -14759, -170042]], ![![22673, 103094, 18521, -3623, -42804]], ![![197012, 643442, 114897, -22827, -261909]]]
  g := ![![![4273, -17333, -20665, 776, 55984], ![-34759, 20984, 140791, -17561, -197552], ![104855, 124177, -382052, 70547, 193134], ![-38410, -835232, -39761, -99864, 1626062], ![-32833, 165785, 166205, -2907, -500217]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [13, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 78], [0, 1]]
 g := ![![[6, 73], [10, 73], [13, 31], [14, 72], [1], [1]], ![[0, 6], [4, 6], [44, 48], [7, 7], [1], [1]]]
 h' := ![![[1, 78], [28, 51], [68, 28], [55, 30], [77, 54], [66, 1], [0, 1]], ![[0, 1], [0, 28], [17, 51], [6, 49], [52, 25], [67, 78], [1, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [48, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [13, 78, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9053, -1088, 11888, 11008, -25160]
  a := ![-42, -24, -2, 2, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11613, -3472, 11888, 11008, -25160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![290697, 973407, 173966, -34469, -396776]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![290697, 973407, 173966, -34469, -396776]] 
 ![![79, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![290697, 973407, 173966, -34469, -396776], ![-310986, -1020655, -182452, 36090, 415158], ![325056, 1060926, 188729, -38092, -433572], ![-333856, -1104496, -201698, 36361, 439160], ![106224, 355096, 63178, -12754, -145417]]]
  hmulB := by decide  
  f := ![![![1161969, 4018961, 2807752, -506545, -1597850]], ![![314068, 900813, 636348, -105522, -501170]], ![![631589, 3033735, 2087321, -419069, -551258]], ![![2219095, 6143723, 4350106, -708158, -3623694]], ![![-41248, -92284, -66378, 9454, 75543]]]
  g := ![![![-305918, 973407, 173966, -34469, -396776], ![320858, -1020655, -182452, 36090, 415158], ![-331985, 1060926, 188729, -38092, -433572], ![354315, -1104496, -201698, 36361, 439160], ![-111124, 355096, 63178, -12754, -145417]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![423, 1248, 880, -148, -662]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![423, 1248, 880, -148, -662]] 
 ![![79, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![423, 1248, 880, -148, -662], ![748, -1041, -590, 288, -2384], ![-8800, -11092, -8481, 562, 19328], ![30788, 64016, 46330, -6233, -58204], ![-4388, -12064, -8546, 1386, 7197]]]
  hmulB := by decide  
  f := ![![![22561, 28176, 4852, -1056, -10162]], ![![10782, 13431, 2318, -500, -4828]], ![![16287, 20436, 3551, -746, -7302]], ![![12974, 16408, 3006, -501, -5496]], ![![12664, 15832, 2738, -586, -5683]]]
  g := ![![![-775, 1248, 880, -148, -662], ![2096, -1041, -590, 288, -2384], ![251, -11092, -8481, 562, 19328], ![-27784, 64016, 46330, -6233, -58204], ![7098, -12064, -8546, 1386, 7197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2

def I79N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-501, -466, -77, 19, 160]] i)))

def SI79N3: IdealEqSpanCertificate' Table ![![-501, -466, -77, 19, 160]] 
 ![![79, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-501, -466, -77, 19, 160], ![54, -13, -5, -1, 6], ![26, 86, 6, -9, -58], ![10, -134, -79, -30, -74], ![-186, -178, -33, 5, 53]]]
  hmulB := by decide  
  f := ![![![497, 434, 351, 1, -1164]], ![![222, 167, 139, 5, -530]], ![![427, 496, 383, -20, -954]], ![![184, -62, -17, 38, -514]], ![![122, 114, 91, -1, -283]]]
  g := ![![![228, -466, -77, 19, 160], ![9, -13, -5, -1, 6], ![-26, 86, 6, -9, -58], ![157, -134, -79, -30, -74], ![93, -178, -33, 5, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N3 : Nat.card (O ⧸ I79N3) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N3)

lemma isPrimeI79N3 : Ideal.IsPrime I79N3 := prime_ideal_of_norm_prime hp79.out _ NI79N3
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-24685, -26385, -20665, 776, 55984]] ![![290697, 973407, 173966, -34469, -396776]]
  ![![85, 158, 29, -5, -58]] where
 M := ![![![85, 158, 29, -5, -58]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![85, 158, 29, -5, -58]] ![![423, 1248, 880, -148, -662]]
  ![![-497, -434, -351, -1, 1164]] where
 M := ![![![-497, -434, -351, -1, 1164]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N2 : IdealMulLeCertificate' Table 
  ![![-497, -434, -351, -1, 1164]] ![![-501, -466, -77, 19, 160]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2, I79N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
    exact isPrimeI79N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1 ⊙ MulI79N2)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![537, -2468, -1560, 498, -2356]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![537, -2468, -1560, 498, -2356]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![64, 39, 68, 1, 0], ![74, 46, 28, 0, 1]] where
  M :=![![![537, -2468, -1560, 498, -2356], ![-11684, -12871, -10034, 432, 26356], ![46664, 90284, 65765, -8306, -90736], ![-65188, -249832, -173618, 32541, 80540], ![-2148, 27904, 18158, -5044, 16153]]]
  hmulB := by decide  
  f := ![![![67027, 219532, 39212, -7782, -89356]], ![![-69764, -228141, -40754, 8084, 92836]], ![![72496, 236908, 42283, -8418, -96488]], ![![77392, 253207, 45196, -8995, -103128]], ![![45846, 150174, 26810, -5332, -61159]]]
  g := ![![![1723, 1042, 368, 498, -2356], ![-23972, -14965, -9366, 432, 26356], ![87864, 55278, 38207, -8306, -90736], ![-97684, -62937, -55922, 32541, 80540], ![-10538, -6246, -1098, -5044, 16153]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [45, 19, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 47, 71], [32, 35, 12], [0, 1]]
 g := ![![[5, 53, 23], [8, 9, 49], [8, 3], [0, 65], [46, 56, 1], []], ![[2, 51, 56, 34], [43, 64, 9, 56], [9, 10], [46, 12], [65, 58, 9, 74], [47, 61]], ![[33, 12, 29, 28], [53, 79, 30, 31], [39, 68], [11, 1], [1, 1, 25, 31], [23, 61]]]
 h' := ![![[24, 47, 71], [55, 31, 43], [16, 59, 76], [25, 70, 70], [5, 9, 56], [0, 0, 1], [0, 1]], ![[32, 35, 12], [26, 48, 54], [4, 80, 43], [49, 8, 33], [25, 55, 26], [38, 29, 35], [24, 47, 71]], ![[0, 1], [76, 4, 69], [72, 27, 47], [1, 5, 63], [9, 19, 1], [72, 54, 47], [32, 35, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 9], []]
 b := ![[], [81, 7, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [45, 19, 27, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3751444, -1058704, -618608, 351992, -10378344]
  a := ![23, 14, 4, 0, -54]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9026764, 5573704, 3205296, 351992, -10378344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67027, -219532, -39212, 7782, 89356]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-67027, -219532, -39212, 7782, 89356]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![5, 15, 1, 0, 0], ![8, 29, 0, 1, 0], ![58, 77, 0, 0, 1]] where
  M :=![![![-67027, -219532, -39212, 7782, 89356], ![69764, 228141, 40754, -8084, -92836], ![-72496, -236908, -42283, 8418, 96488], ![75124, 246112, 44138, -8611, -99740], ![-24476, -80136, -14302, 2848, 32645]]]
  hmulB := by decide  
  f := ![![![-537, 2468, 1560, -498, 2356]], ![![11684, 12871, 10034, -432, -26356]], ![![1517, 1387, 1115, -8, -3528]], ![![4816, 7745, 5748, -591, -9952]], ![![10490, 13329, 10180, -688, -22999]]]
  g := ![![![-61637, -81174, -39212, 7782, 89356], ![64038, 84333, 40754, -8084, -92836], ![-66563, -87667, -42283, 8418, 96488], ![68774, 90527, 44138, -8611, -99740], ![-22520, -29661, -14302, 2848, 32645]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [52, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 82], [0, 1]]
 g := ![![[79, 75], [], [17], [63], [0, 21], [1]], ![[75, 8], [], [17], [63], [52, 62], [1]]]
 h' := ![![[42, 82], [0, 65], [56], [44, 73], [0, 35], [31, 42], [0, 1]], ![[0, 1], [74, 18], [56], [39, 10], [59, 48], [52, 41], [42, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [81, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [52, 41, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3556, 6310, 11180, 5188, 11608]
  a := ![-19, -14, -1, 4, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9328, -14526, 11180, 5188, 11608]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![537, -2468, -1560, 498, -2356]] ![![-67027, -219532, -39212, 7782, 89356]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30595, -68643, -49362, 7045, 55960]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-30595, -68643, -49362, 7045, 55960]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![22, 8, 1, 0, 0], ![2, 47, 0, 1, 0], ![1, 62, 0, 0, 1]] where
  M :=![![![-30595, -68643, -49362, 7045, 55960], ![13290, 136885, 92192, -21182, 15690], ![327928, 245506, 205137, 7464, -782948], ![-1670392, -2863576, -2110802, 234993, 3385568], ![299080, 641936, 463322, -63946, -557905]]]
  hmulB := by decide  
  f := ![![![499627, 1635541, 292504, -57741, -664774]], ![![-521174, -1697541, -301040, 61540, 695902]], ![![82614, 271592, 48937, -9358, -109540]], ![![-270900, -879877, -155198, 32427, 362662]], ![![-355441, -1157445, -205170, 42017, 474701]]]
  g := ![![![11071, -39038, -49362, 7045, 55960], ![-22340, -6493, 92192, -21182, 15690], ![-38394, 525802, 205137, 7464, -782948], ![459682, -2325023, -2110802, 234993, 3385568], ![-103463, 387988, 463322, -63946, -557905]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [6, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 88], [0, 1]]
 g := ![![[5, 2], [57], [79], [33, 67], [60, 10], [1]], ![[34, 87], [57], [79], [70, 22], [27, 79], [1]]]
 h' := ![![[59, 88], [61, 64], [15, 71], [69, 48], [85, 45], [83, 59], [0, 1]], ![[0, 1], [10, 25], [21, 18], [53, 41], [70, 44], [4, 30], [59, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [53, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [6, 30, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38369, 68932, 115478, 52978, 123910]
  a := ![-55, -31, 0, 13, 134]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31559, -123902, 115478, 52978, 123910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1769, 1989, 1497, -64, -3972]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![1769, 1989, 1497, -64, -3972]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![22, 6, 1, 0, 0], ![46, 75, 0, 1, 0], ![51, 63, 0, 0, 1]] where
  M :=![![![1769, 1989, 1497, -64, -3972], ![-7048, -13607, -9863, 1241, 13712], ![10050, 37872, 26288, -4899, -12654], ![43278, -1374, 4809, 6692, -115950], ![-15302, -15050, -11965, 263, 35193]]]
  hmulB := by decide  
  f := ![![![-374693225, -397307763, -66363051, 15962306, 141240414]], ![![59008544, 62569983, 10451173, -2513827, -22243252]], ![![-88747108, -94103424, -15718270, 3780715, 33453174]], ![![-143918920, -152605131, -25489926, 6131085, 54250146]], ![![-174524377, -185057770, -30910547, 7434910, 65786863]]]
  g := ![![![1959, 2787, 1497, -64, -3972], ![-6140, -10240, -9863, 1241, 13712], ![3398, 11739, 26288, -4899, -12654], ![62282, 76098, 4809, 6692, -115950], ![-17517, -24496, -11965, 263, 35193]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [81, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 88], [0, 1]]
 g := ![![[68, 11], [68], [79], [85, 16], [3, 11], [1]], ![[0, 78], [68], [79], [67, 73], [24, 78], [1]]]
 h' := ![![[10, 88], [78, 10], [54, 35], [57, 41], [24, 4], [8, 10], [0, 1]], ![[0, 1], [0, 79], [48, 54], [22, 48], [64, 85], [19, 79], [10, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [23, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [81, 79, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22399, 37588, 60296, 26386, 71816]
  a := ![-37, -20, -3, 10, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-69947, -76714, 60296, 26386, 71816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17189, -13841, -6897, 4912, -51018]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![17189, -13841, -6897, 4912, -51018]] 
 ![![89, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![17189, -13841, -6897, 4912, -51018], ![-170804, -226179, -171807, 12751, 371080], ![563646, 1211508, 874310, -120803, -1050786], ![-410330, -2673074, -1820047, 391098, 95842], ![-123662, 198378, 114907, -52061, 403947]]]
  hmulB := by decide  
  f := ![![![873307, -252737, -62393, 1922, 179712]], ![![739669, -195264, -49382, 1005, 144100]], ![![690603, -222339, -53471, 2271, 151838]], ![![153803, -20689, -6554, -422, 21482]], ![![621935, -179757, -44388, 1363, 127891]]]
  g := ![![![52645, -13841, -6897, 4912, -51018], ![60917, -226179, -171807, 12751, 371080], ![-947909, 1211508, 874310, -120803, -1050786], ![3566169, -2673074, -1820047, 391098, 95842], ![-537395, 198378, 114907, -52061, 403947]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-30595, -68643, -49362, 7045, 55960]] ![![1769, 1989, 1497, -64, -3972]]
  ![![-617821201, -1848143648, -1302085057, 220459175, 957449802]] where
 M := ![![![-617821201, -1848143648, -1302085057, 220459175, 957449802]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-617821201, -1848143648, -1302085057, 220459175, 957449802]] ![![17189, -13841, -6897, 4912, -51018]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-637725605701493, -1550290629764717, -1107869233313248, 167070712028039, 1121811829256424]]]
 hmul := by decide  
 g := ![![![![-7165456243837, -17418995840053, -12447968913632, 1877199011551, 12604627295016]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [52, 19, 6, 17, 83, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 96, 83, 12, 3], [12, 38, 27, 13, 95], [43, 91, 51, 85, 50], [81, 65, 33, 84, 46], [0, 1]]
 g := ![![[21, 32, 84, 24, 95], [20, 57, 54, 73], [82, 7, 15, 81], [28, 32, 91, 31], [14, 1], []], ![[13, 3, 43, 78, 55, 7, 6, 12], [60, 28, 83, 6], [3, 5, 83, 2], [90, 47, 91, 11], [52, 6, 6, 86], [50, 37, 7, 39, 37, 5, 23, 27]], ![[34, 68, 9, 47, 31, 19, 36, 31], [94, 54, 83, 22], [21, 55, 18, 31], [74, 84, 36, 31], [53, 86, 20, 62], [24, 86, 75, 60, 64, 62, 44, 89]], ![[22, 67, 72, 56, 59, 64, 55, 11], [0, 14, 21, 85], [73, 52, 40, 48], [40, 67, 3, 88], [8, 5, 75, 93], [76, 18, 34, 55, 17, 38, 39, 64]], ![[14, 0, 94, 45, 24, 94, 10, 15], [4, 40, 65, 2], [75, 57, 49, 70], [19, 52, 83, 65], [79, 56, 55, 88], [28, 41, 9, 69, 19, 41, 71, 45]]]
 h' := ![![[72, 96, 83, 12, 3], [5, 82, 27, 27, 80], [47, 22, 44, 95, 48], [72, 62, 77, 51, 9], [48, 70, 91, 47, 82], [0, 0, 0, 1], [0, 1]], ![[12, 38, 27, 13, 95], [45, 54, 58, 66, 95], [62, 73, 30, 44, 54], [11, 53, 75, 47, 14], [36, 49, 87, 66, 37], [11, 4, 50, 94, 38], [72, 96, 83, 12, 3]], ![[43, 91, 51, 85, 50], [81, 67, 75, 68, 79], [64, 69, 55, 1, 33], [63, 88, 45, 12, 15], [82, 18, 5, 32, 15], [92, 42, 61, 75, 81], [12, 38, 27, 13, 95]], ![[81, 65, 33, 84, 46], [79, 47, 4, 42, 13], [51, 58, 7, 70, 45], [89, 62, 51, 60, 40], [36, 14, 5, 85, 31], [89, 34, 86, 7, 44], [43, 91, 51, 85, 50]], ![[0, 1], [10, 41, 30, 88, 24], [11, 69, 58, 81, 14], [82, 26, 43, 24, 19], [10, 43, 6, 61, 29], [74, 17, 94, 17, 31], [81, 65, 33, 84, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 92, 19, 41], [], [], []]
 b := ![[], [5, 67, 75, 78, 51], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [52, 19, 6, 17, 83, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-408034708636, 269779561812, 590680748250, 333399277344, 1162953424902]
  a := ![-1, 0, 0, 3, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4206543388, 2781232596, 6089492250, 3437105952, 11989210566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 8587340257 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![82249147, 268895376, 48026278, -9533014, -109436400]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![82249147, 268895376, 48026278, -9533014, -109436400]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![11, 32, 0, 1, 0], ![28, 29, 93, 0, 1]] where
  M :=![![![82249147, 268895376, 48026278, -9533014, -109436400], ![-85410604, -279232341, -49880810, 9894222, 113623124], ![88727140, 289928116, 51742809, -10303922, -118088948], ![-91922988, -301197276, -54034806, 10527121, 122022444], ![30037868, 98157164, 17516070, -3489622, -39984441]]]
  hmulB := by decide  
  f := ![![![81439, -3268816, -2149366, 565438, -1438384]], ![![-10792900, -10195601, -8149406, 112386, 24978428]], ![![48383452, 88221724, 64627297, -7699862, -96092588]], ![![-4246179, -6303012, -4720596, 432119, 8970916]], ![![41495776, 77747831, 56804973, -6956638, -81634313]]]
  g := ![![![32191401, 37105024, 101243678, -9533014, -109436400], ![-33422718, -38523941, -105117142, 9894222, 113623124], ![34738226, 40041912, 109247673, -10303922, -118088948], ![-35884651, -41353624, -112892298, 10527121, 122022444], ![11762258, 13558157, 36990783, -3489622, -39984441]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [85, 70, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 48, 7], [78, 52, 94], [0, 1]]
 g := ![![[74, 32, 24], [77, 5], [67, 23, 21], [1, 82], [32, 76], [1]], ![[58, 26, 59, 42], [37, 33], [34, 97, 83, 93], [87, 49], [3, 20], [11, 75, 67, 40]], ![[9, 17, 72, 59], [76, 54], [11, 8, 72, 51], [5, 65], [0, 6], [95, 9, 89, 61]]]
 h' := ![![[73, 48, 7], [26, 21, 78], [62, 21, 56], [0, 65, 83], [61, 69, 53], [16, 31, 50], [0, 1]], ![[78, 52, 94], [70, 10, 62], [65, 61, 29], [93, 95, 24], [32, 26, 7], [40, 4, 90], [73, 48, 7]], ![[0, 1], [80, 70, 62], [50, 19, 16], [67, 42, 95], [47, 6, 41], [59, 66, 62], [78, 52, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 20], []]
 b := ![[], [18, 26, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [85, 70, 51, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6438688071, -3579253857, -8491154020, -5015043613, -18119346926]
  a := ![147, 87, -1, -39, -356]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5633127542, 6756071313, 16600080298, -5015043613, -18119346926]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1787, 5194, 3666, -612, -2826]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![1787, 5194, 3666, -612, -2826]] 
 ![![101, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1787, 5194, 3666, -612, -2826], ![2916, -4621, -2672, 1218, -9504], ![-36060, -44844, -34351, 2200, 79428], ![128056, 264052, 191240, -25551, -242912], ![-18472, -50132, -35544, 5724, 30541]]]
  hmulB := by decide  
  f := ![![![-75985, -169474, -29886, 6152, 66886]], ![![-31126, -69065, -12180, 2506, 27236]], ![![-41050, -92032, -16251, 3328, 36296]], ![![-40851, -90882, -16130, 3233, 35602]], ![![-1778, -3976, -708, 140, 1553]]]
  g := ![![![-3713, 5194, 3666, -612, -2826], ![2904, -4621, -2672, 1218, -9504], ![33886, -44844, -34351, 2200, 79428], ![-192059, 264052, 191240, -25551, -242912], ![35946, -50132, -35544, 5724, 30541]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75, 102, 80, -6, -170]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![75, 102, 80, -6, -170]] 
 ![![101, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![75, 102, 80, -6, -170], ![-256, -557, -402, 56, 476], ![168, 1200, 815, -178, 0], ![2492, 1592, 1378, 103, -6052], ![-716, -904, -690, 46, 1569]]]
  hmulB := by decide  
  f := ![![![-97441, -318462, -56892, 11282, 129574]], ![![-55919, -182759, -32650, 6474, 74358]], ![![-53134, -173668, -31029, 6150, 70652]], ![![-43282, -141524, -25306, 4999, 57528]], ![![-12893, -42142, -7530, 1492, 17143]]]
  g := ![![![-77, 102, 80, -6, -170], ![451, -557, -402, 56, 476], ![-1054, 1200, 815, -178, 0], ![-910, 1592, 1378, 103, -6052], ![667, -904, -690, 46, 1569]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![82249147, 268895376, 48026278, -9533014, -109436400]] ![![1787, 5194, 3666, -612, -2826]]
  ![![97441, 318462, 56892, -11282, -129574]] where
 M := ![![![97441, 318462, 56892, -11282, -129574]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![97441, 318462, 56892, -11282, -129574]] ![![75, 102, 80, -6, -170]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2551, -1848, -1647, -53, 6120]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-2551, -1848, -1647, -53, 6120]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![90, 83, 1, 0, 0], ![49, 102, 0, 1, 0], ![90, 88, 0, 0, 1]] where
  M :=![![![-2551, -1848, -1647, -53, 6120], ![12982, 22353, 16565, -1859, -26282], ![-26538, -77274, -54634, 9129, 41922], ![-43962, 68118, 39363, -18118, 142698], ![22250, 13970, 12109, 967, -54125]]]
  hmulB := by decide  
  f := ![![![-154784317, -164126316, -27414339, 6593957, 58345836]], ![![24376274, 25847371, 4317235, -1038511, -9188806]], ![![-115642682, -122622403, -20481947, 4926436, 43591264]], ![![-49489753, -52476876, -8765448, 2108233, 18654882]], ![![-114987012, -121927162, -20365821, 4898503, 43344107]]]
  g := ![![![-3908, -3867, -1647, -53, 6120], ![9501, 11164, 16565, -1859, -26282], ![6507, -1582, -54634, 9129, 41922], ![-150890, -135033, 39363, -18118, 142698], ![36469, 35663, 12109, 967, -54125]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [94, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 102], [0, 1]]
 g := ![![[49, 14], [24, 100], [32, 18], [100], [58], [29, 1]], ![[43, 89], [40, 3], [39, 85], [100], [58], [58, 102]]]
 h' := ![![[29, 102], [10, 80], [82, 93], [41, 92], [45, 10], [55, 26], [0, 1]], ![[0, 1], [64, 23], [101, 10], [31, 11], [26, 93], [88, 77], [29, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [88, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [94, 74, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55238, 86536, 141230, 63871, 174691]
  a := ![54, 34, 1, -16, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-306969, -325468, 141230, 63871, 174691]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1795, -5868, -1048, 208, 2388]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-1795, -5868, -1048, 208, 2388]] 
 ![![103, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![-1795, -5868, -1048, 208, 2388], ![1864, 6093, 1088, -216, -2480], ![-1936, -6328, -1131, 224, 2576], ![2016, 6576, 1176, -235, -2688], ![-656, -2144, -384, 76, 873]]]
  hmulB := by decide  
  f := ![![![25555, 27092, 4520, -1088, -9628]], ![![2442, 2589, 432, -104, -920]], ![![751, 796, 133, -32, -284]], ![![18109, 19196, 3200, -771, -6820]], ![![19446, 20616, 3440, -828, -7327]]]
  g := ![![![-1373, -5868, -1048, 208, 2388], ![1426, 6093, 1088, -216, -2480], ![-1481, -6328, -1131, 224, 2576], ![1549, 6576, 1176, -235, -2688], ![-502, -2144, -384, 76, 873]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77301, 82188, 13616, -3374, -29518]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![77301, 82188, 13616, -3374, -29518]] 
 ![![103, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![95, 0, 0, 1, 0], ![90, 0, 0, 0, 1]] where
  M :=![![![77301, 82188, 13616, -3374, -29518], ![-11800, -13779, -2992, 120, 3356], ![5032, 664, -3831, -2512, -9344], ![16480, -12248, -24856, -13879, -48032], ![30152, 30160, 3524, -2166, -14217]]]
  hmulB := by decide  
  f := ![![![-379621, -426468, -331480, 15438, 853222]], ![![-26073, -17295, -14840, -970, 63082]], ![![-332695, -428676, -326799, 22826, 727234]], ![![-445101, -400972, -323200, 1335, 1037398]], ![![-299174, -339352, -263388, 12718, 671195]]]
  g := ![![![9641, 82188, 13616, -3374, -29518], ![783, -13779, -2992, 120, 3356], ![13621, 664, -3831, -2512, -9344], ![76751, -12248, -24856, -13879, -48032], ![8584, 30160, 3524, -2166, -14217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2

def I103N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -84, -15, 3, 34]] i)))

def SI103N3: IdealEqSpanCertificate' Table ![![-27, -84, -15, 3, 34]] 
 ![![103, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![102, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-27, -84, -15, 3, 34], ![26, 85, 15, -3, -34], ![-26, -86, -14, 3, 34], ![26, 86, 13, -2, -34], ![-10, -30, -5, 1, 13]]]
  hmulB := by decide  
  f := ![![![-105, -112, -15, 5, 34]], ![![-104, -111, -15, 5, 34]], ![![-104, -110, -14, 5, 34]], ![![-104, -110, -13, 6, 34]], ![![-62, -66, -9, 3, 21]]]
  g := ![![![75, -84, -15, 3, 34], ![-76, 85, 15, -3, -34], ![76, -86, -14, 3, 34], ![-76, 86, 13, -2, -34], ![26, -30, -5, 1, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N3 : Nat.card (O ⧸ I103N3) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N3)

lemma isPrimeI103N3 : Ideal.IsPrime I103N3 := prime_ideal_of_norm_prime hp103.out _ NI103N3
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-2551, -1848, -1647, -53, 6120]] ![![-1795, -5868, -1048, 208, 2388]]
  ![![201397, 661812, 113173, -22793, -266196]] where
 M := ![![![201397, 661812, 113173, -22793, -266196]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![201397, 661812, 113173, -22793, -266196]] ![![77301, 82188, 13616, -3374, -29518]]
  ![![-73675999, -240846736, -43017611, 8537969, 98017822]] where
 M := ![![![-73675999, -240846736, -43017611, 8537969, 98017822]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N2 : IdealMulLeCertificate' Table 
  ![![-73675999, -240846736, -43017611, 8537969, 98017822]] ![![-27, -84, -15, 3, 34]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-3912496303, -12789943424, -2284410014, 453401262, 5205147024]]]
 hmul := by decide  
 g := ![![![![-37985401, -124174208, -22178738, 4401954, 50535408]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2, I103N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
    exact isPrimeI103N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1 ⊙ MulI103N2)


lemma PB2201I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB2201I2 : PrimesBelowBoundCertificateInterval O 61 103 2201 where
  m := 9
  g := ![2, 2, 3, 4, 2, 3, 1, 3, 4]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB2201I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1, I79N2, I79N3]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1, I103N2, I103N3]
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
    · exact ![300763, 4489]
    · exact ![25411681, 71]
    · exact ![5329, 5329, 73]
    · exact ![6241, 79, 79, 79]
    · exact ![571787, 6889]
    · exact ![7921, 7921, 89]
    · exact ![8587340257]
    · exact ![1030301, 101, 101]
    · exact ![10609, 103, 103, 103]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
      exact NI79N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
      exact NI103N3
  β := ![I71N1, I73N2, I79N1, I79N2, I79N3, I89N2, I101N1, I101N2, I103N1, I103N2, I103N3]
  Il := ![[], [I71N1], [I73N2], [I79N1, I79N2, I79N3], [], [I89N2], [], [I101N1, I101N2], [I103N1, I103N2, I103N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
