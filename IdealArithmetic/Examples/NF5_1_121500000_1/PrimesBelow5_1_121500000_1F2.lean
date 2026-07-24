
import IdealArithmetic.Examples.NF5_1_121500000_1.RI5_1_121500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0, 0, 0]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]] where
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [7, 22, 1, 32, 51, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 41, 12, 21, 39], [63, 66, 49, 7, 22], [25, 20, 41, 6, 3], [21, 6, 32, 33, 3], [0, 1]]
 g := ![![[42, 55, 20, 52, 6], [27, 22, 23, 22, 49], [63, 16, 9, 10], [56, 23, 16, 1], [], []], ![[5, 1, 20, 10, 24, 38, 27, 15], [4, 26, 53, 31, 8, 41, 63, 6], [2, 30, 12, 59], [5, 28, 28, 36], [34, 40], [45, 57, 45, 47]], ![[29, 13, 47, 46, 41, 46, 44, 54], [65, 5, 13, 58, 63, 14, 52, 35], [54, 34, 34, 17], [58, 57, 22, 39], [43, 62], [28, 41, 12, 15]], ![[54, 14, 7, 15, 1, 38, 57, 46], [1, 14, 0, 60, 0, 53, 30, 51], [2, 28, 15, 25], [26, 11, 58, 36], [17, 50, 49, 60], [24, 60, 46, 9]], ![[53, 7, 63, 35, 36, 31, 17, 57], [14, 54, 16, 0, 11, 28, 40, 66], [36, 23, 14, 40], [59, 35, 53, 65], [5, 23, 55, 60], [31, 33, 7, 9]]]
 h' := ![![[41, 41, 12, 21, 39], [12, 25, 8, 61, 26], [61, 55, 40, 3, 7], [10, 14, 63, 37, 55], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[63, 66, 49, 7, 22], [25, 44, 34, 49, 50], [63, 66, 60, 17, 14], [55, 9, 34, 15, 27], [36, 63, 33, 66, 6], [26, 30, 46, 24], [41, 41, 12, 21, 39]], ![[25, 20, 41, 6, 3], [55, 10, 3, 32, 46], [43, 55, 45, 8, 37], [32, 20, 62, 37, 33], [6, 24, 57, 59, 46], [21, 43, 2, 14], [63, 66, 49, 7, 22]], ![[21, 6, 32, 33, 3], [52, 20, 63, 42, 44], [59, 33, 22, 39, 34], [41, 45, 4, 5, 62], [25, 38, 49, 32, 61], [55, 52, 47, 37, 23], [25, 20, 41, 6, 3]], ![[0, 1], [24, 35, 26, 17, 35], [3, 59, 34, 0, 42], [11, 46, 38, 40, 24], [25, 9, 62, 44, 20], [23, 9, 38, 59, 44], [21, 6, 32, 33, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 55, 16, 16], [], [], []]
 b := ![[], [47, 38, 49, 11, 58], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [7, 22, 1, 32, 51, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![507916327637, -844224770436, 427609413618, -178943959924, 55067209349]
  a := ![0, -8, -10, -22, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7580840711, -12600369708, 6382230054, -2670805372, 821898647]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 1350125107 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165837, -44848, 16455, 28962, 39349]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![165837, -44848, 16455, 28962, 39349]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![69, 4, 38, 1, 0], ![50, 60, 33, 0, 1]] where
  M :=![![![165837, -44848, 16455, 28962, 39349], ![236094, -64189, 23463, 41098, 55725], ![334350, -89420, 32634, 58770, 79413], ![120192, -32974, 12650, 20827, 29328], ![-125842, 33484, -12811, -22204, -31024]]]
  hmulB := by decide  
  f := ![![![34663, -25384, 2353, 8708, 12625]], ![![75750, -42651, -4051, 5580, 14373]], ![![86238, -23332, -22698, -20108, -9639]], ![![83169, -38478, -10435, -2633, 7173]], ![![127850, -64600, -12133, 1670, 16645]]]
  g := ![![![-53521, -35516, -33558, 28962, 39349], ![-75858, -50311, -47566, 41098, 55725], ![-108330, -71680, -67905, 58770, 79413], ![-39201, -26422, -24600, 20827, 29328], ![41654, 27940, 26123, -22204, -31024]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [28, 17, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 11, 17], [10, 59, 54], [0, 1]]
 g := ![![[56, 20, 29], [22, 6, 6], [51, 43, 5], [54, 1], [4, 1], []], ![[49, 17, 64, 14], [21, 50, 34, 53], [3, 69, 18, 62], [15, 27], [12, 2], [39, 5]], ![[70, 19, 18, 19], [31, 7, 3, 40], [57, 58, 7, 3], [54, 2], [38, 50], [2, 5]]]
 h' := ![![[65, 11, 17], [23, 19, 61], [63, 7, 19], [27, 39, 54], [30, 46, 70], [0, 0, 1], [0, 1]], ![[10, 59, 54], [32, 45, 17], [50, 62, 33], [66, 65, 15], [29, 21, 13], [9, 59, 59], [65, 11, 17]], ![[0, 1], [57, 7, 64], [46, 2, 19], [24, 38, 2], [20, 4, 59], [44, 12, 11], [10, 59, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 57], []]
 b := ![[], [68, 56, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [28, 17, 67, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4354267133, -6125577728, 2702214841, -1096917455, 442243962]
  a := ![3, -126, -123, -313, -430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![815906668, -398204868, 419591935, -1096917455, 442243962]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-853937, 229702, -84711, -148828, -201905]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-853937, 229702, -84711, -148828, -201905]] 
 ![![71, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-853937, 229702, -84711, -148828, -201905], ![-1211430, 325859, -121031, -212096, -287253], ![-1723518, 466214, -173490, -303844, -410817], ![-626736, 174504, -63708, -112391, -151680], ![650846, -176110, 66013, 115314, 155634]]]
  hmulB := by decide  
  f := ![![![-640371, 1491542, -1116669, 377050, -657953]], ![![-181872, 339539, -203137, 77358, -70073]], ![![204657, -96060, -159265, 14084, -318470]], ![![-599304, 1071616, -605328, 238209, -165292]], ![![-345002, 787258, -579485, 197368, -331810]]]
  g := ![![![155750, 229702, -84711, -148828, -201905], ![222025, 325859, -121031, -212096, -287253], ![317832, 466214, -173490, -303844, -410817], ![116980, 174504, -63708, -112391, -151680], ![-120653, -176110, 66013, 115314, 155634]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![573, -155, 55, 98, 134]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![573, -155, 55, 98, 134]] 
 ![![71, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![573, -155, 55, 98, 134], ![804, -212, 77, 136, 186], ![1116, -285, 110, 190, 258], ![372, -89, 43, 69, 90], ![-416, 103, -41, -70, -95]]]
  hmulB := by decide  
  f := ![![![-37, 95, -79, 24, -58]], ![![-32, 74, -57, 18, -38]], ![![-7, 52, -63, 16, -64]], ![![-61, 130, -92, 31, -52]], ![![-21, 50, -40, 12, -29]]]
  g := ![![![-114, -155, 55, 98, 134], ![-161, -212, 77, 136, 186], ![-234, -285, 110, 190, 258], ![-96, -89, 43, 69, 90], ![88, 103, -41, -70, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![165837, -44848, 16455, 28962, 39349]] ![![-853937, 229702, -84711, -148828, -201905]]
  ![![-108186015097, 29274749970, -10722563328, -18886438204, -25629504570]] where
 M := ![![![-108186015097, 29274749970, -10722563328, -18886438204, -25629504570]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-108186015097, 29274749970, -10722563328, -18886438204, -25629504570]] ![![573, -155, 55, 98, 134]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-46783949459517, 12659569924321, -4636864204127, -8167249432082, -11083220371412]]]
 hmul := by decide  
 g := ![![![![-658928865627, 178303801751, -65307946537, -115031682142, -156101695372]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [72, 69, 5, 53, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 8, 11, 30, 70], [29, 22, 32, 20, 21], [55, 5, 6, 13, 47], [33, 37, 24, 10, 8], [0, 1]]
 g := ![![[7, 41, 5, 18, 49], [48, 51, 22, 72], [65, 61, 13, 4], [25, 1, 66, 51, 1], [], []], ![[51, 61, 21, 48, 34, 12, 33, 71], [57, 8, 49, 38], [64, 56, 68, 41], [32, 37, 40, 38, 71, 48, 25, 65], [50, 12, 23, 27], [31, 59, 60, 9]], ![[15, 5, 15, 44, 18, 6, 59, 10], [53, 45, 57, 37], [40, 45, 33, 23], [52, 6, 65, 1, 27, 55, 41, 20], [67, 71, 15, 48], [7, 33, 44, 3]], ![[9, 68, 65, 59, 32, 20, 60, 56], [62, 10, 68, 50], [26, 68, 32, 38], [4, 36, 12, 36, 66, 1, 10, 10], [37, 10, 38, 38], [55, 69, 1, 19]], ![[22, 16, 38, 3, 1, 66, 71, 6], [17, 55, 41, 23], [60, 59, 34, 6], [9, 0, 64, 58, 38, 42, 14, 64], [67, 62, 62, 64], [26, 20, 66, 64]]]
 h' := ![![[7, 8, 11, 30, 70], [42, 22, 1, 26, 66], [33, 42, 10, 0, 46], [25, 28, 18, 7, 2], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[29, 22, 32, 20, 21], [7, 33, 58, 57, 5], [60, 5, 33, 59, 44], [19, 63, 47, 34, 25], [26, 35, 38, 29, 63], [7, 3, 67, 2, 63], [7, 8, 11, 30, 70]], ![[55, 5, 6, 13, 47], [47, 13, 61, 44, 56], [40, 59, 16, 7, 57], [0, 21, 61, 27, 60], [48, 0, 38, 17, 40], [45, 23, 72, 21, 62], [29, 22, 32, 20, 21]], ![[33, 37, 24, 10, 8], [60, 28, 38, 35, 45], [61, 40, 8, 0, 59], [53, 69, 52, 53, 44], [14, 71, 58, 41, 33], [14, 36, 30, 5, 29], [55, 5, 6, 13, 47]], ![[0, 1], [11, 50, 61, 57, 47], [33, 0, 6, 7, 13], [22, 38, 41, 25, 15], [29, 40, 12, 59, 9], [20, 11, 49, 45, 65], [33, 37, 24, 10, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 54, 69, 24], [], [], []]
 b := ![[], [32, 51, 20, 60, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [72, 69, 5, 53, 22, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41802631086, -18474802113, 85295907570, -15555760676, 121643585697]
  a := ![1, -9, -9, -23, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-572638782, -253079481, 1168437090, -213092612, 1666350489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 2073071593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491253, 6278219, -9208513, 2335272, -9806186]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![491253, 6278219, -9208513, 2335272, -9806186]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![55, 11, 56, 1, 0], ![65, 58, 61, 0, 1]] where
  M :=![![![491253, 6278219, -9208513, 2335272, -9806186], ![-58837116, 62261314, -1192695, 8201162, 43430190], ![260581140, -355839979, 113892666, -64642284, -81083598], ![-213832236, 407577697, -250186583, 93912257, -94016550], ![-20724436, -106857523, 174222197, -42649824, 194204375]]]
  hmulB := by decide  
  f := ![![![-2939701, 1605233, 195497, -161366, -503914]], ![![-3023484, 621828, 939953, 914724, 543546]], ![![3261276, -4973629, 2080098, 3536986, 3857706]], ![![9803, -2440114, 1750859, 2561121, 2517062]], ![![-2146003, -2026183, 2442344, 3244414, 2935135]]]
  g := ![![![6448777, 6953785, 5799919, 2335272, -9806186], ![-42188144, -32239272, -39363283, 8201162, 43430190], ![115016970, 64026251, 109872912, -64642284, -81083598], ![9266701, 61107630, 2857425, 93912257, -94016550], ![-130357829, -137994471, -117517146, -42649824, 194204375]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [30, 48, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 44, 29], [61, 34, 50], [0, 1]]
 g := ![![[39, 58, 38], [4, 55, 52], [74, 38, 1], [35, 54, 20], [76, 1], []], ![[42, 75, 38, 15], [2, 44, 14, 27], [25, 52, 25, 59], [36, 15, 14, 14], [13, 50], [29, 51]], ![[46, 1, 47, 21], [7, 70, 36, 26], [66, 65, 11, 36], [7, 33, 15, 51], [78, 40], [8, 51]]]
 h' := ![![[15, 44, 29], [38, 39, 65], [71, 24, 62], [56, 60, 1], [11, 35, 40], [0, 0, 1], [0, 1]], ![[61, 34, 50], [15, 49, 23], [20, 8, 39], [74, 11, 36], [16, 28, 5], [66, 57, 34], [15, 44, 29]], ![[0, 1], [56, 70, 70], [28, 47, 57], [8, 8, 42], [55, 16, 34], [5, 22, 44], [61, 34, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 58], []]
 b := ![[], [43, 58, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [30, 48, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-409860226, 559740472, -201148569, 102239426, 68125161]
  a := ![1, 44, 49, 114, 175]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-132419799, -57166488, -127622674, 102239426, 68125161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2939701, -1605233, -195497, 161366, 503914]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![2939701, -1605233, -195497, 161366, 503914]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![41, 46, 1, 0, 0], ![5, 69, 0, 1, 0], ![59, 75, 0, 0, 1]] where
  M :=![![![2939701, -1605233, -195497, 161366, 503914], ![3023484, -621828, -939953, -914724, -543546], ![-3261276, 4973629, -2080098, -3536986, -3857706], ![-13084860, 9373705, -740555, -3070509, -4552626], ![2029436, -2916743, 1165381, 2012642, 2215659]]]
  hmulB := by decide  
  f := ![![![-491253, -6278219, 9208513, -2335272, 9806186]], ![![58837116, -62261314, 1192695, -8201162, -43430190]], ![![30706137, -35007436, 4031903, -5169080, -19172804]], ![![54065025, -59936702, 4791457, -8499605, -36121970]], ![![55753471, -62445012, 5804205, -8990106, -36365869]]]
  g := ![![![-247882, -525825, -195497, 161366, 503914], ![989929, 1854404, -939953, -914724, -543546], ![4143194, 8025799, -2080098, -3536986, -3857706], ![3813106, 7553814, -740555, -3070509, -4552626], ![-2361244, -4576848, 1165381, 2012642, 2215659]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [27, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 78], [0, 1]]
 g := ![![[7, 21], [77, 76], [49, 51], [60, 49], [13], [1]], ![[67, 58], [12, 3], [48, 28], [42, 30], [13], [1]]]
 h' := ![![[48, 78], [54, 69], [20, 47], [39, 29], [62, 7], [52, 48], [0, 1]], ![[0, 1], [48, 10], [64, 32], [9, 50], [3, 72], [65, 31], [48, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [76, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [27, 31, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29301, -31723, 869, -6342, -24108]
  a := ![-1, -7, -13, -23, -54]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18326, 27519, 869, -6342, -24108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![491253, 6278219, -9208513, 2335272, -9806186]] ![![2939701, -1605233, -195497, 161366, 503914]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65133, -127717, 265333, -60452, 321242]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-65133, -127717, 265333, -60452, 321242]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![37, 11, 15, 51, 1]] where
  M :=![![![-65133, -127717, 265333, -60452, 321242], ![1927452, -2108946, 133073, -293174, -1326438], ![-7958628, 11052417, -3728558, 2039500, 2220270], ![5697084, -11540315, 7589557, -2742991, 3451314], ![1607968, 2010321, -5000863, 1088360, -6343277]]]
  hmulB := by decide  
  f := ![![![41657, -10099, 3519, 6302, 8882]], ![![53292, -10696, 5085, 8180, 11166]], ![![66996, -11605, 8650, 12378, 15582]], ![![20100, -5177, 5635, 7545, 8178]], ![![49827, -11170, 7228, 10715, 13219]]]
  g := ![![![-143989, -44113, -54859, -198118, 321242], ![614526, 150384, 241321, 811508, -1326438], ![-1085646, -161091, -446176, -1339690, 2220270], ![-1469898, -596443, -532291, -2153735, 3451314], ![2847099, 864896, 1086124, 3910789, -6343277]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [13, 65, 36, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 24, 64, 43], [77, 67, 17, 56], [13, 74, 2, 67], [0, 1]]
 g := ![![[7, 61, 79, 81], [3, 68, 50, 28], [60, 3, 16], [21, 58, 63], [82, 1], []], ![[44, 26, 59, 54, 77, 56], [8, 65, 82, 16, 45, 46], [71, 37, 77], [44, 27, 68], [3, 22, 43, 37, 21, 60], [17, 3, 23]], ![[78, 26, 54, 57, 54, 42], [63, 62, 40, 3, 29, 2], [31, 54, 81], [62, 54, 75], [43, 10, 71, 78, 13, 46], [45, 13, 65]], ![[29, 55, 12, 45, 63, 24], [24, 14, 75, 59, 16, 50], [16, 1, 51], [14, 81, 9], [57, 72, 26, 60, 62, 66], [28, 12, 7]]]
 h' := ![![[75, 24, 64, 43], [44, 49, 28, 74], [76, 55, 74, 51], [62, 63, 8, 79], [13, 52, 54, 48], [0, 0, 1], [0, 1]], ![[77, 67, 17, 56], [38, 16, 63, 27], [13, 38, 57, 13], [40, 4, 74, 49], [60, 51, 75, 20], [9, 49, 23, 17], [75, 24, 64, 43]], ![[13, 74, 2, 67], [75, 28, 12, 48], [10, 3, 65, 70], [9, 22, 34, 74], [20, 40, 52, 18], [32, 3, 62, 22], [77, 67, 17, 56]], ![[0, 1], [19, 73, 63, 17], [36, 70, 53, 32], [24, 77, 50, 47], [66, 23, 68, 80], [54, 31, 80, 44], [13, 74, 2, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [39, 22, 41], []]
 b := ![[], [], [29, 56, 42, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [13, 65, 36, 1, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3125617331, 12148172316, -12051652862, 3558983574, -9976450284]
  a := ![0, -4, 10, -2, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4409675219, 1468543680, 1657772306, 6172987326, -9976450284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41657, -10099, 3519, 6302, 8882]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![41657, -10099, 3519, 6302, 8882]] 
 ![![83, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![72, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![41657, -10099, 3519, 6302, 8882], ![53292, -10696, 5085, 8180, 11166], ![66996, -11605, 8650, 12378, 15582], ![20100, -5177, 5635, 7545, 8178], ![-21920, 2311, -3349, -4274, -5091]]]
  hmulB := by decide  
  f := ![![![-65133, -127717, 265333, -60452, 321242]], ![![465, -70033, 94310, -24654, 96260]], ![![-152388, 22371, 185246, -27868, 305418]], ![![19986, -234443, 289641, -78205, 281546]], ![![-1030, -15787, 22865, -5824, 24205]]]
  g := ![![![-6512, -10099, 3519, 6302, 8882], ![-9640, -10696, 5085, 8180, 11166], ![-16769, -11605, 8650, 12378, 15582], ![-11035, -5177, 5635, 7545, 8178], ![6621, 2311, -3349, -4274, -5091]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-65133, -127717, 265333, -60452, 321242]] ![![41657, -10099, 3519, 6302, 8882]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-377, 114, -44, -62, -90]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-377, 114, -44, -62, -90]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![21, 64, 44, 62, 1]] where
  M :=![![![-377, 114, -44, -62, -90], ![-540, 147, -38, -94, -102], ![-612, 42, -49, -154, -258], ![-504, 422, -166, 25, -24], ![420, -322, 168, -6, 109]]]
  hmulB := by decide  
  f := ![![![-1, 6, -4, -6, -6]], ![![-36, 31, -6, -14, -18]], ![![-108, 70, -1, -18, -30]], ![![-72, 26, 14, 9, 0]], ![![-129, 76, 4, -14, -29]]]
  g := ![![![17, 66, 44, 62, -90], ![18, 75, 50, 70, -102], ![54, 186, 127, 178, -258], ![0, 22, 10, 17, -24], ![-21, -82, -52, -76, 109]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [80, 71, 60, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 58, 31, 83], [34, 69, 24, 69], [27, 50, 34, 26], [0, 1]]
 g := ![![[42, 51, 43, 84], [42, 23, 73], [62, 76, 34], [26, 62, 27, 42], [83, 1], []], ![[6, 20, 85, 33, 6, 33], [41, 68, 80], [11, 67, 40], [79, 44, 70, 22, 37, 65], [17, 54, 8, 85, 71, 35], [31, 35, 36]], ![[47, 6, 13, 40, 37, 25], [35, 30, 55], [80, 86, 88], [48, 31, 13, 61, 55, 55], [7, 79, 56, 63, 20, 47], [28, 22, 44]], ![[3, 24, 65, 79, 52, 13], [5, 21, 69], [17, 16, 73], [85, 65, 78, 4, 86, 58], [33, 43, 51, 67, 19, 33], [64, 26, 53]]]
 h' := ![![[22, 58, 31, 83], [0, 68, 68, 23], [45, 84, 68, 42], [56, 26, 78, 52], [35, 79, 22, 65], [0, 0, 1], [0, 1]], ![[34, 69, 24, 69], [13, 15, 68, 67], [0, 53, 69, 13], [41, 56, 59, 29], [59, 10, 46, 87], [51, 43, 84, 3], [22, 58, 31, 83]], ![[27, 50, 34, 26], [84, 56, 33, 56], [6, 78, 74, 77], [40, 0, 25, 55], [45, 66, 15, 8], [73, 54, 76, 10], [34, 69, 24, 69]], ![[0, 1], [34, 39, 9, 32], [73, 52, 56, 46], [86, 7, 16, 42], [33, 23, 6, 18], [59, 81, 17, 76], [27, 50, 34, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 57, 79], []]
 b := ![[], [], [26, 70, 66, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [80, 71, 60, 6, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9844956274, -12920091330, 3606604235, -2270327446, -3766767575]
  a := ![13, -8, -12, -24, -49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![999405341, 2563517230, 1902745815, 2598531036, -3766767575]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 6, -4, -6, -6]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-1, 6, -4, -6, -6]] 
 ![![89, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-1, 6, -4, -6, -6], ![-36, 31, -6, -14, -18], ![-108, 70, -1, -18, -30], ![-72, 26, 14, 9, 0], ![60, -38, 0, 10, 17]]]
  hmulB := by decide  
  f := ![![![-377, 114, -44, -62, -90]], ![![-328, 99, -38, -54, -78]], ![![-45, 12, -5, -8, -12]], ![![-281, 88, -34, -45, -66]], ![![-80, 22, -8, -14, -19]]]
  g := ![![![1, 6, -4, -6, -6], ![-12, 31, -6, -14, -18], ![-41, 70, -1, -18, -30], ![-31, 26, 14, 9, 0], ![22, -38, 0, 10, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-377, 114, -44, -62, -90]] ![![-1, 6, -4, -6, -6]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
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


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [12, 71, 0, 47, 28, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 49, 8, 43, 71], [33, 6, 12, 10, 20], [8, 41, 82, 96, 96], [24, 0, 92, 45, 7], [0, 1]]
 g := ![![[32, 73, 85, 64, 36], [61, 18, 21, 53], [35, 6, 49, 61], [2, 9, 70, 66], [69, 1], []], ![[45, 69, 79, 26, 26, 25, 84, 68], [4, 95, 83, 33], [37, 53, 91, 3], [50, 62, 32, 43], [62, 94, 8, 49], [24, 91, 49, 10, 66, 76, 48, 78]], ![[28, 67, 85, 5, 52, 13, 30, 87], [85, 38, 9, 53], [5, 3, 65, 64], [84, 62, 25, 4], [19, 90, 80, 79], [63, 75, 9, 11, 51, 87, 42, 46]], ![[45, 88, 76, 31, 8, 29, 14, 96], [5, 49, 86, 9], [73, 0, 13, 3], [36, 82, 64, 35], [42, 75, 65, 43], [92, 18, 47, 85, 55, 75, 25, 96]], ![[31, 92, 53, 2, 28, 38, 45, 26], [80, 23, 48, 53], [27, 77, 89, 44], [70, 57, 64, 1], [47, 64, 16, 8], [76, 41, 3, 59, 16, 42, 18, 52]]]
 h' := ![![[4, 49, 8, 43, 71], [53, 65, 38, 40, 91], [3, 25, 44, 52, 21], [61, 80, 23, 93, 35], [45, 36, 26, 55, 58], [0, 0, 0, 1], [0, 1]], ![[33, 6, 12, 10, 20], [33, 38, 93, 51, 13], [9, 92, 62, 63, 18], [68, 91, 58, 64, 87], [59, 61, 35, 49, 72], [67, 41, 31, 40, 90], [4, 49, 8, 43, 71]], ![[8, 41, 82, 96, 96], [82, 18, 74, 5, 40], [61, 78, 93, 73, 76], [11, 61, 61, 13, 8], [90, 50, 67, 10, 2], [67, 67, 87, 51, 51], [33, 6, 12, 10, 20]], ![[24, 0, 92, 45, 7], [64, 71, 81, 55, 1], [30, 46, 93, 24, 3], [18, 24, 96, 0, 87], [81, 22, 79, 34, 61], [87, 57, 23, 70, 25], [8, 41, 82, 96, 96]], ![[0, 1], [89, 2, 5, 43, 49], [46, 50, 96, 79, 76], [51, 35, 53, 24, 74], [42, 25, 84, 46, 1], [11, 29, 53, 32, 28], [24, 0, 92, 45, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 94, 12, 71], [], [], []]
 b := ![[], [11, 76, 29, 79, 96], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [12, 71, 0, 47, 28, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-623163211, 1084165508, -611524375, 245876570, -182617923]
  a := ![-1, -4, -1, -8, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6424363, 11176964, -6304375, 2534810, -1882659]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-773387, 937368, -177008, 149868, 405600]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-773387, 937368, -177008, 149868, 405600]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![43, 36, 78, 1, 0], ![22, 9, 77, 0, 1]] where
  M :=![![![-773387, 937368, -177008, 149868, 405600], ![2433600, -3639727, 1492836, -715612, -317592], ![-1905552, 5433968, -4672931, 1474020, -3340896], ![-11239488, 10960768, 1037128, 1236801, 9592200], ![15123936, -18464584, 3643080, -2978092, -7745651]]]
  hmulB := by decide  
  f := ![![![175025, -51096, 13040, 26612, 38592]], ![![231552, -55467, 14108, 28732, 43896]], ![![263376, -32880, 17161, 26620, 40704]], ![![360511, -66532, 23934, 42149, 63480]], ![![258670, -41119, 17141, 28604, 43261]]]
  g := ![![![-159811, -80280, -426712, 149868, 405600], ![397940, 247333, 809556, -715612, -317592], ![81300, -173888, 1362401, 1474020, -3340896], ![-2727231, -1187068, -8257750, 1236801, 9592200], ![3104814, 1568887, 8241083, -2978092, -7745651]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [75, 98, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 19, 32], [97, 81, 69], [0, 1]]
 g := ![![[33, 20, 4], [13, 84], [31, 100, 100], [48, 31], [46, 96], [1]], ![[99, 6, 38, 91], [91, 92], [65, 25, 40, 98], [72, 82], [6, 54], [78, 50, 95, 44]], ![[26, 78, 11, 26], [21, 36], [66, 66, 100, 44], [90, 25], [44, 92], [36, 44, 65, 57]]]
 h' := ![![[50, 19, 32], [39, 41, 99], [99, 91, 36], [23, 78, 10], [54, 63, 58], [26, 3, 46], [0, 1]], ![[97, 81, 69], [56, 39, 39], [35, 0, 71], [49, 31, 74], [46, 33, 48], [71, 8, 85], [50, 19, 32]], ![[0, 1], [88, 21, 64], [42, 10, 95], [60, 93, 17], [89, 5, 96], [64, 90, 71], [97, 81, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 50], []]
 b := ![[], [40, 18, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [75, 98, 55, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8595729, 6932879, 2775915, 427948, 9372906]
  a := ![3, 3, 14, 13, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2308925, -919103, -7448691, 427948, 9372906]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1457171, -887646, -29754, 177820, 345746]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![1457171, -887646, -29754, 177820, 345746]] 
 ![![101, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![1457171, -887646, -29754, 177820, 345746], ![2074476, -814985, -364080, -217540, 29682], ![178092, 1285082, -1002843, -1440144, -1394286], ![-5220096, 4155046, -592634, -1660003, -2243844], ![-9224, -783510, 566004, 826684, 811275]]]
  hmulB := by decide  
  f := ![![![516231, -995266, 619070, -230724, 242222]], ![![80835, -135935, 69942, -29088, 10276]], ![![43263, -173620, 174147, -51236, 145500]], ![![610998, -1101066, 628518, -245883, 180016]], ![![125705, -238552, 145550, -54840, 53625]]]
  g := ![![![-153167, -887646, -29754, 177820, 345746], ![408375, -814985, -364080, -217540, 29682], ![1926851, 1285082, -1002843, -1440144, -1394286], ![1910166, 4155046, -592634, -1660003, -2243844], ![-1100739, -783510, 566004, 826684, 811275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-252501, 68326, -25026, -44080, -59818]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-252501, 68326, -25026, -44080, -59818]] 
 ![![101, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-252501, 68326, -25026, -44080, -59818], ![-358908, 97119, -35572, -62656, -85026], ![-510156, 138046, -50563, -89060, -120858], ![-183120, 49554, -18150, -31967, -43380], ![193024, -52234, 19132, 33696, 45727]]]
  hmulB := by decide  
  f := ![![![527, 794, -810, -1112, -1030]], ![![111, 317, -278, -392, -372]], ![![-98, 318, -183, -284, -290]], ![![225, 660, -576, -815, -774]], ![![271, 148, -230, -296, -259]]]
  g := ![![![30535, 68326, -25026, -44080, -59818], ![43403, 97119, -35572, -62656, -85026], ![61694, 138046, -50563, -89060, -120858], ![22143, 49554, -18150, -31967, -43380], ![-23341, -52234, 19132, 33696, 45727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-773387, 937368, -177008, 149868, 405600]] ![![1457171, -887646, -29754, 177820, 345746]]
  ![![527, 794, -810, -1112, -1030]] where
 M := ![![![527, 794, -810, -1112, -1030]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![527, 794, -810, -1112, -1030]] ![![-252501, 68326, -25026, -44080, -59818]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37261, 11358, -2867, -5884, -8467]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-37261, 11358, -2867, -5884, -8467]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![29, 11, 19, 1, 0], ![25, 36, 61, 0, 1]] where
  M :=![![![-37261, 11358, -2867, -5884, -8467], ![-50802, 13257, -2993, -6452, -9903], ![-59418, 9074, -3098, -5536, -9003], ![-1608, -9144, -1236, 827, 1848], ![21022, -1642, 555, 970, 2130]]]
  hmulB := by decide  
  f := ![![![-6159, 6550, -169, 870, 4501]], ![![27006, -36965, 11921, -6730, -8283]], ![![-49698, 90178, -51978, 20218, -15531]], ![![-8601, 14843, -7960, 3229, -1627]], ![![-20305, 40802, -26604, 9660, -11844]]]
  g := ![![![3350, 3698, 6072, -5884, -8467], ![3727, 4279, 7026, -6452, -9903], ![3167, 3826, 6323, -5536, -9003], ![-697, -823, -1259, 827, 1848], ![-586, -864, -1435, 970, 2130]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [86, 34, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 39, 37], [25, 63, 66], [0, 1]]
 g := ![![[71, 53, 17], [47, 76, 64], [37, 36, 1], [3, 46], [2, 16], [1]], ![[46, 25, 36, 71], [3, 17, 36, 95], [49, 19, 70, 43], [80, 63], [59, 92], [41, 52, 100, 80]], ![[80, 36, 30, 52], [21, 101, 90, 63], [42, 87, 36, 32], [90, 52], [50, 34], [6, 37, 16, 23]]]
 h' := ![![[74, 39, 37], [78, 21, 74], [11, 5, 95], [41, 83, 102], [14, 78, 56], [17, 69, 99], [0, 1]], ![[25, 63, 66], [88, 66, 83], [19, 37, 93], [35, 50, 21], [80, 28, 28], [101, 37, 35], [74, 39, 37]], ![[0, 1], [50, 16, 49], [90, 61, 18], [76, 73, 83], [20, 100, 19], [71, 100, 72], [25, 63, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 84], []]
 b := ![[], [3, 9, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [86, 34, 4, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6493447, 8021358, -1716081, 1347000, 3158921]
  a := ![1, 6, 9, 18, 37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1209024, -1170066, -2135954, 1347000, 3158921]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6159, 6550, -169, 870, 4501]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-6159, 6550, -169, 870, 4501]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![84, 65, 1, 0, 0], ![51, 93, 0, 1, 0], ![49, 94, 0, 0, 1]] where
  M :=![![![-6159, 6550, -169, 870, 4501], ![27006, -36965, 11921, -6730, -8283], ![-49698, 90178, -51978, 20218, -15531], ![-60096, 32112, 41472, -2755, 88092], ![121922, -131262, 5515, -17788, -86878]]]
  hmulB := by decide  
  f := ![![![-37261, 11358, -2867, -5884, -8467]], ![![-50802, 13257, -2993, -6452, -9903]], ![![-63024, 17717, -4257, -8924, -13242]], ![![-64335, 17505, -4134, -8731, -13116]], ![![-63885, 17486, -4090, -8678, -13045]]]
  g := ![![![-2494, -4723, -169, 870, 4501], ![-2187, 5754, 11921, -6730, -8283], ![39285, 29596, -51978, 20218, -15531], ![-74949, -103767, 41472, -2755, 88092], ![46824, 90593, 5515, -17788, -86878]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [21, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 102], [0, 1]]
 g := ![![[3, 29], [28, 68], [29, 17], [2], [23], [40, 1]], ![[30, 74], [70, 35], [91, 86], [2], [23], [80, 102]]]
 h' := ![![[40, 102], [30, 82], [9, 45], [90, 29], [82, 38], [87, 34], [0, 1]], ![[0, 1], [14, 21], [58, 58], [14, 74], [57, 65], [5, 69], [40, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [59, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [21, 63, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![577, -146, -362, -56, -888]
  a := ![4, 0, -2, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![751, 1088, -362, -56, -888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-37261, 11358, -2867, -5884, -8467]] ![![-6159, 6550, -169, 870, 4501]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB687I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB687I2 : PrimesBelowBoundCertificateInterval O 61 103 687 where
  m := 9
  g := ![1, 3, 1, 2, 2, 2, 1, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB687I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
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
    · exact ![1350125107]
    · exact ![357911, 71, 71]
    · exact ![2073071593]
    · exact ![493039, 6241]
    · exact ![47458321, 83]
    · exact ![62742241, 89]
    · exact ![8587340257]
    · exact ![1030301, 101, 101]
    · exact ![1092727, 10609]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
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
  β := ![I71N1, I71N2, I83N1, I89N1, I101N1, I101N2]
  Il := ![[], [I71N1, I71N2], [], [], [I83N1], [I89N1], [], [I101N1, I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
