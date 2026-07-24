
import IdealArithmetic.Examples.NF5_3_6075000000_7.RI5_3_6075000000_7
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187269, 124517, 24447, -31840, -39092]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![187269, 124517, 24447, -31840, -39092]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![56, 51, 9, 1, 0], ![16, 37, 24, 0, 1]] where
  M :=![![![187269, 124517, 24447, -31840, -39092], ![820932, 546490, 107463, -139878, -172116], ![3614436, 2402391, 471442, -614124, -753480], ![3978814, 2648285, 520663, -677765, -833742], ![-990384, -660435, -130167, 169284, 208969]]]
  hmulB := by decide  
  f := ![![![1891, 89, -157, 94, 236]], ![![-4956, -170, 309, -96, -336]], ![![7056, -2145, -692, 990, 1008]], ![![-1274, -360, 4, 155, 98]], ![![232, -849, -112, 322, 225]]]
  g := ![![![38743, 47683, 18645, -31840, -39092], ![170268, 209680, 82047, -139878, -172116], ![747180, 919425, 359434, -614124, -753480], ![824978, 1015862, 397468, -677765, -833742], ![-206176, -254116, -99537, 169284, 208969]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [19, 20, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 27, 44], [54, 39, 23], [0, 1]]
 g := ![![[8, 6, 62], [64, 57, 39], [52, 55], [44, 9], [36, 1], []], ![[66, 16, 19, 34], [5, 25, 58, 3], [48, 21], [3, 37], [12, 47], [47, 60]], ![[62, 46, 42, 22], [25, 21, 48, 59], [38, 1], [46, 19], [35, 59], [1, 60]]]
 h' := ![![[49, 27, 44], [57, 21, 14], [46, 56, 46], [30, 10, 51], [53, 65, 3], [0, 0, 1], [0, 1]], ![[54, 39, 23], [21, 49, 63], [66, 11, 37], [43, 58, 17], [57, 36, 29], [34, 30, 39], [49, 27, 44]], ![[0, 1], [8, 64, 57], [54, 0, 51], [46, 66, 66], [60, 33, 35], [16, 37, 27], [54, 39, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 66], []]
 b := ![[], [64, 16, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [19, 20, 31, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38573664808, 25163505222, 4890386131, -15757361183, -16904692165]
  a := ![0, 14, 13, -137, -247]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17782999488, 21705410980, 8245063414, -15757361183, -16904692165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1117368, 110006, -95391, 48781, 150307]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![1117368, 110006, -95391, 48781, 150307]] 
 ![![67, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![1117368, 110006, -95391, 48781, 150307], ![-3156447, -188785, 252007, -133317, -369215], ![7753515, 47798, -559482, 312189, 718067], ![-454804, 240836, -2064, -9355, 68516], ![517962, -240610, -2470, 11892, -62741]]]
  hmulB := by decide  
  f := ![![![10136, -3124, -3173, 1133, 7589]], ![![2765, -2423, -1579, 443, 3295]], ![![19243, 396, -3136, -155, 7709]], ![![-2604, -384, 295, -2506, -3339]], ![![11940, 1870, -1214, 492, 4243]]]
  g := ![![![-13437, 110006, -95391, 48781, 150307], ![-26254, -188785, 252007, -133317, -369215], ![283462, 47798, -559482, 312189, 718067], ![-144893, 240836, -2064, -9355, 68516], ![147288, -240610, -2470, 11892, -62741]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, 115, -29, 12, 128]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![479, 115, -29, 12, 128]] 
 ![![67, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![479, 115, -29, 12, 128], ![-2688, -656, 161, -66, -728], ![15288, 3769, -912, 372, 4172], ![-9954, -2473, 593, -241, -2730], ![11394, 2831, -679, 276, 3125]]]
  hmulB := by decide  
  f := ![![![-943, -605, -113, 210, 232]], ![![-692, -444, -83, 156, 172]], ![![-511, -322, -59, 132, 140]], ![![-597, -374, -68, 167, 174]], ![![-219, -140, -26, 48, 53]]]
  g := ![![![-106, 115, -29, 12, 128], ![605, -656, 161, -66, -728], ![-3476, 3769, -912, 372, 4172], ![2280, -2473, 593, -241, -2730], ![-2610, 2831, -679, 276, 3125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![187269, 124517, 24447, -31840, -39092]] ![![1117368, 110006, -95391, 48781, 150307]]
  ![![46954, -2645, -3014, 1819, 3109]] where
 M := ![![![46954, -2645, -3014, 1819, 3109]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![46954, -2645, -3014, 1819, 3109]] ![![479, 115, -29, 12, 128]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![840314, 78256, -71087, 36515, 111019]]]
 hmul := by decide  
 g := ![![![![12542, 1168, -1061, 545, 1657]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6048, -3650, -631, 2135, 2105]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-6048, -3650, -631, 2135, 2105]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![63, 4, 65, 14, 1]] where
  M :=![![![-6048, -3650, -631, 2135, 2105], ![-44205, -26497, -4523, 15429, 15155], ![-318255, -191506, -32880, 111723, 109921], ![-498176, -299316, -51292, 174517, 171612], ![36948, 22138, 3784, -12900, -12677]]]
  hmulB := by decide  
  f := ![![![56, 20, -1, -1, 11]], ![![-231, -41, 23, -15, -91]], ![![1911, 580, -72, 3, 427]], ![![-896, -124, 100, -69, -364]], ![![1627, 526, -47, -12, 329]]]
  g := ![![![-1953, -170, -1936, -385, 2105], ![-14070, -1227, -13938, -2771, 15155], ![-102018, -8890, -101095, -20101, 109921], ![-159292, -13884, -157832, -31381, 171612], ![11769, 1026, 11659, 2318, -12677]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [11, 3, 3, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 2, 70, 67], [70, 58, 53, 55], [35, 10, 19, 20], [0, 1]]
 g := ![![[49, 36, 7, 12], [35, 58, 54, 57], [63, 28, 8, 60], [27, 33, 64], [1], []], ![[27, 17, 48, 13], [30, 30, 21, 9, 44, 21], [3, 42, 37, 16, 39, 62], [23, 64, 16], [25], [45, 22, 16]], ![[50, 37, 20, 68, 33, 67], [18, 33, 48, 2, 41, 59], [12, 47, 53, 8, 6, 51], [53, 13, 38], [16, 9, 15], [33, 19, 43]], ![[49, 55, 24, 47, 7, 48], [56, 2, 26, 63, 7, 58], [8, 9, 35, 18, 47, 32], [59, 41, 6], [49, 35, 15], [53, 45, 45]]]
 h' := ![![[29, 2, 70, 67], [41, 43, 20, 15], [17, 20, 67, 25], [37, 48, 43, 42], [60, 68, 68, 63], [0, 0, 1], [0, 1]], ![[70, 58, 53, 55], [34, 62, 60], [50, 17, 7, 41], [37, 28, 64, 34], [19, 8, 47, 67], [62, 23, 66], [29, 2, 70, 67]], ![[35, 10, 19, 20], [14, 13, 64, 36], [1, 27, 39, 14], [68, 57, 8, 27], [15, 38, 20, 31], [64, 2, 2, 50], [70, 58, 53, 55]], ![[0, 1], [49, 24, 69, 20], [27, 7, 29, 62], [14, 9, 27, 39], [38, 28, 7, 52], [3, 46, 2, 21], [35, 10, 19, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [50, 11, 6], []]
 b := ![[], [], [52, 40, 31, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [11, 3, 3, 8, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36098813199370213868, -21977443491958642614, -3849508474717779300, 12969266676124337737, 12956165587269641494]
  a := ![3, 252, 254, -2387, -4062]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12004749932357149690, -1039466279451228290, -11915496783764006710, -2372071148530290749, 12956165587269641494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56, 20, -1, -1, 11]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![56, 20, -1, -1, 11]] 
 ![![71, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![56, 20, -1, -1, 11], ![-231, -41, 23, -15, -91], ![1911, 580, -72, 3, 427], ![-896, -124, 100, -69, -364], ![1242, 286, -86, 42, 371]]]
  hmulB := by decide  
  f := ![![![-6048, -3650, -631, 2135, 2105]], ![![-2667, -1607, -277, 939, 925]], ![![-9849, -5936, -1023, 3468, 3416]], ![![-11872, -7146, -1229, 4172, 4107]], ![![-1524, -922, -160, 540, 533]]]
  g := ![![![-8, 20, -1, -1, 11], ![33, -41, 23, -15, -91], ![-252, 580, -72, 3, 427], ![119, -124, 100, -69, -364], ![-162, 286, -86, 42, 371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-6048, -3650, -631, 2135, 2105]] ![![56, 20, -1, -1, 11]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [51, 38, 23, 70, 62, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 59, 66, 58, 50], [18, 22, 19, 19, 19], [67, 45, 52, 72, 61], [22, 19, 9, 70, 16], [0, 1]]
 g := ![![[62, 26, 33, 28, 50], [67, 72, 12, 72], [9, 11, 61, 72], [11, 60, 51, 11, 1], [], []], ![[54, 9, 46, 18, 62, 9, 7, 32], [52, 53, 25, 2], [49, 29, 55, 2], [62, 29, 59, 30, 38, 25, 66, 24], [24, 7, 26, 24], [71, 3, 12, 18]], ![[65, 3, 25, 37, 9, 56, 45, 69], [62, 21, 5, 71], [16, 65, 64, 2], [52, 44, 53, 28, 15, 26, 10, 12], [16, 53, 62, 4], [48, 61, 21, 69]], ![[53, 36, 59, 7, 51, 61, 51, 69], [62, 48, 17, 72], [51, 44, 18, 6], [66, 48, 36, 34, 48, 64, 51, 16], [20, 20, 67, 38], [0, 10, 2, 71]], ![[9, 30, 44, 3, 3, 52, 6, 37], [15, 13, 3, 61], [33, 33, 14, 71], [37, 8, 62, 62, 7, 6, 50, 23], [41, 72, 46, 71], [50, 33, 19, 37]]]
 h' := ![![[50, 59, 66, 58, 50], [23, 54, 21, 70, 14], [70, 1, 70, 18, 27], [23, 26, 49, 23, 46], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[18, 22, 19, 19, 19], [53, 4, 3, 23, 30], [2, 21, 8, 49, 41], [26, 45, 51, 28, 41], [36, 53, 72, 71, 23], [47, 56, 57, 21, 43], [50, 59, 66, 58, 50]], ![[67, 45, 52, 72, 61], [14, 68, 8, 8, 26], [57, 71, 57, 65, 12], [17, 23, 11, 44, 32], [36, 14, 12, 2, 4], [66, 18, 33, 32, 71], [18, 22, 19, 19, 19]], ![[22, 19, 9, 70, 16], [54, 20, 0, 20, 7], [2, 38, 66, 60, 27], [62, 67, 30, 13, 15], [57, 0, 46, 46, 60], [36, 45, 43, 35, 44], [67, 45, 52, 72, 61]], ![[0, 1], [65, 0, 41, 25, 69], [63, 15, 18, 27, 39], [33, 58, 5, 38, 12], [72, 6, 16, 27, 58], [51, 27, 12, 58, 61], [22, 19, 9, 70, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 52, 13, 67], [], [], []]
 b := ![[], [65, 5, 11, 37, 41], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [51, 38, 23, 70, 62, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8149632105870378884, 4917431595854131796, 848621724031578323, -2877353526006188775, -2843758924818181227]
  a := ![1, 17, 17, -162, -279]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![111638795970827108, 67362076655536052, 11624955123720251, -39415801726112175, -38955601709838099]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4100, 2621, 490, -993, -1079]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![4100, 2621, 490, -993, -1079]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![61, 69, 15, 1, 0], ![37, 57, 49, 0, 1]] where
  M :=![![![4100, 2621, 490, -993, -1079], ![22659, 14314, 2634, -5997, -6349], ![133329, 83163, 15043, -38169, -39515], ![186522, 115455, 20661, -55933, -57190], ![-22980, -14651, -2729, 5700, 6151]]]
  hmulB := by decide  
  f := ![![![-6844, -1677, 416, -171, -1849]], ![![38829, 9552, -2338, 957, 10549]], ![![-221529, -54731, 13271, -5415, -60445]], ![![-11608, -2891, 690, -280, -3191]], ![![-114682, -28359, 6864, -2799, -31318]]]
  g := ![![![1324, 1679, 864, -993, -1079], ![7891, 10000, 5110, -5997, -6349], ![49667, 62901, 31947, -38169, -39515], ![72335, 91578, 46354, -55933, -57190], ![-7573, -9602, -4932, 5700, 6151]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [54, 47, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 34, 56], [73, 44, 23], [0, 1]]
 g := ![![[2], [25, 46, 65], [3, 0, 25], [38, 27, 49], [44, 1], []], ![[19, 42, 72, 77], [24, 75, 30, 35], [60, 0, 10, 39], [38, 46, 29, 29], [69, 40], [66, 55]], ![[53, 35, 72, 2], [67, 58, 10, 72], [70, 41, 66, 9], [68, 1, 70, 40], [63, 50], [20, 55]]]
 h' := ![![[50, 34, 56], [72, 70], [75, 21, 12], [2, 31, 74], [73, 11, 72], [0, 0, 1], [0, 1]], ![[73, 44, 23], [17, 10, 49], [49, 13, 45], [78, 36, 15], [13, 39, 71], [42, 14, 44], [50, 34, 56]], ![[0, 1], [47, 78, 30], [61, 45, 22], [59, 12, 69], [47, 29, 15], [62, 65, 34], [73, 44, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 65], []]
 b := ![[], [77, 27, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [54, 47, 35, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9486915585100, -6107927014324, -1165436536747, 3790980863092, 4017374795774]
  a := ![1, -88, -84, 851, 1501]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4928855894650, -6287037594010, -3226348284507, 3790980863092, 4017374795774]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![717930, 123453, -68846, 33283, 120539]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![717930, 123453, -68846, 33283, 120539]] 
 ![![79, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![717930, 123453, -68846, 33283, 120539], ![-2531319, -331358, 227862, -113529, -377811], ![7934031, 754647, -673553, 345411, 1055271], ![-1470658, -9555, 106183, -59221, -136402], ![1535934, 15663, -111717, 62070, 145057]]]
  hmulB := by decide  
  f := ![![![4375982, 1484511, -80416, -78499, 741373]], ![![689201, 273604, 5534, -30949, 70549]], ![![4995183, 1640055, -116723, -64149, 909579]], ![![1915016, 818412, 41979, -113162, 128475]], ![![3232460, 978087, -113587, -2650, 685235]]]
  g := ![![![-44461, 123453, -68846, 33283, 120539], ![120848, -331358, 227862, -113529, -377811], ![-280662, 754647, -673553, 345411, 1055271], ![6971, -9555, 106183, -59221, -136402], ![-9256, 15663, -111717, 62070, 145057]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1815, 211, -169, 88, 278]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![1815, 211, -169, 88, 278]] 
 ![![79, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![1815, 211, -169, 88, 278], ![-5838, -606, 461, -222, -714], ![14994, 349, -1306, 768, 1890], ![-2590, -231, 7, 65, 98], ![2172, -123, -87, 42, 37]]]
  hmulB := by decide  
  f := ![![![-182920783, -45521893, 10921327, -4439050, -50187434]], ![![-102431684, -25491276, 6115707, -2485772, -28103878]], ![![-141699418, -35263493, 8460196, -3438706, -38877650]], ![![-120928324, -30094373, 7220053, -2934641, -33178746]], ![![-106320237, -26458986, 6347874, -2580138, -29170769]]]
  g := ![![![-207, 211, -169, 88, 278], ![544, -606, 461, -222, -714], ![-790, 349, -1306, 768, 1890], ![24, -231, 7, 65, 98], ![87, -123, -87, 42, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![4100, 2621, 490, -993, -1079]] ![![717930, 123453, -68846, 33283, 120539]]
  ![![-308301, 32750, 19656, -14896, -19258]] where
 M := ![![![-308301, 32750, 19656, -14896, -19258]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-308301, 32750, 19656, -14896, -19258]] ![![1815, 211, -169, 88, 278]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-459286487, -72228357, 43101057, -21082256, -74113692]]]
 hmul := by decide  
 g := ![![![![-5813753, -914283, 545583, -266864, -938148]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-324324, -67259, 25518, -14467, -104919]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-324324, -67259, 25518, -14467, -104919]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![35, 46, 25, 1, 0], ![59, 77, 24, 0, 1]] where
  M :=![![![-324324, -67259, 25518, -14467, -104919], ![2203299, 608896, -103828, 22905, 531895], ![-11169795, -2502833, 793647, -416823, -3402595], ![8553034, 2446661, -364973, 33289, 1951558], ![-9066180, -2328085, 508421, -184554, -2402113]]]
  hmulB := by decide  
  f := ![![![17154284, 1892243, -1493600, 756383, 2399931]], ![![-50398551, -3707878, 4123060, -2154153, -6210155]], ![![130413255, 3523937, -9799845, 5350983, 13312943]], ![![18444265, -158689, -1291912, 732629, 1584464]], ![![3300257, -1112380, -75969, 91238, -208725]]]
  g := ![![![76774, 104542, 35003, -14467, -104919], ![-361207, -498803, -161951, 22905, 531895], ![2459905, 3357480, 1118994, -416823, -3402595], ![-1298241, -1799453, -578730, 33289, 1951558], ![1676119, 2302700, 756301, -184554, -2402113]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [21, 4, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 67, 60], [18, 15, 23], [0, 1]]
 g := ![![[2, 42, 12], [17, 8, 41], [58, 81], [36, 21], [74, 59, 1], []], ![[74, 62, 71, 39], [71, 31, 64, 82], [72, 70], [17, 16], [50, 63, 75, 54], [75, 31]], ![[47, 44, 61, 30], [76, 82, 6, 59], [24, 27], [43, 33], [47, 70, 52, 78], [29, 31]]]
 h' := ![![[41, 67, 60], [58, 16, 57], [13, 65, 37], [22, 19, 9], [23, 42, 42], [0, 0, 1], [0, 1]], ![[18, 15, 23], [33, 67, 72], [43, 55, 56], [12, 79, 30], [55, 64, 79], [23, 61, 15], [41, 67, 60]], ![[0, 1], [37, 0, 37], [17, 46, 73], [40, 68, 44], [14, 60, 45], [47, 22, 67], [18, 15, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 81], []]
 b := ![[], [41, 40, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [21, 4, 24, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68695189204, 58560637441, 15074224310, -42722439681, -54301235338]
  a := ![-1, 17, 10, -189, -406]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![57442812807, 74758891371, 28751383909, -42722439681, -54301235338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17154284, -1892243, 1493600, -756383, -2399931]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-17154284, -1892243, 1493600, -756383, -2399931]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![25, 14, 1, 0, 0], ![33, 59, 0, 1, 0], ![59, 19, 0, 0, 1]] where
  M :=![![![-17154284, -1892243, 1493600, -756383, -2399931], ![50398551, 3707878, -4123060, 2154153, 6210155], ![-130413255, -3523937, 9799845, -5350983, -13312943], ![11523974, -3064271, -382669, 348735, -356482], ![-12588882, 3037759, 462367, -392346, 248801]]]
  hmulB := by decide  
  f := ![![![324324, 67259, -25518, 14467, 104919]], ![![-2203299, -608896, 103828, -22905, -531895]], ![![-139377, -52292, 265, 5516, -17120]], ![![-1540301, -435566, 68057, -10931, -359892]], ![![-164595, -63526, -497, 7264, -18237]]]
  g := ![![![1350148, 812321, 1493600, -756383, -2399931], ![-3421821, -2212738, -4123060, 2154153, 6210155], ![7067912, 5155809, 9799845, -5350983, -13312943], ![368854, -138664, -382669, 348735, -356482], ![-311806, 180552, 462367, -392346, 248801]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [34, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 82], [0, 1]]
 g := ![![[2, 78], [18, 26], [31], [70], [31, 59], [1]], ![[10, 5], [76, 57], [31], [70], [3, 24], [1]]]
 h' := ![![[15, 82], [52, 59], [3, 21], [71, 60], [25, 30], [49, 15], [0, 1]], ![[0, 1], [24, 24], [69, 62], [58, 23], [60, 53], [25, 68], [15, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [44, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [34, 68, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3852610, 878260, -303836, 282660, 1477784]
  a := ![0, 0, 12, 42, 196]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1024922, -477384, -303836, 282660, 1477784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-324324, -67259, 25518, -14467, -104919]] ![![-17154284, -1892243, 1493600, -756383, -2399931]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6509, -685, 677, -468, -1208]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-6509, -685, 677, -468, -1208]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![84, 78, 67, 72, 1]] where
  M :=![![![-6509, -685, 677, -468, -1208], ![25368, 4154, -1571, -150, 1904], ![-39984, 9953, 7446, -10776, -15428], ![44898, 21043, 3193, -12335, -11970], ![-11952, -965, 295, 588, 379]]]
  hmulB := by decide  
  f := ![![![-36193, -24083, -4733, 6162, 7576]], ![![-159096, -105806, -20779, 27060, 33236]], ![![-697956, -464501, -91308, 118866, 146188]], ![![-770826, -512669, -100691, 131123, 161070]], ![![-1320444, -878444, -172591, 224724, 276183]]]
  g := ![![![1067, 1051, 917, 972, -1208], ![-1512, -1622, -1451, -1542, 1904], ![14112, 13633, 11698, 12360, -15428], ![11802, 10727, 9047, 9545, -11970], ![-492, -343, -282, -300, 379]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [55, 76, 25, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 81, 78, 14], [13, 44, 3, 23], [43, 52, 8, 52], [0, 1]]
 g := ![![[48, 59, 38, 53], [14, 13, 57], [58, 44, 44], [71, 63, 65, 78], [86, 1], []], ![[55, 27, 16, 84, 88, 7], [38, 70, 11], [10, 40, 42], [42, 52, 80, 48, 36, 38], [87, 82, 26, 69, 74, 33], [88, 83, 18]], ![[44, 72, 64, 33, 47, 82], [73, 76, 44], [35, 44, 16], [5, 46, 17, 33, 85, 26], [79, 83, 43, 41, 63, 62], [8, 64, 84]], ![[82, 51, 3, 54, 30, 58], [42, 65, 64], [47], [53, 87, 46, 85, 8, 61], [21, 12, 5, 47, 46, 58], [29, 18, 34]]]
 h' := ![![[30, 81, 78, 14], [11, 9, 39, 63], [46, 62, 15, 18], [11, 30, 49, 69], [76, 84, 88, 73], [0, 0, 1], [0, 1]], ![[13, 44, 3, 23], [6, 53, 71, 32], [82, 68, 63, 10], [86, 59, 22, 24], [35, 50, 44, 48], [65, 15, 52, 68], [30, 81, 78, 14]], ![[43, 52, 8, 52], [78, 57, 1, 36], [34, 85, 66, 69], [88, 43, 33, 85], [46, 7, 13, 19], [85, 42, 73, 63], [13, 44, 3, 23]], ![[0, 1], [82, 59, 67, 47], [16, 52, 34, 81], [51, 46, 74], [60, 37, 33, 38], [76, 32, 52, 47], [43, 52, 8, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [51, 76, 30], []]
 b := ![[], [], [65, 69, 87, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [55, 76, 25, 3, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1340027344952639, -868489699026182, -167227723119730, 537264472318624, 573293063658966]
  a := ![13, 18, 13, -191, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-556142075194447, -512194928813770, -433459134699668, -457750967540752, 573293063658966]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36193, -24083, -4733, 6162, 7576]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-36193, -24083, -4733, 6162, 7576]] 
 ![![89, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![-36193, -24083, -4733, 6162, 7576], ![-159096, -105806, -20779, 27060, 33236], ![-697956, -464501, -91308, 118866, 146188], ![-770826, -512669, -100691, 131123, 161070], ![192708, 128059, 25123, -32730, -40141]]]
  hmulB := by decide  
  f := ![![![-6509, -685, 677, -468, -1208]], ![![-4615, -469, 492, -354, -888]], ![![-4106, -273, 464, -384, -852]], ![![-3006, -133, 401, -391, -786]], ![![-5400, -565, 551, -372, -973]]]
  g := ![![![10930, -24083, -4733, 6162, 7576], ![48056, -105806, -20779, 27060, 33236], ![210763, -464501, -91308, 118866, 146188], ![232827, -512669, -100691, 131123, 161070], ![-58227, 128059, 25123, -32730, -40141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-6509, -685, 677, -468, -1208]] ![![-36193, -24083, -4733, 6162, 7576]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [43, 35, 58, 90, 57, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 26, 89, 88, 86], [90, 29, 6, 41, 83], [63, 25, 44, 59, 59], [17, 16, 55, 6, 63], [0, 1]]
 g := ![![[91, 94, 33, 19, 12], [37, 81, 23, 33], [7, 63, 91, 95], [40, 75, 17, 18], [40, 1], []], ![[3, 2, 87, 40, 35, 10, 49, 49], [15, 73, 40, 53], [96, 78, 31, 91], [16, 7, 19, 1], [40, 42, 0, 8], [15, 32, 69, 71, 72, 58, 44, 27]], ![[40, 43, 62, 13, 65, 80, 70, 14], [13, 7, 43, 88], [42, 44, 10, 96], [28, 59, 72, 66], [96, 62, 33, 11], [34, 46, 22, 83, 25, 8, 96, 69]], ![[43, 19, 2, 96, 8, 2, 84, 10], [80, 32, 30, 47], [38, 30, 24, 1], [58, 73, 67, 61], [16, 54, 51, 16], [13, 52, 81, 47, 31, 8, 29, 30]], ![[90, 57, 25, 59, 82, 52, 15, 38], [48, 38, 44, 31], [70, 63, 37, 61], [63, 4, 7, 66], [79, 25, 68, 8], [39, 46, 69, 41, 61, 37, 66, 78]]]
 h' := ![![[64, 26, 89, 88, 86], [50, 93, 23, 77, 77], [34, 16, 43, 96, 18], [23, 73, 48, 25, 17], [26, 12, 70, 28, 55], [0, 0, 0, 1], [0, 1]], ![[90, 29, 6, 41, 83], [37, 21, 14, 75, 64], [10, 63, 11, 29, 21], [89, 19, 8, 40, 24], [1, 52, 35, 59, 96], [84, 9, 50, 22, 28], [64, 26, 89, 88, 86]], ![[63, 25, 44, 59, 59], [89, 4, 11, 56, 22], [39, 57, 92, 55, 31], [14, 84, 68, 32, 22], [32, 79, 52, 79, 39], [38, 28, 33, 43, 37], [90, 29, 6, 41, 83]], ![[17, 16, 55, 6, 63], [5, 66, 15, 60, 35], [27, 57, 6, 28, 12], [77, 81, 64, 8, 96], [7, 84, 46, 63, 62], [4, 7, 44, 84, 4], [63, 25, 44, 59, 59]], ![[0, 1], [45, 10, 34, 23, 93], [13, 1, 42, 83, 15], [93, 34, 6, 89, 35], [59, 64, 88, 62, 39], [35, 53, 67, 44, 28], [17, 16, 55, 6, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 79, 22, 54], [], [], []]
 b := ![[], [58, 71, 45, 83, 49], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [43, 35, 58, 90, 57, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112125413741937077, 67387192366106240, 11551577900889695, -39305881952439012, -38657378628932598]
  a := ![-1, 8, 10, -69, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1155932100432341, 694713323361920, 119088431967935, -405215277860196, -398529676586934]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-891417, -593014, -116508, 151702, 186432]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-891417, -593014, -116508, 151702, 186432]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![99, 49, 23, 1, 0], ![21, 68, 40, 0, 1]] where
  M :=![![![-891417, -593014, -116508, 151702, 186432], ![-3915072, -2604499, -511700, 666270, 818804], ![-17194884, -11438878, -2247369, 2926230, 3596152], ![-18970672, -12620228, -2479468, 3228431, 3967544], ![4736262, 3150796, 619030, -806022, -990551]]]
  hmulB := by decide  
  f := ![![![1459, 298, -148, 70, 264]], ![![-5544, -839, 524, -258, -868]], ![![18228, 2002, -1629, 822, 2464]], ![![2857, 341, -259, 129, 396]], ![![3825, 290, -326, 168, 449]]]
  g := ![![![-196287, -204988, -109534, 151702, 186432], ![-862086, -900301, -481070, 666270, 818804], ![-3786246, -3954084, -2112839, 2926230, 3596152], ![-4177265, -4362439, -2331041, 3228431, 3967544], ![1042911, 1089142, 581976, -806022, -990551]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [15, 77, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 71, 13], [77, 29, 88], [0, 1]]
 g := ![![[89, 18, 78], [9, 9], [32, 56, 4], [56, 25], [42, 96], [1]], ![[31, 28, 88, 82], [36, 17], [65, 80, 12, 85], [98, 54], [15, 43], [31, 72, 80, 76]], ![[46, 87, 72, 5], [5, 88], [15, 29, 22, 20], [28, 37], [53, 31], [60, 7, 19, 25]]]
 h' := ![![[79, 71, 13], [86, 91, 52], [25, 81, 98], [70, 41, 99], [100, 60, 5], [86, 24, 55], [0, 1]], ![[77, 29, 88], [82, 48, 65], [4, 94, 57], [39, 15, 71], [87, 87, 16], [98, 39, 89], [79, 71, 13]], ![[0, 1], [59, 63, 85], [29, 27, 47], [48, 45, 32], [93, 55, 80], [22, 38, 58], [77, 29, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 47], []]
 b := ![[], [95, 84, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [15, 77, 46, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16307691, -402639596, -189804400, 437147154, 725161640]
  a := ![3, -3, 1, 39, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-579105495, -704295462, -388620342, 437147154, 725161640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1459, -298, 148, -70, -264]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-1459, -298, 148, -70, -264]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![55, 62, 1, 0, 0], ![56, 96, 0, 1, 0], ![2, 77, 0, 0, 1]] where
  M :=![![![-1459, -298, 148, -70, -264], ![5544, 839, -524, 258, 868], ![-18228, -2002, 1629, -822, -2464], ![3472, -4, -284, 165, 280], ![-3558, -4, 290, -162, -269]]]
  hmulB := by decide  
  f := ![![![891417, 593014, 116508, -151702, -186432]], ![![3915072, 2604499, 511700, -666270, -818804]], ![![3058983, 2034986, 399809, -520580, -639760]], ![![4403336, 2929316, 575516, -749363, -920920]], ![![2955516, 1966155, 386286, -502972, -618121]]]
  g := ![![![-51, 174, 148, -70, -264], ![180, -577, -524, 258, 868], ![-563, 1640, 1629, -822, -2464], ![92, -196, -284, 165, 280], ![-98, 181, 290, -162, -269]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [10, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 100], [0, 1]]
 g := ![![[57, 36], [56], [86, 84], [14], [22], [36, 1]], ![[40, 65], [56], [80, 17], [14], [22], [72, 100]]]
 h' := ![![[36, 100], [23, 6], [49, 64], [63, 36], [100, 32], [44, 74], [0, 1]], ![[0, 1], [37, 95], [30, 37], [46, 65], [40, 69], [82, 27], [36, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [10, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [10, 65, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1518123, -2252340, -798231, 2125927, 3131885]
  a := ![1, -14, -10, 149, 303]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-821100, -3940655, -798231, 2125927, 3131885]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-891417, -593014, -116508, 151702, 186432]] ![![-1459, -298, 148, -70, -264]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [67, 45, 97, 45, 35, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 22, 90, 21, 52], [28, 45, 45, 51, 78], [60, 12, 58, 46, 8], [94, 23, 13, 88, 68], [0, 1]]
 g := ![![[14, 83, 78, 24, 81], [4, 6, 67, 79, 49], [71, 50, 29, 73, 100], [32, 98, 23, 46], [68, 1], []], ![[22, 53, 15, 79, 81, 14, 48, 66], [36, 34, 73, 86, 55, 95, 10, 66], [45, 2, 64, 36, 50, 81, 18, 76], [66, 84, 36, 92], [53, 21, 13, 79], [37, 27, 72, 84, 27, 42, 50, 13]], ![[76, 33, 21, 54, 45, 72, 90, 99], [29, 29, 57, 73, 33, 9, 94, 90], [16, 66, 28, 18, 81, 38, 80, 48], [80, 90, 89, 15], [44, 60, 60, 81], [94, 4, 9, 31, 79, 47, 89, 31]], ![[82, 95, 69, 90, 99, 38, 46, 19], [31, 33, 84, 74, 25, 6, 67, 23], [62, 92, 33, 26, 55, 76, 88, 16], [17, 1, 65, 55], [27, 36, 40, 9], [60, 39, 3, 9, 97, 65, 79, 100]], ![[8, 81, 46, 5, 35, 87, 1, 97], [59, 36, 86, 87, 32, 25, 69, 68], [35, 57, 56, 92, 37, 12, 28, 98], [93, 48, 20, 56], [73, 3, 38, 8], [71, 44, 31, 32, 80, 97, 101, 76]]]
 h' := ![![[92, 22, 90, 21, 52], [41, 88, 54, 30, 94], [84, 61, 78, 19, 96], [80, 53, 22, 19, 10], [79, 66, 54, 36, 47], [0, 0, 0, 1], [0, 1]], ![[28, 45, 45, 51, 78], [54, 68, 35, 98, 21], [48, 46, 47, 3, 21], [45, 10, 37, 44, 96], [55, 82, 64, 30, 68], [1, 83, 66, 99, 39], [92, 22, 90, 21, 52]], ![[60, 12, 58, 46, 8], [9, 15, 59, 42, 82], [63, 62, 50, 1, 74], [94, 20, 82, 91, 95], [43, 14, 70, 23, 85], [101, 93, 93, 28, 94], [28, 45, 45, 51, 78]], ![[94, 23, 13, 88, 68], [93, 12, 93, 3, 12], [15, 86, 102, 74, 14], [66, 63, 7, 68, 38], [81, 85, 57, 91, 63], [6, 69, 73, 61, 100], [60, 12, 58, 46, 8]], ![[0, 1], [49, 23, 68, 33, 100], [6, 54, 32, 6, 1], [65, 60, 58, 87, 70], [61, 62, 64, 26, 46], [76, 64, 77, 17, 76], [94, 23, 13, 88, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 23, 89, 16], [], [], []]
 b := ![[], [9, 71, 26, 46, 71], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [67, 45, 97, 45, 35, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-661662813121, -157252796334, 42924164483, -23937996087, -194566353366]
  a := ![4, 0, -1, -3, -14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6423910807, -1526726178, 416739461, -232407729, -1888993722]
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



lemma PB3811I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB3811I2 : PrimesBelowBoundCertificateInterval O 61 103 3811 where
  m := 9
  g := ![3, 2, 1, 3, 2, 2, 1, 2, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB3811I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
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
    · exact ![300763, 67, 67]
    · exact ![25411681, 71]
    · exact ![2073071593]
    · exact ![493039, 79, 79]
    · exact ![571787, 6889]
    · exact ![62742241, 89]
    · exact ![8587340257]
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
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I67N1, I67N2, I71N1, I79N1, I79N2, I89N1]
  Il := ![[I67N1, I67N2], [I71N1], [], [I79N1, I79N2], [], [I89N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
