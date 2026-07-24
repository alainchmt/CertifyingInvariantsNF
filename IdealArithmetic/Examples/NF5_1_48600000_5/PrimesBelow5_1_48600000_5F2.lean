
import IdealArithmetic.Examples.NF5_1_48600000_5.RI5_1_48600000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![627, 1010, 542, 128, -56]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![627, 1010, 542, 128, -56]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![56, 9, 13, 1, 0], ![51, 48, 32, 0, 1]] where
  M :=![![![627, 1010, 542, 128, -56], ![-144, 1705, 2164, 1340, 880], ![-2220, 150, 3925, 3504, 3140], ![-6572, -4346, 5712, 6759, 6932], ![-1376, -2500, -638, 332, 779]]]
  hmulB := by decide  
  f := ![![![-391, -750, 994, -360, 16]], ![![688, -197, -2188, 1268, -2192]], ![![924, 5998, -1121, -920, 5996]], ![![-136, 273, 501, -349, 768]], ![![705, 2298, -1516, 252, 1323]]]
  g := ![![![-55, 38, 10, 128, -56], ![-1792, -785, -648, 1340, 880], ![-5352, -2718, -2121, 3504, 3140], ![-11024, -5939, -4537, 6759, 6932], ![-891, -640, -446, 332, 779]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [54, 0, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 57, 46], [51, 9, 21], [0, 1]]
 g := ![![[60, 61, 15], [36, 43, 21], [15, 55], [46, 64], [27, 1], []], ![[47, 56, 20, 32], [30, 24, 3, 51], [36, 1], [8, 33], [54, 14], [66, 39]], ![[38, 59, 27, 6], [50, 22, 25, 21], [31, 24], [4, 56], [62, 33], [24, 39]]]
 h' := ![![[43, 57, 46], [66, 47, 22], [15, 24, 17], [50, 42, 16], [16, 13, 59], [0, 0, 1], [0, 1]], ![[51, 9, 21], [1, 5, 15], [32, 57, 51], [10, 29, 66], [24, 14, 57], [27, 49, 9], [43, 57, 46]], ![[0, 1], [18, 15, 30], [41, 53, 66], [24, 63, 52], [21, 40, 18], [32, 18, 57], [51, 9, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 13], []]
 b := ![[], [26, 62, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [54, 0, 40, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![98364, 19214, 21084, -75568, -206634]
  a := ![5, -7, -8, -8, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![221918, 158474, 113668, -75568, -206634]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![346, 481, 12, -164, -239]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![346, 481, 12, -164, -239]] 
 ![![67, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![346, 481, 12, -164, -239], ![806, 1225, 156, -304, -506], ![810, 1442, 415, -148, -406], ![151, 867, 810, 419, 215], ![-685, -897, 44, 366, 500]]]
  hmulB := by decide  
  f := ![![![12656, -2749, -740, 590, 2413]], ![![2366, -518, -136, 110, 449]], ![![3046, -654, -185, 144, 582]], ![![10803, -2350, -622, 499, 2066]], ![![2903, -636, -172, 138, 545]]]
  g := ![![![102, 481, 12, -164, -239], ![109, 1225, 156, -304, -506], ![-150, 1442, 415, -148, -406], ![-764, 867, 810, 419, 215], ![-270, -897, 44, 366, 500]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-157, -591, 314, -22, -408]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-157, -591, 314, -22, -408]] 
 ![![67, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-157, -591, 314, -22, -408], ![860, 2153, -2042, 584, 684], ![-1268, -1717, 3421, -1458, 1068], ![-40, -4128, -1086, 1671, -5784], ![1468, 6223, -2740, -78, 4807]]]
  hmulB := by decide  
  f := ![![![-340115883, 74994111, 19997712, -16202062, -63476916]], ![![-139759504, 30816379, 8217406, -6657708, -26083764]], ![![-51320770, 11316013, 3017495, -2444762, -9578160]], ![![-239647455, 52841249, 14090494, -11416059, -44726172]], ![![-103390764, 22797225, 6079042, -4925214, -19296149]]]
  g := ![![![335, -591, 314, -22, -408], ![-1196, 2153, -2042, 584, 684], ![892, -1717, 3421, -1458, 1068], ![2441, -4128, -1086, 1671, -5784], ![-3550, 6223, -2740, -78, 4807]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![627, 1010, 542, 128, -56]] ![![346, 481, 12, -164, -239]]
  ![![1527710, 2481609, 491230, -456948, -881445]] where
 M := ![![![1527710, 2481609, 491230, -456948, -881445]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![1527710, 2481609, 491230, -456948, -881445]] ![![-157, -591, 314, -22, -408]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-4229710, -2365234, 4158020, 4629298, 4629633]]]
 hmul := by decide  
 g := ![![![![-63130, -35302, 62060, 69094, 69099]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [3, 31, 39, 31, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 24, 16, 38, 16], [28, 61, 37, 22, 67], [31, 57, 28, 65, 66], [62, 70, 61, 17, 64], [0, 1]]
 g := ![![[25, 65, 63, 26, 29], [0, 1, 20, 44, 30], [57, 30, 32, 11, 8], [15, 26, 46, 1], [], []], ![[33, 48, 60, 38, 31, 32], [28, 47, 28, 55, 63, 18, 19, 10], [68, 9, 1, 13, 59, 29, 18, 27], [4, 22, 47, 40], [59, 55, 39, 30], [42, 9, 70, 43]], ![[13, 68, 39, 19, 9, 16, 40, 47], [0, 38, 42, 0, 14, 65, 41, 33], [40, 37, 65, 17, 33, 22, 28, 59], [60, 45, 57, 58], [17, 30, 2, 43], [56, 34, 63, 16]], ![[36, 20, 12, 44, 12, 62, 15, 33], [49, 58, 7, 5, 26, 60, 37, 67], [69, 49, 33, 67, 42, 46, 6, 21], [1, 6, 59, 18], [14, 13, 0, 25], [29, 42, 3, 25]], ![[23, 1, 69, 41, 7, 47, 61, 60], [42, 49, 50, 47, 23, 52, 36, 4], [47, 54, 0, 60, 69, 1, 21, 5], [64, 19, 64, 24], [16, 28, 69, 40], [39, 56, 28, 49]]]
 h' := ![![[67, 24, 16, 38, 16], [0, 57, 34, 37, 61], [42, 26, 39, 12, 39], [26, 25, 33, 3, 47], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[28, 61, 37, 22, 67], [46, 49, 67, 59], [43, 38, 26, 50, 20], [13, 42, 67, 35, 50], [66, 62, 10, 35, 18], [32, 41, 25, 62, 39], [67, 24, 16, 38, 16]], ![[31, 57, 28, 65, 66], [31, 6, 25, 16, 52], [10, 2, 3, 1, 51], [39, 3, 18, 8, 43], [52, 67, 13, 19, 49], [48, 16, 23, 44, 55], [28, 61, 37, 22, 67]], ![[62, 70, 61, 17, 64], [64, 7, 37, 25, 6], [48, 68, 27, 62, 50], [40, 5, 42, 61, 62], [16, 15, 49, 12, 36], [22, 24, 58, 44, 66], [31, 57, 28, 65, 66]], ![[0, 1], [67, 23, 50, 5, 23], [36, 8, 47, 17, 53], [69, 67, 53, 35, 11], [41, 69, 70, 5, 38], [35, 61, 35, 63, 53], [62, 70, 61, 17, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 18, 58, 41], [], [], []]
 b := ![[], [48, 13, 12, 51, 64], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [3, 31, 39, 31, 25, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42028378855089, 66452779816016, -89044434486671, 27746515807377, -18809395715181]
  a := ![-6, -56, 11, -57, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![591948997959, 935954645296, -1254146964601, 390795997287, -264921066411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 1804229351 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23952, 5262, 1408, -1134, -4459]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-23952, 5262, 1408, -1134, -4459]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![12, 20, 12, 1, 0], ![45, 15, 28, 0, 1]] where
  M :=![![![-23952, 5262, 1408, -1134, -4459], ![11186, -2517, -662, 548, 2114], ![-2662, 525, 145, -114, -470], ![-5009, 1061, 272, -243, -929], ![-8765, 1968, 514, -432, -1658]]]
  hmulB := by decide  
  f := ![![![30, 66, -74, 24, 11]], ![![-70, -51, 202, -100, 122]], ![![-22, -339, -29, 102, -422]], ![![-13, -43, 28, -5, -25]], ![![-9, -111, -4, 30, -133]]]
  g := ![![![2607, 1299, 1916, -1134, -4459], ![-1240, -619, -910, 548, 2114], ![272, 135, 201, -114, -470], ![544, 272, 400, -243, -929], ![973, 486, 714, -432, -1658]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [18, 48, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 38, 41], [13, 34, 32], [0, 1]]
 g := ![![[51, 71, 1], [38, 18], [50, 23], [23, 61, 27], [44, 1], []], ![[67, 57, 19, 46], [56, 70], [4, 35], [28, 14, 21, 4], [41, 61], [65, 2]], ![[52, 5, 36, 64], [54, 36], [1, 67], [24, 13, 35, 35], [17, 57], [1, 2]]]
 h' := ![![[31, 38, 41], [48, 50, 1], [41, 9, 23], [24, 36, 13], [11, 60, 63], [0, 0, 1], [0, 1]], ![[13, 34, 32], [2, 5, 40], [39, 46, 56], [29, 20, 20], [19, 60, 3], [10, 3, 34], [31, 38, 41]], ![[0, 1], [46, 18, 32], [54, 18, 67], [46, 17, 40], [11, 26, 7], [5, 70, 38], [13, 34, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 62], []]
 b := ![[], [55, 52, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [18, 48, 29, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17294, 20564, -11958, -5642, -13824]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9686, 4668, 6066, -5642, -13824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30, -66, 74, -24, -11]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-30, -66, 74, -24, -11]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![25, 61, 1, 0, 0], ![8, 15, 0, 1, 0], ![34, 12, 0, 0, 1]] where
  M :=![![![-30, -66, 74, -24, -11], ![70, 51, -202, 100, -122], ![22, 339, 29, -102, 422], ![-355, -1157, 760, -123, -667], ![341, 816, -820, 246, 218]]]
  hmulB := by decide  
  f := ![![![23952, -5262, -1408, 1134, 4459]], ![![-11186, 2517, 662, -548, -2114]], ![![-1108, 294, 69, -68, -233]], ![![395, -74, -22, 15, 67]], ![![9437, -2064, -554, 444, 1752]]]
  g := ![![![-18, -56, 74, -24, -11], ![116, 169, -202, 100, -122], ![-195, -68, 29, -102, 422], ![59, -516, 760, -123, -667], ![157, 610, -820, 246, 218]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [67, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 72], [0, 1]]
 g := ![![[39, 12], [18], [54], [4, 46], [6], [1]], ![[0, 61], [18], [54], [37, 27], [6], [1]]]
 h' := ![![[15, 72], [27, 42], [24, 50], [24, 45], [72, 51], [6, 15], [0, 1]], ![[0, 1], [0, 31], [44, 23], [42, 28], [34, 22], [12, 58], [15, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [37, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [67, 58, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15590, -11002, 12619, 13184, 16672]
  a := ![-8, 27, 13, 26, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13745, -16145, 12619, 13184, 16672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-23952, 5262, 1408, -1134, -4459]] ![![-30, -66, 74, -24, -11]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-212, -210, 64, 134, 159]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-212, -210, 64, 134, 159]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![65, 37, 34, 1, 0], ![5, 46, 11, 0, 1]] where
  M :=![![![-212, -210, 64, 134, 159], ![-586, -675, 166, 396, 486], ![-882, -1029, 207, 562, 702], ![-971, -1193, 152, 571, 741], ![305, 332, -114, -224, -266]]]
  hmulB := by decide  
  f := ![![![2, 22, -10, 0, 15]], ![![-30, -83, 74, -20, -30]], ![![50, 77, -133, 54, -30]], ![![9, 14, -30, 13, -12]], ![![-11, -39, 25, -4, -23]]]
  g := ![![![-123, -158, -79, 134, 159], ![-364, -477, -236, 396, 486], ![-518, -685, -337, 562, 702], ![-529, -714, -347, 571, 741], ![205, 264, 132, -224, -266]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [57, 64, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 46, 20], [78, 32, 59], [0, 1]]
 g := ![![[27, 31, 36], [58, 65, 13], [50, 25, 13], [24, 31, 40], [40, 1], []], ![[3, 47, 32, 22], [48, 30, 6, 13], [45, 1, 52, 20], [24, 13, 45, 38], [21, 76], [65, 5]], ![[55, 38, 43, 39], [53, 70, 65, 56], [2, 64, 23, 12], [29, 77, 43, 47], [11, 62], [26, 5]]]
 h' := ![![[41, 46, 20], [12, 45, 73], [73, 29, 48], [54, 57, 31], [11, 69, 35], [0, 0, 1], [0, 1]], ![[78, 32, 59], [18, 25, 76], [16, 77, 62], [3, 8, 78], [19, 1, 51], [30, 38, 32], [41, 46, 20]], ![[0, 1], [5, 9, 9], [56, 52, 48], [64, 14, 49], [10, 9, 72], [20, 41, 46], [78, 32, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7], []]
 b := ![[], [77, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [57, 64, 39, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![603381, -26590, -1430990, 743340, -1671800]
  a := ![10, -9, -15, -7, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-498161, 624970, -105250, 743340, -1671800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 22, -10, 0, 15]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![2, 22, -10, 0, 15]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![22, 45, 1, 0, 0], ![37, 1, 0, 1, 0], ![78, 42, 0, 0, 1]] where
  M :=![![![2, 22, -10, 0, 15], ![-30, -83, 74, -20, -30], ![50, 77, -133, 54, -30], ![-9, 129, 64, -69, 207], ![-49, -220, 84, 10, -182]]]
  hmulB := by decide  
  f := ![![![-212, -210, 64, 134, 159]], ![![-586, -675, 166, 396, 486]], ![![-404, -456, 115, 270, 330]], ![![-119, -122, 34, 75, 90]], ![![-517, -562, 150, 340, 412]]]
  g := ![![![-12, -2, -10, 0, 15], ![18, -27, 74, -20, -30], ![42, 92, -133, 54, -30], ![-190, -144, 64, -69, 207], ![151, 46, 84, 10, -182]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [52, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 78], [0, 1]]
 g := ![![[45, 38], [77, 1], [24, 64], [0, 10], [31], [1]], ![[0, 41], [28, 78], [48, 15], [63, 69], [31], [1]]]
 h' := ![![[30, 78], [25, 65], [16, 78], [0, 71], [65, 22], [27, 30], [0, 1]], ![[0, 1], [0, 14], [65, 1], [76, 8], [14, 57], [58, 49], [30, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [40, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [52, 49, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3866, 7356, -11322, 5062, -402]
  a := ![-6, -4, 10, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1228, 6692, -11322, 5062, -402]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-212, -210, 64, 134, 159]] ![![2, 22, -10, 0, 15]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1366, -2007, 3762, -1578, 1049]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-1366, -2007, 3762, -1578, 1049]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![67, 26, 16, 1, 0], ![35, 19, 29, 0, 1]] where
  M :=![![![-1366, -2007, 3762, -1578, 1049], ![1058, -6005, -5072, 4368, -11566], ![7198, 31276, -13203, -704, 24670], ![-24495, -62379, 57778, -16091, -20999], ![17321, 29383, -45070, 17512, -6110]]]
  hmulB := by decide  
  f := ![![![-5492, -9025, -1890, 1568, 3121]], ![![-9378, -19851, -8672, -644, 3166]], ![![-2522, -17584, -17329, -9316, -5098]], ![![-7627, -16852, -7916, -1049, 2234]], ![![-5191, -14271, -8819, -2806, 159]]]
  g := ![![![815, 230, -17, -1578, 1049], ![1364, 1207, 3138, 4368, -11566], ![-9748, -5050, -8643, -704, 24670], ![21549, 9096, 11135, -16091, -20999], ![-11351, -3733, -1784, 17512, -6110]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [8, 6, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 67, 7], [12, 15, 76], [0, 1]]
 g := ![![[55, 13, 70], [71, 42, 40], [21, 78], [46, 12], [80, 70, 1], []], ![[20, 72, 9, 70], [58, 15, 28, 81], [72, 3], [61, 1], [11, 36, 69, 81], [52, 49]], ![[42, 36, 48, 20], [14, 74, 31, 55], [74, 38], [26, 44], [55, 2, 71, 34], [66, 49]]]
 h' := ![![[58, 67, 7], [13, 14, 30], [19, 3, 66], [42, 6, 24], [24, 39, 26], [0, 0, 1], [0, 1]], ![[12, 15, 76], [40, 0, 50], [43, 63, 15], [11, 50, 70], [1, 46, 82], [43, 13, 15], [58, 67, 7]], ![[0, 1], [32, 69, 3], [26, 17, 2], [28, 27, 72], [53, 81, 58], [31, 70, 67], [12, 15, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 32], []]
 b := ![[], [59, 31, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [8, 6, 13, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2860439, -2541585, 616268, 2447224, 2973655]
  a := ![-6, 19, 16, 20, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3263884, -1477938, -1503317, 2447224, 2973655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5492, -9025, -1890, 1568, 3121]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-5492, -9025, -1890, 1568, 3121]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![41, 67, 1, 0, 0], ![75, 14, 0, 1, 0], ![74, 19, 0, 0, 1]] where
  M :=![![![-5492, -9025, -1890, 1568, 3121], ![-9378, -19851, -8672, -644, 3166], ![-2522, -17584, -17329, -9316, -5098], ![19103, 3429, -27662, -26323, -24433], ![12687, 18487, 1482, -5378, -8350]]]
  hmulB := by decide  
  f := ![![![-1366, -2007, 3762, -1578, 1049]], ![![1058, -6005, -5072, 4368, -11566]], ![![266, -5462, -2395, 2738, -8521]], ![![-1351, -3578, 3240, -883, -1256]], ![![-767, -2810, 1650, -196, -1786]]]
  g := ![![![-3332, 438, -1890, 1568, 3121], ![1930, 6145, -8672, -644, 3166], ![21493, 16515, -17329, -9316, -5098], ![59464, 32404, -27662, -26323, -24433], ![11725, 1845, 1482, -5378, -8350]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [51, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 82], [0, 1]]
 g := ![![[82, 70], [53, 25], [63], [30], [44, 28], [1]], ![[0, 13], [0, 58], [63], [30], [61, 55], [1]]]
 h' := ![![[51, 82], [36, 53], [6, 78], [56, 35], [80, 14], [32, 51], [0, 1]], ![[0, 1], [0, 30], [0, 5], [15, 48], [47, 69], [60, 32], [51, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [53, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [51, 32, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![334, 660, -863, 340, 202]
  a := ![-2, -3, 3, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-57, 601, -863, 340, 202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-1366, -2007, 3762, -1578, 1049]] ![![-5492, -9025, -1890, 1568, 3121]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101162, 22305, 5950, -4820, -18879]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-101162, 22305, 5950, -4820, -18879]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![71, 54, 6, 1, 0], ![12, 80, 34, 0, 1]] where
  M :=![![![-101162, 22305, 5950, -4820, -18879], ![47398, -10457, -2788, 2260, 8838], ![-11098, 2470, 641, -528, -2058], ![-21113, 4617, 1278, -1017, -3945], ![-37129, 8201, 2158, -1758, -6940]]]
  hmulB := by decide  
  f := ![![![-468, -495, 174, 338, 399]], ![![-1474, -1613, 484, 1024, 1230]], ![![-2254, -2546, 641, 1508, 1842]], ![![-1449, -1580, 482, 1011, 1212]], ![![-2241, -2481, 700, 1536, 1856]]]
  g := ![![![5254, 20145, 7604, -4820, -18879], ![-2462, -9433, -3560, 2260, 8838], ![574, 2198, 829, -528, -2058], ![1106, 4215, 1590, -1017, -3945], ![1921, 7397, 2794, -1758, -6940]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [2, 37, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 66, 49], [58, 22, 40], [0, 1]]
 g := ![![[2, 17, 84], [26, 72], [53, 11], [85, 0, 10], [31, 54, 1], []], ![[71, 46, 39, 69], [76, 57], [87, 21], [16, 0, 72, 44], [34, 18, 67, 42], [41, 87]], ![[62, 28, 37, 49], [66, 69], [69, 84], [73, 84, 45, 55], [18, 64, 41, 67], [50, 87]]]
 h' := ![![[85, 66, 49], [21, 43, 23], [47, 34, 61], [8, 76, 79], [27, 80, 30], [0, 0, 1], [0, 1]], ![[58, 22, 40], [22, 39, 32], [68, 29, 71], [8, 61, 33], [41, 31, 41], [23, 6, 22], [85, 66, 49]], ![[0, 1], [68, 7, 34], [72, 26, 46], [78, 41, 66], [59, 67, 18], [60, 83, 66], [58, 22, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 67], []]
 b := ![[], [74, 62, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [2, 37, 35, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1572396, -1978538, 3149720, -950113, 1356189]
  a := ![-10, 9, 20, 5, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![557431, -664804, -418652, -950113, 1356189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-468, -495, 174, 338, 399]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-468, -495, 174, 338, 399]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![49, 83, 1, 0, 0], ![27, 78, 0, 1, 0], ![65, 33, 0, 0, 1]] where
  M :=![![![-468, -495, 174, 338, 399], ![-1474, -1613, 484, 1024, 1230], ![-2254, -2546, 641, 1508, 1842], ![-2613, -3097, 562, 1637, 2067], ![723, 735, -302, -544, -632]]]
  hmulB := by decide  
  f := ![![![-101162, 22305, 5950, -4820, -18879]], ![![47398, -10457, -2788, 2260, 8838]], ![![-11618, 2556, 683, -552, -2175]], ![![10613, -2346, -624, 507, 1974]], ![![-56725, 12505, 3336, -2702, -10589]]]
  g := ![![![-495, -612, 174, 338, 399], ![-1492, -1823, 484, 1024, 1230], ![-2181, -2631, 641, 1508, 1842], ![-2345, -2760, 562, 1637, 2067], ![801, 1001, -302, -544, -632]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [47, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 88], [0, 1]]
 g := ![![[66, 36], [4], [20], [82, 1], [85, 80], [1]], ![[0, 53], [4], [20], [6, 88], [57, 9], [1]]]
 h' := ![![[13, 88], [11, 6], [56, 87], [62, 51], [10, 88], [42, 13], [0, 1]], ![[0, 1], [0, 83], [30, 2], [13, 38], [86, 1], [33, 76], [13, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [4, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [47, 76, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1846, -2104, 1045, 2132, 934]
  a := ![-6, 7, 9, 6, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1925, -3213, 1045, 2132, 934]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-101162, 22305, 5950, -4820, -18879]] ![![-468, -495, 174, 338, 399]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27030, -7201, 36244, 35474, 33413]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-27030, -7201, 36244, 35474, 33413]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![46, 62, 79, 8, 1]] where
  M :=![![![-27030, -7201, 36244, 35474, 33413], ![-137774, -86903, 123372, 143436, 146018], ![-289454, -228810, 202551, 266808, 284290], ![-482211, -443917, 260602, 397641, 443125], ![13881, -22849, -51144, -38056, -30074]]]
  hmulB := by decide  
  f := ![![![-188, -49, 548, -292, 431]], ![![-278, -2379, 180, 512, -2614]], ![![2102, 6998, -4481, 692, 4150]], ![![-4703, -9683, 11750, -4045, -767]], ![![1083, 3379, -2379, 454, 1810]]]
  g := ![![![-16124, -21431, -26839, -2390, 33413], ![-70666, -94227, -117650, -10564, 146018], ![-137802, -184070, -229447, -20696, 284290], ![-215113, -287811, -358209, -32447, 443125], ![14405, 18987, 23966, 2088, -30074]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [53, 40, 42, 95, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 95, 3, 7], [5, 5, 42, 58], [26, 93, 52, 32], [0, 1]]
 g := ![![[28, 27, 0, 66], [64, 92, 16], [90, 22, 49], [63, 73, 36], [59, 2, 1], []], ![[42, 89, 7, 43, 59, 15], [31, 13, 16], [75, 95, 4], [0, 53, 6], [40, 7, 33], [1, 79, 57, 62, 60, 52]], ![[10, 23, 15, 77, 86, 67], [6, 47, 44], [94, 30, 72], [3, 12, 44], [14, 36, 16], [1, 76, 77, 32, 64, 45]], ![[78, 76, 30, 69, 52, 25], [2, 41, 88], [12, 82, 33], [4, 47, 11], [30, 14, 31], [80, 80, 15, 18, 46, 79]]]
 h' := ![![[68, 95, 3, 7], [67, 6, 39, 58], [89, 32, 41, 93], [3, 56, 47, 90], [74, 56, 8, 91], [0, 0, 0, 1], [0, 1]], ![[5, 5, 42, 58], [0, 72, 9, 93], [24, 72, 63, 93], [33, 42, 46, 2], [18, 28, 58, 43], [2, 39, 28, 18], [68, 95, 3, 7]], ![[26, 93, 52, 32], [21, 48, 48, 76], [40, 2, 3, 74], [47, 59, 79, 84], [77, 16, 11, 23], [72, 90, 48, 93], [5, 5, 42, 58]], ![[0, 1], [16, 68, 1, 64], [92, 88, 87, 31], [90, 37, 22, 18], [37, 94, 20, 37], [47, 65, 21, 82], [26, 93, 52, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [96, 66, 81], []]
 b := ![[], [], [69, 68, 83, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [53, 40, 42, 95, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38746449, -41493010, 10813300, 26670244, 34202042]
  a := ![-3, 8, 6, 9, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16618973, -22288862, -27743794, -2545836, 34202042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![188, 49, -548, 292, -431]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![188, 49, -548, 292, -431]] 
 ![![97, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![188, 49, -548, 292, -431], ![278, 2379, -180, -512, 2614], ![-2102, -6998, 4481, -692, -4150], ![4703, 9683, -11750, 4045, 767], ![-2501, -2137, 7132, -3418, 3902]]]
  hmulB := by decide  
  f := ![![![27030, 7201, -36244, -35474, -33413]], ![![15632, 4682, -20328, -20130, -19073]], ![![5492, 3027, -5451, -6042, -6031]], ![![15003, 7249, -16138, -17265, -16969]], ![![22707, 6323, -30112, -29596, -27936]]]
  g := ![![![283, 49, -548, 292, -431], ![-3251, 2379, -180, -512, 2614], ![7007, -6998, 4481, -692, -4150], ![-6102, 9683, -11750, 4045, 767], ![-1594, -2137, 7132, -3418, 3902]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-27030, -7201, 36244, 35474, 33413]] ![![188, 49, -548, 292, -431]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![92, 50, -82, 30, 15]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![92, 50, -82, 30, 15]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![60, 37, 8, 2, 1]] where
  M :=![![![92, 50, -82, 30, 15], ![-90, -5, 190, -104, 150], ![-46, -429, 41, 86, -462], ![421, 1241, -900, 179, 645], ![-339, -810, 884, -284, -142]]]
  hmulB := by decide  
  f := ![![![-26, -34, 4, 16, 21]], ![![-74, -95, 6, 40, 54]], ![![-94, -129, -1, 46, 66]], ![![-75, -119, -20, 25, 45]], ![![-51, -67, 4, 28, 38]]]
  g := ![![![-8, -5, -2, 0, 15], ![-90, -55, -10, -4, 150], ![274, 165, 37, 10, -462], ![-379, -224, -60, -11, 645], ![81, 44, 20, 0, -142]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [12, 15, 99, 94, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 71, 41, 75], [36, 55, 57, 38], [68, 75, 3, 89], [0, 1]]
 g := ![![[67, 1, 18, 36], [61, 60, 5], [65, 75, 36, 31], [41, 95, 82], [51, 7, 1], []], ![[9, 0, 100, 54, 18, 73], [58, 29, 16], [93, 5, 43, 13, 34, 27], [6, 94, 84], [96, 30, 71], [98, 4, 6, 15, 11, 99]], ![[55, 63, 96, 33, 66, 90], [25, 43, 33], [86, 42, 8, 10, 10, 94], [42, 59, 70], [66, 20, 100], [50, 59, 71, 39, 81, 29]], ![[50, 45, 53, 28, 28, 3], [0, 59, 24], [81, 20, 87, 38, 23, 67], [2, 9, 95], [55, 81, 13], [91, 84, 46, 86, 7, 90]]]
 h' := ![![[4, 71, 41, 75], [52, 46, 70, 95], [28, 21, 39, 56], [49, 50, 39, 43], [95, 60, 86, 53], [0, 0, 0, 1], [0, 1]], ![[36, 55, 57, 38], [95, 3, 85, 77], [65, 63, 23, 97], [13, 75, 36, 41], [61, 76, 24, 36], [100, 72, 5, 24], [4, 71, 41, 75]], ![[68, 75, 3, 89], [3, 18, 24, 35], [0, 56, 52, 72], [55, 5, 26, 34], [16, 83, 83, 26], [0, 80, 67, 10], [36, 55, 57, 38]], ![[0, 1], [30, 34, 23, 96], [63, 62, 88, 78], [47, 72, 0, 84], [77, 84, 9, 87], [38, 50, 29, 66], [68, 75, 3, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [55, 23, 4], []]
 b := ![[], [], [35, 60, 88, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [12, 15, 99, 94, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1690559228, 4378479887, -4083902415, 1129133177, 1562747215]
  a := ![16, -7, -33, -7, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-911626472, -529140268, -164216635, -19765953, 1562747215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26, -34, 4, 16, 21]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-26, -34, 4, 16, 21]] 
 ![![101, 0, 0, 0, 0], ![91, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![-26, -34, 4, 16, 21], ![-74, -95, 6, 40, 54], ![-94, -129, -1, 46, 66], ![-75, -119, -20, 25, 45], ![49, 58, -10, -30, -38]]]
  hmulB := by decide  
  f := ![![![92, 50, -82, 30, 15]], ![![82, 45, -72, 26, 15]], ![![46, 21, -41, 16, 3]], ![![57, 41, -56, 19, 15]], ![![85, 40, -70, 26, 13]]]
  g := ![![![-1, -34, 4, 16, 21], ![7, -95, 6, 40, 54], ![26, -129, -1, 46, 66], ![59, -119, -20, 25, 45], ![7, 58, -10, -30, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![92, 50, -82, 30, 15]] ![![-26, -34, 4, 16, 21]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 245, 120, -130, 396]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-11, 245, 120, -130, 396]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![26, 43, 24, 1, 0], ![92, 28, 55, 0, 1]] where
  M :=![![![-11, 245, 120, -130, 396], ![-532, -2131, 1022, -20, -1572], ![1592, 4155, -3723, 1002, 1512], ![-2248, -2778, 6158, -2711, 2280], ![536, -1819, -2182, 1682, -4079]]]
  hmulB := by decide  
  f := ![![![615, 639, -214, -426, -504]], ![![1860, 2069, -582, -1280, -1548]], ![![2828, 3229, -759, -1862, -2292]], ![![1622, 1815, -480, -1095, -1332]], ![![2556, 2848, -751, -1716, -2087]]]
  g := ![![![-321, -51, -180, -130, 396], ![1404, 415, 854, -20, -1572], ![-1588, -789, -1077, 1002, 1512], ![-1374, 485, -526, -2711, 2280], ![3224, 389, 1765, 1682, -4079]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [56, 72, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 88, 9], [55, 14, 94], [0, 1]]
 g := ![![[97, 8, 72], [57, 33, 66], [35, 56, 33], [41, 28], [46, 29], [1]], ![[99, 34, 102, 50], [38, 8, 97, 52], [49, 15, 8, 2], [96, 32], [17, 19], [57, 51, 101, 8]], ![[82, 71, 10, 75], [75, 75, 85, 35], [11, 12, 69, 35], [2, 16], [102, 60], [54, 11, 68, 95]]]
 h' := ![![[27, 88, 9], [1, 31, 81], [100, 11, 13], [38, 33, 41], [45, 38, 53], [47, 31, 82], [0, 1]], ![[55, 14, 94], [100, 5, 74], [84, 91, 75], [29, 43, 47], [96, 30, 54], [11, 96, 88], [27, 88, 9]], ![[0, 1], [30, 67, 51], [38, 1, 15], [98, 27, 15], [2, 35, 99], [96, 79, 36], [55, 14, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 29], []]
 b := ![[], [63, 8, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [56, 72, 21, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![296040, 347084, -560710, 174670, -294980]
  a := ![7, -4, -13, -5, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![222260, 10638, 111370, 174670, -294980]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 63, 50, -44, 118]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-11, 63, 50, -44, 118]] 
 ![![103, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-11, 63, 50, -44, 118], ![-148, -639, 274, 12, -500], ![488, 1325, -1127, 286, 536], ![-748, -1054, 2010, -847, 572], ![224, -405, -812, 556, -1201]]]
  hmulB := by decide  
  f := ![![![-2721, -4403, -1040, 656, 1414]], ![![-1863, -3042, -742, 432, 958]], ![![-1060, -1787, -493, 202, 516]], ![![-1981, -3347, -938, 365, 954]], ![![-125, -210, -62, 20, 57]]]
  g := ![![![-36, 63, 50, -44, 118], ![345, -639, 274, 12, -500], ![-701, 1325, -1127, 286, 536], ![529, -1054, 2010, -847, 572], ![244, -405, -812, 556, -1201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7083640136, 1561912392, 416495114, -337442454, -1322042269]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-7083640136, 1561912392, 416495114, -337442454, -1322042269]] 
 ![![103, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-7083640136, 1561912392, 416495114, -337442454, -1322042269], ![3318969446, -731818585, -195144662, 158105320, 619429814], ![-777535134, 171443177, 45716549, -37039342, -145113854], ![-1477331527, 325745293, 86862312, -70375453, -275719079], ![-2600549463, 573410048, 152903892, -123882040, -485348810]]]
  hmulB := by decide  
  f := ![![![20118, 47044, -48800, 15076, 11267]], ![![16872, 40117, -40742, 12372, 10395]], ![![972, 437, -2897, 1502, -2077]], ![![10313, 26513, -24312, 6717, 9199]], ![![1325, 2692, -3346, 1174, 160]]]
  g := ![![![-1069970628, 1561912392, 416495114, -337442454, -1322042269], ![501324143, -731818585, -195144662, 158105320, 619429814], ![-117445232, 171443177, 45716549, -37039342, -145113854], ![-223148172, 325745293, 86862312, -70375453, -275719079], ![-392808145, 573410048, 152903892, -123882040, -485348810]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-11, 245, 120, -130, 396]] ![![-11, 63, 50, -44, 118]]
  ![![208365, -21608, -651512, 368030, -609434]] where
 M := ![![![208365, -21608, -651512, 368030, -609434]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![208365, -21608, -651512, 368030, -609434]] ![![-7083640136, 1561912392, 416495114, -337442454, -1322042269]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![35441047932, -7814599906, -2083818750, 1688300604, 6614475321]]]
 hmul := by decide  
 g := ![![![![344087844, -75869902, -20231250, 16391268, 64218207]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)


lemma PB434I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB434I2 : PrimesBelowBoundCertificateInterval O 61 103 434 where
  m := 9
  g := ![3, 1, 2, 2, 2, 2, 2, 2, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB434I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
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
    · exact ![1804229351]
    · exact ![389017, 5329]
    · exact ![493039, 6241]
    · exact ![571787, 6889]
    · exact ![704969, 7921]
    · exact ![88529281, 97]
    · exact ![104060401, 101]
    · exact ![1092727, 103, 103]
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
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
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I67N1, I67N2, I97N1, I101N1, I103N1, I103N2]
  Il := ![[I67N1, I67N2], [], [], [], [], [], [I97N1], [I101N1], [I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
