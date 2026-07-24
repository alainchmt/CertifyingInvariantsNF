
import IdealArithmetic.Examples.NF5_3_3037500000_1.RI5_3_3037500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-462, -861, -356, -83, 74]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-462, -861, -356, -83, 74]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![28, 11, 21, 1, 0], ![65, 17, 45, 0, 1]] where
  M :=![![![-462, -861, -356, -83, 74], ![3987, 4316, 1294, 75, -240], ![-13125, -11091, -2479, 399, 390], ![1648, -450, -742, -435, 188], ![-2203, 2247, 1934, 929, -465]]]
  hmulB := by decide  
  f := ![![![-2918, -2055, -548, -61, 112]], ![![6099, 4286, 1142, 123, -234]], ![![-12747, -8961, -2389, -279, 480]], ![![-4194, -2951, -787, -93, 158]], ![![-9951, -7001, -1867, -220, 375]]]
  g := ![![![-44, -18, -29, -83, 74], ![261, 113, 157, 75, -240], ![-741, -330, -424, 399, 390], ![24, 17, -1, -435, 188], ![30, -1, 50, 929, -465]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [37, 42, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 54, 6], [48, 12, 61], [0, 1]]
 g := ![![[9, 56, 36], [56, 17, 60], [11, 35], [48, 39], [50, 1], []], ![[14, 2, 41, 29], [13, 4, 53, 1], [8, 17], [18, 14], [6, 10], [36, 36]], ![[63, 57, 51, 3], [24, 62, 34, 31], [9, 39], [52, 29], [20, 35], [48, 36]]]
 h' := ![![[2, 54, 6], [5, 56, 61], [42, 43, 44], [39, 54, 54], [26, 7, 46], [0, 0, 1], [0, 1]], ![[48, 12, 61], [45, 32, 63], [53, 54, 49], [58, 29, 34], [56, 23, 58], [12, 52, 12], [2, 54, 6]], ![[0, 1], [61, 46, 10], [12, 37, 41], [55, 51, 46], [61, 37, 30], [59, 15, 54], [48, 12, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 1], []]
 b := ![[], [56, 1, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [37, 42, 17, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2112938753, -3301354086, -1113323818, -1940982552, -351417918]
  a := ![-5, -2, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1120548319, 358560576, 827777852, -1940982552, -351417918]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2918, -2055, -548, -61, 112]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-2918, -2055, -548, -61, 112]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![8, 8, 1, 0, 0], ![34, 47, 0, 1, 0], ![34, 44, 0, 0, 1]] where
  M :=![![![-2918, -2055, -548, -61, 112], ![6099, 4286, 1142, 123, -234], ![-12747, -8961, -2389, -279, 480], ![1304, 858, 222, -17, -56], ![-7115, -5109, -1378, -311, 223]]]
  hmulB := by decide  
  f := ![![![-462, -861, -356, -83, 74]], ![![3987, 4316, 1294, 75, -240]], ![![225, 247, 75, 5, -14]], ![![2587, 2584, 716, 4, -128]], ![![2351, 2431, 698, 21, -127]]]
  g := ![![![-4, 4, -548, -61, 112], ![11, -5, 1142, 123, -234], ![-7, 32, -2389, -279, 480], ![30, 35, 222, -17, -56], ![103, 160, -1378, -311, 223]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [38, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 66], [0, 1]]
 g := ![![[30, 14], [51, 33], [35], [64], [1], [1]], ![[16, 53], [18, 34], [35], [64], [1], [1]]]
 h' := ![![[66, 66], [5, 58], [36, 57], [48, 54], [66, 8], [29, 66], [0, 1]], ![[0, 1], [14, 9], [46, 10], [61, 13], [58, 59], [30, 1], [66, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [4, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [38, 1, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-512344, -566525, -182055, -55194, 53316]
  a := ![6, -62, -1, -57, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15044, 16987, -182055, -55194, 53316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-462, -861, -356, -83, 74]] ![![-2918, -2055, -548, -61, 112]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36822, 44449, 14956, 2049, -2938]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![36822, 44449, 14956, 2049, -2938]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![33, 5, 8, 1, 0], ![44, 48, 19, 0, 1]] where
  M :=![![![36822, 44449, 14956, 2049, -2938], ![-159541, -150412, -39864, 707, 7036], ![387687, 276711, 45889, -20361, -5622], ![24842, 88742, 43208, 13095, -9368], ![-88061, -221043, -99466, -26785, 21121]]]
  hmulB := by decide  
  f := ![![![20458, 30207, 10056, 16351, 2712]], ![![165511, 264874, 89792, 160759, 29990]], ![![1810209, 2804097, 943835, 1629201, 291528]], ![![265429, 411741, 138632, 239693, 42974]], ![![805766, 1255004, 422937, 734694, 132451]]]
  g := ![![![1387, 2468, 766, 2049, -2938], ![-6936, -6925, -2524, 707, 7036], ![18408, 9132, 4445, -20361, -5622], ![69, 6661, 1640, 13095, -9368], ![-1880, -15506, -4035, -26785, 21121]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [68, 27, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 60, 25], [10, 10, 46], [0, 1]]
 g := ![![[42, 6, 60], [65, 31, 20], [63, 15, 2], [70, 10], [65, 1], []], ![[42, 44, 48, 3], [8, 9, 52, 8], [35, 39, 0, 16], [59, 37], [7, 29], [31, 57]], ![[67, 56, 51, 33], [51, 2, 56, 55], [14, 57, 21, 22], [37, 18], [34, 50], [10, 57]]]
 h' := ![![[55, 60, 25], [53, 50, 42], [47, 68, 34], [37, 10, 12], [53, 23, 9], [0, 0, 1], [0, 1]], ![[10, 10, 46], [66, 36, 37], [33, 7, 52], [18, 27, 15], [57, 45, 26], [65, 41, 10], [55, 60, 25]], ![[0, 1], [49, 56, 63], [35, 67, 56], [64, 34, 44], [33, 3, 36], [59, 30, 60], [10, 10, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 10], []]
 b := ![[], [38, 22, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [68, 27, 6, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-87004450, -135894014, -45824622, -79864810, -14452810]
  a := ![-1, -3, 1, -5, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![44851520, 13481196, 12221088, -79864810, -14452810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20458, -30207, -10056, -16351, -2712]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-20458, -30207, -10056, -16351, -2712]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![16, 23, 1, 0, 0], ![57, 57, 0, 1, 0], ![21, 66, 0, 0, 1]] where
  M :=![![![-20458, -30207, -10056, -16351, -2712], ![-165511, -264874, -89792, -160759, -29990], ![-1810209, -2804097, -943835, -1629201, -291528], ![-2861118, -4479634, -1511384, -2641217, -479484], ![-13970735, -21784381, -7343182, -12772579, -2306141]]]
  hmulB := by decide  
  f := ![![![-36822, -44449, -14956, -2049, 2938]], ![![159541, 150412, 39864, -707, -7036]], ![![37924, 34811, 8897, -404, -1538]], ![![98171, 83819, 19388, -2397, -3158]], ![![138655, 129786, 34034, -886, -5969]]]
  g := ![![![15907, 18480, -10056, -16351, -2712], ![155834, 182295, -89792, -160759, -29990], ![1581376, 1845203, -943835, -1629201, -291528], ![2562529, 2992641, -1511384, -2641217, -479484], ![12394171, 14469734, -7343182, -12772579, -2306141]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [48, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 70], [0, 1]]
 g := ![![[10, 37], [24, 32], [54, 1], [12], [5], [1]], ![[0, 34], [0, 39], [0, 70], [12], [5], [1]]]
 h' := ![![[17, 70], [55, 26], [35, 23], [17, 70], [5, 15], [23, 17], [0, 1]], ![[0, 1], [0, 45], [0, 48], [0, 1], [47, 56], [28, 54], [17, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [58, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [48, 54, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![731879, 1147733, 387518, 674515, 122117]
  a := ![8, 19, -3, 26, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-654651, -764398, 387518, 674515, 122117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![36822, 44449, 14956, 2049, -2938]] ![![-20458, -30207, -10056, -16351, -2712]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [30, 31, 62, 68, 37, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 62, 34, 58, 13], [1, 24, 32, 25, 51], [46, 34, 38, 6, 36], [22, 25, 42, 57, 46], [0, 1]]
 g := ![![[23, 63, 16, 11, 36], [6, 44, 46, 3], [18, 4, 35, 54], [37, 15, 60, 36, 1], [], []], ![[65, 22, 8, 69, 49, 24, 2, 5], [58, 44, 25, 38], [36, 65, 61, 32], [48, 13, 47, 24, 54, 44, 13, 53], [10, 43, 57, 12], [14, 56, 0, 23]], ![[32, 67, 3, 32, 51, 29, 24, 15], [62, 5, 56, 12], [47, 22, 70, 72], [55, 2, 7, 69, 25, 15, 17, 11], [33, 41, 51, 27], [48, 45, 45, 46]], ![[38, 71, 39, 0, 26, 30, 3, 57], [33, 6, 18, 32], [61, 45, 17, 72], [53, 45, 30, 63, 9, 49, 58, 49], [60, 1, 54, 48], [12, 16, 3, 55]], ![[49, 68, 13, 56, 37, 61, 16, 72], [34, 52, 54, 3], [49, 33, 5, 27], [19, 46, 16, 25, 33, 71, 38, 61], [23, 11, 32, 3], [59, 51, 25, 72]]]
 h' := ![![[40, 62, 34, 58, 13], [57, 54, 34, 45, 6], [50, 1, 22, 2, 21], [58, 9, 40, 38, 45], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[1, 24, 32, 25, 51], [6, 65, 66, 14, 15], [40, 48, 58, 37, 44], [5, 34, 38, 65, 18], [63, 55, 55, 57, 7], [12, 72, 18, 19, 42], [40, 62, 34, 58, 13]], ![[46, 34, 38, 6, 36], [38, 45, 31, 48, 19], [0, 69, 24, 72, 42], [13, 56, 32, 44, 46], [35, 68, 58, 56, 6], [21, 57, 29, 57, 63], [1, 24, 32, 25, 51]], ![[22, 25, 42, 57, 46], [35, 1, 65, 58, 55], [52, 20, 48, 5, 18], [35, 8, 32, 51, 27], [41, 39, 58, 22, 11], [4, 13, 37, 23, 62], [46, 34, 38, 6, 36]], ![[0, 1], [63, 54, 23, 54, 51], [39, 8, 67, 30, 21], [7, 39, 4, 21, 10], [21, 57, 48, 11, 48], [28, 4, 61, 47, 52], [22, 25, 42, 57, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 64, 67, 49], [], [], []]
 b := ![[], [55, 16, 70, 29, 58], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [30, 31, 62, 68, 37, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2719574739431050342, -4247632349567192183, -1432336961258611873, -2496116233966095319, -451682435376594067]
  a := ![-10, 1, 5, -7, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37254448485356854, -58186744514619071, -19621054263816601, -34193373068028703, -6187430621597179]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [1, 47, 64, 75, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 20, 47, 68, 60], [44, 17, 15, 16, 22], [59, 25, 40, 37, 4], [78, 16, 56, 37, 72], [0, 1]]
 g := ![![[53, 33, 58, 27, 36], [4, 18, 54, 25, 49], [72, 78, 70, 77, 18], [7, 30, 35, 49, 1], [], []], ![[54, 15, 32, 23, 63, 17, 1, 60], [59, 11, 69, 38, 74, 55, 45, 70], [4, 56, 0, 40, 0, 23, 61, 78], [16, 70, 33, 24, 24, 56, 28, 54], [65, 23, 6, 52], [67, 10, 16, 45]], ![[45, 21, 65, 34, 38, 27, 14, 10], [25, 3, 45, 35, 16, 2, 30, 20], [6, 38, 66, 14, 21, 76, 14, 73], [14, 39, 38, 32, 29, 42, 20, 11], [4, 75, 68, 9], [31, 54, 9, 10]], ![[64, 20, 38, 33, 25, 29, 31, 16], [56, 54, 1, 43, 12, 29, 61, 40], [50, 21, 30, 39, 44, 36, 49, 25], [24, 36, 78, 15, 29, 16, 31, 45], [44, 8, 43, 45], [65, 5, 53, 16]], ![[70, 26, 7, 64, 11, 19, 52, 13], [42, 15, 45, 77, 6, 12, 24, 8], [30, 1, 46, 45, 42, 32, 77, 38], [21, 70, 12, 41, 31, 44, 34, 38], [64, 33, 65, 25], [46, 65, 66, 49]]]
 h' := ![![[26, 20, 47, 68, 60], [75, 1, 42, 33, 6], [7, 63, 0, 56, 7], [72, 36, 3, 48, 27], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[44, 17, 15, 16, 22], [41, 3, 5, 23, 1], [4, 13, 55, 21, 15], [56, 12, 8, 25, 5], [69, 70, 68, 35, 54], [56, 14, 45, 60, 17], [26, 20, 47, 68, 60]], ![[59, 25, 40, 37, 4], [64, 41, 24, 70, 38], [66, 56, 53, 56, 53], [4, 38, 73, 51, 34], [77, 20, 28, 52, 44], [9, 64, 1, 49, 76], [44, 17, 15, 16, 22]], ![[78, 16, 56, 37, 72], [71, 45, 60, 2, 77], [19, 43, 25, 69, 57], [35, 14, 68, 59, 42], [1, 64, 54, 78, 30], [19, 48, 28, 7, 60], [59, 25, 40, 37, 4]], ![[0, 1], [76, 68, 27, 30, 36], [44, 62, 25, 35, 26], [20, 58, 6, 54, 50], [65, 4, 8, 72, 29], [34, 32, 4, 42, 5], [78, 16, 56, 37, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 57, 39, 43], [], [], []]
 b := ![[], [47, 65, 40, 38, 48], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [1, 47, 64, 75, 30, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45421437853487859, 70947261605648850, 23924362113686554, 41695856683652550, 7545694164779572]
  a := ![6, -10, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![574954909537821, 898066602603150, 302840026755526, 527795654223450, 95515116009868]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 3077056399 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀

instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]] where
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [80, 20, 25, 31, 61, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 14, 71, 29, 11], [33, 50, 7, 76, 67], [40, 27, 69, 54, 50], [71, 74, 19, 7, 38], [0, 1]]
 g := ![![[70, 16, 19, 57, 51], [59, 77, 52, 48, 77], [60, 68, 32, 40], [82, 31, 71, 69], [1], []], ![[58, 25, 13, 27, 56, 69, 67, 59], [66, 19, 73, 10, 78, 34, 57, 33], [2, 29, 10, 69], [62, 6, 42, 7], [79, 42, 46, 46, 21, 49, 38, 3], [35, 38, 63, 38]], ![[29, 54, 14, 72, 19, 17, 18, 80], [5, 18, 72, 60, 7, 63, 76, 76], [20, 4, 17, 41], [56, 20, 15, 77], [51, 61, 67, 25, 9, 15, 10, 57], [49, 39, 46, 7]], ![[78, 53, 25, 77, 80, 79, 42, 52], [9, 52, 46, 36, 34, 21, 50, 13], [72, 48, 51, 59], [21, 67, 49, 10], [22, 57, 36, 23, 42, 0, 11, 55], [81, 14, 59, 10]], ![[41, 62, 40, 76, 42, 77, 55, 9], [70, 40, 35, 62, 33, 38, 33, 17], [33, 15, 61, 51], [38, 42, 82, 49], [50, 78, 63, 26, 56, 7, 66, 17], [46, 9, 13, 33]]]
 h' := ![![[44, 14, 71, 29, 11], [11, 57, 29, 39, 47], [50, 82, 17, 71, 34], [6, 76, 34, 19, 17], [3, 63, 58, 52, 22], [0, 0, 1], [0, 1]], ![[33, 50, 7, 76, 67], [33, 1, 9, 49, 51], [10, 67, 21, 2, 13], [2, 5, 66, 72, 61], [56, 28, 80, 45, 67], [49, 65, 18, 31, 11], [44, 14, 71, 29, 11]], ![[40, 27, 69, 54, 50], [22, 34, 11, 30, 59], [52, 3, 8, 74, 79], [18, 27, 50, 43, 37], [4, 1, 18, 40, 34], [74, 30, 16, 82, 26], [33, 50, 7, 76, 67]], ![[71, 74, 19, 7, 38], [9, 11, 66, 26, 54], [57, 8, 2, 21, 56], [16, 20, 82, 11, 15], [6, 13, 46, 29, 50], [17, 1, 54, 51, 62], [40, 27, 69, 54, 50]], ![[0, 1], [23, 63, 51, 22, 38], [8, 6, 35, 81, 67], [18, 38, 17, 21, 36], [30, 61, 47, 0, 76], [33, 70, 77, 2, 67], [71, 74, 19, 7, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 34, 78, 30], [], [], []]
 b := ![[], [59, 35, 21, 21, 35], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [80, 20, 25, 31, 61, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![742667826622988, 1159928486882954, 391135282329308, 681611816654632, 123337660567018]
  a := ![6, 13, 4, 20, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8947805140036, 13975042010638, 4712473281076, 8212190562104, 1485995910446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 3939040643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![156283713, -23007640, -59032828, -36737742, 15216346]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![156283713, -23007640, -59032828, -36737742, 15216346]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![21, 40, 10, 80, 1]] where
  M :=![![![156283713, -23007640, -59032828, -36737742, 15216346], ![800161288, 1181276563, 439787790, 80772016, -88691830], ![-4797278634, -4887129912, -1382866693, -29947974, 250235862], ![1888756762, 1213154116, 138343138, -135358743, -7342720], ![-3690763726, -2176782546, -159630152, 304612138, -10506265]]]
  hmulB := by decide  
  f := ![![![-22018255, -15030756, -3965040, -333526, 792066]], ![![43230104, 28659839, 7480618, 430280, -1459118]], ![![-79821210, -49598364, -12625745, 81330, 2319678]], ![![-337782, -3403900, -1195094, -842327, 370056]], ![![4748415, 668830, -64482, -606828, 119341]]]
  g := ![![![-1834377, -7097320, -2372992, -14090398, 15216346], ![29917862, 53134267, 14906810, 80630544, -88691830], ![-112946424, -167377128, -43654217, -225267606, 250235862], ![22954538, 16931044, 2379442, 5079313, -7342720], ![-38990249, -19736314, -613118, 12866442, -10506265]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [18, 45, 51, 62, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 86, 73, 26], [24, 40, 83, 55], [1, 51, 22, 8], [0, 1]]
 g := ![![[79, 62, 2, 78], [80], [22, 57, 57], [17, 21, 15, 88], [27, 1], []], ![[80, 20, 51, 40, 47, 3], [1, 2, 78], [16, 26, 85], [5, 13, 64, 51, 78, 35], [34, 11, 10, 3, 72, 27], [42, 65, 53]], ![[53, 48, 37, 53, 84, 8], [8, 76, 22], [72, 84, 68], [56, 61, 70, 21, 2, 49], [54, 32, 62, 23, 53, 68], [0, 25, 88]], ![[88, 40, 72, 12, 80, 36], [65, 30, 21], [15, 86, 16], [19, 76, 41, 47, 66, 16], [34, 3, 10, 17, 1, 10], [84, 33, 64]]]
 h' := ![![[2, 86, 73, 26], [29, 55, 1, 16], [57, 75, 13], [50, 4, 56, 71], [48, 13, 2, 55], [0, 0, 1], [0, 1]], ![[24, 40, 83, 55], [51, 74, 4, 61], [43, 67, 1, 16], [8, 84, 18, 68], [7, 31, 84, 67], [49, 43, 65, 84], [2, 86, 73, 26]], ![[1, 51, 22, 8], [34, 52, 68, 19], [0, 38, 79, 17], [53, 20, 36, 35], [68, 1, 22, 81], [42, 46, 27, 40], [24, 40, 83, 55]], ![[0, 1], [31, 86, 16, 82], [69, 87, 85, 56], [61, 70, 68, 4], [15, 44, 70, 64], [2, 0, 85, 54], [1, 51, 22, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [52, 45, 50], []]
 b := ![[], [], [76, 79, 81, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [18, 45, 51, 62, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![288346556720, 450745181567, 152023791229, 265186597744, 48041038681]
  a := ![2, -5, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8095677029, -16526925457, -3689737029, -40203331424, 48041038681]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22018255, 15030756, 3965040, 333526, -792066]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![22018255, 15030756, 3965040, 333526, -792066]] 
 ![![89, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![22018255, 15030756, 3965040, 333526, -792066], ![-43230104, -28659839, -7480618, -430280, 1459118], ![79821210, 49598364, 12625745, -81330, -2319678], ![337782, 3403900, 1195094, 842327, -370056], ![18977210, 2926174, -167192, -2358014, 448577]]]
  hmulB := by decide  
  f := ![![![-156283713, 23007640, 59032828, 36737742, -15216346]], ![![-42354515, -8361027, 7661078, 6935338, -2251896]], ![![-93601722, 76626648, 71254205, 35010318, -17173134]], ![![-84437870, -4324484, 22324030, 16381095, -6072424]], ![![-104278477, 45914794, 56846684, 30838432, -14072477]]]
  g := ![![![-6099943, 15030756, 3965040, 333526, -792066], ![11506315, -28659839, -7480618, -430280, 1459118], ![-19411788, 49598364, 12625745, -81330, -2319678], ![-1846442, 3403900, 1195094, 842327, -370056], ![281805, 2926174, -167192, -2358014, 448577]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![156283713, -23007640, -59032828, -36737742, 15216346]] ![![22018255, 15030756, 3965040, 333526, -792066]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [22, 48, 73, 51, 75, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 58, 26, 94, 5], [52, 4, 4, 52, 1], [26, 68, 21, 77, 43], [13, 63, 46, 68, 48], [0, 1]]
 g := ![![[34, 45, 92, 82, 62], [18, 27, 59, 12], [74, 6, 29, 64], [89, 89, 50, 85], [22, 1], []], ![[64, 95, 78, 7, 89, 18, 34, 74], [39, 81, 56, 18], [73, 34, 58, 48], [71, 74, 75, 32], [12, 24, 44, 85], [50, 29, 60, 36, 75, 44, 3, 28]], ![[46, 14, 18, 3, 79, 84, 22, 73], [79, 79, 52, 11], [95, 41, 85, 11], [52, 6, 42, 4], [46, 41, 11, 75], [73, 92, 3, 68, 36, 58, 81, 1]], ![[2, 47, 73, 21, 61, 61, 53, 33], [3, 63, 8, 25], [18, 90, 71, 35], [20, 68, 7, 70], [48, 79], [3, 25, 14, 58, 57, 87, 78, 64]], ![[30, 75, 93, 14, 45, 68, 55, 73], [27, 26, 34, 22], [12, 66, 29, 73], [83, 55, 30, 54], [75, 59, 83, 25], [72, 43, 81, 47, 7, 47, 24, 12]]]
 h' := ![![[28, 58, 26, 94, 5], [62, 79, 88, 63, 16], [19, 43, 8, 90, 77], [80, 53, 76, 68, 89], [1, 86, 92, 66, 45], [0, 0, 0, 1], [0, 1]], ![[52, 4, 4, 52, 1], [39, 19, 56, 81, 48], [86, 5, 95, 56, 42], [25, 25, 94, 44, 57], [36, 42, 20, 29, 41], [94, 3, 0, 53, 45], [28, 58, 26, 94, 5]], ![[26, 68, 21, 77, 43], [62, 34, 48, 52, 49], [32, 93, 48, 42, 37], [52, 73, 64, 48, 60], [56, 96, 60, 60, 95], [1, 51, 10, 29, 47], [52, 4, 4, 52, 1]], ![[13, 63, 46, 68, 48], [31, 22, 11, 82, 24], [0, 36, 37, 4, 5], [69, 4, 53, 59, 36], [86, 91, 20, 48, 78], [50, 52, 50, 51], [26, 68, 21, 77, 43]], ![[0, 1], [54, 40, 88, 13, 57], [39, 17, 6, 2, 33], [20, 39, 4, 72, 49], [87, 73, 2, 88, 32], [31, 88, 37, 60, 5], [13, 63, 46, 68, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 34, 45, 86], [], [], []]
 b := ![[], [82, 74, 55, 6, 41], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [22, 48, 73, 51, 75, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1712751261601247242, 2675104288594301876, 902067648692813952, 1572024425058886700, 284464680503643276]
  a := ![10, -1, 0, 5, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17657229501043786, 27578394727776308, 9299666481369216, 16206437371741100, 2932625572202508]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [75, 84, 65, 7, 34, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 58, 89, 54, 30], [69, 59, 12, 33, 67], [46, 16, 32, 79, 36], [10, 68, 69, 36, 69], [0, 1]]
 g := ![![[91, 35, 60, 73, 54], [81, 44, 61, 85], [19, 43, 89, 36, 84], [13, 32, 8, 30], [67, 1], []], ![[46, 63, 76, 75, 25, 4, 29, 95], [28, 22, 99, 6], [90, 95, 87, 95, 41, 40, 37, 82], [99, 1, 21, 1], [46, 40, 75, 23], [1, 27, 59, 46, 32, 86, 46, 33]], ![[48, 20, 96, 50, 37, 18, 96, 91], [20, 29, 28, 82], [2, 59, 1, 88, 63, 52, 74, 53], [87, 22, 89, 30], [27, 92, 98, 13], [7, 68, 47, 41, 41, 92, 16, 86]], ![[38, 22, 29, 32, 57, 26, 62, 79], [20, 97, 58, 85], [77, 75, 81, 30, 66, 23, 76, 65], [88, 31, 98, 58], [44, 3, 39, 65], [61, 70, 4, 17, 40, 43, 13, 95]], ![[96, 90, 16, 12, 45, 34, 36, 27], [99, 52, 60, 95], [56, 42, 38, 89, 23, 42, 19, 12], [71, 37, 22, 21], [98, 42, 53, 81], [46, 84, 64, 81, 57, 31, 79, 57]]]
 h' := ![![[43, 58, 89, 54, 30], [5, 92, 27, 6, 16], [90, 14, 3, 78, 61], [54, 16, 43, 57, 36], [25, 54, 5, 72, 38], [0, 0, 0, 1], [0, 1]], ![[69, 59, 12, 33, 67], [37, 94, 63, 31, 11], [97, 94, 13, 0, 62], [86, 62, 13, 58, 20], [80, 32, 55, 23, 100], [46, 53, 64, 96, 86], [43, 58, 89, 54, 30]], ![[46, 16, 32, 79, 36], [39, 99, 69, 62, 38], [23, 64, 2, 38, 53], [15, 66, 26, 95, 89], [51, 35, 51, 8, 63], [37, 22, 36, 50, 66], [69, 59, 12, 33, 67]], ![[10, 68, 69, 36, 69], [94, 19, 66, 72, 56], [68, 14, 50, 52, 40], [21, 70, 81, 11, 10], [64, 52, 27, 97, 19], [43, 92, 59, 73, 41], [46, 16, 32, 79, 36]], ![[0, 1], [66, 100, 78, 31, 81], [44, 16, 33, 34, 87], [92, 89, 39, 82, 47], [93, 29, 64, 2, 83], [75, 35, 43, 83, 9], [10, 68, 69, 36, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 16, 39, 10], [], [], []]
 b := ![[], [24, 50, 29, 25, 67], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [75, 84, 65, 7, 34, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![212100811265164158, 331274642166999409, 111708561630687878, 194673126460756755, 35226891981673945]
  a := ![6, 1, -3, 6, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2100008032328358, 3279946952148509, 1106025362680078, 1927456697631255, 348781108729445]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51130, -45670, -11073, 1009, 1844]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-51130, -45670, -11073, 1009, 1844]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![25, 11, 1, 0, 0], ![40, 36, 0, 1, 0], ![58, 67, 0, 0, 1]] where
  M :=![![![-51130, -45670, -11073, 1009, 1844], ![102429, 61327, 4953, -8265, 174], ![1305, 131034, 74464, 26847, -16704], ![-199860, -213150, -63064, -3233, 11646], ![444796, 460418, 132386, 4240, -24153]]]
  hmulB := by decide  
  f := ![![![1487472, 1070860, 287679, 37157, -59762]], ![![-3249753, -2370689, -639633, -89391, 134076]], ![![84702, 59391, 15814, 1697, -3224]], ![![-569874, -422270, -114506, -17403, 24250]], ![![-1226197, -899451, -243113, -35033, 51147]]]
  g := ![![![761, -813, -11073, 1009, 1844], ![2904, 2842, 4953, -8265, 174], ![-19081, -5198, 74464, 26847, -16704], ![8064, -1780, -63064, -3233, 11646], ![-15860, 4561, 132386, 4240, -24153]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [4, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 102], [0, 1]]
 g := ![![[98, 26], [54, 68], [66, 63], [68], [50], [20, 1]], ![[0, 77], [75, 35], [90, 40], [68], [50], [40, 102]]]
 h' := ![![[20, 102], [93, 52], [45, 45], [25, 75], [20, 58], [23, 87], [0, 1]], ![[0, 1], [0, 51], [18, 58], [83, 28], [47, 45], [12, 16], [20, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [14, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [4, 83, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27561, 42931, 14272, 25915, 4824]
  a := ![3, 5, 0, 9, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15977, -13303, 14272, 25915, 4824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-417, -329, -91, -18, 20]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-417, -329, -91, -18, 20]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![72, 11, 1, 0, 0], ![74, 61, 0, 1, 0], ![18, 37, 0, 0, 1]] where
  M :=![![![-417, -329, -91, -18, 20], ![1082, 890, 249, 56, -56], ![-3024, -2595, -734, -186, 168], ![968, 896, 258, 75, -62], ![-3455, -3159, -908, -271, 211]]]
  hmulB := by decide  
  f := ![![![-13, 87, 53, 20, -12]], ![![-640, -802, -269, -34, 52]], ![![-50, 1, 15, 10, -4]], ![![-396, -416, -121, -5, 22]], ![![-219, -269, -89, -11, 17]]]
  g := ![![![69, 10, -91, -18, 20], ![-194, -31, 249, 56, -56], ![588, 103, -734, -186, 168], ![-214, -41, 258, 75, -62], ![759, 151, -908, -271, 211]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [71, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 102], [0, 1]]
 g := ![![[3, 49], [19, 8], [57, 98], [29], [72], [96, 1]], ![[72, 54], [66, 95], [92, 5], [29], [72], [89, 102]]]
 h' := ![![[96, 102], [93, 96], [73, 76], [29, 43], [53, 82], [85, 81], [0, 1]], ![[0, 1], [39, 7], [56, 27], [37, 60], [97, 21], [33, 22], [96, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [18, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [71, 7, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2015699, 3629248, 1255370, 2598434, 554052]
  a := ![-16, 9, -1, -7, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2821631, -1836740, 1255370, 2598434, 554052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19506, 13549, 3596, 357, -728]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![19506, 13549, 3596, 357, -728]] 
 ![![103, 0, 0, 0, 0], ![81, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![89, 0, 0, 0, 1]] where
  M :=![![![19506, 13549, 3596, 357, -728], ![-39683, -27218, -7192, -635, 1442], ![78675, 52659, 13793, 915, -2712], ![-4866, -2090, -436, 251, 36], ![33133, 18935, 4650, -471, -777]]]
  hmulB := by decide  
  f := ![![![3286, 11227, 5448, 1651, -1182]], ![![1969, 8113, 4056, 1276, -886]], ![![3361, 5518, 2165, 454, -444]], ![![1278, 5958, 3028, 971, -664]], ![![3713, 9790, 4502, 1264, -965]]]
  g := ![![![-11113, 13549, 3596, 357, -728], ![22283, -27218, -7192, -635, 1442], ![-42953, 52659, 13793, 915, -2712], ![1560, -2090, -436, 251, 36], ![-15041, 18935, 4650, -471, -777]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-51130, -45670, -11073, 1009, 1844]] ![![-417, -329, -91, -18, 20]]
  ![![-3286, -11227, -5448, -1651, 1182]] where
 M := ![![![-3286, -11227, -5448, -1651, 1182]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-3286, -11227, -5448, -1651, 1182]] ![![19506, 13549, 3596, 357, -728]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB2695I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB2695I2 : PrimesBelowBoundCertificateInterval O 61 103 2695 where
  m := 9
  g := ![2, 2, 1, 1, 1, 2, 1, 1, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB2695I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0]
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0]
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
    · exact ![300763, 4489]
    · exact ![357911, 5041]
    · exact ![2073071593]
    · exact ![3077056399]
    · exact ![3939040643]
    · exact ![62742241, 89]
    · exact ![8587340257]
    · exact ![10510100501]
    · exact ![10609, 10609, 103]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I89N1, I103N2]
  Il := ![[], [], [], [], [], [I89N1], [], [], [I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
