
import IdealArithmetic.Examples.NF5_1_25312500_1.RI5_1_25312500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-323, -115, -178, 79, 466]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-323, -115, -178, 79, 466]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![63, 16, 37, 63, 1]] where
  M :=![![![-323, -115, -178, 79, 466], ![-24, 230, -850, 177, 2284], ![3666, 1215, 2303, -957, -6042], ![-300, -1011, 2976, -568, -8032], ![1002, 414, 346, -204, -887]]]
  hmulB := by decide  
  f := ![![![31, -1, 16, -5, -50]], ![![-60, -4, -16, 3, 40]], ![![66, -39, 35, -21, -114]], ![![12, -27, 62, -28, -232]], ![![63, -49, 89, -42, -319]]]
  g := ![![![-443, -113, -260, -437, 466], ![-2148, -542, -1274, -2145, 2284], ![5736, 1461, 3371, 5667, -6042], ![7548, 1903, 4480, 7544, -8032], ![849, 218, 495, 831, -887]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [33, 44, 42, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 65, 35, 57], [11, 7, 24, 39], [57, 61, 8, 38], [0, 1]]
 g := ![![[64, 35, 20, 59], [59, 5, 12, 47], [16, 66, 15], [22, 0, 17], [1], []], ![[5, 16, 41, 35, 14, 20], [28, 62, 33, 21, 17, 66], [35, 5, 35], [25, 66, 60], [12, 31, 16], [53, 54, 33]], ![[12, 65, 47, 42, 64, 10], [12, 41, 11, 44, 35, 4], [37, 16, 1], [36, 36, 16], [55, 16, 25], [16, 6, 47]], ![[7, 53, 4, 40, 33, 13], [25, 34, 18, 13, 45, 52], [10, 63, 64], [40, 48, 49], [57, 41, 1], [54, 20, 37]]]
 h' := ![![[32, 65, 35, 57], [63, 63, 40, 27], [55, 9, 55, 39], [28, 60, 7, 22], [34, 23, 25, 33], [0, 0, 1], [0, 1]], ![[11, 7, 24, 39], [46, 43, 20, 47], [1, 9, 19, 28], [34, 39, 3, 54], [16, 22, 5, 23], [12, 46, 37, 63], [32, 65, 35, 57]], ![[57, 61, 8, 38], [37, 32, 44, 9], [45, 9, 66, 32], [44, 1, 42, 66], [19, 43, 39, 4], [62, 56, 33, 5], [11, 7, 24, 39]], ![[0, 1], [59, 63, 30, 51], [40, 40, 61, 35], [13, 34, 15, 59], [44, 46, 65, 7], [60, 32, 63, 66], [57, 61, 8, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [64, 27, 47], []]
 b := ![[], [], [3, 39, 27, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [33, 44, 42, 34, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44593584, 622607247, -600675495, 372463980, 2324372779]
  a := ![45, -18, 66, -24, -205]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2184938679, -545781451, -1292574154, -2180045091, 2324372779]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 1, -16, 5, 50]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-31, 1, -16, 5, 50]] 
 ![![67, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-31, 1, -16, 5, 50], ![60, 4, 16, -3, -40], ![-66, 39, -35, 21, 114], ![-12, 27, -62, 28, 232], ![-30, 12, -10, 6, 29]]]
  hmulB := by decide  
  f := ![![![323, 115, 178, -79, -466]], ![![10, 0, 18, -5, -48]], ![![249, 90, 133, -60, -348]], ![![125, 58, 22, -21, -54]], ![![67, 23, 40, -17, -105]]]
  g := ![![![0, 1, -16, 5, 50], ![-3, 4, 16, -3, -40], ![-6, 39, -35, 21, 114], ![-12, 27, -62, 28, 232], ![-1, 12, -10, 6, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-323, -115, -178, 79, 466]] ![![-31, 1, -16, 5, 50]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 11, -111, 28, 296]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-35, 11, -111, 28, 296]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![8, 28, 34, 1, 0], ![8, 48, 12, 0, 1]] where
  M :=![![![-35, 11, -111, 28, 296], ![384, 161, 143, -81, -368], ![354, -183, 1244, -300, -3330], ![-1530, -582, -691, 344, 1790], ![234, 3, 394, -111, -1049]]]
  hmulB := by decide  
  f := ![![![11, 28, -27, 17, 108]], ![![18, 130, -107, 72, 422]], ![![-30, 522, -548, 327, 2106]], ![![-4, 315, -317, 193, 1224]], ![![8, 181, -170, 107, 661]]]
  g := ![![![-37, -211, -65, 28, 296], ![56, 283, 103, -81, -368], ![414, 2367, 724, -300, -3330], ![-262, -1354, -477, 344, 1790], ![134, 753, 236, -111, -1049]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [49, 70, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 7, 69], [51, 63, 2], [0, 1]]
 g := ![![[54, 34, 27], [56, 70, 50], [70, 54, 19], [20, 38], [32, 1], []], ![[45, 15, 46, 51], [17, 0, 35, 44], [39, 35, 0, 44], [65, 1], [30, 64], [29, 4]], ![[68, 55, 52, 45], [7, 44, 18, 32], [44, 5, 9, 40], [23, 48], [33, 49], [25, 4]]]
 h' := ![![[52, 7, 69], [25, 21, 58], [49, 66, 11], [50, 66, 27], [65, 54, 31], [0, 0, 1], [0, 1]], ![[51, 63, 2], [58, 25, 62], [57, 30, 64], [67, 60, 7], [46, 19, 70], [5, 64, 63], [52, 7, 69]], ![[0, 1], [35, 25, 22], [20, 46, 67], [27, 16, 37], [35, 69, 41], [27, 7, 7], [51, 63, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 15], []]
 b := ![[], [48, 28, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [49, 70, 39, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-239734601, -5470230264, 5499737480, -3352807452, -21051598258]
  a := ![537, -240, 776, -300, -2446]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2746415649, 15477254856, 5241047464, -3352807452, -21051598258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 2, -1, -8]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-1, -1, 2, -1, -8]] 
 ![![71, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 2, -1, -8], ![-6, -8, 2, -3, -10], ![24, -27, 43, -21, -156], ![-30, -41, 24, -20, -106], ![12, -6, 14, -6, -49]]]
  hmulB := by decide  
  f := ![![![-95, -27, -44, 19, 120]], ![![-72, -20, -36, 15, 98]], ![![-78, -21, -35, 15, 96]], ![![-25, -10, -2, 3, 6]], ![![-55, -15, -26, 11, 71]]]
  g := ![![![4, -1, 2, -1, -8], ![11, -8, 2, -3, -10], ![81, -27, 43, -21, -156], ![78, -41, 24, -20, -106], ![23, -6, 14, -6, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, -1, 0, 2]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-5, -1, -1, 0, 2]] 
 ![![71, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![-5, -1, -1, 0, 2], ![6, -5, 5, -3, -18], ![0, -15, 22, -12, -84], ![-12, -28, 19, -14, -76], ![0, -3, 6, -3, -23]]]
  hmulB := by decide  
  f := ![![![17, 20, -5, -3, 14]], ![![15, 16, -2, -3, 6]], ![![-1, 2, -1, 0, 2]], ![![2, 9, -11, 1, 30]], ![![16, 19, -4, -3, 11]]]
  g := ![![![-1, -1, -1, 0, 2], ![22, -5, 5, -3, -18], ![95, -15, 22, -12, -84], ![99, -28, 19, -14, -76], ![25, -3, 6, -3, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-35, 11, -111, 28, 296]] ![![-1, -1, 2, -1, -8]]
  ![![17, 20, -5, -3, 14]] where
 M := ![![![17, 20, -5, -3, 14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![17, 20, -5, -3, 14]] ![![-5, -1, -1, 0, 2]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2431367, 314975, 781007, -124288, -2098052]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![2431367, 314975, 781007, -124288, -2098052]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![2, 16, 5, 1, 0], ![17, 7, 26, 0, 1]] where
  M :=![![![2431367, 314975, 781007, -124288, -2098052], ![-4056972, 1561351, -2623405, 1224429, 8690852], ![4032834, 4514031, -5425676, 3149646, 22185510], ![3287634, 8693452, -4656627, 4023262, 19533794], ![1678584, 851565, -1384084, 734907, 5837891]]]
  hmulB := by decide  
  f := ![![![153559319, 38409528, 139732613, -48801433, -369722256]], ![![-230740974, -188050712, 246881451, -20015058, -674217202]], ![![-1662380562, -370846380, -1670295752, 560508831, 4426720062]], ![![-145657160, -55239687, -66621715, 32820974, 173247878]], ![![-585823241, -143449565, -543875590, 188382556, 1439551135]]]
  g := ![![![525299, 232739, 766463, -124288, -2098052], ![-2113018, -1080349, -3215174, 1224429, 8690852], ![-5197536, -2755875, -8191742, 3149646, 22185510], ![-4614156, -2635826, -7296597, 4023262, 19533794], ![-1356649, -709208, -2148545, 734907, 5837891]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [30, 42, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 51, 30], [38, 21, 43], [0, 1]]
 g := ![![[12, 44, 32], [12, 70], [18, 19], [14, 20, 32], [43, 1], []], ![[25, 29, 4, 47], [17, 3], [9, 4], [28, 44, 10, 66], [21, 3], [4, 24]], ![[22, 17, 72, 58], [18, 16], [49, 65], [68, 43, 7, 31], [19, 46], [64, 24]]]
 h' := ![![[5, 51, 30], [14, 36, 18], [3, 2, 17], [18, 45, 26], [24, 62, 55], [0, 0, 1], [0, 1]], ![[38, 21, 43], [17, 69, 71], [4, 27, 52], [36, 59, 71], [0, 38, 22], [51, 60, 21], [5, 51, 30]], ![[0, 1], [41, 41, 57], [17, 44, 4], [10, 42, 49], [71, 46, 69], [35, 13, 51], [38, 21, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 44], []]
 b := ![[], [1, 60, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [30, 42, 30, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19576, -1321680, 1383192, -826005, -5236749]
  a := ![38, -16, 56, -21, -173]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1241879, 665091, 1940667, -826005, -5236749]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153559319, 38409528, 139732613, -48801433, -369722256]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![153559319, 38409528, 139732613, -48801433, -369722256]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![31, 58, 1, 0, 0], ![9, 57, 0, 1, 0], ![56, 11, 0, 0, 1]] where
  M :=![![![153559319, 38409528, 139732613, -48801433, -369722256], ![-230740974, -188050712, 246881451, -20015058, -674217202], ![-1662380562, -370846380, -1670295752, 560508831, 4426720062], ![1063667076, 753727085, -741474877, 11230741, 2040414528], ![-538523586, -166419357, -378853096, 148426749, 997310009]]]
  hmulB := by decide  
  f := ![![![2431367, 314975, 781007, -124288, -2098052]], ![![-4056972, 1561351, -2623405, 1224429, 8690852]], ![![-2135605, 1436118, -1827013, 963200, 6318018]], ![![-2822979, 1377058, -2015913, 995851, 6794930]], ![![1276828, 488562, 184861, 99226, -219913]]]
  g := ![![![232404213, -16677473, 139732613, -48801433, -369722256], ![411674423, -81505854, 246881451, -20015058, -674217202], ![-2778412537, 217306619, -1670295752, 560508831, 4426720062], ![-1237190438, 283213122, -741474877, 11230741, 2040414528], ![-629853135, 32552403, -378853096, 148426749, 997310009]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [52, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 72], [0, 1]]
 g := ![![[21, 37], [64], [24], [61, 49], [9], [1]], ![[59, 36], [64], [24], [62, 24], [9], [1]]]
 h' := ![![[3, 72], [53, 57], [60, 8], [40, 43], [46, 7], [21, 3], [0, 1]], ![[0, 1], [5, 16], [11, 65], [23, 30], [67, 66], [30, 70], [3, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [33, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [52, 70, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24842, 200545, -260941, 136148, 921531]
  a := ![-232, 100, -337, 125, 1057]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-613243, -35098, -260941, 136148, 921531]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![2431367, 314975, 781007, -124288, -2098052]] ![![153559319, 38409528, 139732613, -48801433, -369722256]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5124213305, 1964750758, 2268666758, -1139299372, -5892741384]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![5124213305, 1964750758, 2268666758, -1139299372, -5892741384]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![73, 46, 1, 0, 0], ![13, 30, 0, 1, 0], ![40, 55, 0, 0, 1]] where
  M :=![![![5124213305, 1964750758, 2268666758, -1139299372, -5892741384], ![2829164544, -2850882299, 15047609650, -3447694074, -40387876048], ![-59105134812, -21304693974, -30926770445, 14113582284, 80779970364], ![-3901523340, 13229980392, -53343834850, 11413976407, 143431338004], ![-15407936628, -6865592190, -3464377108, 2739776670, 8681548397]]]
  hmulB := by decide  
  f := ![![![-45992785, 1371586, -20204810, 6190112, 60894640]], ![![71261904, -2662001, 16922482, -4903422, -40462576]], ![![-1424707, 184958, -8711067, 2948828, 32229276]], ![![18509033, -728936, 2021232, -485805, -1608772]], ![![26148548, -985819, 1649710, -268900, 2254973]]]
  g := ![![![1139646673, 3239061230, 2268666758, -1139299372, -5892741384], ![7147958544, 20629406059, 15047609650, -3447694074, -40387876048], ![-15394003501, -43860494836, -30926770445, 14113582284, 80779970364], ![-25258693579, -72963246822, -53343834850, 11413976407, 143431338004], ![-1840347346, -5154211483, -3464377108, 2739776670, 8681548397]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [1, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 78], [0, 1]]
 g := ![![[63, 1], [63, 1], [16, 4], [12, 40], [19], [1]], ![[0, 78], [0, 78], [1, 75], [20, 39], [19], [1]]]
 h' := ![![[16, 78], [16, 78], [63, 1], [67, 2], [61, 35], [78, 16], [0, 1]], ![[0, 1], [0, 1], [0, 78], [20, 77], [68, 44], [18, 63], [16, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [59, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [1, 63, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10277, 18530, -19403, 8919, 66006]
  a := ![97, -38, 146, -47, -442]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16829, -37808, -19403, 8919, 66006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1823, 613, -5406, 1345, 14476]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-1823, 613, -5406, 1345, 14476]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![38, 61, 1, 0, 0], ![70, 10, 0, 1, 0], ![52, 78, 0, 0, 1]] where
  M :=![![![-1823, 613, -5406, 1345, 14476], ![19218, 7592, 7726, -4113, -19994], ![14052, -9573, 58661, -13839, -157320], ![-74286, -27607, -35960, 17144, 93694], ![10404, -78, 18862, -5226, -50339]]]
  hmulB := by decide  
  f := ![![![583, -1833, 1856, -1115, -6980]], ![![-870, -7222, 7332, -4467, -28610]], ![![-460, -6865, 6903, -4216, -26826]], ![![412, -3099, 3134, -1896, -11974]], ![![-500, -8436, 8538, -5198, -33151]]]
  g := ![![![-8143, -10281, -5406, 1345, 14476], ![13332, 14392, 7726, -4113, -19994], ![87776, 111664, 58661, -13839, -157320], ![-60506, -67261, -35960, 17144, 93694], ![28824, 35798, 18862, -5226, -50339]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [10, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 78], [0, 1]]
 g := ![![[15, 8], [33, 65], [22, 19], [7, 32], [64], [1]], ![[0, 71], [0, 14], [16, 60], [26, 47], [64], [1]]]
 h' := ![![[8, 78], [65, 61], [17, 67], [9, 63], [13, 36], [69, 8], [0, 1]], ![[0, 1], [0, 18], [0, 12], [39, 16], [64, 43], [54, 71], [8, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [53, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [10, 71, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1198, 3010, 2664, -1528, -5412]
  a := ![-36, 14, -52, 8, 164]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3650, 3518, 2664, -1528, -5412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![228095, 98935174, -346374631, 70742817, 932403470]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![228095, 98935174, -346374631, 70742817, 932403470]] 
 ![![79, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![228095, 98935174, -346374631, 70742817, 932403470], ![1523839704, 495427814, 986089525, -402438540, -2590720236], ![-528266988, -1293230076, 3589107686, -663678285, -9683478156], ![-5701408446, -1724671661, -4141450283, 1598072831, 10909894678], ![370134978, -190210089, 1328032146, -320161269, -3559411441]]]
  hmulB := by decide  
  f := ![![![-18411451, -3455029, -4727823, 248490, 11315602]], ![![-11512785, -2441500, -2751094, 9189, 6273816]], ![![-1769802, -947919, 419480, -439050, -2260596]], ![![-13423628, -3641442, -2578577, -419068, 4864660]], ![![-17162377, -3334414, -4170087, 120711, 9646023]]]
  g := ![![![-949294545, 98935174, -346374631, 70742817, 932403470], ![2303792652, 495427814, 986089525, -402438540, -2590720236], ![9974072280, -1293230076, 3589107686, -663678285, -9683478156], ![-9858339773, -1724671661, -4141450283, 1598072831, 10909894678], ![3542642062, -190210089, 1328032146, -320161269, -3559411441]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![5124213305, 1964750758, 2268666758, -1139299372, -5892741384]] ![![-1823, 613, -5406, 1345, 14476]]
  ![![83622356284901, 28251855227123, 50380745352628, -21321714197175, -132122576051824]] where
 M := ![![![83622356284901, 28251855227123, 50380745352628, -21321714197175, -132122576051824]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![83622356284901, 28251855227123, 50380745352628, -21321714197175, -132122576051824]] ![![228095, 98935174, -346374631, 70742817, 932403470]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![89116502574205429380901, 19020055294174740577179, 92555907158058794155073, -30663681551328431345052, -245422772409345306964792]]]
 hmul := by decide  
 g := ![![![![1128056994610195308619, 240760193597148614901, 1171593761494415115887, -388147867738334573988, -3106617372270193759048]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2161, 149, 1148, -299, -3582]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![2161, 149, 1148, -299, -3582]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![56, 28, 43, 1, 0], ![27, 66, 40, 0, 1]] where
  M :=![![![2161, 149, 1148, -299, -3582], ![-5364, 68, -2524, 753, 7720], ![9606, -93, 2897, -795, -7734], ![-2964, 1347, -610, 512, 1472], ![4362, -144, 1390, -414, -3803]]]
  hmulB := by decide  
  f := ![![![419, 415, -706, 89, 1918]], ![![4152, 1042, 3766, -1317, -9964]], ![![-6186, -5067, 6709, -555, -18318]], ![![-1702, -2034, 4089, -611, -11078]], ![![453, -1491, 6036, -1293, -16229]]]
  g := ![![![1393, 2951, 1895, -299, -3582], ![-3084, -6392, -4141, 753, 7720], ![3168, 6417, 4174, -795, -7734], ![-860, -1327, -982, 512, 1472], ![1569, 3162, 2064, -414, -3803]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [26, 76, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 82, 45], [76, 0, 38], [0, 1]]
 g := ![![[8, 37, 3], [44, 32, 28], [25, 17], [7, 9], [1, 34, 1], []], ![[58, 32, 41, 6], [79, 69, 60, 22], [16, 68], [60, 23], [78, 24], [36, 33]], ![[22, 31, 62, 12], [40, 47, 29, 28], [66, 17], [68, 23], [36, 62, 49, 38], [43, 33]]]
 h' := ![![[41, 82, 45], [18, 44, 70], [30, 4, 51], [79, 18, 10], [57, 36, 80], [0, 0, 1], [0, 1]], ![[76, 0, 38], [22, 19, 71], [9, 17, 14], [50, 74, 63], [45, 36, 43], [81, 59], [41, 82, 45]], ![[0, 1], [78, 20, 25], [14, 62, 18], [53, 74, 10], [24, 11, 43], [10, 24, 82], [76, 0, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 19], []]
 b := ![[], [80, 33, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [26, 76, 49, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![275056, 3499223, -3445800, 2084931, 13204450]
  a := ![-10, 7, -8, 12, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5698810, -11161115, -7485251, 2084931, 13204450]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-419, -415, 706, -89, -1918]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-419, -415, 706, -89, -1918]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![40, 37, 1, 0, 0], ![60, 55, 0, 1, 0], ![18, 53, 0, 0, 1]] where
  M :=![![![-419, -415, 706, -89, -1918], ![-4152, -1042, -3766, 1317, 9964], ![6186, 5067, -6709, 555, 18318], ![14988, 3357, 15012, -5044, -39784], ![306, 1050, -3134, 600, 8449]]]
  hmulB := by decide  
  f := ![![![-2161, -149, -1148, 299, 3582]], ![![5364, -68, 2524, -753, -7720]], ![![1234, -101, 537, -182, -1622]], ![![2028, -169, 850, -289, -2544]], ![![2904, -74, 1346, -411, -4107]]]
  g := ![![![135, 964, 706, -89, -1918], ![-1348, -5569, -3766, 1317, 9964], ![-1066, -9013, -6709, 555, 18318], ![5220, 22095, 15012, -5044, -39784], ![-752, -4383, -3134, 600, 8449]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [24, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 82], [0, 1]]
 g := ![![[44, 36], [48, 29], [51], [48], [24, 31], [1]], ![[42, 47], [51, 54], [51], [48], [73, 52], [1]]]
 h' := ![![[23, 82], [10, 77], [1, 64], [35, 47], [5, 52], [59, 23], [0, 1]], ![[0, 1], [38, 6], [62, 19], [37, 36], [39, 31], [7, 60], [23, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [52, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [24, 60, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![586, 1421, -851, 726, 4041]
  a := ![16, -8, 23, -11, -73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-984, -2665, -851, 726, 4041]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![2161, 149, 1148, -299, -3582]] ![![-419, -415, 706, -89, -1918]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11431, -2631, -385, -350, 4884]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![11431, -2631, -385, -350, 4884]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![57, 17, 46, 1, 0], ![68, 30, 52, 0, 1]] where
  M :=![![![11431, -2631, -385, -350, 4884], ![20952, 8981, 21471, -4305, -72656], ![-140478, -9183, -92752, 25668, 300894], ![146886, 13066, 66821, -15748, -201090], ![-65556, -5355, -41804, 11187, 134743]]]
  hmulB := by decide  
  f := ![![![11975, -11338, 61137, -14071, -164072]], ![![-238938, -86522, -123637, 56772, 322826]], ![![-53418, 158466, -650888, 140037, 1749870]], ![![-55359, 61587, -314781, 71618, 845034]], ![![-103678, 54923, -377754, 90857, 1012529]]]
  g := ![![![-3379, -1609, -2677, -350, 4884], ![58505, 25414, 44917, -4305, -72656], ![-247914, -106431, -190112, 25668, 300894], ![165378, 70938, 126381, -15748, -201090], ![-110851, -47616, -84978, 11187, 134743]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [11, 83, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 35, 30], [28, 53, 59], [0, 1]]
 g := ![![[70, 55, 78], [46, 71], [27, 69], [24, 77, 79], [16, 59, 1], []], ![[53, 2, 43, 38], [37, 69], [82, 1], [65, 79, 13, 30], [58, 6, 16, 76], [20, 10]], ![[35, 13, 64, 19], [2, 55], [72, 73], [55, 50, 28, 35], [21, 16, 30, 7], [80, 10]]]
 h' := ![![[31, 35, 30], [24, 22, 16], [68, 15, 31], [3, 13, 43], [2, 70, 41], [0, 0, 1], [0, 1]], ![[28, 53, 59], [13, 50, 84], [8, 20, 46], [51, 33, 88], [68, 71, 1], [29, 44, 53], [31, 35, 30]], ![[0, 1], [83, 17, 78], [4, 54, 12], [66, 43, 47], [73, 37, 47], [82, 45, 35], [28, 53, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 24], []]
 b := ![[], [28, 40, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [11, 83, 30, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31819, 709429, -643696, 396837, 2448956]
  a := ![-21, 9, -23, 8, 96]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2125624, -893320, -1643190, 396837, 2448956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52423321, -46934784, 70848781, -7562841, -192906814]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-52423321, -46934784, 70848781, -7562841, -192906814]] 
 ![![89, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-52423321, -46934784, 70848781, -7562841, -192906814], ![-442589304, -105363208, -421458519, 144480774, 1116008364], ![747371160, 568776114, -658319014, 35951409, 1803348192], ![1587639738, 333010341, 1669377549, -550464787, -4427372730], ![56963622, 121792251, -325122954, 58918587, 877568495]]]
  hmulB := by decide  
  f := ![![![13459027, 1550571, 6882847, -1601436, -21236446]], ![![8530327, 1053176, 4350202, -991563, -13406068]], ![![12701717, 1474842, 6259135, -1428684, -19153382]], ![![11535606, 1593810, 5826597, -1275418, -17898936]], ![![1249074, 120615, 557736, -127779, -1669579]]]
  g := ![![![-12730138, -46934784, 70848781, -7562841, -192906814], ![237118117, -105363208, -421458519, 144480774, 1116008364], ![62612174, 568776114, -658319014, 35951409, 1803348192], ![-903823674, 333010341, 1669377549, -550464787, -4427372730], ![97695207, 121792251, -325122954, 58918587, 877568495]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![301, 172, 112, 16, -302]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![301, 172, 112, 16, -302]] 
 ![![89, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![87, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![301, 172, 112, 16, -302], ![-1194, 413, -1166, 480, 4030], ![3450, 2166, -457, 822, 3090], ![-1842, 3068, -3586, 2009, 13198], ![1548, 528, 226, 102, -281]]]
  hmulB := by decide  
  f := ![![![1421, 14988, -49996, 10028, 134642]], ![![3628, 12593, -37658, 7216, 101522]], ![![294, 11958, -41389, 8418, 111426]], ![![-7983, 11860, -55834, 12461, 149964]], ![![1870, 13476, -43894, 8722, 118235]]]
  g := ![![![25, 172, 112, 16, -302], ![-3420, 413, -1166, 480, 4030], ![-4884, 2166, -457, 822, 3090], ![-13173, 3068, -3586, 2009, 13198], ![-452, 528, 226, 102, -281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![11431, -2631, -385, -350, 4884]] ![![-52423321, -46934784, 70848781, -7562841, -192906814]]
  ![![1421, 14988, -49996, 10028, 134642]] where
 M := ![![![1421, 14988, -49996, 10028, 134642]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![1421, 14988, -49996, 10028, 134642]] ![![301, 172, 112, 16, -302]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42707, -16131, -19763, 9670, 51414]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-42707, -16131, -19763, 9670, 51414]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![66, 17, 79, 41, 1]] where
  M :=![![![-42707, -16131, -19763, 9670, 51414], ![-19818, 24983, -122979, 27741, 330214], ![491304, 174369, 266618, -119268, -697164], ![18444, -114524, 434371, -91186, -1168500], ![129330, 56751, 32152, -23625, -81143]]]
  hmulB := by decide  
  f := ![![![481, 214, 595, -131, -2050]], ![![-3792, -436, -2399, 606, 7708]], ![![12216, 450, 6326, -1743, -19680]], ![![-9222, 5, -3843, 1097, 11398]], ![![5772, 440, 3542, -947, -11347]]]
  g := ![![![-35423, -9177, -42077, -21632, 51414], ![-224886, -57615, -270205, -139289, 330214], ![479424, 123981, 570542, 293448, -697164], ![795252, 203608, 956143, 492962, -1168500], ![56544, 14806, 66417, 34054, -81143]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [63, 92, 80, 82, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 60, 51, 19], [64, 15, 5, 7], [52, 21, 41, 71], [0, 1]]
 g := ![![[17, 44, 46, 47], [4, 1, 36], [7, 10, 65], [80, 18, 3], [48, 15, 1], []], ![[49, 70, 80, 37, 79, 77], [19, 49, 53], [82, 6, 62], [37, 44, 4], [17, 37, 72], [35, 91, 84, 63, 8, 69]], ![[7, 56, 60, 39, 20, 74], [36, 22, 12], [67, 11, 88], [67, 65, 95], [96, 95, 62], [63, 14, 96, 52, 60, 52]], ![[89, 1, 73, 65, 10, 23], [25, 14, 75], [81, 82, 33], [53, 69, 81], [26, 33, 8], [23, 11, 23, 83, 25, 78]]]
 h' := ![![[93, 60, 51, 19], [15, 49, 17, 12], [48, 5, 44, 6], [2, 53, 72, 29], [80, 71, 52, 10], [0, 0, 0, 1], [0, 1]], ![[64, 15, 5, 7], [62, 85, 8, 27], [80, 55, 70, 21], [28, 16, 41, 81], [82, 7, 4, 95], [59, 38, 14, 84], [93, 60, 51, 19]], ![[52, 21, 41, 71], [52, 26, 61, 39], [63, 96, 30, 20], [4, 81, 79, 66], [32, 10, 40, 80], [58, 35, 17, 81], [64, 15, 5, 7]], ![[0, 1], [27, 34, 11, 19], [27, 38, 50, 50], [38, 44, 2, 18], [46, 9, 1, 9], [61, 24, 66, 28], [52, 21, 41, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [87, 72, 60], []]
 b := ![[], [], [72, 49, 67, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [63, 92, 80, 82, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![292158681, 2184886113, -2174617123, 1251238218, 8199555027]
  a := ![-70, 28, -105, 35, 319]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5576066733, -1414510818, -6700406848, -3452891937, 8199555027]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-481, -214, -595, 131, 2050]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-481, -214, -595, 131, 2050]] 
 ![![97, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-481, -214, -595, 131, 2050], ![3792, 436, 2399, -606, -7708], ![-12216, -450, -6326, 1743, 19680], ![9222, -5, 3843, -1097, -11398], ![-5640, -213, -2896, 795, 8993]]]
  hmulB := by decide  
  f := ![![![42707, 16131, 19763, -9670, -51414]], ![![18696, 6727, 9825, -4473, -25666]], ![![29717, 11340, 13347, -6646, -34686]], ![![25346, 10826, 7339, -4842, -18696]], ![![14957, 5568, 7207, -3445, -18775]]]
  g := ![![![-288, -214, -595, 131, 2050], ![1199, 436, 2399, -606, -7708], ![-3328, -450, -6326, 1743, 19680], ![1971, -5, 3843, -1097, -11398], ![-1513, -213, -2896, 795, 8993]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-42707, -16131, -19763, 9670, 51414]] ![![-481, -214, -595, 131, 2050]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1565, -192043, 170569, -110056, -661180]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![1565, -192043, 170569, -110056, -661180]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![43, 29, 50, 1, 0], ![95, 54, 9, 0, 1]] where
  M :=![![![1565, -192043, 170569, -110056, -661180], ![-2532, -768827, 795929, -478797, -3073972], ![-603570, -3354111, 2936776, -1921386, -11595606], ![-67290, -4684424, 4578831, -2827382, -17731066], ![-218844, -808965, 659072, -448419, -2635987]]]
  hmulB := by decide  
  f := ![![![3548089, 1106652, 2460375, -970619, -6474680]], ![![-1952898, -3246244, 7889325, -1354446, -21318638]], ![![-39575886, -11434020, -30632116, 11477961, 80803170]], ![![-18524011, -5986793, -12112169, 4917666, 31829982]], ![![-1348433, -1755819, 3745163, -587405, -10137843]]]
  g := ![![![668773, 383201, 115089, -110056, -661180], ![3095179, 1773374, 518827, -478797, -3073972], ![11718798, 6718107, 2013530, -1921386, -11595606], ![17880806, 10245418, 3025025, -2827382, -17731066], ![2668138, 1530084, 463405, -448419, -2635987]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [13, 59, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 44, 91], [11, 56, 10], [0, 1]]
 g := ![![[41, 61, 76], [91, 17], [71, 52, 68], [52, 14], [22, 87], [1]], ![[77, 3, 55, 62], [33, 36], [93, 43, 72, 15], [63, 84], [99, 47], [29, 78, 1, 10]], ![[63, 17, 41, 8], [80, 76], [70, 86, 23, 61], [78, 79], [27, 19], [56, 67, 2, 91]]]
 h' := ![![[73, 44, 91], [23, 40, 51], [87, 37, 57], [85, 39, 88], [85, 14, 32], [88, 42, 84], [0, 1]], ![[11, 56, 10], [6, 36, 32], [58, 22, 95], [9, 80, 94], [90, 67, 36], [93, 66, 42], [73, 44, 91]], ![[0, 1], [1, 25, 18], [43, 42, 50], [2, 83, 20], [62, 20, 33], [98, 94, 76], [11, 56, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 3], []]
 b := ![[], [13, 98, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [13, 59, 17, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20055, 1079733, -1126265, 691794, 4297276]
  a := ![-28, 12, -41, 17, 128]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4336717, -2485497, -736549, 691794, 4297276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 9, 13, -6, -34]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![25, 9, 13, -6, -34]] 
 ![![101, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![25, 9, 13, -6, -34], ![6, -17, 69, -15, -186], ![-288, -99, -170, 72, 444], ![12, 72, -237, 46, 636], ![-78, -33, -24, 15, 61]]]
  hmulB := by decide  
  f := ![![![785, 102, 535, -135, -1738]], ![![431, 58, 298, -75, -970]], ![![486, 54, 316, -81, -1020]], ![![343, 51, 248, -62, -812]], ![![147, 15, 93, -24, -299]]]
  g := ![![![-4, 9, 13, -6, -34], ![8, -17, 69, -15, -186], ![45, -99, -170, 72, 444], ![-32, 72, -237, 46, 636], ![15, -33, -24, 15, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7279, 29, -13107, 3638, 34978]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-7279, 29, -13107, 3638, 34978]] 
 ![![101, 0, 0, 0, 0], ![94, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![-7279, 29, -13107, 3638, 34978], ![39450, 18187, 6737, -6579, -16486], ![68964, -6603, 146362, -39000, -391104], ![-157104, -68012, -42305, 29362, 107312], ![32466, 4335, 42812, -13029, -113887]]]
  hmulB := by decide  
  f := ![![![-90527, 1170, -37369, 10957, 110682]], ![![-82918, 952, -34409, 10064, 102044]], ![![-47104, 1002, -18670, 5549, 54732]], ![![-50100, 245, -21269, 6151, 63414]], ![![-71005, 1107, -28959, 8528, 85517]]]
  g := ![![![-22655, 29, -13107, 3638, 34978], ![-3592, 18187, 6737, -6579, -16486], ![258238, -6603, 146362, -39000, -391104], ![-16112, -68012, -42305, 29362, 107312], ![70291, 4335, 42812, -13029, -113887]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![1565, -192043, 170569, -110056, -661180]] ![![25, 9, 13, -6, -34]]
  ![![14363, 287393, -275760, 171947, 1071828]] where
 M := ![![![14363, 287393, -275760, 171947, 1071828]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![14363, 287393, -275760, 171947, 1071828]] ![![-7279, 29, -13107, 3638, 34978]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-707, -8686, 8181, -5151, -31916]]]
 hmul := by decide  
 g := ![![![![-7, -86, 81, -51, -316]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-888943, -1088753, -544902, -134799, 1628838]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-888943, -1088753, -544902, -134799, 1628838]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![39, 88, 8, 96, 1]] where
  M :=![![![-888943, -1088753, -544902, -134799, 1628838], ![7312896, -1832536, 7437334, -2847897, -25713060], ![-25877034, -12622383, -2078497, -3319071, -2110014], ![17804412, -16370177, 23554164, -12035710, -84391232], ![-11739534, -3252294, -3348246, -17604, 8347001]]]
  hmulB := by decide  
  f := ![![![-20880433, -14490019, 13482668, -1239, -37166382]], ![![-111476844, -20889106, -125955712, 40436853, 334395840]], ![![275324166, 171581127, -109496617, -13935459, 306259386]], ![![389872140, 59258651, 488872226, -151302994, -1299680704]], ![![281985249, 45617093, 343926954, -107459529, -914017453]]]
  g := ![![![-625375, -1402199, -131802, -1519449, 1628838], ![9807012, 21950648, 2069338, 23937921, -25713060], ![547704, 1680183, 143705, 1934391, -2110014], ![32126820, 71942313, 6783340, 78539054, -84391232], ![-3274491, -7162994, -680818, -7779900, 8347001]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [24, 85, 61, 85, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 65, 80, 38], [81, 23, 26, 91], [49, 14, 100, 77], [0, 1]]
 g := ![![[39, 60, 60, 93], [19, 101, 58, 52], [48, 1, 94, 55], [39, 84, 32], [57, 18, 1], []], ![[74, 77, 100, 68, 46, 56], [90, 21, 34, 19, 30, 15], [67, 102, 90, 85, 33, 9], [87, 92, 29], [54, 19, 55], [80, 47, 91, 23, 97, 76]], ![[27, 85, 91, 9, 38, 76], [101, 14, 40, 101, 40, 29], [52, 78, 23, 62, 79, 60], [24, 31, 16], [86, 19, 18], [32, 7, 57, 82, 7, 23]], ![[5, 31, 53, 10, 67, 88], [41, 69, 4, 53, 5, 42], [14, 94, 68, 13, 82, 74], [81, 100, 17], [39, 60, 76], [88, 0, 91, 9, 41, 37]]]
 h' := ![![[94, 65, 80, 38], [59, 30, 38, 14], [84, 80, 99, 84], [8, 78, 73, 63], [74, 79, 16, 49], [0, 0, 0, 1], [0, 1]], ![[81, 23, 26, 91], [72, 33, 2, 72], [24, 67, 21, 39], [70, 28, 69, 58], [60, 100, 29, 21], [29, 39, 87, 40], [94, 65, 80, 38]], ![[49, 14, 100, 77], [73, 42, 40, 53], [91, 94, 38, 35], [0, 19, 75, 43], [79, 21, 58, 4], [17, 20, 56, 92], [81, 23, 26, 91]], ![[0, 1], [40, 101, 23, 67], [34, 68, 48, 48], [77, 81, 92, 42], [8, 6, 0, 29], [74, 44, 63, 73], [49, 14, 100, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [48, 16, 45], []]
 b := ![[], [], [57, 82, 75, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [24, 85, 61, 85, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5473717986, 1804981138, -15137469069, 3971080705, 40914506298]
  a := ![-85, 36, -148, 47, 388]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15545043336, -34938558962, -3324791451, -38095354601, 40914506298]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20880433, -14490019, 13482668, -1239, -37166382]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-20880433, -14490019, 13482668, -1239, -37166382]] 
 ![![103, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![99, 0, 0, 0, 1]] where
  M :=![![![-20880433, -14490019, 13482668, -1239, -37166382], ![-111476844, -20889106, -125955712, 40436853, 334395840], ![275324166, 171581127, -109496617, -13935459, 306259386], ![389872140, 59258651, 488872226, -151302994, -1299680704], ![38461038, 40433136, -73005894, 9844866, 198129815]]]
  hmulB := by decide  
  f := ![![![-888943, -1088753, -544902, -134799, 1628838]], ![![-515876, -736580, -287534, -116643, 825708]], ![![-346169, -238822, -78373, -46620, 153468]], ![![-638410, -1152553, -268608, -239872, 667180]], ![![-968397, -1078047, -556248, -129735, 1646621]]]
  g := ![![![43647765, -14490019, 13482668, -1239, -37166382], ![-332152982, -20889106, -125955712, 40436853, 334395840], ![-380558017, 171581127, -109496617, -13935459, 306259386], ![1299743306, 59258651, 488872226, -151302994, -1299680704], ![-217943655, 40433136, -73005894, 9844866, 198129815]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-888943, -1088753, -544902, -134799, 1628838]] ![![-20880433, -14490019, 13482668, -1239, -37166382]]
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


lemma PB314I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB314I2 : PrimesBelowBoundCertificateInterval O 61 103 314 where
  m := 9
  g := ![2, 3, 2, 3, 2, 3, 2, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB314I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
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
    · exact ![20151121, 67]
    · exact ![357911, 71, 71]
    · exact ![389017, 5329]
    · exact ![6241, 6241, 79]
    · exact ![571787, 6889]
    · exact ![704969, 89, 89]
    · exact ![88529281, 97]
    · exact ![1030301, 101, 101]
    · exact ![112550881, 103]
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
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I71N1, I71N2, I79N2, I89N1, I89N2, I97N1, I101N1, I101N2, I103N1]
  Il := ![[I67N1], [I71N1, I71N2], [], [I79N2], [], [I89N1, I89N2], [I97N1], [I101N1, I101N2], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
