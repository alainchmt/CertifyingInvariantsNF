
import IdealArithmetic.Examples.NF5_3_1687500000_3.RI5_3_1687500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![612, -311, -81, -123, 263]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![612, -311, -81, -123, 263]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![39, 59, 1, 0, 0], ![22, 55, 0, 1, 0], ![58, 18, 0, 0, 1]] where
  M :=![![![612, -311, -81, -123, 263], ![94, 22, 15, 24, -58], ![-152, 215, 72, 114, -256], ![-213, 191, 53, 84, -189], ![-472, 340, 98, 152, -335]]]
  hmulB := by decide  
  f := ![![![-430, 307, 165, 291, -681]], ![![-1398, 998, 535, 948, -2214]], ![![-1548, 1106, 592, 1049, -2451]], ![![-1387, 989, 532, 940, -2197]], ![![-824, 588, 316, 558, -1305]]]
  g := ![![![-131, 97, -81, -123, 263], ![35, -17, 15, 24, -58], ![140, -85, 72, 114, -256], ![102, -62, 53, 84, -189], ![176, -116, 98, 152, -335]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [40, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 66], [0, 1]]
 g := ![![[20, 62], [55, 22], [19], [10], [16], [1]], ![[0, 5], [9, 45], [19], [10], [16], [1]]]
 h' := ![![[4, 66], [11, 14], [65, 25], [17, 32], [22, 12], [27, 4], [0, 1]], ![[0, 1], [0, 53], [31, 42], [11, 35], [3, 55], [43, 63], [4, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [13, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [40, 63, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![300523, -300349, -6517, -316701, 476569]
  a := ![-189, -11, 173, 177, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-300282, 133201, -6517, -316701, 476569]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -60, -20, -32, 72]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![55, -60, -20, -32, 72]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![55, 21, 1, 0, 0], ![59, 42, 0, 1, 0], ![19, 46, 0, 0, 1]] where
  M :=![![![55, -60, -20, -32, 72], ![96, -101, -36, -56, 128], ![208, -180, -93, -136, 304], ![136, -180, -4, -81, 168], ![128, -136, -32, -80, 175]]]
  hmulB := by decide  
  f := ![![![5525, -3244, -900, -1376, 2984]], ![![1888, -1111, -308, -472, 1024]], ![![5137, -3017, -837, -1280, 2776]], ![![6037, -3546, -984, -1505, 3264]], ![![2821, -1658, -460, -704, 1527]]]
  g := ![![![25, -24, -20, -32, 72], ![44, -43, -36, -56, 128], ![113, -97, -93, -136, 304], ![29, -66, -4, -81, 168], ![49, -62, -32, -80, 175]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [20, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 66], [0, 1]]
 g := ![![[20, 64], [33, 55], [1], [25], [4], [1]], ![[14, 3], [9, 12], [1], [25], [4], [1]]]
 h' := ![![[2, 66], [10, 8], [29, 16], [60, 66], [52, 62], [47, 2], [0, 1]], ![[0, 1], [26, 59], [61, 51], [58, 1], [42, 5], [51, 65], [2, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [37, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [20, 65, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3667876, -1162858, 4142960, 4027642, -8145406]
  a := ![171, -54, -156, -226, 350]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4692520, 1751682, 4142960, 4027642, -8145406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, -9, -7, -13, 31]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![10, -9, -7, -13, 31]] 
 ![![67, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![10, -9, -7, -13, 31], ![74, -54, -29, -52, 122], ![256, -181, -100, -174, 408], ![389, -273, -151, -266, 617], ![304, -214, -116, -204, 475]]]
  hmulB := by decide  
  f := ![![![-3892, 4357, 1435, 2229, -4993]], ![![-3230, 3616, 1191, 1850, -4144]], ![![-2008, 2249, 740, 1150, -2576]], ![![-2803, 3138, 1034, 1605, -3596]], ![![-1060, 1187, 391, 607, -1360]]]
  g := ![![![12, -9, -7, -13, 31], ![64, -54, -29, -52, 122], ![216, -181, -100, -174, 408], ![328, -273, -151, -266, 617], ![255, -214, -116, -204, 475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![612, -311, -81, -123, 263]] ![![55, -60, -20, -32, 72]]
  ![![3892, -4357, -1435, -2229, 4993]] where
 M := ![![![3892, -4357, -1435, -2229, 4993]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![3892, -4357, -1435, -2229, 4993]] ![![10, -9, -7, -13, 31]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2528, 2581, -4395, -2689, 6421]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![2528, 2581, -4395, -2689, 6421]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![22, 26, 30, 69, 1]] where
  M :=![![![2528, 2581, -4395, -2689, 6421], ![15482, -13666, -1705, -16808, 25586], ![-194216, -45425, 206884, 208362, -422048], ![147381, 432553, -497511, -153520, 505813], ![21536, 166122, -160732, -21244, 121879]]]
  hmulB := by decide  
  f := ![![![6154, -8025, -2709, -4219, 9489]], ![![12582, -14482, -4797, -7460, 16726]], ![![21200, -23861, -7884, -12262, 27480]], ![![11007, -12103, -4003, -6234, 13971]], ![![26333, -29809, -9875, -15368, 34454]]]
  g := ![![![-1954, -2315, -2775, -6278, 6421], ![-7710, -9562, -10835, -25102, 25586], ![128040, 153913, 181244, 413094, -422048], ![-154655, -179135, -220731, -493727, 505813], ![-37462, -42292, -53762, -118745, 121879]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [32, 4, 14, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 52, 8, 38], [63, 45, 10, 40], [20, 44, 53, 64], [0, 1]]
 g := ![![[68, 64, 15, 49], [58, 24, 41, 54], [2, 49, 16, 16], [28, 59, 20], [1], []], ![[4, 33, 6, 43, 25, 29], [65, 4, 1, 52, 10, 24], [14, 13, 53, 30, 60, 6], [3, 35, 8], [35, 8, 15], [31, 5, 24]], ![[2, 39, 42, 22, 25, 15], [43, 1, 48, 3, 25, 6], [33, 40, 31, 69, 37, 15], [60, 66, 18], [26, 38, 10], [16, 5, 38]], ![[37, 18, 61, 1, 28, 45], [29, 58, 48, 61, 70, 18], [65, 44, 46, 27, 56, 2], [44, 48, 57], [47, 32, 2], [25, 6, 49]]]
 h' := ![![[25, 52, 8, 38], [61, 43, 44, 7], [7, 40, 29, 14], [57, 31, 70, 4], [39, 67, 57, 37], [0, 0, 1], [0, 1]], ![[63, 45, 10, 40], [27, 58, 70, 18], [65, 27, 62, 31], [15, 59, 53, 20], [18, 39, 70, 24], [59, 44, 36, 21], [25, 52, 8, 38]], ![[20, 44, 53, 64], [66, 51, 32, 13], [50, 52, 62, 66], [46, 56, 23, 13], [7, 30, 32, 35], [49, 50, 50, 62], [63, 45, 10, 40]], ![[0, 1], [20, 61, 67, 33], [27, 23, 60, 31], [20, 67, 67, 34], [24, 6, 54, 46], [26, 48, 55, 59], [20, 44, 53, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 7, 29], []]
 b := ![[], [], [62, 14, 61, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [32, 4, 14, 34, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-102759382057, -40129635192, 123213116661, 110111263778, -230826112998]
  a := ![-62, -6, 57, 55, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![70076269069, 83962666236, 99267556431, 225874831840, -230826112998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6154, -8025, -2709, -4219, 9489]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![6154, -8025, -2709, -4219, 9489]] 
 ![![71, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![6154, -8025, -2709, -4219, 9489], ![12582, -14482, -4797, -7460, 16726], ![21200, -23861, -7884, -12262, 27480], ![11007, -12103, -4003, -6234, 13971], ![11640, -12420, -4078, -6344, 14201]]]
  hmulB := by decide  
  f := ![![![2528, 2581, -4395, -2689, 6421]], ![![2390, 2025, -3800, -2547, 5877]], ![![-1240, 887, 314, 1344, -2146]], ![![2147, 6165, -7131, -2238, 7305]], ![![2048, 4121, -5297, -2155, 6148]]]
  g := ![![![2154, -8025, -2709, -4219, 9489], ![4124, -14482, -4797, -7460, 16726], ![6843, -23861, -7884, -12262, 27480], ![3455, -12103, -4003, -6234, 13971], ![3625, -12420, -4078, -6344, 14201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![2528, 2581, -4395, -2689, 6421]] ![![6154, -8025, -2709, -4219, 9489]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -15, -19, -16, 48]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![33, -15, -19, -16, 48]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![62, 15, 37, 1, 0], ![32, 64, 53, 0, 1]] where
  M :=![![![33, -15, -19, -16, 48], ![288, -66, -207, -262, 544], ![-124, -987, 904, 274, -772], ![-2110, 1083, 829, 2503, -3930], ![-752, 154, 464, 980, -1539]]]
  hmulB := by decide  
  f := ![![![-60907, 68343, 22509, 34976, -78348]], ![![-97968, 109902, 36195, 56242, -125984]], ![![-157516, 176695, 58192, 90422, -202548]], ![![-152760, 171378, 56442, 87703, -196458]], ![![-228004, 255779, 84238, 130894, -293207]]]
  g := ![![![-7, -39, -27, -16, 48], ![-12, -424, -265, -262, 544], ![104, 607, 434, 274, -772], ![-432, 2946, 1596, 2503, -3930], ![-168, 1150, 627, 980, -1539]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [43, 51, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 35, 15], [56, 37, 58], [0, 1]]
 g := ![![[11, 8, 41], [15, 61], [70, 38], [15, 57, 41], [21, 1], []], ![[2, 21, 49, 39], [1, 69], [14, 65], [43, 65, 28, 28], [10, 55], [8, 6]], ![[32, 23, 50, 53], [69, 35], [66, 25], [62, 71, 46, 62], [25, 57], [38, 6]]]
 h' := ![![[38, 35, 15], [8, 72, 25], [54, 5, 34], [12, 68, 29], [46, 54, 25], [0, 0, 1], [0, 1]], ![[56, 37, 58], [22, 29, 34], [49, 8, 19], [40, 54, 49], [33, 56, 56], [5, 23, 37], [38, 35, 15]], ![[0, 1], [53, 45, 14], [10, 60, 20], [1, 24, 68], [32, 36, 65], [42, 50, 35], [56, 37, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 29], []]
 b := ![[], [38, 64, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [43, 51, 52, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-773133050, -5607266036, 5448822270, 819986427, -4228582433]
  a := ![295, 33, -270, -263, 604]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1146607484, 3461948127, 2729098540, 819986427, -4228582433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60907, -68343, -22509, -34976, 78348]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![60907, -68343, -22509, -34976, 78348]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![70, 72, 1, 0, 0], ![35, 35, 0, 1, 0], ![37, 26, 0, 0, 1]] where
  M :=![![![60907, -68343, -22509, -34976, 78348], ![97968, -109902, -36195, -56242, 125984], ![157516, -176695, -58192, -90422, 202548], ![77634, -87083, -28679, -44563, 99822], ![76968, -86328, -28430, -44176, 98955]]]
  hmulB := by decide  
  f := ![![![-33, 15, 19, 16, -48]], ![![-288, 66, 207, 262, -544]], ![![-314, 93, 210, 270, -572]], ![![-125, 24, 97, 99, -230]], ![![-109, 29, 77, 88, -197]]]
  g := ![![![-523, 10129, -22509, -34976, 78348], ![-840, 16288, -36195, -56242, 125984], ![-1350, 26187, -58192, -90422, 202548], ![-665, 12906, -28679, -44563, 99822], ![-659, 12794, -28430, -44176, 98955]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [35, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 72], [0, 1]]
 g := ![![[46, 48], [18], [71], [62, 9], [16], [1]], ![[0, 25], [18], [71], [26, 64], [16], [1]]]
 h' := ![![[69, 72], [29, 62], [32, 50], [20, 12], [8, 70], [38, 69], [0, 1]], ![[0, 1], [0, 11], [51, 23], [45, 61], [20, 3], [54, 4], [69, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [33, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [35, 4, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![855768, -1907954, 881913, -910592, 865496]
  a := ![-421, -19, 386, 404, -862]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-836038, -767642, 881913, -910592, 865496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![33, -15, -19, -16, 48]] ![![60907, -68343, -22509, -34976, 78348]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [59, 37, 14, 51, 54, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 30, 18, 8, 69], [21, 40, 41, 72, 5], [32, 36, 62, 63, 63], [12, 51, 37, 15, 21], [0, 1]]
 g := ![![[77, 59, 57, 41, 9], [18, 61, 18, 52, 51], [10, 59, 28, 3, 18], [61, 26, 21, 25, 1], [], []], ![[47, 51, 37, 10, 46, 58, 11, 66], [52, 57, 75, 36, 62, 64, 9, 12], [3, 49, 66, 14, 68, 18, 74, 28], [23, 19, 30, 28, 30, 65, 75, 28], [64, 55, 28, 40], [60, 16, 49, 21]], ![[5, 73, 58, 52, 37, 28, 49, 72], [32, 63, 58, 43, 24, 66, 27, 36], [63, 1, 33, 20, 62, 29, 55, 51], [42, 28, 77, 77, 41, 10, 9, 31], [36, 31, 10, 25], [53, 24, 2, 25]], ![[6, 54, 32, 40, 25, 8, 14, 70], [62, 70, 12, 20, 43, 78, 44, 17], [58, 55, 21, 35, 61, 17, 75, 34], [54, 31, 71, 40, 70, 1, 1, 69], [19, 48, 13, 32], [65, 16, 39, 19]], ![[19, 62, 33, 68, 59, 41, 65, 16], [48, 3, 26, 39, 49, 11, 70, 18], [53, 63, 35, 58, 67, 78, 29, 10], [70, 10, 69, 5, 55, 53, 36, 23], [67, 46, 8, 16], [59, 9, 42, 46]]]
 h' := ![![[39, 30, 18, 8, 69], [44, 27, 47, 57, 76], [42, 60, 45, 62, 29], [35, 1, 26, 40, 27], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[21, 40, 41, 72, 5], [69, 5, 57, 14, 74], [58, 17, 40, 14, 33], [77, 67, 2, 74, 48], [56, 65, 50, 41, 48], [35, 45, 35, 29, 35], [39, 30, 18, 8, 69]], ![[32, 36, 62, 63, 63], [54, 52, 43, 50, 21], [69, 63, 63, 26, 24], [13, 51, 50, 51, 37], [9, 78, 72, 54, 41], [0, 41, 73, 57, 5], [21, 40, 41, 72, 5]], ![[12, 51, 37, 15, 21], [21, 65, 14, 63, 19], [51, 47, 26, 35, 51], [36, 38, 44, 10, 64], [47, 17, 10, 54, 34], [33, 61, 39, 23, 43], [32, 36, 62, 63, 63]], ![[0, 1], [69, 9, 76, 53, 47], [8, 50, 63, 21, 21], [53, 1, 36, 62, 61], [42, 77, 26, 9, 34], [60, 11, 10, 49, 75], [12, 51, 37, 15, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 6, 41, 75], [], [], []]
 b := ![[], [59, 0, 40, 28, 47], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [59, 37, 14, 51, 54, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112780330529692027, -283803445451547256, 340335831940047064, 118025192290031220, -365065093091840938]
  a := ![210, 0, -192, -220, 430]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1427599120629013, -3592448676601864, 4308048505570216, 1493989775823180, -4621077127744822]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-667, 548, 252, 434, -1004]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-667, 548, 252, 434, -1004]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![73, 56, 10, 8, 1]] where
  M :=![![![-667, 548, 252, 434, -1004], ![-1852, 1457, 690, 1216, -2836], ![-5648, 4106, 2245, 3788, -8864], ![-8166, 5790, 3186, 5653, -12978], ![-6248, 4478, 2430, 4268, -9883]]]
  hmulB := by decide  
  f := ![![![-8109, 4760, 1320, 2018, -4376]], ![![-2764, 1623, 450, 688, -1492]], ![![-944, 554, 155, 236, -512]], ![![1218, -714, -198, -301, 654]], ![![-8943, 5250, 1456, 2226, -4827]]]
  g := ![![![875, 684, 124, 102, -1004], ![2472, 1931, 350, 288, -2836], ![7728, 6030, 1095, 900, -8864], ![11316, 8826, 1602, 1319, -12978], ![8617, 6722, 1220, 1004, -9883]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [72, 55, 39, 40, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 17, 54, 31], [20, 35, 47, 5], [69, 30, 65, 47], [0, 1]]
 g := ![![[26, 13, 69, 30], [59, 32, 21, 27], [36, 62, 23], [26, 32, 7], [43, 1], []], ![[47, 62, 77, 18, 5, 29], [31, 54, 29, 60, 65, 41], [11, 58, 1], [43, 32, 44], [75, 27, 40, 19, 35, 63], [7, 17, 48]], ![[9, 29, 46, 12, 5, 71], [18, 46, 42, 41, 25, 24], [15, 44, 1], [43, 51, 69], [31, 18, 6, 51, 16, 72], [42, 51, 25]], ![[35, 65, 60, 54, 37, 5], [16, 70, 8, 39, 55, 66], [19, 41, 23], [42, 64, 29], [7, 47, 77, 56, 64, 43], [39, 3, 51]]]
 h' := ![![[37, 17, 54, 31], [68, 71, 11, 69], [68, 2, 62, 39], [81, 7, 60, 40], [58, 53, 11, 67], [0, 0, 1], [0, 1]], ![[20, 35, 47, 5], [3, 63, 34, 10], [64, 20, 73, 81], [62, 26, 49, 1], [2, 74, 4, 58], [35, 64, 36, 49], [37, 17, 54, 31]], ![[69, 30, 65, 47], [66, 2, 82, 8], [50, 17, 2, 72], [36, 58, 41, 82], [71, 40, 62, 22], [32, 66, 16, 23], [20, 35, 47, 5]], ![[0, 1], [61, 30, 39, 79], [21, 44, 29, 57], [12, 75, 16, 43], [31, 82, 6, 19], [44, 36, 30, 11], [69, 30, 65, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [41, 2, 66], []]
 b := ![[], [], [6, 40, 14, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [72, 55, 39, 40, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6304232781, -535959182153, 463785404167, 994591063, -262962488874]
  a := ![-29, 11, 29, 41, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![231204306687, 170963134877, 37270003529, 25357765085, -262962488874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8109, -4760, -1320, -2018, 4376]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![8109, -4760, -1320, -2018, 4376]] 
 ![![83, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![8109, -4760, -1320, -2018, 4376], ![2764, -1623, -450, -688, 1492], ![944, -554, -155, -236, 512], ![-1218, 714, 198, 301, -654], ![-4168, 2446, 678, 1036, -2247]]]
  hmulB := by decide  
  f := ![![![667, -548, -252, -434, 1004]], ![![175, -143, -66, -114, 264]], ![![502, -406, -191, -328, 760]], ![![235, -182, -90, -157, 362]], ![![236, -186, -90, -156, 361]]]
  g := ![![![1405, -4760, -1320, -2018, 4376], ![479, -1623, -450, -688, 1492], ![164, -554, -155, -236, 512], ![-211, 714, 198, 301, -654], ![-722, 2446, 678, 1036, -2247]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-667, 548, 252, 434, -1004]] ![![8109, -4760, -1320, -2018, 4376]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44162, 50059, 16315, 25253, -56489]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-44162, 50059, 16315, 25253, -56489]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![13, 5, 49, 71, 1]] where
  M :=![![![-44162, 50059, 16315, 25253, -56489], ![-69154, 79148, 25505, 39312, -87802], ![-104936, 122777, 38614, 58966, -131248], ![-39617, 51855, 14407, 20870, -45521], ![-43232, 54230, 15788, 23356, -51365]]]
  hmulB := by decide  
  f := ![![![-20, -1, 19, 25, -47]], ![![110, 96, -177, -116, 270]], ![![528, -569, 30, -574, 824]], ![![-3869, -755, 3993, 4152, -8337]], ![![-2809, -915, 3213, 3011, -6225]]]
  g := ![![![7755, 3736, 31284, 45348, -56489], ![12048, 5822, 48627, 70486, -87802], ![17992, 8753, 72694, 105366, -131248], ![6204, 3140, 25224, 36549, -45521], ![7017, 3495, 28457, 41239, -51365]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [39, 16, 3, 54, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 56, 60, 22], [68, 70, 36, 72], [34, 51, 82, 84], [0, 1]]
 g := ![![[4, 42, 43, 79], [80, 83, 57], [25, 61, 36], [78, 25, 69, 42], [35, 1], []], ![[71, 85, 29, 85, 83, 50], [28, 20, 88], [45, 88, 84], [26, 83, 72, 15, 53, 69], [35, 5, 14, 28, 22, 10], [73, 0, 39]], ![[59, 5, 27, 25, 41, 16], [58, 84, 64], [72, 21, 53], [79, 60, 61, 17, 30, 68], [17, 33, 65, 86, 62, 79], [48, 80, 22]], ![[2, 79, 51, 27, 61, 80], [39, 71, 67], [73, 67, 88], [42, 63, 71, 25, 14, 42], [37, 83, 42, 26, 66, 9], [54, 55, 25]]]
 h' := ![![[22, 56, 60, 22], [44, 71, 18, 48], [82, 41, 26, 18], [73, 12, 41, 6], [59, 24, 57, 65], [0, 0, 1], [0, 1]], ![[68, 70, 36, 72], [20, 88, 53, 45], [69, 65, 44, 34], [20, 32, 27, 23], [15, 2, 27, 13], [40, 50, 31, 7], [22, 56, 60, 22]], ![[34, 51, 82, 84], [34, 41, 25, 38], [31, 1, 68, 81], [13, 69, 64, 26], [88, 54, 54, 68], [82, 25, 38, 78], [68, 70, 36, 72]], ![[0, 1], [14, 67, 82, 47], [72, 71, 40, 45], [31, 65, 46, 34], [6, 9, 40, 32], [29, 14, 19, 4], [34, 51, 82, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [86, 34, 22], []]
 b := ![[], [], [41, 43, 66, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [39, 16, 3, 54, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![961408297657, 481927285744, -1244011563044, -1028457071900, 2209034033092]
  a := ![83, -1, -76, -85, 170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-311865552051, -118688122244, -1230187406568, -1773818802488, 2209034033092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, -1, 19, 25, -47]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-20, -1, 19, 25, -47]] 
 ![![89, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-20, -1, 19, 25, -47], ![110, 96, -177, -116, 270], ![528, -569, 30, -574, 824], ![-3869, -755, 3993, 4152, -8337], ![-1464, -416, 1622, 1568, -3213]]]
  hmulB := by decide  
  f := ![![![-44162, 50059, 16315, 25253, -56489]], ![![-42458, 48136, 15685, 24276, -54302]], ![![-32936, 37377, 12166, 18822, -42096]], ![![-14835, 16894, 5478, 8463, -18918]], ![![-10906, 12421, 4027, 6221, -13906]]]
  g := ![![![-10, -1, 19, 25, -47], ![12, 96, -177, -116, 270], ![514, -569, 30, -574, 824], ![-1588, -755, 3993, 4152, -8337], ![-543, -416, 1622, 1568, -3213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-44162, 50059, 16315, 25253, -56489]] ![![-20, -1, 19, 25, -47]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-94, 118, -4, 53, -121]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-94, 118, -4, 53, -121]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![46, 3, 22, 1, 0], ![57, 30, 73, 0, 1]] where
  M :=![![![-94, 118, -4, 53, -121], ![-194, 129, 108, 50, -282], ![-3540, 296, 2973, 3292, -6980], ![-571, 6434, -4770, -72, 2097], ![-1368, 2978, -1178, 916, -1221]]]
  hmulB := by decide  
  f := ![![![-24452, 14932, 4204, 6437, -14003]], ![![-9706, 6629, 1940, 2982, -6538]], ![![-5516, 4736, 1477, 2284, -5068]], ![![-13125, 8355, 2388, 3662, -7991]], ![![-21412, 14332, 4167, 6401, -14016]]]
  g := ![![![45, 37, 79, 53, -121], ![140, 87, 202, 50, -282], ![2504, 2060, 4537, 3292, -6980], ![-1204, -580, -1611, -72, 2097], ![269, 380, 699, 916, -1221]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [57, 69, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 61, 10], [83, 35, 87], [0, 1]]
 g := ![![[83, 33, 96], [59, 47], [93, 12], [70, 54], [87, 64], [1]], ![[90, 83, 74, 60], [8, 25], [87, 16], [86, 79], [15, 96], [2, 58, 13, 30]], ![[43, 30, 39, 42], [93, 95], [95, 62], [14, 2], [5, 2], [26, 35, 75, 67]]]
 h' := ![![[22, 61, 10], [54, 63, 75], [33, 90, 85], [22, 51, 77], [36, 58, 32], [40, 28, 8], [0, 1]], ![[83, 35, 87], [29, 60, 54], [0, 58, 92], [20, 7, 4], [84, 46, 51], [58, 59, 75], [22, 61, 10]], ![[0, 1], [77, 71, 65], [25, 46, 17], [69, 39, 16], [24, 90, 14], [42, 10, 14], [83, 35, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 43], []]
 b := ![[], [80, 9, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [57, 69, 89, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4759926200, -288884108, 4364639940, 5117954156, -9960138288]
  a := ![213, 9, -193, -208, 436]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3376722320, 2919189712, 6379997356, 5117954156, -9960138288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24452, 14932, 4204, 6437, -14003]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-24452, 14932, 4204, 6437, -14003]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![16, 53, 1, 0, 0], ![61, 59, 0, 1, 0], ![68, 26, 0, 0, 1]] where
  M :=![![![-24452, 14932, 4204, 6437, -14003], ![-9706, 6629, 1940, 2982, -6538], ![-5516, 4736, 1477, 2284, -5068], ![2137, -516, -62, -82, 121], ![10648, -5518, -1450, -2204, 4723]]]
  hmulB := by decide  
  f := ![![![-94, 118, -4, 53, -121]], ![![-194, 129, 108, 50, -282]], ![![-158, 93, 89, 70, -246]], ![![-183, 219, 14, 63, -226]], ![![-132, 148, 14, 60, -173]]]
  g := ![![![4823, -2305, 4204, 6437, -14003], ![2288, -1053, 1940, 2982, -6538], ![1816, -789, 1477, 2284, -5068], ![-1, 46, -62, -82, 121], ![-1576, 810, -1450, -2204, 4723]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [31, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 96], [0, 1]]
 g := ![![[4, 72], [27], [33], [48], [70], [70, 1]], ![[0, 25], [27], [33], [48], [70], [43, 96]]]
 h' := ![![[70, 96], [37, 84], [1, 67], [65, 79], [96, 40], [61, 19], [0, 1]], ![[0, 1], [0, 13], [35, 30], [66, 18], [83, 57], [33, 78], [70, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [41, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [31, 27, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![398284, -644028, 202016, -420861, 516485]
  a := ![253, 13, -232, -241, 518]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-126623, 529, 202016, -420861, 516485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-94, 118, -4, 53, -121]] ![![-24452, 14932, 4204, 6437, -14003]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1044, -605, -177, -261, 569]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![1044, -605, -177, -261, 569]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![9, 33, 41, 1, 0], ![83, 62, 95, 0, 1]] where
  M :=![![![1044, -605, -177, -261, 569], ![418, -224, -99, -156, 314], ![-272, -307, 522, 390, -856], ![-579, 1055, -433, 504, -507], ![-784, 658, 8, 404, -641]]]
  hmulB := by decide  
  f := ![![![394, -589, -141, -189, 399]], ![![42, -524, -1, 96, -294]], ![![-1848, 527, 730, 1450, -3504]], ![![-747, 19, 301, 635, -1558]], ![![-1422, -290, 583, 1291, -3204]]]
  g := ![![![-434, -270, -431, -261, 569], ![-240, -144, -233, -156, 314], ![666, 395, 652, 390, -856], ![366, 157, 268, 504, -507], ![483, 268, 439, 404, -641]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [38, 7, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 24, 67], [87, 76, 34], [0, 1]]
 g := ![![[11, 48, 88], [95, 56], [23, 84, 1], [46, 19], [54, 77], [1]], ![[19, 16, 50, 69], [21, 87], [66, 74, 6, 34], [82, 16], [57, 33], [34, 98, 24, 86]], ![[51, 30, 79, 55], [61, 88], [50, 19, 19, 27], [99, 37], [58, 1], [19, 52, 43, 15]]]
 h' := ![![[87, 24, 67], [39, 74, 47], [35, 2, 37], [74, 45, 100], [99, 56, 25], [63, 94, 73], [0, 1]], ![[87, 76, 34], [6, 61, 46], [81, 99, 17], [48, 85, 10], [72, 60, 97], [4, 50, 29], [87, 24, 67]], ![[0, 1], [52, 67, 8], [42, 0, 47], [90, 72, 92], [32, 86, 80], [69, 58, 100], [87, 76, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 44], []]
 b := ![[], [65, 25, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [38, 7, 28, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42262850, -56019081, 11020379, -45016998, 60730516]
  a := ![67, 8, -61, -58, 137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-45477396, -23126239, -38739423, -45016998, 60730516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52, -76, 22, -59, 73]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![52, -76, 22, -59, 73]] 
 ![![101, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![52, -76, 22, -59, 73], ![-1018, -117, 984, 1090, -2154], ![2700, 4300, -6009, -2860, 7580], ![16249, -8246, -7002, -17574, 29697], ![7104, -2492, -4012, -7672, 13503]]]
  hmulB := by decide  
  f := ![![![-261470, 156526, 47758, 75209, -165833]], ![![-4152, 2565, 894, 1459, -3279]], ![![-261620, 156900, 48271, 76200, -168240]], ![![-3259, 2376, 1322, 2356, -5527]], ![![-193164, 115976, 35864, 56698, -125283]]]
  g := ![![![-74, -76, 22, -59, 73], ![595, -117, 984, 1090, -2154], ![380, 4300, -6009, -2860, 7580], ![-14583, -8246, -7002, -17574, 29697], ![-5826, -2492, -4012, -7672, 13503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-597721, 350840, 97290, 148734, -322526]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-597721, 350840, 97290, 148734, -322526]] 
 ![![101, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![-597721, 350840, 97290, 148734, -322526], ![-203692, 119563, 33156, 50688, -109916], ![-69424, 40756, 11303, 17280, -37472], ![90006, -52826, -14648, -22393, 48558], ![307384, -180418, -50030, -76484, 165853]]]
  hmulB := by decide  
  f := ![![![-353, -16, 338, 346, -722]], ![![-62, 11, 48, 60, -120]], ![![-176, -36, 199, 160, -368]], ![![-633, -218, 750, 649, -1396]], ![![-381, -98, 428, 382, -821]]]
  g := ![![![-28729, 350840, 97290, 148734, -322526], ![-9790, 119563, 33156, 50688, -109916], ![-3336, 40756, 11303, 17280, -37472], ![4327, -52826, -14648, -22393, 48558], ![14775, -180418, -50030, -76484, 165853]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![1044, -605, -177, -261, 569]] ![![52, -76, 22, -59, 73]]
  ![![-6535, -35401, 35935, 6620, -29988]] where
 M := ![![![-6535, -35401, 35935, 6620, -29988]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-6535, -35401, 35935, 6620, -29988]] ![![-597721, 350840, 97290, 148734, -322526]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![264115, -155439, -42521, -65246, 141602]]]
 hmul := by decide  
 g := ![![![![2615, -1539, -421, -646, 1402]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![965, -1094, -348, -552, 1234]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![965, -1094, -348, -552, 1234]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![22, 98, 53, 1, 0], ![89, 73, 69, 0, 1]] where
  M :=![![![965, -1094, -348, -552, 1234], ![1496, -1721, -544, -828, 1888], ![2984, -2592, -1525, -1952, 4312], ![1380, -2518, 388, -879, 1360], ![1376, -1788, -228, -872, 1695]]]
  hmulB := by decide  
  f := ![![![-565, 486, 356, 656, -1562]], ![![-3688, 2665, 1456, 2588, -6064]], ![![-12584, 9008, 4821, 8544, -19992]], ![![-10286, 7404, 4011, 7121, -16676]], ![![-11675, 8445, 4623, 8220, -19263]]]
  g := ![![![-939, -360, -546, -552, 1234], ![-1440, -567, -844, -828, 1888], ![-3280, -1224, -1899, -1952, 4312], ![-974, -152, -455, -879, 1360], ![-1265, -389, -689, -872, 1695]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [91, 50, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 76, 80], [57, 26, 23], [0, 1]]
 g := ![![[7, 102, 28], [73, 55, 49], [8, 41, 16], [59, 58], [87, 2], [1]], ![[33, 26, 76, 62], [36, 95, 77, 47], [15, 101, 99, 44], [16, 32], [61, 7], [51, 60, 20, 90]], ![[95, 77, 66, 55], [55, 82, 50, 7], [35, 41], [28, 14], [58, 66], [54, 94, 41, 13]]]
 h' := ![![[84, 76, 80], [52, 46, 50], [96, 99, 7], [25, 58, 99], [55, 36, 26], [12, 53, 38], [0, 1]], ![[57, 26, 23], [25, 31, 36], [99, 4, 68], [83, 9, 4], [71, 69, 54], [36, 35, 78], [84, 76, 80]], ![[0, 1], [17, 26, 17], [79, 0, 28], [91, 36], [95, 101, 23], [29, 15, 90], [57, 26, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 38], []]
 b := ![[], [15, 52, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [91, 50, 65, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11539055127, -307930670, -9719148496, -12416032744, 23674581876]
  a := ![-287, -5, 258, 282, -588]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17692679723, -4968749502, -9565199636, -12416032744, 23674581876]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![565, -486, -356, -656, 1562]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![565, -486, -356, -656, 1562]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![45, 100, 1, 0, 0], ![16, 70, 0, 1, 0], ![48, 59, 0, 0, 1]] where
  M :=![![![565, -486, -356, -656, 1562], ![3688, -2665, -1456, -2588, 6064], ![12584, -9008, -4821, -8544, 19992], ![18652, -13326, -7100, -12575, 29416], ![14720, -10484, -5548, -9816, 22951]]]
  hmulB := by decide  
  f := ![![![-965, 1094, 348, 552, -1234]], ![![-1496, 1721, 544, 828, -1888]], ![![-1903, 2174, 695, 1064, -2414]], ![![-1180, 1364, 420, 657, -1488]], ![![-1320, 1513, 476, 740, -1673]]]
  g := ![![![-465, -108, -356, -656, 1562], ![-1752, -327, -1456, -2588, 6064], ![-5761, -1052, -4821, -8544, 19992], ![-8472, -1540, -7100, -12575, 29416], ![-6604, -1191, -5548, -9816, 22951]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [93, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 102], [0, 1]]
 g := ![![[9, 72], [8, 64], [72, 61], [19], [8], [90, 1]], ![[0, 31], [0, 39], [0, 42], [19], [8], [77, 102]]]
 h' := ![![[90, 102], [80, 22], [102, 95], [3, 24], [88, 15], [76, 76], [0, 1]], ![[0, 1], [0, 81], [0, 8], [0, 79], [99, 88], [15, 27], [90, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [30, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [93, 13, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135506, -386152, 211264, -144089, 97319]
  a := ![-188, -6, 171, 181, -385]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-113954, -166681, 211264, -144089, 97319]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![965, -1094, -348, -552, 1234]] ![![565, -486, -356, -656, 1562]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB2009I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB2009I2 : PrimesBelowBoundCertificateInterval O 61 103 2009 where
  m := 9
  g := ![3, 2, 2, 1, 2, 2, 2, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB2009I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
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
    · exact ![4489, 4489, 67]
    · exact ![25411681, 71]
    · exact ![389017, 5329]
    · exact ![3077056399]
    · exact ![47458321, 83]
    · exact ![62742241, 89]
    · exact ![912673, 9409]
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
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
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
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N2, I71N1, I83N1, I89N1, I101N1, I101N2]
  Il := ![[I67N2], [I71N1], [], [], [I83N1], [I89N1], [], [I101N1, I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
