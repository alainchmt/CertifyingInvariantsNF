
import IdealArithmetic.Examples.NF5_1_202500000_1.RI5_1_202500000_1
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


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [58, 44, 46, 0, 55, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 64, 19, 10, 24], [14, 4, 15, 35, 27], [14, 35, 8, 62, 41], [28, 30, 25, 27, 42], [0, 1]]
 g := ![![[10, 64, 43, 49, 17], [9, 41, 54, 27, 14], [21, 3, 53, 40], [7, 10, 12, 1], [], []], ![[40, 45, 30, 5, 37, 35, 21, 64], [24, 14, 54, 0, 51, 12, 1, 47], [55, 39, 16, 35], [20, 53, 31, 10], [64, 24, 60, 55], [40, 3, 22, 40]], ![[52, 25, 7, 52, 20, 16, 59, 7], [35, 60, 7, 14, 10, 7, 17, 12], [15, 47, 48, 4], [24, 37, 66, 24], [17, 22, 14, 49], [42, 46, 52, 59]], ![[60, 28, 23, 59, 55, 20], [55, 30, 63, 19, 41, 0, 25, 50], [19, 32, 17, 23], [10, 46, 47, 26], [34, 2, 2, 19], [3, 42, 64, 6]], ![[37, 57, 55, 53, 31, 3, 60, 3], [59, 46, 48, 43, 22, 51, 29, 61], [28, 50, 32, 59], [7, 40, 58, 49], [36, 61, 14, 10], [17, 48, 53, 22]]]
 h' := ![![[23, 64, 19, 10, 24], [14, 56, 19, 46, 34], [4, 43, 9, 19, 58], [63, 50, 16, 26, 24], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[14, 4, 15, 35, 27], [34, 38, 39, 38, 5], [14, 2, 63, 64, 51], [16, 4, 48, 31, 54], [29, 59, 66, 40, 55], [18, 5, 47, 2, 51], [23, 64, 19, 10, 24]], ![[14, 35, 8, 62, 41], [62, 2, 44, 7, 13], [5, 61, 18, 7, 23], [2, 41, 15, 0, 65], [56, 14, 42, 61, 52], [38, 18, 30, 41, 60], [14, 4, 15, 35, 27]], ![[28, 30, 25, 27, 42], [43, 27, 41, 62], [26, 42, 64, 62, 37], [18, 35, 12, 25, 31], [53, 5, 13, 23, 19], [22, 20, 39, 14, 35], [14, 35, 8, 62, 41]], ![[0, 1], [15, 11, 58, 48, 15], [21, 53, 47, 49, 32], [29, 4, 43, 52, 27], [57, 56, 13, 10, 7], [66, 24, 17, 10, 55], [28, 30, 25, 27, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 46, 44, 14], [], [], []]
 b := ![[], [47, 18, 6, 31, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [58, 44, 46, 0, 55, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28912189221688, -56351645522854, 26969931916889, 1947912560935, -8875644264753]
  a := ![0, 6, 2, 5, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![431525212264, -841069336162, 402536297267, 29073321805, -132472302459]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [63, 26, 7, 49, 32, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 65, 62, 19, 39], [1, 36, 33, 34, 64], [59, 36, 27, 38, 6], [69, 4, 20, 51, 33], [0, 1]]
 g := ![![[42, 28, 56, 49, 64], [10, 6, 26, 49, 4], [56, 57, 65, 61, 32], [39, 52, 39, 1], [], []], ![[9, 16, 20, 14, 55, 65, 11, 46], [43, 2, 22, 4, 69, 51, 48, 44], [26, 53, 61, 19, 64, 20, 68, 56], [17, 37, 56, 32], [15, 52, 19, 50], [12, 16, 25, 30]], ![[60, 52, 34, 19, 29, 14, 30, 15], [55, 8, 33, 48, 9, 36, 14, 58], [31, 11, 53, 50, 11, 38, 41, 2], [12, 33, 35, 5], [29, 27, 24, 36], [1, 14, 15, 49]], ![[18, 31, 69, 51, 3, 41, 57, 27], [50, 69, 52, 44, 36, 5, 57, 8], [55, 8, 44, 23, 4, 14, 56, 19], [23, 40, 9, 12], [18, 8, 43, 5], [63, 53, 14, 36]], ![[49, 51, 7, 10, 26, 68, 19, 46], [59, 9, 66, 38, 65, 24, 57, 61], [62, 11, 33, 21, 26, 5, 23, 52], [26, 9, 12, 29], [27, 0, 29, 20], [47, 52, 42, 24]]]
 h' := ![![[52, 65, 62, 19, 39], [9, 59, 63, 29, 8], [22, 68, 19, 62, 2], [28, 41, 36, 56, 23], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[1, 36, 33, 34, 64], [0, 51, 4, 63, 43], [41, 23, 28, 0, 16], [37, 13, 18, 56, 67], [16, 56, 0, 29, 48], [31, 44, 7, 51, 11], [52, 65, 62, 19, 39]], ![[59, 36, 27, 38, 6], [54, 4, 67, 51, 47], [18, 2, 60, 57, 56], [14, 7, 2, 24, 37], [29, 34, 16, 12, 17], [9, 16, 46, 27, 6], [1, 36, 33, 34, 64]], ![[69, 4, 20, 51, 33], [33, 13, 45, 34, 53], [70, 45, 31, 26, 66], [44, 65, 19, 37, 21], [12, 35, 53, 6, 15], [9, 52, 6, 54, 17], [59, 36, 27, 38, 6]], ![[0, 1], [14, 15, 34, 36, 62], [67, 4, 4, 68, 2], [45, 16, 67, 40, 65], [60, 17, 2, 24, 61], [25, 30, 11, 10, 37], [69, 4, 20, 51, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 22, 65, 44], [], [], []]
 b := ![[], [39, 12, 12, 56, 28], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [63, 26, 7, 49, 32, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![304596095439602, -818957694274294, 415622476473865, -418751022611249, 147304862768988]
  a := ![3, -2, -1, -3, -56]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4290085851262, -11534615412314, 5853837696815, -5897901726919, 2074716377028]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1119, 1973, -937, -498, 590]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-1119, 1973, -937, -498, 590]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![69, 49, 2, 63, 1]] where
  M :=![![![-1119, 1973, -937, -498, 590], ![5900, -11831, 5664, -288, -1402], ![-14020, 32826, -15693, 10502, -2554], ![-5760, -4411, 2223, -32723, 21004], ![47600, -89985, 42995, 8916, -17959]]]
  hmulB := by decide  
  f := ![![![61193, -30201, -2603, -308, 4378]], ![![43780, -21681, -1850, -212, 3146]], ![![31460, -15782, -1297, -130, 2298]], ![![-4240, 1855, 217, 47, -260]], ![![84649, -42044, -3559, -397, 6105]]]
  g := ![![![-573, -369, -29, -516, 590], ![1406, 779, 116, 1206, -1402], ![2222, 2164, -145, 2348, -2554], ![-19932, -14159, -545, -18575, 21004], ![17627, 10822, 1081, 15621, -17959]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [30, 32, 25, 70, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 16, 26, 3], [47, 44, 27, 43], [46, 12, 20, 27], [0, 1]]
 g := ![![[3, 39, 67, 36], [60, 40, 64], [30, 61, 4], [1, 58, 23, 9], [1], []], ![[33, 23, 50, 14, 10, 12], [60, 37, 4], [29, 15, 67], [59, 32, 71, 64, 10, 27], [20, 72, 12], [1, 37, 9]], ![[50, 13, 60, 62, 52, 62], [14, 62, 2], [2, 58, 70], [49, 35, 35, 57, 25, 31], [16, 67, 55], [72, 58, 24]], ![[56, 7, 46, 24, 44, 72], [63, 19, 12], [50, 43, 41], [2, 1, 67, 42, 10, 67], [10, 41, 36], [70, 55, 72]]]
 h' := ![![[56, 16, 26, 3], [25, 19, 27, 6], [0, 36, 46, 65], [43, 4, 6, 71], [43, 41, 48, 3], [0, 0, 1], [0, 1]], ![[47, 44, 27, 43], [31, 55, 50, 2], [15, 42, 12, 71], [3, 42, 37, 33], [51, 71, 21, 70], [40, 66, 10, 31], [56, 16, 26, 3]], ![[46, 12, 20, 27], [67, 72, 13, 55], [7, 24, 63, 41], [33, 10, 17, 17], [23, 70, 4, 69], [49, 19, 25, 36], [47, 44, 27, 43]], ![[0, 1], [10, 0, 56, 10], [41, 44, 25, 42], [9, 17, 13, 25], [29, 37, 0, 4], [16, 61, 37, 6], [46, 12, 20, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [44, 45, 26], []]
 b := ![[], [], [3, 24, 61, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [30, 32, 25, 70, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3666082498, -7156368766, 3384730476, 173648274, -1046078944]
  a := ![1, 3, 1, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1038979858, 604130130, 75025868, 905159202, -1046078944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61193, -30201, -2603, -308, 4378]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![61193, -30201, -2603, -308, 4378]] 
 ![![73, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![61193, -30201, -2603, -308, 4378], ![43780, -21681, -1850, -212, 3146], ![31460, -15782, -1297, -130, 2298], ![-4240, 1855, 217, 47, -260], ![16040, -8275, -627, -42, 1213]]]
  hmulB := by decide  
  f := ![![![-1119, 1973, -937, -498, 590]], ![![-517, 892, -423, -270, 296]], ![![-376, 774, -369, 62, 62]], ![![-876, 1345, -637, -803, 708]], ![![-283, 416, -194, -294, 247]]]
  g := ![![![13962, -30201, -2603, -308, 4378], ![10009, -21681, -1850, -212, 3146], ![7248, -15782, -1297, -130, 2298], ![-901, 1855, 217, 47, -260], ![3760, -8275, -627, -42, 1213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-1119, 1973, -937, -498, 590]] ![![61193, -30201, -2603, -308, 4378]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [56, 23, 55, 53, 58, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 5, 8, 30, 65], [10, 61, 72, 5, 33], [61, 56, 7, 36, 19], [74, 35, 71, 8, 41], [0, 1]]
 g := ![![[53, 36, 72, 35, 44], [55, 24, 64, 60, 46], [2, 19, 33, 72, 16], [18, 28, 72, 21, 1], [], []], ![[28, 32, 49, 62, 5, 14, 46, 76], [47, 67, 12, 0, 32, 23, 70, 50], [16, 47, 74, 18, 21, 54, 55, 13], [58, 21, 21, 74, 36, 42, 63, 13], [78, 12, 64, 4], [71, 71, 37, 38]], ![[74, 27, 34, 67, 62, 18, 38, 39], [55, 15, 61, 14, 13, 10, 42, 59], [76, 46, 76, 19, 0, 9, 47, 33], [70, 71, 4, 53, 58, 40, 54, 39], [21, 21, 62, 64], [51, 55, 52, 62]], ![[77, 50, 15, 62, 69, 78, 10, 10], [32, 65, 46, 58, 25, 4, 63, 26], [31, 40, 17, 31, 36, 29, 35, 13], [47, 50, 34, 28, 68, 38, 37, 40], [28, 64, 73, 73], [21, 34, 22, 45]], ![[72, 55, 73, 6, 69, 32, 18, 24], [71, 39, 72, 3, 25, 16, 43, 35], [52, 20, 49, 51, 43, 12, 12, 6], [60, 44, 14, 2, 68, 76, 45, 68], [23, 58, 9, 50], [1, 74, 12, 22]]]
 h' := ![![[34, 5, 8, 30, 65], [1, 60, 8, 49, 53], [46, 41, 25, 78, 58], [19, 72, 22, 46, 4], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[10, 61, 72, 5, 33], [12, 41, 49, 18, 50], [41, 56, 20, 11, 63], [70, 18, 45, 77, 75], [0, 29, 4, 64, 4], [24, 24, 69, 5, 77], [34, 5, 8, 30, 65]], ![[61, 56, 7, 36, 19], [12, 58, 44, 14, 28], [3, 19, 56, 45, 32], [55, 63, 46, 35, 78], [11, 74, 45, 40, 28], [9, 48, 75, 68, 8], [10, 61, 72, 5, 33]], ![[74, 35, 71, 8, 41], [58, 10, 9, 39, 31], [71, 56, 51, 54, 52], [33, 49, 78, 2, 3], [64, 41, 4, 50, 62], [17, 21, 31, 36, 28], [61, 56, 7, 36, 19]], ![[0, 1], [49, 68, 48, 38, 75], [71, 65, 6, 49, 32], [64, 35, 46, 77, 77], [68, 14, 26, 4, 63], [48, 65, 61, 49, 45], [74, 35, 71, 8, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 43, 12, 1], [], [], []]
 b := ![[], [51, 0, 68, 64, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [56, 23, 55, 53, 58, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-364384433244174, 730750444949014, -351230755995429, 16322050004179, 88811679278125]
  a := ![1, -6, -3, -7, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4612461180306, 9250005632266, -4445958936651, 206608227901, 1124198471875]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, -477, -12, 13, 65]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![331, -477, -12, 13, 65]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![14, 39, 1, 0, 0], ![52, 57, 0, 1, 0], ![79, 14, 0, 0, 1]] where
  M :=![![![331, -477, -12, 13, 65], ![650, -917, -47, 15, 117], ![1170, -1588, -160, -7, 177], ![300, -299, -171, -61, -14], ![570, -619, -264, -87, 2]]]
  hmulB := by decide  
  f := ![![![-1047, 523, 40, 5, -73]], ![![-730, 335, 47, -3, -53]], ![![-526, 249, 29, 0, -38]], ![![-1158, 560, 56, 0, -81]], ![![-1121, 552, 48, 4, -79]]]
  g := ![![![-64, -20, -12, 13, 65], ![-105, -19, -47, 15, 117], ![-123, 31, -160, -7, 177], ![84, 121, -171, -61, -14], ![104, 176, -264, -87, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [64, 41, 1] where
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
 g := ![![[59, 48], [3, 77], [37], [49], [71, 21], [1]], ![[0, 35], [0, 6], [37], [49], [40, 62], [1]]]
 h' := ![![[42, 82], [57, 52], [66, 34], [44, 28], [21, 7], [19, 42], [0, 1]], ![[0, 1], [0, 31], [0, 49], [58, 55], [66, 76], [40, 41], [42, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [3, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [64, 41, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46304, -78015, 29501, 19858, -16240]
  a := ![-1, 7, 5, 9, -28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1402, -25700, 29501, 19858, -16240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26529, -12718, -1220, -188, 1818]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![26529, -12718, -1220, -188, 1818]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![33, 51, 1, 0, 0], ![55, 60, 0, 1, 0], ![18, 59, 0, 0, 1]] where
  M :=![![![26529, -12718, -1220, -188, 1818], ![18180, -7825, -1024, -246, 1066], ![10660, -1828, -1141, -490, 82], ![-4920, 5710, -382, -365, -980], ![2300, 3958, -1024, -620, -813]]]
  hmulB := by decide  
  f := ![![![227, -1006, 484, -1152, 626]], ![![6260, -10515, 5012, 3898, -3982]], ![![3457, -5921, 2823, 1916, -2058]], ![![5615, -10296, 4914, 1707, -2506]], ![![4762, -7981, 3804, 3002, -3051]]]
  g := ![![![535, -560, -1220, -188, 1818], ![558, -45, -1024, -246, 1066], ![889, 975, -1141, -490, 82], ![547, 1264, -382, -365, -980], ![1022, 1703, -1024, -620, -813]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [42, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 82], [0, 1]]
 g := ![![[67, 69], [56, 28], [31], [41], [6, 64], [1]], ![[38, 14], [31, 55], [31], [41], [20, 19], [1]]]
 h' := ![![[8, 82], [55, 22], [13, 51], [30, 23], [80, 37], [41, 8], [0, 1]], ![[0, 1], [65, 61], [6, 32], [48, 60], [44, 46], [22, 75], [8, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [51, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [42, 75, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23242, -41132, 10014, -22, 3648]
  a := ![0, 4, -2, -6, -16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4478, -9226, 10014, -22, 3648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2897, -5061, 2414, 1401, -1603]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![2897, -5061, 2414, 1401, -1603]] 
 ![![83, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![2897, -5061, 2414, 1401, -1603], ![-16030, 31953, -15269, 423, 4001], ![40010, -92472, 44268, -27383, 5693], ![8460, 25849, -12619, 88189, -54766], ![-126690, 238001, -113640, -26741, 49538]]]
  hmulB := by decide  
  f := ![![![66859, -123697, 26794, 15949, 26707]], ![![64438, -118765, 25427, 15187, 25545]], ![![38292, -68754, 13418, 8243, 14363]], ![![26967, -47194, 8217, 5240, 9533]], ![![24354, -40981, 5846, 4007, 7856]]]
  g := ![![![3514, -5061, 2414, 1401, -1603], ![-23679, 31953, -15269, 423, 4001], ![72741, -92472, 44268, -27383, 5693], ![-33307, 25849, -12619, 88189, -54766], ![-171557, 238001, -113640, -26741, 49538]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![331, -477, -12, 13, 65]] ![![26529, -12718, -1220, -188, 1818]]
  ![![66859, -123697, 26794, 15949, 26707]] where
 M := ![![![66859, -123697, 26794, 15949, 26707]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![66859, -123697, 26794, 15949, 26707]] ![![2897, -5061, 2414, 1401, -1603]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -22, 14, -6, -2]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![9, -22, 14, -6, -2]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![18, 62, 52, 1, 0], ![75, 3, 15, 0, 1]] where
  M :=![![![9, -22, 14, -6, -2], ![-20, 53, -16, 38, -26], ![-260, 436, -183, -134, 126], ![760, -1478, 726, 81, -268], ![-360, 826, -364, 272, -95]]]
  hmulB := by decide  
  f := ![![![481, -330, -10, 6, 50]], ![![500, -475, 4, 18, 74]], ![![740, -924, 29, 46, 146]], ![![882, -944, 18, 41, 148]], ![![555, -461, -3, 14, 71]]]
  g := ![![![3, 4, 4, -6, -2], ![14, -25, -18, 38, -26], ![-82, 94, 55, -134, 126], ![218, -64, 6, 81, -268], ![21, -177, -147, 272, -95]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [28, 36, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 57, 12], [0, 31, 77], [0, 1]]
 g := ![![[44, 65, 10], [75, 8], [19, 18], [55, 23, 22], [71, 14, 1], []], ![[49, 1, 68, 24], [16, 40], [12, 40], [28, 70, 51, 7], [46, 40, 66, 51], [2, 55]], ![[0, 79, 82, 12], [47, 11], [79, 69], [47, 88, 62, 15], [68, 30, 71, 83], [26, 55]]]
 h' := ![![[14, 57, 12], [41, 68, 59], [19, 60, 39], [62, 56, 75], [59, 78, 17], [0, 0, 1], [0, 1]], ![[0, 31, 77], [86, 84, 64], [0, 37, 60], [43, 34, 60], [60, 80, 39], [51, 73, 31], [14, 57, 12]], ![[0, 1], [76, 26, 55], [18, 81, 79], [19, 88, 43], [54, 20, 33], [73, 16, 57], [0, 31, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 61], []]
 b := ![[], [34, 39, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [28, 36, 75, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31606638, -57191938, 27988508, 11998840, -16150786]
  a := ![13, 6, 4, 7, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11538612, -8456940, -3974038, 11998840, -16150786]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, -280, 190, 102, -150]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![149, -280, 190, 102, -150]] 
 ![![89, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![149, -280, 190, 102, -150], ![-1500, 2897, -1242, 26, 258], ![2580, -6428, 3435, -2278, 362], ![520, 2204, -808, 7033, -4556], ![-10860, 20232, -9238, -2106, 3771]]]
  hmulB := by decide  
  f := ![![![135238813701, -66666684792, -5766632086, -689922310, 9660583798]], ![![37554352436, -18512615631, -1601331214, -191583946, 2682639390]], ![![72193631343, -35588230428, -3078362635, -368296612, 5157044832]], ![![121452229000, -59870515324, -5178767112, -619589895, 8675759596]], ![![68769232645, -33900155072, -2932345032, -350827004, 4912427997]]]
  g := ![![![-39, -280, 190, 102, -150], ![-296, 2897, -1242, 26, 258], ![1813, -6428, 3435, -2278, 362], ![-4180, 2204, -808, 7033, -4556], ![-713, 20232, -9238, -2106, 3771]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13489, -20893, 1271, 1324, 3442]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![13489, -20893, 1271, 1324, 3442]] 
 ![![89, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![13489, -20893, 1271, 1324, 3442], ![34420, -53233, 3148, 3336, 8738], ![87380, -134938, 7745, 8362, 22082], ![66720, -102801, 5637, 6243, 16724], ![105620, -162763, 8957, 9924, 26491]]]
  hmulB := by decide  
  f := ![![![6898414441, -3400609695, -294150895, -35192338, 492777990]], ![![4008392319, -1975958084, -170919303, -20448858, 286333552]], ![![5387760481, -2655924877, -229736062, -27485720, 384866668]], ![![5807621355, -2862897504, -247639082, -29627645, 414858806]], ![![5290595152, -2608026717, -225592897, -26990030, 377925807]]]
  g := ![![![7393, -20893, 1271, 1324, 3442], ![18963, -53233, 3148, 3336, 8738], ![48383, -134938, 7745, 8362, 22082], ![37249, -102801, 5637, 6243, 16724], ![58908, -162763, 8957, 9924, 26491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![9, -22, 14, -6, -2]] ![![149, -280, 190, 102, -150]]
  ![![89061, -209934, 100448, -69532, 17836]] where
 M := ![![![89061, -209934, 100448, -69532, 17836]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89061, -209934, 100448, -69532, 17836]] ![![13489, -20893, 1271, 1324, 3442]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-2774931, 5331189, -1900773, 439304, -122286]]]
 hmul := by decide  
 g := ![![![![-31179, 59901, -21357, 4936, -1374]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52107, -196750, 95898, -620880, 383592]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-52107, -196750, 95898, -620880, 383592]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![45, 18, 62, 1, 0], ![34, 44, 93, 0, 1]] where
  M :=![![![-52107, -196750, 95898, -620880, 383592], ![3835920, -6719475, 3205172, 1817148, -2099928], ![-20999280, 41917404, -20030947, 676120, 5168664], ![36342960, -80898710, 38710966, -18460795, 1352240], ![17261240, -24372074, 11583722, 20316860, -16679431]]]
  hmulB := by decide  
  f := ![![![210169056189, -103603942330, -8961684786, -1072179752, 15013114424]], ![![150131144240, -74007938115, -6401646396, -765895644, 10724395416]], ![![107243954160, -52866473020, -4572920955, -547106088, 7660812840]], ![![193750261545, -95510212098, -8261581322, -988419003, 13840262376]], ![![245145930738, -120845978290, -10453111237, -1250614524, 17511635777]]]
  g := ![![![153045, -60814, 30066, -620880, 383592], ![-67404, 546069, 884900, 1817148, -2099928], ![-2341848, -2037876, -5594187, 676120, 5168664], ![8464975, 1978320, 10902288, -18460795, 1352240], ![-3400998, 3544530, 3125005, 20316860, -16679431]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [58, 16, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 61], [64, 35], [0, 1]]
 g := ![![[74, 38, 81], [4, 48], [57, 93], [93, 70], [58, 48], [1]], ![[34, 84, 22], [16, 18], [56, 47], [62, 2], [70, 18], [1]], ![[20, 72, 91], [69, 31], [92, 54], [14, 25], [26, 31], [1]]]
 h' := ![![[73, 61], [32, 70, 9], [78, 10, 40], [38, 78, 53], [0, 84, 78], [39, 81, 40], [0, 1]], ![[64, 35], [44, 34, 24], [83, 84, 42], [79, 21, 12], [38, 34, 14], [86, 50, 42], [73, 61]], ![[0, 1], [54, 90, 64], [46, 3, 15], [85, 95, 32], [11, 76, 5], [89, 63, 15], [64, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44], []]
 b := ![[], [78, 95, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [58, 16, 57, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103042, 112658, -61511, -199229, 154203]
  a := ![-1, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![37313, -31816, -21136, -199229, 154203]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1533650189, -756021000, -65395353, -7823921, 109553999]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![1533650189, -756021000, -65395353, -7823921, 109553999]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![53, 71, 1, 0, 0], ![32, 41, 0, 1, 0], ![68, 70, 0, 0, 1]] where
  M :=![![![1533650189, -756021000, -65395353, -7823921, 109553999], ![1095539990, -540051871, -46714439, -5588865, 78258315], ![782583150, -385779130, -33369240, -3992833, 55902855], ![-111777300, 55100434, 4766844, 571437, -7985666], ![393677970, -194062804, -16788453, -2008419, 28122480]]]
  hmulB := by decide  
  f := ![![![-111644347, 169315224, -6173251, -8998873, -26526789]], ![![-265267890, 401363517, -13546677, -20875545, -62522281]], ![![-261612303, 396021109, -13587216, -20690397, -61763157]], ![![-153258902, 231966795, -7921089, -12103508, -36164947]], ![![-276611018, 418725558, -14365991, -21876523, -65304060]]]
  g := ![![![-22677346, -35679898, -65395353, -7823921, 109553999], ![-16199139, -25487271, -46714439, -5588865, 78258315], ![-11571862, -18206771, -33369240, -3992833, 55902855], ![1652776, 2600229, 4766844, 571437, -7985666], ![-5820549, -9157846, -16788453, -2008419, 28122480]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [8, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 96], [0, 1]]
 g := ![![[87, 85], [31], [53], [18], [3], [80, 1]], ![[0, 12], [31], [53], [18], [3], [63, 96]]]
 h' := ![![[80, 96], [11, 52], [29, 15], [68, 21], [42, 42], [39, 87], [0, 1]], ![[0, 1], [0, 45], [65, 82], [2, 76], [7, 55], [15, 10], [80, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [49, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [8, 17, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5548, -7291, 2289, 6252, -3696]
  a := ![3, -3, 0, -7, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-665, -1726, 2289, 6252, -3696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-52107, -196750, 95898, -620880, 383592]] ![![1533650189, -756021000, -65395353, -7823921, 109553999]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-1234619783, 2048283622, -976211395, -821724345, 816940887]]]
 hmul := by decide  
 g := ![![![![-12728039, 21116326, -10064035, -8471385, 8422071]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2890428081, -1424851731, -123248902, -14745551, 206473437]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![2890428081, -1424851731, -123248902, -14745551, 206473437]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![35, 21, 1, 0, 0], ![19, 39, 0, 1, 0], ![81, 77, 0, 0, 1]] where
  M :=![![![2890428081, -1424851731, -123248902, -14745551, 206473437], ![2064734370, -1017821671, -88041023, -10533265, 147491233], ![1474912330, -727065792, -62890798, -7524283, 105358173], ![-210665300, 103848559, 8982851, 1074713, -15048566], ![741957610, -365751901, -31637346, -3785103, 53000640]]]
  hmulB := by decide  
  f := ![![![193421, -281197, -3922, 8995, 39365]], ![![393650, -563509, -18559, 13531, 75345]], ![![156335, -225020, -5893, 6041, 30589]], ![![191069, -273789, -8678, 6717, 36720]], ![![459961, -661097, -18477, 17259, 89484]]]
  g := ![![![-91485577, -140198049, -123248902, -14745551, 206473437], ![-65351363, -100148394, -88041023, -10533265, 147491233], ![-46682776, -71539518, -62890798, -7524283, 105358173], ![6667814, 10218163, 8982851, 1074713, -15048566], ![-23483863, -35988098, -31637346, -3785103, 53000640]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [40, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 100], [0, 1]]
 g := ![![[68, 88], [49], [24, 100], [33], [81], [7, 1]], ![[78, 13], [49], [17, 1], [33], [81], [14, 100]]]
 h' := ![![[7, 100], [35, 47], [50, 94], [47, 10], [16, 72], [23, 9], [0, 1]], ![[0, 1], [61, 54], [1, 7], [16, 91], [15, 29], [86, 92], [7, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [70, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [40, 94, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17675, -30316, 10838, 6280, -3600]
  a := ![1, -4, -3, -5, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1875, -2234, 10838, 6280, -3600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, -1214, 579, 361, -401]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![701, -1214, 579, 361, -401]] 
 ![![101, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![701, -1214, 579, 361, -401], ![-4010, 7959, -3803, 35, 1043], ![10430, -23862, 11422, -6633, 1183], ![700, 9224, -4474, 21963, -13266], ![-31210, 58334, -27851, -7203, 12570]]]
  hmulB := by decide  
  f := ![![![293081, -159154, -10323, 53, 23583]], ![![57469, -31475, -1986, 38, 4672]], ![![127133, -69928, -4353, 114, 10388]], ![![218195, -119270, -7579, 118, 17695]], ![![74455, -41612, -2462, 132, 6199]]]
  g := ![![![-180, -1214, 579, 361, -401], ![-202, 7959, -3803, 35, 1043], ![4362, -23862, 11422, -6633, 1183], ![-12849, 9224, -4474, 21963, -13266], ![2812, 58334, -27851, -7203, 12570]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2972523421, -1465321377, -126749421, -15164324, 212337856]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![2972523421, -1465321377, -126749421, -15164324, 212337856]] 
 ![![101, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![2972523421, -1465321377, -126749421, -15164324, 212337856], ![2123378560, -1046731519, -90541482, -10832338, 151680560], ![1516805600, -747719742, -64676743, -7737728, 108351208], ![-216646760, 106795059, 9238221, 1105453, -15475456], ![763034020, -376144923, -32535537, -3892270, 54506803]]]
  hmulB := by decide  
  f := ![![![-3045159, 5652237, -2698359, -784394, 1275064]], ![![-537058, 968933, -462378, -196134, 259296]], ![![-817559, 1677111, -801718, 119786, 145568]], ![![-837169, 1266672, -602778, -810191, 704624]], ![![-1325218, 2341869, -1117209, -585444, 700259]]]
  g := ![![![204222128, -1465321377, -126749421, -15164324, 212337856], ![145883098, -1046731519, -90541482, -10832338, 151680560], ![104209579, -747719742, -64676743, -7737728, 108351208], ![-14884290, 106795059, 9238221, 1105453, -15475456], ![52423027, -376144923, -32535537, -3892270, 54506803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2

def I101N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![967381, -476843, -41253, -4938, 69098]] i)))

def SI101N3: IdealEqSpanCertificate' Table ![![967381, -476843, -41253, -4938, 69098]] 
 ![![101, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![967381, -476843, -41253, -4938, 69098], ![690980, -340543, -29472, -3532, 49346], ![493460, -243062, -21061, -2534, 35218], ![-70640, 34957, 2999, 349, -5068], ![248120, -122097, -10601, -1284, 17689]]]
  hmulB := by decide  
  f := ![![![-399, -37, 13, -1724, 1142]], ![![-41, -216, 101, -620, 384]], ![![-945, 1115, -538, -1578, 1200]], ![![839, -2084, 996, -877, 302]], ![![225, -880, 414, -910, 491]]]
  g := ![![![175285, -476843, -41253, -4938, 69098], ![125195, -340543, -29472, -3532, 49346], ![89389, -243062, -21061, -2534, 35218], ![-12819, 34957, 2999, 349, -5068], ![44929, -122097, -10601, -1284, 17689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N3 : Nat.card (O ⧸ I101N3) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N3)

lemma isPrimeI101N3 : Ideal.IsPrime I101N3 := prime_ideal_of_norm_prime hp101.out _ NI101N3
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![2890428081, -1424851731, -123248902, -14745551, 206473437]] ![![701, -1214, 579, 361, -401]]
  ![![1623761, -806305, -65465, -9702, 115676]] where
 M := ![![![1623761, -806305, -65465, -9702, 115676]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![1623761, -806305, -65465, -9702, 115676]] ![![2972523421, -1465321377, -126749421, -15164324, 212337856]]
  ![![3105645804344621, -1530944439876938, -132425863966030, -15843486577480, 221847195451836]] where
 M := ![![![3105645804344621, -1530944439876938, -132425863966030, -15843486577480, 221847195451836]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N2 : IdealMulLeCertificate' Table 
  ![![3105645804344621, -1530944439876938, -132425863966030, -15843486577480, 221847195451836]] ![![967381, -476843, -41253, -4938, 69098]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![1937307797981202760081, -955006072328150618761, -82607507448817751503, -9883197256694171406, 138388705211603790414]]]
 hmul := by decide  
 g := ![![![![19181265326546561981, -9455505666615352661, -817896113354631203, -97853438185090806, 1370185200114889014]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2, I101N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
    exact isPrimeI101N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1 ⊙ MulI101N2)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-661, -371, 98, 63, 67]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-661, -371, 98, 63, 67]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![67, 99, 3, 24, 1]] where
  M :=![![![-661, -371, 98, 63, 67], ![670, -1997, 133, 137, 319], ![3190, -5528, 232, 311, 867], ![2740, -4033, 115, 199, 622], ![3890, -6217, 208, 325, 962]]]
  hmulB := by decide  
  f := ![![![-3, 5, -2, -1, 1]], ![![10, -21, 11, -1, -3]], ![![-30, 68, -30, 21, -7]], ![![-20, 7, -1, -65, 42]], ![![3, -15, 9, -16, 7]]]
  g := ![![![-50, -68, -1, -15, 67], ![-201, -326, -8, -73, 319], ![-533, -887, -23, -199, 867], ![-378, -637, -17, -143, 622], ![-588, -985, -26, -221, 962]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [4, 1, 5, 97, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 85, 97, 50], [102, 60, 41, 94], [35, 60, 68, 62], [0, 1]]
 g := ![![[7, 70, 72, 76], [7, 27, 79, 32], [72, 85, 44, 91], [0, 94, 26], [31, 6, 1], []], ![[48, 18, 21, 9, 70, 19], [47, 93, 29, 76, 85, 29], [0, 67, 73, 100, 3, 14], [40, 10, 36], [25, 25, 33], [68, 89, 23, 77, 68, 61]], ![[48, 61, 32, 15, 102, 90], [97, 86, 59, 57, 94, 3], [48, 100, 100, 40, 64, 67], [39, 0, 91], [86, 47, 49], [45, 33, 2, 89, 27, 95]], ![[89, 60, 94, 98, 47, 77], [31, 67, 1, 80, 6, 5], [8, 5, 88, 97, 20, 75], [4, 65, 7], [100, 60, 32], [14, 65, 84, 77, 56, 89]]]
 h' := ![![[75, 85, 97, 50], [75, 17, 27, 73], [21, 17, 2, 49], [29, 80, 75, 20], [82, 48, 41, 52], [0, 0, 0, 1], [0, 1]], ![[102, 60, 41, 94], [91, 17, 77, 46], [44, 33, 82, 18], [22, 13, 87, 98], [64, 82, 0, 6], [24, 88, 72, 41], [75, 85, 97, 50]], ![[35, 60, 68, 62], [44, 80, 23, 14], [17, 13, 57, 31], [10, 4, 49, 101], [75, 82, 43, 20], [25, 3, 78, 7], [102, 60, 41, 94]], ![[0, 1], [88, 92, 79, 73], [3, 40, 65, 5], [1, 6, 98, 90], [29, 97, 19, 25], [74, 12, 56, 54], [35, 60, 68, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 2, 80], []]
 b := ![[], [], [55, 74, 9, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [4, 1, 5, 97, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-392448, 753340, -383210, -95572, 191220]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-128196, -176480, -9290, -45484, 191220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -5, 2, 1, -1]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![3, -5, 2, 1, -1]] 
 ![![103, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![3, -5, 2, 1, -1], ![-10, 21, -11, 1, 3], ![30, -68, 30, -21, 7], ![20, -7, 1, 65, -42], ![-90, 173, -86, -15, 36]]]
  hmulB := by decide  
  f := ![![![661, 371, -98, -63, -67]], ![![32, 41, -7, -5, -7]], ![![399, 295, -66, -44, -52]], ![![121, 122, -23, -16, -21]], ![![97, 136, -22, -16, -23]]]
  g := ![![![-1, -5, 2, 1, -1], ![5, 21, -11, 1, 3], ![-12, -68, 30, -21, 7], ![-6, -7, 1, 65, -42], ![41, 173, -86, -15, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-661, -371, 98, 63, 67]] ![![3, -5, 2, 1, -1]]
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


lemma PB886I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB886I2 : PrimesBelowBoundCertificateInterval O 61 103 886 where
  m := 9
  g := ![1, 1, 2, 1, 3, 3, 2, 4, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB886I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2, I101N3]
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
    · exact ![1804229351]
    · exact ![28398241, 73]
    · exact ![3077056399]
    · exact ![6889, 6889, 83]
    · exact ![704969, 89, 89]
    · exact ![912673, 9409]
    · exact ![10201, 101, 101, 101]
    · exact ![112550881, 103]
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
      exact NI83N2
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
      exact NI101N3
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I73N1, I83N2, I89N1, I89N2, I101N1, I101N2, I101N3, I103N1]
  Il := ![[], [], [I73N1], [], [I83N2], [I89N1, I89N2], [], [I101N1, I101N2, I101N3], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
