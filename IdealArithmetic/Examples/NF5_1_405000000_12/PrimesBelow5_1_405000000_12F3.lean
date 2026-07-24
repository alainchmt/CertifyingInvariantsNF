
import IdealArithmetic.Examples.NF5_1_405000000_12.RI5_1_405000000_12
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -30, 58, -38, -85]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-2, -30, 58, -38, -85]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![23, 2, 1, 0, 0], ![61, 8, 0, 1, 0], ![103, 85, 0, 0, 1]] where
  M :=![![![-2, -30, 58, -38, -85], ![-510, -275, 16, 720, 18], ![54, 500, -995, 664, 1422], ![4521, 2464, -172, -6379, -103], ![-2133, -3024, 4002, 92, -5574]]]
  hmulB := by decide  
  f := ![![![40622, 80924, 60474, 15400, 14785]], ![![88710, 176251, 131048, 33468, 32030]], ![![11288, 22478, 16783, 4276, 4103]], ![![30355, 60434, 45110, 11495, 11028]], ![![109633, 218031, 162408, 41434, 39699]]]
  g := ![![![91, 69, 58, -38, -85], ![-436, -71, 16, 720, 18], ![-1533, -1156, -995, 664, 1422], ![3815, 585, -172, -6379, -103], ![4433, 4318, 4002, 92, -5574]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [15, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 106], [0, 1]]
 g := ![![[82, 105], [9, 19], [76], [35, 1], [37], [54, 1]], ![[81, 2], [72, 88], [76], [89, 106], [37], [1, 106]]]
 h' := ![![[54, 106], [79, 31], [30, 74], [10, 66], [63, 106], [46, 12], [0, 1]], ![[0, 1], [41, 76], [67, 33], [43, 41], [9, 1], [52, 95], [54, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [47, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [15, 53, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2382, 797, -4736, 6810, 6703]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9339, -5738, -4736, 6810, 6703]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, -20, 36, 2, 9]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-46, -20, 36, 2, 9]] 
 ![![107, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![-46, -20, 36, 2, 9], ![54, 21, -44, 4, -10], ![-30, -6, 17, 0, 18], ![27, 10, 16, -57, -13], ![-75, -46, 56, 32, -30]]]
  hmulB := by decide  
  f := ![![![92170, 183346, 136584, 34844, 33387]], ![![16516, 32855, 24476, 6244, 5983]], ![![15818, 31466, 23441, 5980, 5730]], ![![15059, 29956, 22316, 5693, 5455]], ![![72495, 144208, 107428, 27406, 26260]]]
  g := ![![![-10, -20, 36, 2, 9], ![11, 21, -44, 4, -10], ![-16, -6, 17, 0, 18], ![15, 10, 16, -57, -13], ![17, -46, 56, 32, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 14, 4, 2, 1]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![2, 14, 4, 2, 1]] 
 ![![107, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![2, 14, 4, 2, 1], ![6, 13, 24, 4, 6], ![18, 28, 9, 4, 2], ![3, 14, 12, 3, 3], ![9, 8, -8, 0, -2]]]
  hmulB := by decide  
  f := ![![![-14, 4, 0, 4, 11]], ![![-2, 1, 0, 0, 2]], ![![-2, 0, 1, 0, 0]], ![![-13, 0, 0, 9, 7]], ![![-7, 6, -4, 2, 13]]]
  g := ![![![-5, 14, 4, 2, 1], ![-12, 13, 24, 4, 6], ![-10, 28, 9, 4, 2], ![-8, 14, 12, 3, 3], ![1, 8, -8, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2

def I107N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7359206, -14641924, -10909110, -2782806, -2666693]] i)))

def SI107N3: IdealEqSpanCertificate' Table ![![-7359206, -14641924, -10909110, -2782806, -2666693]] 
 ![![107, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-7359206, -14641924, -10909110, -2782806, -2666693], ![-16000158, -31834007, -23718236, -6050288, -5797838], ![-17393514, -34606242, -25783719, -6577172, -6302738], ![-10908135, -21702892, -16169952, -4124795, -3952687], ![-1171641, -2331106, -1736814, -443044, -424558]]]
  hmulB := by decide  
  f := ![![![-598, -546, 770, 40, -591]], ![![-402, -351, 464, 84, -352]], ![![-348, -296, 423, 24, -275]], ![![89, -78, 380, -513, -359]], ![![-619, -576, 678, 254, -676]]]
  g := ![![![18537520, -14641924, -10909110, -2782806, -2666693], ![40303684, -31834007, -23718236, -6050288, -5797838], ![43813495, -34606242, -25783719, -6577172, -6302738], ![27477111, -21702892, -16169952, -4124795, -3952687], ![2951315, -2331106, -1736814, -443044, -424558]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N3 : Nat.card (O ⧸ I107N3) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N3)

lemma isPrimeI107N3 : Ideal.IsPrime I107N3 := prime_ideal_of_norm_prime hp107.out _ NI107N3
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-2, -30, 58, -38, -85]] ![![-46, -20, 36, 2, 9]]
  ![![2081, 2592, -3134, -678, 4370]] where
 M := ![![![2081, 2592, -3134, -678, 4370]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![2081, 2592, -3134, -678, 4370]] ![![2, 14, 4, 2, 1]]
  ![![598, 546, -770, -40, 591]] where
 M := ![![![598, 546, -770, -40, 591]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N2 : IdealMulLeCertificate' Table 
  ![![598, 546, -770, -40, 591]] ![![-7359206, -14641924, -10909110, -2782806, -2666693]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2, I107N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
    exact isPrimeI107N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1 ⊙ MulI107N2)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [108, 8, 108, 53, 46, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 16, 34, 61, 34], [85, 2, 37, 3, 42], [71, 13, 72, 3, 6], [80, 77, 75, 42, 27], [0, 1]]
 g := ![![[45, 14, 41, 47, 34], [94, 98, 2, 108], [60, 45, 102, 77, 38], [65, 51, 54, 106, 64], [63, 1], []], ![[22, 82, 16, 5, 92, 55, 26, 45], [64, 67, 37, 84], [28, 44, 74, 62, 45, 27, 86, 74], [48, 91, 27, 11, 75, 0, 23, 26], [85, 68, 89, 73], [105, 59, 24, 13, 5, 105, 87, 64]], ![[88, 91, 20, 95, 48, 41, 79, 58], [14, 4, 107, 87], [85, 26, 47, 74, 71, 69, 6, 68], [61, 48, 28, 49, 66, 101, 60, 2], [17, 96, 55, 97], [100, 1, 30, 66, 26, 17, 17, 77]], ![[80, 63, 29, 31, 90, 104, 44, 53], [108, 70, 68, 60], [46, 90, 59, 25, 10, 52, 22, 99], [104, 10, 58, 105, 102, 55, 97, 30], [50, 104, 30, 71], [49, 74, 78, 19, 22, 26, 89, 107]], ![[80, 61, 35, 26, 14, 103, 65, 4], [45, 42, 62, 102], [65, 7, 65, 99, 69, 64, 89, 3], [28, 62, 83, 2, 86, 55, 28, 46], [92, 70, 11, 108], [86, 34, 67, 53, 97, 107, 12, 63]]]
 h' := ![![[45, 16, 34, 61, 34], [97, 52, 95, 58, 90], [60, 84, 54, 72, 33], [65, 12, 98, 69, 93], [63, 42, 55, 41, 101], [0, 0, 0, 1], [0, 1]], ![[85, 2, 37, 3, 42], [63, 15, 90, 59, 77], [33, 40, 25, 44, 53], [36, 88, 14, 84, 61], [94, 100, 86, 104, 42], [106, 63, 95, 78, 20], [45, 16, 34, 61, 34]], ![[71, 13, 72, 3, 6], [95, 13, 83, 39, 99], [9, 37, 75, 44, 95], [51, 27, 108, 47, 11], [8, 17, 104, 48, 35], [10, 41, 5, 72, 73], [85, 2, 37, 3, 42]], ![[80, 77, 75, 42, 27], [0, 63, 57, 71, 38], [1, 47, 97, 17, 96], [38, 57, 47, 101, 17], [66, 25, 20, 43, 21], [4, 81, 53, 89, 92], [71, 13, 72, 3, 6]], ![[0, 1], [33, 75, 2, 100, 23], [36, 10, 76, 41, 50], [108, 34, 60, 26, 36], [108, 34, 62, 91, 19], [4, 33, 65, 87, 33], [80, 77, 75, 42, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 0, 37, 51], [], [], []]
 b := ![[], [76, 16, 31, 40, 53], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [108, 8, 108, 53, 46, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14386223300109000, 10221617828378682, -5562002999432808, -16567751194985928, 6864683528516360]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![131983700001000, 93776310352098, -51027550453512, -151997717385192, 62978747968040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 15386239549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10640558, -21170550, -15773348, -4023622, -3855739]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-10640558, -21170550, -15773348, -4023622, -3855739]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![7, 89, 105, 1, 0], ![81, 1, 16, 0, 1]] where
  M :=![![![-10640558, -21170550, -15773348, -4023622, -3855739], ![-23134434, -46028367, -34293856, -8748028, -8383010], ![-25149030, -50036688, -37280339, -9509844, -9113046], ![-15771921, -31379914, -23379916, -5963985, -5715137], ![-1694043, -3370508, -2511248, -640592, -613866]]]
  hmulB := by decide  
  f := ![![![-106, -72, 88, 44, -67]], ![![-402, -131, -232, 800, 310]], ![![930, 948, -931, -672, 1290]], ![![577, 785, -1027, -55, 1414]], ![![3, 43, -44, -6, 103]]]
  g := ![![![2918935, 3015819, 4145122, -4023622, -3855739], ![6346244, 6556895, 9012188, -8748028, -8383010], ![6898908, 7127898, 9797009, -9509844, -9113046], ![4326567, 4470176, 6144077, -5963985, -5715137], ![464719, 480142, 659936, -640592, -613866]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [97, 60, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 13, 62], [37, 99, 51], [0, 1]]
 g := ![![[17, 107, 109], [97, 32], [42, 77], [5, 49], [99, 104, 109], [1]], ![[41, 79, 111, 25], [47, 53], [66, 106], [13, 77], [39, 97, 105, 28], [0, 77, 87, 11]], ![[23, 60, 68, 85], [9, 87], [27, 2], [105, 30], [71, 77, 82, 88], [60, 99, 20, 102]]]
 h' := ![![[46, 13, 62], [98, 36, 83], [44, 71, 91], [84, 111, 90], [2, 48, 106], [16, 53, 83], [0, 1]], ![[37, 99, 51], [21, 28, 53], [88, 73, 77], [106, 51, 85], [24, 107, 23], [43, 23, 90], [46, 13, 62]], ![[0, 1], [103, 49, 90], [33, 82, 58], [36, 64, 51], [86, 71, 97], [85, 37, 53], [37, 99, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 83], []]
 b := ![[], [70, 105, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [97, 60, 30, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1432124, 531372, 471771, -2411553, -786123]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![725566, 1911024, 2356308, -2411553, -786123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-106, -72, 88, 44, -67]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-106, -72, 88, 44, -67]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![79, 8, 1, 0, 0], ![46, 89, 0, 1, 0], ![4, 11, 0, 0, 1]] where
  M :=![![![-106, -72, 88, 44, -67], ![-402, -131, -232, 800, 310], ![930, 948, -931, -672, 1290], ![4071, 1328, 1736, -7163, -2789], ![-5553, -4346, 3028, 5710, -3884]]]
  hmulB := by decide  
  f := ![![![-10640558, -21170550, -15773348, -4023622, -3855739]], ![![-23134434, -46028367, -34293856, -8748028, -8383010]], ![![-9299368, -18502098, -13785183, -3516462, -3369739]], ![![-22692055, -45148229, -33638116, -8580753, -8222717]], ![![-2643673, -5259865, -3918912, -999676, -957964]]]
  g := ![![![-78, -35, 88, 44, -67], ![-178, -645, -232, 800, 310], ![887, 478, -931, -672, 1290], ![1837, 5802, 1736, -7163, -2789], ![-4353, -4372, 3028, 5710, -3884]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [51, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 112], [0, 1]]
 g := ![![[46, 82], [31], [100], [8], [], [27, 1]], ![[0, 31], [31], [100], [8], [], [54, 112]]]
 h' := ![![[27, 112], [1, 46], [0, 12], [44, 103], [0, 102], [92], [0, 1]], ![[0, 1], [0, 67], [98, 101], [0, 10], [42, 11], [92], [27, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [53, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [51, 86, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19311, 13360, -41653, 63336, 65838]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![836, -53226, -41653, 63336, 65838]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-10640558, -21170550, -15773348, -4023622, -3855739]] ![![-106, -72, 88, 44, -67]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15114988, -30072939, -22406170, -5715588, -5477109]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-15114988, -30072939, -22406170, -5715588, -5477109]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![59, 10, 71, 1, 0], ![35, 54, 52, 0, 1]] where
  M :=![![![-15114988, -30072939, -22406170, -5715588, -5477109], ![-32862654, -65383661, -48714702, -12426644, -11908134], ![-35724402, -71077523, -52957017, -13508810, -12945154], ![-22404135, -44575420, -33211362, -8471889, -8118399], ![-2406405, -4787839, -3567242, -909966, -872000]]]
  hmulB := by decide  
  f := ![![![8, 61, -100, 46, 173]], ![![1038, 519, 30, -1492, -162]], ![![-486, -1201, 2011, -814, -2822]], ![![-257, -638, 1077, -447, -1500]], ![![289, -202, 748, -974, -1093]]]
  g := ![![![4045697, 2542101, 5261498, -5715588, -5477109], ![8796016, 5526945, 11439370, -12426644, -11908134], ![9562014, 6008259, 12435563, -13508810, -12945154], ![5996703, 3768008, 7798815, -8471889, -8118399], ![644107, 404723, 837672, -909966, -872000]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [79, 18, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 51, 18], [81, 75, 109], [0, 1]]
 g := ![![[20, 17, 19], [101, 45, 124], [2, 63, 107], [77, 47, 68], [62, 120, 117], [1]], ![[56, 125, 115, 104], [75, 124, 122, 49], [126, 51, 70, 107], [97, 39, 24, 16], [4, 68, 87, 41], [95, 103, 46, 117]], ![[35, 58, 29, 126], [65, 60, 112, 86], [52, 35, 36, 111], [43, 50, 123, 85], [53, 11, 117, 96], [78, 50, 125, 10]]]
 h' := ![![[71, 51, 18], [22, 33, 20], [96, 109, 39], [13, 85, 19], [55, 90, 103], [48, 109, 25], [0, 1]], ![[81, 75, 109], [32, 104, 62], [117, 86, 61], [28, 60, 34], [126, 84, 74], [13, 61, 27], [71, 51, 18]], ![[0, 1], [44, 117, 45], [117, 59, 27], [106, 109, 74], [36, 80, 77], [7, 84, 75], [81, 75, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 27], []]
 b := ![[], [70, 44, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [79, 18, 102, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11122362, -13805193, 16750617, 3542745, -23149338]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4646319, 9455367, 7629774, 3542745, -23149338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 61, -100, 46, 173]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![8, 61, -100, 46, 173]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![45, 56, 1, 0, 0], ![20, 62, 0, 1, 0], ![78, 108, 0, 0, 1]] where
  M :=![![![8, 61, -100, 46, 173], ![1038, 519, 30, -1492, -162], ![-486, -1201, 2011, -814, -2822], ![-8985, -4544, -402, 13231, 1275], ![5643, 6637, -7696, -2412, 10626]]]
  hmulB := by decide  
  f := ![![![-15114988, -30072939, -22406170, -5715588, -5477109]], ![![-32862654, -65383661, -48714702, -12426644, -11908134]], ![![-20127618, -40046022, -29836677, -7611042, -7293469]], ![![-18599909, -37006466, -27572018, -7033351, -6739881]], ![![-37248363, -74109547, -55216034, -14085066, -13497362]]]
  g := ![![![-78, -125, -100, 46, 173], ![332, 857, 30, -1492, -162], ![1145, 1901, 2011, -814, -2822], ![-2795, -7402, -402, 13231, 1275], ![-3375, -4413, -7696, -2412, 10626]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [69, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 126], [0, 1]]
 g := ![![[51, 81], [78, 94], [20, 99], [109, 76], [8, 11], [37, 1]], ![[0, 46], [0, 33], [0, 28], [0, 51], [34, 116], [74, 126]]]
 h' := ![![[37, 126], [79, 118], [17, 27], [99, 90], [83, 87], [114, 30], [0, 1]], ![[0, 1], [0, 9], [0, 100], [0, 37], [0, 40], [81, 97], [37, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [78, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [69, 90, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21189, 10412, 1304, -32632, -2096]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6131, 17220, 1304, -32632, -2096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-15114988, -30072939, -22406170, -5715588, -5477109]] ![![8, 61, -100, 46, 173]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -4, 0, 12, 12]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-11, -4, 0, 12, 12]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![92, 60, 1, 0, 0], ![113, 49, 0, 1, 0], ![28, 38, 0, 0, 1]] where
  M :=![![![-11, -4, 0, 12, 12], ![72, 49, -32, -72, 24], ![72, -16, 121, -200, -168], ![-540, -380, 200, 629, -244], ![-96, 204, -528, 524, 777]]]
  hmulB := by decide  
  f := ![![![18887, 37468, 27872, 7116, 6812]], ![![40872, 81427, 60704, 15480, 14840]], ![![32324, 64284, 47881, 12216, 11704]], ![![31793, 63201, 47064, 12009, 11504]], ![![15916, 31674, 23600, 6020, 5769]]]
  g := ![![![-13, -8, 0, 12, 12], ![80, 35, -32, -72, 24], ![124, 68, 121, -200, -168], ![-635, -259, 200, 629, -244], ![-248, -178, -528, 524, 777]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [70, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 130], [0, 1]]
 g := ![![[112, 25], [29, 121], [7], [99], [28], [7], [1]], ![[88, 106], [91, 10], [7], [99], [28], [7], [1]]]
 h' := ![![[20, 130], [66, 5], [67, 120], [65, 20], [107, 19], [87, 91], [61, 20], [0, 1]], ![[0, 1], [35, 126], [109, 11], [72, 111], [94, 112], [73, 40], [68, 111], [20, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [22, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [70, 111, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3761, 4993, -9534, 3772, 12331]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![835, -583, -9534, 3772, 12331]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-986, 906, -430, 62, -93]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-986, 906, -430, 62, -93]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![112, 62, 1, 0, 0], ![130, 77, 0, 1, 0], ![2, 62, 0, 0, 1]] where
  M :=![![![-986, 906, -430, 62, -93], ![-558, -1571, 1688, 8, 434], ![1302, 1224, -1579, -40, -418], ![-975, -20, 420, 49, 121], ![1599, 1384, -1878, -56, -498]]]
  hmulB := by decide  
  f := ![![![-178, -132, 82, 196, -103]], ![![-618, -13, -656, 1380, 990]], ![![-422, -102, -251, 796, 394]], ![![-497, -137, -260, 911, 413]], ![![-403, -76, -286, 794, 442]]]
  g := ![![![300, 218, -430, 62, -93], ![-1462, -1021, 1688, 8, 434], ![1406, 978, -1579, -40, -418], ![-417, -285, 420, 49, 121], ![1681, 1168, -1878, -56, -498]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [84, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 130], [0, 1]]
 g := ![![[31, 39], [12, 81], [91], [7], [41], [125], [1]], ![[0, 92], [129, 50], [91], [7], [41], [125], [1]]]
 h' := ![![[16, 130], [40, 63], [16, 9], [113, 22], [96, 20], [93, 98], [47, 16], [0, 1]], ![[0, 1], [0, 68], [29, 122], [72, 109], [23, 111], [89, 33], [41, 115], [16, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [26, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [84, 115, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![909, 495, -318, -1418, 589]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1677, 709, -318, -1418, 589]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-422, -840, -626, -160, -153]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-422, -840, -626, -160, -153]] 
 ![![131, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-422, -840, -626, -160, -153], ![-918, -1827, -1360, -348, -334], ![-1002, -1988, -1479, -372, -362], ![-627, -1242, -936, -229, -215], ![-51, -126, -98, -50, -28]]]
  hmulB := by decide  
  f := ![![![-20566, -12686, 19518, 798, 5237]], ![![-2586, -1619, 2476, 100, 664]], ![![-15866, -9760, 15033, 616, 4034]], ![![-1267, -792, 1212, 49, 325]], ![![-347, -182, 300, 14, 81]]]
  g := ![![![601, -840, -626, -160, -153], ![1306, -1827, -1360, -348, -334], ![1420, -1988, -1479, -372, -362], ![896, -1242, -936, -229, -215], ![95, -126, -98, -50, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-11, -4, 0, 12, 12]] ![![-986, 906, -430, 62, -93]]
  ![![20566, 12686, -19518, -798, -5237]] where
 M := ![![![20566, 12686, -19518, -798, -5237]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![20566, 12686, -19518, -798, -5237]] ![![-422, -840, -626, -160, -153]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1865, -633, 1294, 86, 348]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-1865, -633, 1294, 86, 348]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![47, 134, 36, 53, 1]] where
  M :=![![![-1865, -633, 1294, 86, 348], ![2088, 645, -1438, -24, -352], ![-1056, -227, 669, -54, 304], ![-132, -114, 546, -589, -236], ![-1860, -747, 1018, 730, -25]]]
  hmulB := by decide  
  f := ![![![5951, 11839, 8820, 2250, 2156]], ![![12936, 25739, 19178, 4892, 4688]], ![![14064, 27981, 20847, 5318, 5096]], ![![8820, 17548, 13074, 3335, 3196]], ![![21809, 43392, 32330, 8247, 7903]]]
  g := ![![![-133, -345, -82, -134, 348], ![136, 349, 82, 136, -352], ![-112, -299, -75, -118, 304], ![80, 230, 66, 87, -236], ![-5, 19, 14, 15, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [3, 114, 42, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 132, 1, 14], [10, 1, 30, 69], [43, 3, 106, 54], [0, 1]]
 g := ![![[114, 20, 8, 81], [95, 86, 60], [102, 120, 107], [110, 97, 34, 63], [59, 77, 88], [1], []], ![[61, 88, 87, 93, 15, 88], [82, 77, 28], [9, 14, 100], [79, 38, 126, 72, 92, 76], [113, 88, 17], [73, 0, 14], [100, 102, 59]], ![[77, 87, 22, 15, 91, 87], [62, 26, 9], [127, 75, 56], [83, 59, 113, 74, 95, 44], [131, 79, 59], [124, 133, 119], [120, 129, 103]], ![[4, 129, 131, 65, 110, 46], [120, 129, 49], [51, 132, 28], [99, 127, 58, 71, 50, 124], [11, 82, 50], [19, 131, 118], [6, 40, 39]]]
 h' := ![![[69, 132, 1, 14], [6, 123, 31, 128], [90, 60, 54, 103], [81, 49, 95, 92], [106, 29, 84, 36], [134, 23, 95, 122], [0, 0, 1], [0, 1]], ![[10, 1, 30, 69], [89, 52, 68, 105], [91, 7, 76, 24], [114, 63, 62, 10], [90, 36, 100, 132], [93, 9, 43, 47], [77, 71, 50, 98], [69, 132, 1, 14]], ![[43, 3, 106, 54], [0, 88, 120, 96], [130, 90, 4, 3], [127, 7, 60, 59], [32, 55, 80, 122], [98, 135, 83, 123], [14, 64, 0, 16], [10, 1, 30, 69]], ![[0, 1], [129, 11, 55, 82], [107, 117, 3, 7], [73, 18, 57, 113], [85, 17, 10, 121], [114, 107, 53, 119], [50, 2, 86, 23], [43, 3, 106, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [132, 75, 123], []]
 b := ![[], [], [29, 103, 97, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [3, 114, 42, 15, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13794206277, 7857602376, -1237492014, -18934919286, 710070732]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-142913271, -637166976, -195620718, -412909986, 710070732]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5951, 11839, 8820, 2250, 2156]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![5951, 11839, 8820, 2250, 2156]] 
 ![![137, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![5951, 11839, 8820, 2250, 2156], ![12936, 25739, 19178, 4892, 4688], ![14064, 27981, 20847, 5318, 5096], ![8820, 17548, 13074, 3335, 3196], ![948, 1885, 1404, 358, 343]]]
  hmulB := by decide  
  f := ![![![-1865, -633, 1294, 86, 348]], ![![-856, -291, 594, 40, 160]], ![![-103, -34, 71, 4, 20]], ![![-246, -84, 174, 7, 44]], ![![-245, -84, 168, 16, 43]]]
  g := ![![![-6501, 11839, 8820, 2250, 2156], ![-14134, 25739, 19178, 4892, 4688], ![-15365, 27981, 20847, 5318, 5096], ![-9636, 17548, 13074, 3335, 3196], ![-1035, 1885, 1404, 358, 343]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-1865, -633, 1294, 86, 348]] ![![5951, 11839, 8820, 2250, 2156]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139808, -75480, -257106, -37084, -67275]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139808, -75480, -257106, -37084, -67275]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![112, 96, 122, 1, 0], ![62, 132, 120, 0, 1]] where
  M :=![![![139808, -75480, -257106, -37084, -67275], ![-403650, -393291, -76792, -50180, -13786], ![-41358, -311080, -343111, -71828, -86574], ![-57897, -197278, -200856, -43553, -50189], ![134811, 15638, -109594, -10874, -29758]]]
  hmulB := by decide  
  f := ![![![26396, 32090, -38306, -9478, 52887]], ![![317322, 127795, 83136, -518664, -143686]], ![![-431058, -533964, 646459, 139216, -893642]], ![![-158341, -362868, 588806, -210427, -832021]], ![![-38075, -306584, 603774, -394688, -862762]]]
  g := ![![![60894, 88956, 88778, -37084, -67275], ![43678, 44919, 55392, -50180, -13786], ![96194, 129584, 135315, -71828, -86574], ![57063, 76322, 80110, -43553, -50189], ![23005, 35882, 34446, -10874, -29758]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [34, 92, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 131, 79], [90, 7, 60], [0, 1]]
 g := ![![[88, 122, 46], [90, 41, 125], [15, 65], [108, 115, 31], [117, 28], [17, 1], []], ![[126, 94, 32, 30], [33, 38, 125, 42], [10, 5], [70, 110, 77, 100], [34, 13], [54, 49], [27, 125]], ![[72, 117, 22, 21], [109, 5, 129, 21], [113, 77], [38, 86, 90, 70], [51, 11], [19, 64], [46, 125]]]
 h' := ![![[66, 131, 79], [137, 111, 121], [74, 117, 60], [81, 137, 64], [120, 77, 93], [117, 70, 58], [0, 0, 1], [0, 1]], ![[90, 7, 60], [67, 54, 25], [16, 94, 72], [83, 49, 12], [93, 77, 62], [89, 65, 98], [102, 133, 7], [66, 131, 79]], ![[0, 1], [65, 113, 132], [81, 67, 7], [93, 92, 63], [101, 124, 123], [58, 4, 122], [3, 6, 131], [90, 7, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 95], []]
 b := ![[], [72, 118, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [34, 92, 122, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1806876, 3292193, -4919029, 1067016, 6921566]
  a := ![1, 5, -3, 4, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3934072, -7286245, -6947359, 1067016, 6921566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1588039, 3159572, 2354070, 600500, 575444]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![1588039, 3159572, 2354070, 600500, 575444]] 
 ![![139, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![99, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![1588039, 3159572, 2354070, 600500, 575444], ![3452664, 6869441, 5118144, 1305588, 1251112], ![3753336, 7467660, 5563853, 1419284, 1360064], ![2353860, 4683254, 3489304, 890087, 852948], ![252828, 503028, 374786, 95604, 91615]]]
  hmulB := by decide  
  f := ![![![19597, 4748, -11902, -852, -3308]], ![![11700, 2841, -7112, -508, -1976]], ![![12194, 2948, -7399, -532, -2056]], ![![14001, 3394, -8502, -613, -2368]], ![![3873, 928, -2348, -160, -653]]]
  g := ![![![-3893903, 3159572, 2354070, 600500, 575444], ![-8466000, 6869441, 5118144, 1305588, 1251112], ![-9203254, 7467660, 5563853, 1419284, 1360064], ![-5771711, 4683254, 3489304, 890087, 852948], ![-619939, 503028, 374786, 95604, 91615]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![413416, 218294, -844, -594466, -30689]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![413416, 218294, -844, -594466, -30689]] 
 ![![139, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![413416, 218294, -844, -594466, -30689], ![-184134, -868427, 1625520, -945108, -2316486], ![-6949458, -3699144, 76681, 9946356, 426270], ![1370877, 7583586, -14458260, 8790511, 20624685], ![26868927, 11384772, 5851248, -43032768, -10462796]]]
  hmulB := by decide  
  f := ![![![1107891275764, 2204267156500, 1642310757664, 418937255752, 401456996549]], ![![726698313110, 1445843341461, 1077239692328, 274793207312, 263327393689]], ![![26808606946, 53338565800, 39740418977, 10137388432, 9714403421]], ![![410336172917, 816407321564, 608272242704, 155164242165, 148689976303]], ![![1268955033, 2524720590, 1881067716, 479841798, 459820282]]]
  g := ![![![77046, 218294, -844, -594466, -30689], ![882991, -868427, 1625520, -945108, -2316486], ![-1259857, -3699144, 76681, 9946356, 426270], ![-7903853, 7583586, -14458260, 8790511, 20624685], ![8341089, 11384772, 5851248, -43032768, -10462796]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139808, -75480, -257106, -37084, -67275]] ![![1588039, 3159572, 2354070, 600500, 575444]]
  ![![-1107891275764, -2204267156500, -1642310757664, -418937255752, -401456996549]] where
 M := ![![![-1107891275764, -2204267156500, -1642310757664, -418937255752, -401456996549]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-1107891275764, -2204267156500, -1642310757664, -418937255752, -401456996549]] ![![413416, 218294, -844, -594466, -30689]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] where
  M :=![![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [135, 54, 106, 29, 101, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 74, 12, 13, 135], [49, 41, 105, 93, 61], [34, 73, 37, 90, 66], [10, 109, 144, 102, 36], [0, 1]]
 g := ![![[50, 100, 80, 143, 6], [80, 115, 75, 123], [65, 0, 97, 15, 80], [93, 55, 56, 127], [97, 124, 40, 48, 1], [], []], ![[130, 134, 113, 112, 80, 14, 88, 139], [12, 45, 115, 116], [25, 63, 105, 106, 26, 129, 85, 101], [112, 94, 45, 140], [52, 124, 128, 84, 105, 55, 124, 78], [78, 134, 139, 96], [117, 35, 104, 47]], ![[89, 12, 79, 87, 68, 12, 10, 20], [91, 43, 146, 29], [131, 134, 114, 53, 138, 36, 87, 6], [145, 140, 53, 31], [35, 136, 9, 126, 25, 89, 43, 116], [81, 86, 140, 110], [28, 5, 128, 145]], ![[132, 83, 148, 138, 76, 113, 104, 141], [78, 51, 87, 120], [119, 58, 71, 72, 24, 90, 83, 93], [108, 34, 135, 85], [52, 88, 71, 148, 129, 96, 80, 66], [5, 12, 10, 22], [78, 97, 1, 35]], ![[31, 143, 87, 50, 111, 148, 137, 47], [54, 133, 108, 96], [107, 55, 49, 99, 119, 112, 78, 16], [124, 140, 84, 143], [122, 28, 123, 88, 147, 55, 87, 39], [117, 107, 119, 42], [85, 27, 118, 104]]]
 h' := ![![[104, 74, 12, 13, 135], [35, 120, 87, 139, 119], [16, 135, 55, 127, 102], [101, 52, 79, 128, 123], [17, 74, 121, 137, 53], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[49, 41, 105, 93, 61], [80, 114, 78, 131, 52], [106, 144, 105, 90, 50], [72, 50, 114, 15, 116], [128, 99, 94, 78, 132], [19, 3, 24, 11, 127], [87, 28, 53, 18, 29], [104, 74, 12, 13, 135]], ![[34, 73, 37, 90, 66], [46, 72, 66, 2, 69], [115, 67, 44, 136, 25], [57, 68, 96, 4, 70], [34, 118, 9, 37, 39], [45, 118, 47, 106, 67], [111, 43, 95, 27, 109], [49, 41, 105, 93, 61]], ![[10, 109, 144, 102, 36], [117, 129, 6, 138, 6], [98, 74, 51, 38, 92], [89, 127, 30, 127, 38], [31, 62, 79, 140, 95], [90, 75, 77, 76, 148], [13, 24, 15, 10, 52], [34, 73, 37, 90, 66]], ![[0, 1], [33, 12, 61, 37, 52], [97, 27, 43, 56, 29], [128, 1, 128, 24, 100], [110, 94, 144, 55, 128], [67, 102, 1, 105, 104], [98, 54, 134, 94, 108], [10, 109, 144, 102, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 96, 16, 11], [], [], []]
 b := ![[], [35, 29, 58, 120, 54], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [135, 54, 106, 29, 101, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![533657655, 514307323, -491079266, -402526331, 662932886]
  a := ![4, 0, 0, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3581595, 3451727, -3295834, -2701519, 4449214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 73439775749 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-996481, -399464, -264966, 1631652, 456800]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-996481, -399464, -264966, 1631652, 456800]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![108, 134, 1, 0, 0], ![24, 143, 0, 1, 0], ![21, 85, 0, 0, 1]] where
  M :=![![![-996481, -399464, -264966, 1631652, 456800], ![2740800, 3372257, -4062232, -921028, 5613008], ![16839024, 6837768, 4293285, -27435292, -7455064], ![-23735592, -29737862, 36304176, 7138763, -50222024], ![-56416128, -14353304, -32412642, 105339004, 50826751]]]
  hmulB := by decide  
  f := ![![![-101813719, -202525440, -150832930, -38484788, -36869712]], ![![-221218272, -440225361, -328081304, -83677740, -80199728]], ![![-270726684, -538685914, -401386747, -102384996, -98118200]], ![![-226679472, -451079415, -336153928, -85739057, -82172840]], ![![-138794037, -276188451, -205817064, -52496116, -50311921]]]
  g := ![![![-139951, -1569856, -264966, 1631652, 456800], ![2289360, 1339819, -4062232, -921028, 5613008], ![2438196, 26413674, 4293285, -27435292, -7455064], ![-20273208, -10903765, 36304176, 7138763, -50222024], ![-1002309, -99700733, -32412642, 105339004, 50826751]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [34, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 150], [0, 1]]
 g := ![![[17, 40], [101, 8], [3, 144], [118], [98, 95], [72], [1]], ![[0, 111], [7, 143], [123, 7], [118], [1, 56], [72], [1]]]
 h' := ![![[26, 150], [39, 74], [49, 59], [14, 12], [141, 32], [67, 104], [117, 26], [0, 1]], ![[0, 1], [0, 77], [73, 92], [24, 139], [67, 119], [53, 47], [38, 125], [26, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [127, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [34, 125, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4366, 35780, -73950, 49106, 102014]
  a := ![7, -21, -1, -21, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![30928, -38068, -73950, 49106, 102014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![917, -571, 168, -52, 28]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![917, -571, 168, -52, 28]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![91, 76, 1, 0, 0], ![30, 8, 0, 1, 0], ![44, 40, 0, 0, 1]] where
  M :=![![![917, -571, 168, -52, 28], ![168, 1065, -1038, 8, -264], ![-792, -823, 1057, 26, 280], ![756, 46, -330, -41, -96], ![-1002, -953, 1256, 36, 327]]]
  hmulB := by decide  
  f := ![![![-63637, -126613, -94334, -24064, -23060]], ![![-138360, -275279, -205098, -52316, -50136]], ![![-108985, -216836, -161555, -41210, -39492]], ![![-20598, -40982, -30534, -7789, -7464]], ![![-55262, -109949, -81918, -20896, -20025]]]
  g := ![![![-93, -93, 168, -52, 28], ![702, 599, -1038, 8, -264], ![-729, -613, 1057, 26, 280], ![240, 194, -330, -41, -96], ![-866, -727, 1256, 36, 327]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [75, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 150], [0, 1]]
 g := ![![[119, 94], [146, 42], [87, 97], [59], [37, 17], [105], [1]], ![[125, 57], [78, 109], [45, 54], [59], [67, 134], [105], [1]]]
 h' := ![![[135, 150], [73, 68], [119, 58], [32, 61], [94, 19], [15, 116], [76, 135], [0, 1]], ![[0, 1], [42, 83], [97, 93], [113, 90], [92, 132], [122, 35], [30, 16], [135, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [69, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [75, 16, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-583, 2871, -6729, 6015, 9672]
  a := ![1, -6, 1, -7, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![38, 525, -6729, 6015, 9672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-405232317205, -806252657411, -600706410320, -153234273144, -146840535588]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-405232317205, -806252657411, -600706410320, -153234273144, -146840535588]] 
 ![![151, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-405232317205, -806252657411, -600706410320, -153234273144, -146840535588], ![-881043213528, -1752928880577, -1306036768534, -333157082224, -319256021400], ![-957768064200, -1905581105355, -1419771798353, -362169765158, -347058143048], ![-600652822380, -1195062470718, -890392955930, -227130450207, -217653376568], ![-64516078998, -128361579137, -95637047200, -24396066296, -23378134463]]]
  hmulB := by decide  
  f := ![![![-4785355, -1354101, -2461402, 8720748, 3898444]], ![![-890901, -150962, -671364, 1782224, 1031356]], ![![-3740163, -1054456, -1931989, 6822106, 3058716]], ![![-2022909, -1471995, 855160, 2275241, -1070052]], ![![-3322718, -572681, -2483602, 6631884, 3817409]]]
  g := ![![![786340798010, -806252657411, -600706410320, -153234273144, -146840535588], ![1709637149157, -1752928880577, -1306036768534, -333157082224, -319256021400], ![1858519352776, -1905581105355, -1419771798353, -362169765158, -347058143048], ![1165548253669, -1195062470718, -890392955930, -227130450207, -217653376568], ![125191459117, -128361579137, -95637047200, -24396066296, -23378134463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-996481, -399464, -264966, 1631652, 456800]] ![![917, -571, 168, -52, 28]]
  ![![4785355, 1354101, 2461402, -8720748, -3898444]] where
 M := ![![![4785355, 1354101, 2461402, -8720748, -3898444]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![4785355, 1354101, 2461402, -8720748, -3898444]] ![![-405232317205, -806252657411, -600706410320, -153234273144, -146840535588]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB1253I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1253I3 : PrimesBelowBoundCertificateInterval O 103 151 1253 where
  m := 9
  g := ![4, 1, 2, 2, 3, 2, 3, 1, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1253I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2, I107N3]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![11449, 107, 107, 107]
    · exact ![15386239549]
    · exact ![1442897, 12769]
    · exact ![2048383, 16129]
    · exact ![17161, 17161, 131]
    · exact ![352275361, 137]
    · exact ![2685619, 139, 139]
    · exact ![73439775749]
    · exact ![22801, 22801, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
      exact NI107N3
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I107N1, I107N2, I107N3, I131N2, I137N1, I139N1, I139N2, I151N2]
  Il := ![[I107N1, I107N2, I107N3], [], [], [], [I131N2], [I137N1], [I139N1, I139N2], [], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
