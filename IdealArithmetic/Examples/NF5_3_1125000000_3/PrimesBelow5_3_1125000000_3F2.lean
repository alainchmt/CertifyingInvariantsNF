
import IdealArithmetic.Examples.NF5_3_1125000000_3.RI5_3_1125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5356, 12758, 7231, -4091, -10404]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![5356, 12758, 7231, -4091, -10404]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![19, 29, 1, 1, 0], ![35, 3, 60, 0, 1]] where
  M :=![![![5356, 12758, 7231, -4091, -10404], ![6214, 14743, 8314, -4642, -11920], ![7476, 17296, 9471, -4876, -13296], ![-4373, -10686, -6229, 3774, 9134], ![-1455, -3842, -2419, 1719, 3721]]]
  hmulB := by decide  
  f := ![![![52, 10, -45, -25, 78]], ![![-214, -195, 266, 34, -356]], ![![1020, 896, -1043, 412, 984]], ![![-65, -69, 87, 9, -114]], ![![939, 805, -952, 364, 909]]]
  g := ![![![6675, 2427, 9486, -4091, -10404], ![7636, 2763, 10868, -4642, -11920], ![8440, 2964, 12121, -4876, -13296], ![-5907, -2202, -8329, 3774, 9134], ![-2453, -968, -3394, 1719, 3721]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [11, 7, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 56, 20], [49, 10, 47], [0, 1]]
 g := ![![[32, 4, 10], [26, 39, 55], [30, 24], [40, 10], [32, 1], []], ![[6, 21, 29, 30], [11, 47, 1, 34], [64, 49], [32, 40], [7, 33], [32, 65]], ![[50, 30, 44, 29], [24, 5, 20, 23], [29, 64], [43, 10], [18, 54], [5, 65]]]
 h' := ![![[50, 56, 20], [49, 65, 12], [26, 14, 51], [50, 29, 15], [50, 33, 12], [0, 0, 1], [0, 1]], ![[49, 10, 47], [64, 9, 13], [59, 42, 53], [19, 50, 60], [6, 26, 43], [4, 38, 10], [50, 56, 20]], ![[0, 1], [30, 60, 42], [26, 11, 30], [12, 55, 59], [4, 8, 12], [1, 29, 56], [49, 10, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 41], []]
 b := ![[], [29, 31, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [11, 7, 35, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6313721040, -6338053204, 2363776862, -8913594938, -8934640032]
  a := ![-176, -194, 145, -109, -324]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7100850506, 4163583882, 8169489160, -8913594938, -8934640032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -3, 1, -4, -4]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-3, -3, 1, -4, -4]] 
 ![![67, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![-3, -3, 1, -4, -4], ![-18, -18, 5, -28, -24], ![-130, -129, 46, -188, -176], ![-60, -60, 20, -89, -84], ![-90, -89, 31, -132, -121]]]
  hmulB := by decide  
  f := ![![![-673, 179, 161, -28, -228]], ![![-205, 53, 48, -8, -68]], ![![-286, 75, 68, -12, -96]], ![![-600, 160, 144, -25, -204]], ![![-664, 177, 159, -28, -225]]]
  g := ![![![8, -3, 1, -4, -4], ![52, -18, 5, -28, -24], ![361, -129, 46, -188, -176], ![172, -60, 20, -89, -84], ![251, -89, 31, -132, -121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-398, 159, 104, -35, -146]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-398, 159, 104, -35, -146]] 
 ![![67, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-398, 159, 104, -35, -146], ![192, -164, 7, 10, 12], ![106, 279, -180, 200, 56], ![105, -6, -89, -96, 192], ![63, 77, -28, 171, -97]]]
  hmulB := by decide  
  f := ![![![-3922, -7095, -2572, -649, 2256]], ![![-2192, -3856, -1305, -540, 1000]], ![![-4058, -6483, -1622, -2062, 288]], ![![-555, -559, 175, -813, -742]], ![![-981, -1151, 112, -1173, -923]]]
  g := ![![![-155, 159, 104, -35, -146], ![80, -164, 7, 10, 12], ![-12, 279, -180, 200, 56], ![61, -6, -89, -96, 192], ![-14, 77, -28, 171, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![5356, 12758, 7231, -4091, -10404]] ![![-3, -3, 1, -4, -4]]
  ![![-3922, -7095, -2572, -649, 2256]] where
 M := ![![![-3922, -7095, -2572, -649, 2256]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-3922, -7095, -2572, -649, 2256]] ![![-398, 159, 104, -35, -146]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3692, 8797, 4988, -2823, -7188]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![3692, 8797, 4988, -2823, -7188]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 38, 24, 70, 1]] where
  M :=![![![3692, 8797, 4988, -2823, -7188], ![4260, 10152, 5713, -3294, -8208], ![4686, 11441, 6912, -3696, -9936], ![-3053, -7418, -4345, 2456, 6206], ![-1349, -2993, -1412, 899, 2083]]]
  hmulB := by decide  
  f := ![![![-260, 103, 76, -9, -102]], ![![216, -18, -65, 78, 132]], ![![186, 335, -66, 432, 360]], ![![211, 118, -67, 218, 224]], ![![389, 223, -124, 407, 417]]]
  g := ![![![52, 3971, 2500, 7047, -7188], ![60, 4536, 2855, 8046, -8208], ![66, 5479, 3456, 9744, -9936], ![-43, -3426, -2159, -6084, 6206], ![-19, -1157, -724, -2041, 2083]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [38, 52, 54, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 23, 31, 45], [44, 27, 45, 20], [23, 20, 66, 6], [0, 1]]
 g := ![![[47, 22, 5, 32], [18, 27, 60, 32], [15, 15, 15, 54], [49, 20, 12], [1], []], ![[61, 38, 56, 2], [19, 64, 63, 21, 15, 32], [19, 23, 25, 32, 26, 10], [17, 35, 8], [1, 45, 58], [26, 34, 37]], ![[3, 69, 34, 1, 54, 12], [3, 13, 16, 4, 8, 36], [29, 36, 46, 12, 8, 19], [41, 9, 8], [65, 18, 9], [59, 60, 45]], ![[68, 70, 18, 13, 61, 20], [25, 17, 50, 39, 34, 27], [3, 21, 58, 24], [0, 57, 12], [48, 64, 57], [8, 39, 36]]]
 h' := ![![[60, 23, 31, 45], [26, 30, 62, 48], [69, 63, 50, 48], [8, 5, 39, 57], [33, 19, 17, 56], [0, 0, 1], [0, 1]], ![[44, 27, 45, 20], [26, 46, 42], [28, 52, 43, 45], [30, 2, 64, 67], [45, 12, 55, 24], [56, 45, 26, 49], [60, 23, 31, 45]], ![[23, 20, 66, 6], [26, 37, 33, 10], [10, 27, 49, 67], [8, 29, 41, 18], [2, 40, 55, 47], [49, 10, 10, 68], [44, 27, 45, 20]], ![[0, 1], [61, 29, 5, 13], [9, 0, 0, 53], [8, 35, 69], [24, 0, 15, 15], [12, 16, 34, 25], [23, 20, 66, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [41, 13, 26], []]
 b := ![[], [], [34, 59, 52, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [38, 52, 54, 15, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2082197192033199668, 2068824077226204748, -673418339356286304, 3117718857263933932, 2835741391410080402]
  a := ![-2547, -2778, 1994, -1752, -4457]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![29326721014552108, -1488582377413476768, -968045235678848112, -2751889838611854848, 2835741391410080402]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![260, -103, -76, 9, 102]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![260, -103, -76, 9, 102]] 
 ![![71, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![260, -103, -76, 9, 102], ![-216, 18, 65, -78, -132], ![-186, -335, 66, -432, -360], ![-211, -118, 67, -218, -224], ![-177, -217, 60, -305, -271]]]
  hmulB := by decide  
  f := ![![![-3692, -8797, -4988, 2823, 7188]], ![![-580, -1382, -783, 444, 1128]], ![![-2250, -5365, -3048, 1722, 4392]], ![![-2869, -6834, -3873, 2192, 5582]], ![![-2009, -4790, -2720, 1538, 3919]]]
  g := ![![![0, -103, -76, 9, 102], ![90, 18, 65, -78, -132], ![544, -335, 66, -432, -360], ![269, -118, 67, -218, -224], ![382, -217, 60, -305, -271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![3692, 8797, 4988, -2823, -7188]] ![![260, -103, -76, 9, 102]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-162, -192, 259, 97, -392]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-162, -192, 259, 97, -392]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![62, 54, 1, 0, 0], ![50, 12, 0, 1, 0], ![72, 41, 0, 0, 1]] where
  M :=![![![-162, -192, 259, 97, -392], ![1158, 1129, -1364, 166, 1560], ![-4400, -3438, 3585, -3556, -1792], ![-93, -582, 1039, 1680, -2526], ![-1687, -880, 541, -2877, 1463]]]
  hmulB := by decide  
  f := ![![![38278, -13812, -11219, 2729, 15954]], ![![-24490, 9053, 7180, -1538, -10076]], ![![14624, -5100, -4285, 1214, 6204]], ![![22065, -7918, -6467, 1616, 9224]], ![![24067, -8551, -7053, 1845, 10113]]]
  g := ![![![98, 10, 259, 97, -392], ![-478, 121, -1364, 166, 1560], ![1098, -1108, 3585, -3556, -1792], ![457, 366, 1039, 1680, -2526], ![45, -761, 541, -2877, 1463]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [44, 2, 1] where
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
 g := ![![[10, 61], [9], [4], [41, 46], [4], [1]], ![[34, 12], [9], [4], [22, 27], [4], [1]]]
 h' := ![![[71, 72], [41, 39], [46, 3], [21, 2], [8, 22], [29, 71], [0, 1]], ![[0, 1], [36, 34], [40, 70], [17, 71], [37, 51], [33, 2], [71, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [45, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [44, 2, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![461626, 448274, -74373, 814746, 572791]
  a := ![-139, -151, 107, -99, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1053500, -394479, -74373, 814746, 572791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2033, 737, 597, -144, -848]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-2033, 737, 597, -144, -848]] 
 ![![73, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![-2033, 737, 597, -144, -848], ![1310, -472, -383, 92, 544], ![-842, 307, 248, -60, -352], ![516, -188, -152, 37, 216], ![-230, 83, 67, -16, -95]]]
  hmulB := by decide  
  f := ![![![15, 13, 3, 24, -16]], ![![4, 4, -1, 4, 0]], ![![-1, -2, 11, 12, -16]], ![![15, 13, -1, 21, -8]], ![![5, 4, 8, 16, -15]]]
  g := ![![![270, 737, 597, -144, -848], ![-173, -472, -383, 92, 544], ![112, 307, 248, -60, -352], ![-69, -188, -152, 37, 216], ![30, 83, 67, -16, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 7, -9, -4, 14]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![5, 7, -9, -4, 14]] 
 ![![73, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![5, 7, -9, -4, 14], ![-42, -42, 51, -4, -60], ![170, 137, -146, 124, 88], ![-2, 16, -32, -63, 86], ![70, 41, -31, 104, -39]]]
  hmulB := by decide  
  f := ![![![373, 1171, 677, -380, -978]], ![![100, 306, 177, -100, -256]], ![![215, 676, 393, -224, -570]], ![![203, 643, 373, -211, -540]], ![![93, 298, 174, -100, -253]]]
  g := ![![![2, 7, -9, -4, 14], ![-1, -42, 51, -4, -60], ![-42, 137, -146, 124, 88], ![27, 16, -32, -63, 86], ![-40, 41, -31, 104, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2

def I73N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-228, -220, 127, -443, -436]] i)))

def SI73N3: IdealEqSpanCertificate' Table ![![-228, -220, 127, -443, -436]] 
 ![![73, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-228, -220, 127, -443, -436], ![-1882, -1801, 680, -2850, -2672], ![-12664, -12554, 4255, -18916, -17456], ![-6189, -6182, 2003, -9126, -8370], ![-8883, -8852, 2921, -13177, -12115]]]
  hmulB := by decide  
  f := ![![![5508, 5032, -5867, 1933, 5810]], ![![4310, 3995, -4700, 1314, 4828]], ![![3512, 2794, -2955, 2662, 1676]], ![![4721, 4422, -5235, 1282, 5512]], ![![469, 168, -6, 1062, -779]]]
  g := ![![![508, -220, 127, -443, -436], ![3646, -1801, 680, -2850, -2672], ![24810, -12554, 4255, -18916, -17456], ![12095, -6182, 2003, -9126, -8370], ![17390, -8852, 2921, -13177, -12115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N3 : Nat.card (O ⧸ I73N3) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N3)

lemma isPrimeI73N3 : Ideal.IsPrime I73N3 := prime_ideal_of_norm_prime hp73.out _ NI73N3
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-162, -192, 259, 97, -392]] ![![-2033, 737, 597, -144, -848]]
  ![![-40, -29, 46, -15, -48]] where
 M := ![![![-40, -29, 46, -15, -48]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-40, -29, 46, -15, -48]] ![![5, 7, -9, -4, 14]]
  ![![5508, 5032, -5867, 1933, 5810]] where
 M := ![![![5508, 5032, -5867, 1933, 5810]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N2 : IdealMulLeCertificate' Table 
  ![![5508, 5032, -5867, 1933, 5810]] ![![-228, -220, 127, -443, -436]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -8, 32, 58, -84]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-11, -8, 32, 58, -84]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![72, 7, 63, 1, 0], ![0, 67, 45, 0, 1]] where
  M :=![![![-11, -8, 32, 58, -84], ![256, 297, -408, -172, 632], ![-1872, -1840, 2249, -184, -2640], ![522, 380, -378, 501, 96], ![-1198, -1068, 1228, -506, -1141]]]
  hmulB := by decide  
  f := ![![![-73, -176, -108, 74, 164]], ![![-24, -153, -144, 164, 264]], ![![320, 176, -281, 712, 784]], ![![190, -29, -335, 653, 800]], ![![166, -25, -283, 550, 675]]]
  g := ![![![-53, 66, 2, 58, -84], ![160, -517, -228, -172, 632], ![144, 2232, 1679, -184, -2640], ![-450, -121, -459, 501, 96], ![446, 999, 1069, -506, -1141]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [59, 62, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 58, 27], [2, 20, 52], [0, 1]]
 g := ![![[29, 37, 42], [9, 49, 45], [3, 29, 40], [73, 44, 42], [29, 1], []], ![[9, 50, 67, 35], [64, 62, 47, 27], [21, 62, 73, 71], [65, 48, 49, 74], [7, 5], [20, 18]], ![[27, 31, 59, 9], [1, 24, 35, 21], [55, 22, 76, 23], [26, 33, 43, 2], [12, 46], [74, 18]]]
 h' := ![![[27, 58, 27], [22, 72, 11], [60, 21, 19], [38, 6, 44], [27, 39, 68], [0, 0, 1], [0, 1]], ![[2, 20, 52], [7, 34, 31], [37, 3, 78], [27, 54, 15], [37, 5, 43], [23, 40, 20], [27, 58, 27]], ![[0, 1], [58, 52, 37], [16, 55, 61], [13, 19, 20], [55, 35, 47], [62, 39, 58], [2, 20, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 5], []]
 b := ![[], [58, 60, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [59, 62, 50, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1280711090412, 1283804741670, -474755076732, 1816401260354, 1803220337359]
  a := ![1030, 1133, -838, 655, 1873]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1639242780444, -1674009704859, -2481682907091, 1816401260354, 1803220337359]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, -176, -108, 74, 164]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-73, -176, -108, 74, 164]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![25, 34, 1, 0, 0], ![35, 51, 0, 1, 0], ![72, 59, 0, 0, 1]] where
  M :=![![![-73, -176, -108, 74, 164], ![-24, -153, -144, 164, 264], ![320, 176, -281, 712, 784], ![274, 364, 22, 255, 152], ![322, 356, -64, 422, 357]]]
  hmulB := by decide  
  f := ![![![-11, -8, 32, 58, -84]], ![![256, 297, -408, -172, 632]], ![![83, 102, -137, -58, 212]], ![![167, 193, -254, -79, 372]], ![![166, 201, -260, -82, 381]]]
  g := ![![![-149, -126, -108, 74, 164], ![-268, -243, -144, 164, 264], ![-937, -922, -281, 712, 784], ![-255, -283, 22, 255, 152], ![-488, -507, -64, 422, 357]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [40, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 78], [0, 1]]
 g := ![![[2, 2], [18, 18], [54, 25], [], [1], [1]], ![[0, 77], [0, 61], [29, 54], [], [1], [1]]]
 h' := ![![[78, 78], [70, 70], [52, 52], [0, 5], [59], [39, 78], [0, 1]], ![[0, 1], [0, 9], [0, 27], [74, 74], [59], [40, 1], [78, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [40, 1, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1280682, 1140023, -10159, 2617602, 1081804]
  a := ![-241, -275, 228, -100, -509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2126219, -2478971, -10159, 2617602, 1081804]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-11, -8, 32, 58, -84]] ![![-73, -176, -108, 74, 164]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40, 160, 93, -51, -134]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![40, 160, 93, -51, -134]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![71, 46, 47, 1, 0], ![34, 42, 0, 0, 1]] where
  M :=![![![40, 160, 93, -51, -134], ![86, 167, 96, -58, -140], ![64, 194, 119, -84, -184], ![-55, -138, -73, 32, 100], ![-31, -56, -25, 3, 27]]]
  hmulB := by decide  
  f := ![![![0, 4, -3, -1, 4]], ![![-14, -15, 16, -6, -16]], ![![40, 26, -23, 52, -16]], ![![15, 10, -7, 25, -14]], ![![-7, -6, 7, -3, -7]]]
  g := ![![![99, 98, 30, -51, -134], ![108, 105, 34, -58, -140], ![148, 142, 49, -84, -184], ![-69, -70, -19, 32, 100], ![-14, -16, -2, 3, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [53, 44, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 63, 22], [4, 19, 61], [0, 1]]
 g := ![![[56, 49, 51], [17, 61, 41], [22, 65], [46, 27], [34, 24, 1], []], ![[61, 32, 23, 72], [30, 71, 79, 62], [21, 36], [34, 68], [4, 42, 5, 57], [29, 69]], ![[43, 2, 38, 61], [82, 50, 36, 61], [22, 26], [19, 78], [62, 19, 50, 81], [73, 69]]]
 h' := ![![[20, 63, 22], [12, 54, 36], [47, 38, 37], [47, 50, 56], [24, 54, 39], [0, 0, 1], [0, 1]], ![[4, 19, 61], [0, 32, 46], [72, 14, 45], [40, 75, 6], [4, 14, 20], [25, 77, 19], [20, 63, 22]], ![[0, 1], [47, 80, 1], [66, 31, 1], [30, 41, 21], [37, 15, 24], [48, 6, 63], [4, 19, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8], []]
 b := ![[], [66, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [53, 44, 59, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61784337, 306924080, 111745924, 195837088, 1231016000]
  a := ![98, 126, -136, -32, 304]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-671050517, -727762096, -109549364, 195837088, 1231016000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-902, -2159, -1230, 705, 1776]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-902, -2159, -1230, 705, 1776]] 
 ![![83, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![-902, -2159, -1230, 705, 1776], ![-1008, -2456, -1427, 858, 2088], ![-954, -2623, -1712, 1296, 2688], ![895, 1966, 1007, -414, -1342], ![467, 871, 338, 35, -331]]]
  hmulB := by decide  
  f := ![![![11846, -4369, -3422, 819, 4890]], ![![3478, -1281, -1005, 243, 1434]], ![![5628, -2068, -1636, 375, 2346]], ![![8663, -3205, -2495, 601, 3566]], ![![8729, -3208, -2532, 596, 3621]]]
  g := ![![![-606, -2159, -1230, 705, 1776], ![-767, -2456, -1427, 858, 2088], ![-1345, -2623, -1712, 1296, 2688], ![236, 1966, 1007, -414, -1342], ![-198, 871, 338, 35, -331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![522, 1246, 707, -401, -1018]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![522, 1246, 707, -401, -1018]] 
 ![![83, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![522, 1246, 707, -401, -1018], ![602, 1435, 814, -462, -1172], ![692, 1652, 939, -532, -1352], ![-445, -1062, -603, 342, 868], ![-169, -402, -227, 129, 327]]]
  hmulB := by decide  
  f := ![![![-178, 42, 59, -27, -88]], ![![-160, 37, 53, -25, -80]], ![![-46, 6, 14, -15, -24]], ![![-127, 26, 43, -22, -66]], ![![-37, 6, 11, -11, -19]]]
  g := ![![![-805, 1246, 707, -401, -1018], ![-927, 1435, 814, -462, -1172], ![-1067, 1652, 939, -532, -1352], ![686, -1062, -603, 342, 868], ![260, -402, -227, 129, 327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![40, 160, 93, -51, -134]] ![![-902, -2159, -1230, 705, 1776]]
  ![![-394305, -940239, -533385, 302432, 767900]] where
 M := ![![![-394305, -940239, -533385, 302432, 767900]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-394305, -940239, -533385, 302432, 767900]] ![![522, 1246, 707, -401, -1018]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-1405310848, -3351577599, -1901656492, 1078758387, 2738113394]]]
 hmul := by decide  
 g := ![![![![-16931456, -40380453, -22911524, 12997089, 32989318]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [5, 57, 26, 32, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 16, 79, 54, 79], [0, 68, 61, 60, 61], [7, 81, 41, 1, 65], [64, 12, 86, 63, 62], [0, 1]]
 g := ![![[53, 1, 77, 44, 36], [0, 30, 75, 8], [17, 75, 32, 11], [34, 61, 7, 43, 78], [1], []], ![[4, 45, 77, 67, 14, 19, 24, 44], [27, 47, 14, 34], [64, 33, 72, 22], [62, 38, 22, 46, 13, 54, 80, 88], [67, 75, 3, 9, 65, 86, 57, 21], [88, 76, 79, 11]], ![[52, 18, 10, 11, 8, 7, 41, 62], [12, 81, 41, 68], [50, 69, 60, 36], [33, 33, 53, 3, 67, 88, 50, 33], [42, 71, 16, 53, 79, 69, 0, 66], [45, 29, 27, 72]], ![[66, 22, 87, 48, 1, 86, 18, 12], [52, 88, 76, 21], [72, 15, 2, 22], [51, 61, 12, 74, 36, 3, 59, 51], [22, 17, 59, 64, 10, 17, 60, 31], [6, 21, 81, 42]], ![[39, 22, 24, 72, 18, 81, 88, 12], [6, 4, 76, 16], [50, 31, 18, 20], [12, 36, 0, 85, 48, 70, 65, 3], [31, 88, 11, 48, 26, 74, 48, 3], [65, 71, 64, 17]]]
 h' := ![![[2, 16, 79, 54, 79], [85, 63, 54, 22, 6], [68, 14, 83, 67, 50], [8, 7, 1, 43, 79], [84, 32, 63, 57, 73], [0, 0, 1], [0, 1]], ![[0, 68, 61, 60, 61], [59, 63, 79, 13, 82], [85, 4, 28, 34, 37], [7, 12, 10, 87, 72], [5, 60, 26, 10, 3], [9, 8, 54, 69, 73], [2, 16, 79, 54, 79]], ![[7, 81, 41, 1, 65], [4, 87, 1, 50, 77], [8, 29, 57, 36, 54], [13, 35, 7, 53, 6], [57, 79, 18, 18, 64], [42, 49, 64, 20, 87], [0, 68, 61, 60, 61]], ![[64, 12, 86, 63, 62], [43, 60, 8, 79, 20], [83, 8, 6, 44, 33], [49, 40, 38, 21, 72], [14, 70, 72, 74, 86], [19, 64, 37, 23, 66], [7, 81, 41, 1, 65]], ![[0, 1], [59, 83, 36, 14, 82], [0, 34, 4, 86, 4], [61, 84, 33, 63, 38], [32, 26, 88, 19, 41], [33, 57, 22, 66, 41], [64, 12, 86, 63, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 18, 53, 16], [], [], []]
 b := ![[], [68, 81, 61, 52, 55], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [5, 57, 26, 32, 16, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14487139208149676536, 14419936539227114176, -4828071726882384127, 21453716913445162593, 19865176331378004610]
  a := ![374, 413, -313, 219, 701]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![162776845035389624, 162021758867720384, -54247996931262743, 241052999027473737, 223204228442449490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 5584059449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-449, -603, -39, -418, -246]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-449, -603, -39, -418, -246]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![59, 6, 25, 64, 1]] where
  M :=![![![-449, -603, -39, -418, -246], ![-2398, -2562, 577, -3272, -2852], ![-15330, -15453, 4822, -22436, -20472], ![-7256, -7084, 2558, -10993, -10234], ![-10564, -10457, 3555, -15770, -14563]]]
  hmulB := by decide  
  f := ![![![59, -23, -17, 2, 26]], ![![-42, 8, 21, 8, -36]], ![![86, 59, -96, -20, 136]], ![![-44, -20, 34, -13, -34]], ![![27, -11, -12, -12, 27]]]
  g := ![![![145, 9, 63, 158, -246], ![1710, 150, 741, 1848, -2852], ![12294, 1107, 5326, 13276, -20472], ![6150, 560, 2664, 6639, -10234], ![8749, 793, 3790, 9446, -14563]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [30, 50, 70, 47, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 25, 89, 34], [77, 17, 52, 64], [50, 54, 53, 96], [0, 1]]
 g := ![![[64, 53, 55, 33], [90, 91, 8], [56, 46, 86], [77, 80, 4], [5, 50, 1], []], ![[76, 21, 5, 85, 41, 76], [39, 89, 27], [16, 92, 11], [45, 53, 4], [91, 59, 96], [84, 81, 32, 6, 75, 19]], ![[14, 52, 49, 25, 36, 33], [1, 14, 62], [53], [58, 51, 73], [70], [32, 10, 10, 45, 15, 50]], ![[37, 56, 66, 70, 39, 75], [32, 34, 2], [62, 54, 1], [77, 20, 73], [43, 91, 53], [45, 12, 23, 68, 12, 96]]]
 h' := ![![[20, 25, 89, 34], [81, 29, 47, 79], [68, 17, 17, 28], [14, 91, 33, 59], [44, 93, 30, 95], [0, 0, 0, 1], [0, 1]], ![[77, 17, 52, 64], [93, 42, 17, 29], [14, 21, 0, 67], [94, 66, 41, 37], [59, 89, 36, 2], [48, 90, 35, 75], [20, 25, 89, 34]], ![[50, 54, 53, 96], [5, 57, 29, 22], [61, 56, 43, 16], [14, 62, 21], [69, 93, 87, 49], [61, 70, 19], [77, 17, 52, 64]], ![[0, 1], [35, 66, 4, 64], [92, 3, 37, 83], [20, 72, 2, 1], [14, 16, 41, 48], [72, 34, 43, 21], [50, 54, 53, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [83, 13, 55], []]
 b := ![[], [], [42, 86, 50, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [30, 50, 70, 47, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5147050745768, 5119375535436, -1684743624628, 7672483813000, 7037023400218]
  a := ![-100, -107, 72, -79, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4227188967702, -382502730576, -1831034315774, -4563886740216, 7037023400218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, 23, 17, -2, -26]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-59, 23, 17, -2, -26]] 
 ![![97, 0, 0, 0, 0], ![72, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-59, 23, 17, -2, -26], ![42, -8, -21, -8, 36], ![-86, -59, 96, 20, -136], ![44, 20, -34, 13, 34], ![-56, -47, 63, -2, -77]]]
  hmulB := by decide  
  f := ![![![449, 603, 39, 418, 246]], ![![358, 474, 23, 344, 212]], ![![408, 495, -28, 464, 348]], ![![459, 589, 7, 471, 316]], ![![220, 257, -27, 266, 211]]]
  g := ![![![-19, 23, 17, -2, -26], ![16, -8, -21, -8, 36], ![6, -59, 96, 20, -136], ![-15, 20, -34, 13, 34], ![20, -47, 63, -2, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-449, -603, -39, -418, -246]] ![![-59, 23, 17, -2, -26]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 81, -81, 102, 24]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![109, 81, -81, 102, 24]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![42, 16, 5, 1, 0], ![7, 49, 89, 0, 1]] where
  M :=![![![109, 81, -81, 102, 24], ![-30, 136, -279, -576, 768], ![-2442, -2961, 3976, 1644, -6144], ![1470, 1392, -1662, 343, 1788], ![-2256, -2397, 3033, 354, -4019]]]
  hmulB := by decide  
  f := ![![![1181, -135, -171, -6, 240]], ![![-570, 542, 369, -144, -528]], ![![582, 171, 62, -84, -96]], ![![426, 37, -10, -29, 12]], ![![319, 403, 221, -144, -323]]]
  g := ![![![-43, -27, -27, 102, 24], ![186, -280, -651, -576, 768], ![-282, 2691, 5372, 1644, -6144], ![-252, -908, -1609, 343, 1788], ![109, 1870, 3554, 354, -4019]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [68, 74, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 2, 33], [16, 98, 68], [0, 1]]
 g := ![![[29, 11, 96], [53, 82], [72, 4, 56], [], [71, 56], [1]], ![[38, 60, 82, 17], [49, 25], [0, 64, 89, 64], [45, 6], [55, 64], [73, 30, 66, 82]], ![[100, 19, 35, 77], [22, 82], [62, 21, 8, 5], [27, 6], [18, 5], [37, 81, 0, 19]]]
 h' := ![![[48, 2, 33], [13, 53, 46], [53, 72, 53], [4, 32, 64], [99, 93], [33, 27, 64], [0, 1]], ![[16, 98, 68], [77, 84, 96], [50, 44, 96], [92, 29, 56], [18, 85, 39], [83, 19, 93], [48, 2, 33]], ![[0, 1], [18, 65, 60], [91, 86, 53], [15, 40, 82], [72, 24, 62], [65, 55, 45], [16, 98, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 41], []]
 b := ![[], [15, 43, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [68, 74, 37, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38133530474, 38671484796, -14785184266, 52858021776, 55855894326]
  a := ![325, 365, -289, 164, 647]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25474204400, -35089066194, -51982672160, 52858021776, 55855894326]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -38, 8, -50, -42]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-23, -38, 8, -50, -42]] 
 ![![101, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![-23, -38, 8, -50, -42], ![-236, -225, 78, -340, -316], ![-1524, -1522, 503, -2272, -2088], ![-744, -736, 246, -1101, -1014], ![-1066, -1062, 352, -1586, -1459]]]
  hmulB := by decide  
  f := ![![![3409, 8102, 4584, -2606, -6602]], ![![1726, 4103, 2322, -1320, -3344]], ![![889, 2112, 1195, -678, -1722]], ![![883, 2098, 1186, -675, -1708]], ![![2183, 5188, 2936, -1668, -4229]]]
  g := ![![![57, -38, 8, -50, -42], ![384, -225, 78, -340, -316], ![2565, -1522, 503, -2272, -2088], ![1243, -736, 246, -1101, -1014], ![1791, -1062, 352, -1586, -1459]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-740, -537, 524, -741, -98]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-740, -537, 524, -741, -98]] 
 ![![101, 0, 0, 0, 0], ![92, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![95, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-740, -537, 524, -741, -98], ![-16, -1182, 2231, 4022, -5732], ![18010, 21495, -28734, -11040, 43640], ![-10397, -9754, 11553, -2786, -12196], ![16205, 17049, -21508, -2027, 28047]]]
  hmulB := by decide  
  f := ![![![15212, 31727, 17596, -9729, -25072]], ![![14020, 29288, 16231, -8950, -23112]], ![![3330, 6835, 3676, -1860, -5120]], ![![14257, 29639, 16377, -8967, -23274]], ![![5325, 10986, 6008, -3198, -8475]]]
  g := ![![![1109, -537, 524, -741, -98], ![-1162, -1182, 2231, 4022, -5732], ![-18450, 21495, -28734, -11040, 43640], ![13341, -9754, 11553, -2786, -12196], ![-18923, 17049, -21508, -2027, 28047]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![109, 81, -81, 102, 24]] ![![-23, -38, 8, -50, -42]]
  ![![349, 355, -13, 676, 510]] where
 M := ![![![349, 355, -13, 676, 510]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![349, 355, -13, 676, 510]] ![![-740, -537, 524, -741, -98]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![738108, 1214828, -1810829, -1604385, 3423092]]]
 hmul := by decide  
 g := ![![![![7308, 12028, -17929, -15885, 33892]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![92, 92, -29, 141, 122]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![92, 92, -29, 141, 122]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![98, 95, 19, 1, 0], ![4, 10, 96, 0, 1]] where
  M :=![![![92, 92, -29, 141, 122], ![634, 633, -228, 910, 884], ![4040, 4018, -1239, 6156, 5512], ![2041, 2022, -689, 3012, 2756], ![2825, 2816, -883, 4275, 3887]]]
  hmulB := by decide  
  f := ![![![-676, -1416, -797, 459, 1148]], ![![-650, -1677, -956, 538, 1376]], ![![-832, -1902, -1077, 612, 1552]], ![![-1391, -3233, -1832, 1042, 2638]], ![![-863, -1986, -1125, 639, 1621]]]
  g := ![![![-138, -141, -140, 141, 122], ![-894, -919, -994, 910, 884], ![-6032, -6174, -6285, 6156, 5512], ![-2953, -3026, -3131, 3012, 2756], ![-4191, -4293, -4420, 4275, 3887]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [23, 61, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 15, 10], [98, 87, 93], [0, 1]]
 g := ![![[42, 34, 72], [57, 5, 63], [62, 20, 82], [92, 2], [9, 82], [1]], ![[63, 62, 79, 71], [16, 85, 87, 102], [43, 97, 15, 85], [20, 41], [40, 81], [11, 51, 52, 73]], ![[50, 24, 46, 28], [63, 43, 28, 52], [75, 8, 65, 66], [2, 28], [101, 28], [48, 49, 60, 30]]]
 h' := ![![[64, 15, 10], [28, 63, 81], [16, 81, 75], [10, 74, 44], [13, 62, 38], [80, 42, 59], [0, 1]], ![[98, 87, 93], [82, 95, 55], [6, 77, 22], [33, 29, 36], [9, 76, 12], [65, 63, 94], [64, 15, 10]], ![[0, 1], [39, 48, 70], [54, 48, 6], [18, 0, 23], [95, 68, 53], [7, 101, 53], [98, 87, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 68], []]
 b := ![[], [76, 35, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [23, 61, 44, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7991701598, 8126924595, -3129166792, 11019100137, 11814760038]
  a := ![194, 219, -176, 93, 393]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10865428660, -11231409600, -13074844981, 11019100137, 11814760038]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, 34, -51, -47, 98]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![20, 34, -51, -47, 98]] 
 ![![103, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![20, 34, -51, -47, 98], ![-298, -325, 418, 78, -572], ![1676, 1532, -1781, 596, 1768], ![-283, -138, 75, -512, 292], ![921, 738, -781, 687, 463]]]
  hmulB := by decide  
  f := ![![![-24628, -31570, -17043, 10615, 24596]], ![![-4646, -6239, -3385, 2089, 4884]], ![![-12424, -16070, -8684, 5399, 12532]], ![![-7505, -9526, -5137, 3206, 7414]], ![![-20767, -26552, -14330, 8930, 20681]]]
  g := ![![![-49, 34, -51, -47, 98], ![309, -325, 418, 78, -572], ![-1063, 1532, -1781, 596, 1768], ![-102, -138, 75, -512, 292], ![-345, 738, -781, 687, 463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 30, -33, 3, 38]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![24, 30, -33, 3, 38]] 
 ![![103, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![24, 30, -33, 3, 38], ![-110, -91, 94, -86, -52], ![116, -36, 149, 540, -584], ![191, 226, -303, -116, 460], ![-117, -210, 321, 317, -631]]]
  hmulB := by decide  
  f := ![![![-1064, -1822, -601, -283, 436]], ![![-678, -1143, -360, -212, 232]], ![![-940, -1464, -349, -498, 24]], ![![-355, -532, -106, -223, -42]], ![![-785, -1238, -311, -389, 59]]]
  g := ![![![-19, 30, -33, 3, 38], ![42, -91, 94, -86, -52], ![142, -36, 149, 540, -584], ![-177, 226, -303, -116, 460], ![210, -210, 321, 317, -631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![92, 92, -29, 141, 122]] ![![20, 34, -51, -47, 98]]
  ![![-1721, -622, 706, -2810, 2778]] where
 M := ![![![-1721, -622, 706, -2810, 2778]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-1721, -622, 706, -2810, 2778]] ![![24, 30, -33, 3, 38]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-752724, -1238884, 1846687, 1636155, -3490876]]]
 hmul := by decide  
 g := ![![![![-7308, -12028, 17929, 15885, -33892]]]]
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


lemma PB1640I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1640I2 : PrimesBelowBoundCertificateInterval O 61 103 1640 where
  m := 9
  g := ![3, 2, 4, 2, 3, 1, 2, 3, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1640I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2, I73N3]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
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
    · exact ![25411681, 71]
    · exact ![5329, 73, 73, 73]
    · exact ![493039, 6241]
    · exact ![571787, 83, 83]
    · exact ![5584059449]
    · exact ![88529281, 97]
    · exact ![1030301, 101, 101]
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
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
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
      exact NI103N2
  β := ![I67N1, I67N2, I71N1, I73N1, I73N2, I73N3, I83N1, I83N2, I97N1, I101N1, I101N2, I103N1, I103N2]
  Il := ![[I67N1, I67N2], [I71N1], [I73N1, I73N2, I73N3], [], [I83N1, I83N2], [], [I97N1], [I101N1, I101N2], [I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
