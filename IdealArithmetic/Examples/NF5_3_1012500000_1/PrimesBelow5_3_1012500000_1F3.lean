
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4775, -7966, 2572, -1146, 968]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-4775, -7966, 2572, -1146, 968]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![88, 82, 20, 1, 0], ![83, 17, 48, 0, 1]] where
  M :=![![![-4775, -7966, 2572, -1146, 968], ![5808, 9745, -2976, 1446, -1146], ![-6876, -11382, 3955, -1566, 1446], ![4884, 8160, -2600, 1183, -984], ![1872, 3222, -732, 546, -323]]]
  hmulB := by decide  
  f := ![![![-229, -118, 52, -18, 20]], ![![120, 71, -24, 6, -18]], ![![-108, -150, 65, 162, 6]], ![![-116, -70, 36, 19, 4]], ![![-205, -143, 64, 54, 15]]]
  g := ![![![147, 650, -196, -1146, 968], ![-246, -835, 216, 1446, -1146], ![102, 864, -319, -1566, 1446], ![-164, -674, 196, 1183, -984], ![-181, -337, 36, 546, -323]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [103, 62, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 102, 58], [60, 4, 49], [0, 1]]
 g := ![![[86, 89, 101], [25, 92, 12], [63, 47], [26, 21, 83], [66, 41], [1]], ![[39, 87, 87, 67], [88, 53, 28, 66], [51, 90], [40, 36, 54, 24], [0, 27], [47, 9, 104, 51]], ![[99, 0, 92, 86], [106, 69, 46, 99], [73, 41], [97, 40, 77, 69], [54, 92], [92, 59, 76, 56]]]
 h' := ![![[23, 102, 58], [100, 64, 84], [47, 72, 71], [104, 46, 49], [66, 70, 61], [4, 45, 83], [0, 1]], ![[60, 4, 49], [58, 37, 89], [59, 22, 73], [47, 5, 82], [39, 43, 24], [50, 101, 53], [23, 102, 58]], ![[0, 1], [87, 6, 41], [11, 13, 70], [19, 56, 83], [91, 101, 22], [14, 68, 78], [60, 4, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 52], []]
 b := ![[], [38, 61, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [103, 62, 24, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-758537, -1727785, 1122774, 3066543, -452544]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2178067, -2294309, -359682, 3066543, -452544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1057397, 563908, -249904, 45562, -89608]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1057397, 563908, -249904, 45562, -89608]] 
 ![![107, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![91, 0, 1, 0, 0], ![90, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1057397, 563908, -249904, 45562, -89608], ![-537648, -286723, 127066, -23166, 45562], ![273372, 145782, -64607, 11778, -23166], ![-159852, -85244, 37778, -6887, 13546], ![-124908, -66612, 29520, -5382, 10585]]]
  hmulB := by decide  
  f := ![![![151, 420, -60, -382, -172]], ![![-4, -7, 10, 22, -10]], ![![107, 294, -59, -296, -110]], ![![174, 472, -90, -467, -158]], ![![41, 144, 72, 28, -151]]]
  g := ![![![163851, 563908, -249904, 45562, -89608], ![-83312, -286723, 127066, -23166, 45562], ![42361, 145782, -64607, 11778, -23166], ![-24770, -85244, 37778, -6887, 13546], ![-19355, -66612, 29520, -5382, 10585]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-391, -1141, -1148, -555, -201]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-391, -1141, -1148, -555, -201]] 
 ![![107, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-391, -1141, -1148, -555, -201], ![-1206, -3406, -3226, -1605, -555], ![-3330, -9531, -9259, -4551, -1605], ![60, 198, 240, 107, 44], ![-2886, -8217, -7904, -3903, -1366]]]
  hmulB := by decide  
  f := ![![![23839, 12707, -5638, 1029, -2013]], ![![20607, 10985, -4874, 888, -1740]], ![![4068, 2169, -961, 177, -345]], ![![7317, 3897, -1730, 320, -617]], ![![9778, 5213, -2318, 411, -820]]]
  g := ![![![1435, -1141, -1148, -555, -201], ![4215, -3406, -3226, -1605, -555], ![11874, -9531, -9259, -4551, -1605], ![-263, 198, 240, 107, 44], ![10210, -8217, -7904, -3903, -1366]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-4775, -7966, 2572, -1146, 968]] ![![1057397, 563908, -249904, 45562, -89608]]
  ![![-774475, -464770, 196412, -42452, 70920]] where
 M := ![![![-774475, -464770, 196412, -42452, 70920]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-774475, -464770, 196412, -42452, 70920]] ![![-391, -1141, -1148, -555, -201]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![2058145, 3524687, -873548, 575339, -369043]]]
 hmul := by decide  
 g := ![![![![19235, 32941, -8164, 5377, -3449]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68063, 3859, -57870, -15443, -13609]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![68063, 3859, -57870, -15443, -13609]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![37, 30, 21, 9, 1]] where
  M :=![![![68063, 3859, -57870, -15443, -13609], ![-81654, -136072, -99872, -55929, -15443], ![-92658, -313299, -317987, -153471, -55929], ![-9600, 1384, 10648, 3271, 2386], ![-107142, -282957, -265530, -132531, -45500]]]
  hmulB := by decide  
  f := ![![![47, 93, -52, -101, 13]], ![![78, 242, -14, -243, -101]], ![![-606, -1437, 847, 2463, -243]], ![![60, 10, -488, -887, 532]], ![![-49, -117, 71, 208, -22]]]
  g := ![![![5244, 3781, 2091, 982, -13609], ![4493, 3002, 2059, 762, -15443], ![18135, 12519, 7858, 3210, -55929], ![-898, -644, -362, -167, 2386], ![14462, 9927, 6330, 2541, -45500]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [33, 37, 64, 79, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 46, 28, 99], [31, 6, 29, 102], [6, 56, 52, 17], [0, 1]]
 g := ![![[96, 57, 24, 88], [101, 80, 108], [76, 93, 78, 73], [30, 33, 51, 7], [73, 30, 1], []], ![[82, 92, 67, 86, 19, 79], [66, 2, 20], [95, 35, 15, 47, 0, 85], [82, 53, 18, 65, 47, 10], [43, 16, 3], [82, 70, 107, 3, 91, 90]], ![[34, 15, 42, 46, 82, 83], [77, 86, 71], [36, 22, 88, 25, 83, 63], [66, 59, 86, 1, 61, 88], [45, 108, 43], [9, 89, 30, 71, 77, 93]], ![[20, 86, 64, 105, 67, 96], [105, 38, 64], [46, 1, 5, 63, 72, 23], [54, 36, 45, 67, 60, 96], [74, 68, 75], [19, 52, 91, 44, 89, 8]]]
 h' := ![![[102, 46, 28, 99], [47, 100, 0, 57], [108, 86, 38, 33], [100, 102, 78, 20], [98, 15, 71, 15], [0, 0, 0, 1], [0, 1]], ![[31, 6, 29, 102], [63, 79, 72, 49], [72, 49, 72, 67], [3, 61, 31, 41], [7, 67, 17, 76], [3, 1, 86, 49], [102, 46, 28, 99]], ![[6, 56, 52, 17], [37, 27, 59, 34], [92, 82, 4, 17], [14, 86, 78, 10], [104, 30, 22, 49], [64, 76, 19, 32], [31, 6, 29, 102]], ![[0, 1], [1, 12, 87, 78], [14, 1, 104, 101], [108, 78, 31, 38], [36, 106, 108, 78], [25, 32, 4, 27], [6, 56, 52, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 86, 101], []]
 b := ![[], [], [19, 12, 93, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [33, 37, 64, 79, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41190408, 133708808, -2442361, -201174619, -19667908]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7054156, 6639872, 3766823, -221683, -19667908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -93, 52, 101, -13]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-47, -93, 52, 101, -13]] 
 ![![109, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-47, -93, 52, 101, -13], ![-78, -242, 14, 243, 101], ![606, 1437, -847, -2463, 243], ![-60, -10, 488, 887, -532], ![-2766, -6633, 3312, 10041, -466]]]
  hmulB := by decide  
  f := ![![![-68063, -3859, 57870, 15443, 13609]], ![![-61694, -2292, 54008, 14681, 12627]], ![![-16634, 1883, 17783, 5375, 4009]], ![![-17396, -1004, 14768, 3937, 3474]], ![![-22121, 1286, 22080, 6458, 5037]]]
  g := ![![![50, -93, 52, 101, -13], ![121, -242, 14, 243, 101], ![-545, 1437, -847, -2463, 243], ![-164, -10, 488, 887, -532], ![2788, -6633, 3312, 10041, -466]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![68063, 3859, -57870, -15443, -13609]] ![![-47, -93, 52, 101, -13]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-457, -971, 857, 2082, -478]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-457, -971, 857, 2082, -478]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![29, 82, 1, 0, 0], ![60, 105, 0, 1, 0], ![102, 96, 0, 0, 1]] where
  M :=![![![-457, -971, 857, 2082, -478], ![-2868, -7627, 1430, 7500, 2082], ![12492, 28362, -19165, -51396, 7500], ![1254, 6651, 8293, 9731, -12316], ![-57642, -135171, 76777, 220050, -19717]]]
  hmulB := by decide  
  f := ![![![-975917, -515615, 236895, -39306, 83876]], ![![503256, 282223, -101128, 29520, -39306]], ![![112651, 71709, -11646, 11442, -6736]], ![![-49254, -10848, 31497, 6611, 7900]], ![![-452220, -224745, 128033, -10182, 42293]]]
  g := ![![![-898, -2159, 857, 2082, -478], ![-6254, -9843, 1430, 7500, 2082], ![25549, 55544, -19165, -51396, 7500], ![3833, -4538, 8293, 9731, -12316], ![-119257, -244631, 76777, 220050, -19717]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [111, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 112], [0, 1]]
 g := ![![[85, 56], [88], [64], [51], [60, 111], [57, 1]], ![[0, 57], [88], [64], [51], [59, 2], [1, 112]]]
 h' := ![![[57, 112], [50, 13], [103, 75], [38, 8], [7, 27], [1, 87], [0, 1]], ![[0, 1], [0, 100], [84, 38], [42, 105], [77, 86], [101, 26], [57, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [48, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [111, 56, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![456, 412, -566, -1304, 332]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![542, 1344, -566, -1304, 332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![102235, 54522, -24162, 4406, -8664]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![102235, 54522, -24162, 4406, -8664]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![35, 13, 1, 0, 0], ![95, 103, 0, 1, 0], ![105, 95, 0, 0, 1]] where
  M :=![![![102235, 54522, -24162, 4406, -8664], ![-51984, -27725, 12286, -2238, 4406], ![26436, 14106, -6253, 1122, -2238], ![-15456, -8242, 3656, -661, 1306], ![-12096, -6486, 2878, -450, 1019]]]
  hmulB := by decide  
  f := ![![![-5029, -8474, 2478, -1286, 972]], ![![5832, 9551, -3642, 1230, -1286]], ![![-955, -1645, 371, -278, 164]], ![![1133, 1657, -1260, 51, -364]], ![![243, 173, -778, -162, -183]]]
  g := ![![![12735, 6530, -24162, 4406, -8664], ![-6478, -3323, 12286, -2238, 4406], ![3307, 1703, -6253, 1122, -2238], ![-1927, -989, 3656, -661, 1306], ![-1567, -835, 2878, -450, 1019]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [104, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 112], [0, 1]]
 g := ![![[9, 25], [41], [106], [31], [107, 30], [81, 1]], ![[0, 88], [41], [106], [31], [51, 83], [49, 112]]]
 h' := ![![[81, 112], [66, 108], [107, 70], [31, 85], [59, 12], [51, 16], [0, 1]], ![[0, 1], [0, 5], [14, 43], [23, 28], [14, 101], [104, 97], [81, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [107, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [104, 32, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2759, 6698, -2231, -8954, 1905]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6473, 6876, -2231, -8954, 1905]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 4, 5, 3, 1]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![1, 4, 5, 3, 1]] 
 ![![113, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![1, 4, 5, 3, 1], ![6, 16, 12, 3, 3], ![18, 51, 37, 9, 3], ![-6, -15, 5, 19, 0], ![0, 0, 33, 39, 22]]]
  hmulB := by decide  
  f := ![![![-4015, -6098, 1973, -867, 745]], ![![-600, -908, 294, -129, 111]], ![![-579, -885, 286, -126, 108]], ![![-110, -163, 53, -23, 20]], ![![-2404, -3650, 1181, -519, 446]]]
  g := ![![![-2, 4, 5, 3, 1], ![-6, 16, 12, 3, 3], ![-15, 51, 37, 9, 3], ![1, -15, 5, 19, 0], ![-19, 0, 33, 39, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-457, -971, 857, 2082, -478]] ![![102235, 54522, -24162, 4406, -8664]]
  ![![13217, 33727, -10385, -39992, -4734]] where
 M := ![![![13217, 33727, -10385, -39992, -4734]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![13217, 33727, -10385, -39992, -4734]] ![![1, 4, 5, 3, 1]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![268601, 662745, -269618, -897107, -20905]]]
 hmul := by decide  
 g := ![![![![2377, 5865, -2386, -7939, -185]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -14, 9, -75, 9]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-103, -14, 9, -75, 9]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![45, 69, 1, 34, 1]] where
  M :=![![![-103, -14, 9, -75, 9], ![54, 32, 52, 117, -75], ![-450, -1071, 371, 1311, 117], ![342, 753, -475, -1291, 160], ![1536, 3930, -1075, -4419, -694]]]
  hmulB := by decide  
  f := ![![![-313, -520, 167, -75, 63]], ![![378, 632, -196, 93, -75]], ![![-450, -747, 251, -105, 93]], ![![318, 531, -169, 77, -64]], ![![177, 297, -91, 44, -35]]]
  g := ![![![-4, -5, 0, -3, 9], ![27, 41, 1, 21, -75], ![-45, -72, 2, -21, 117], ![-54, -81, -5, -53, 160], ![258, 408, -3, 151, -694]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [8, 8, 44, 44, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 61, 2, 47], [102, 91, 39, 23], [110, 101, 86, 57], [0, 1]]
 g := ![![[32, 70, 99, 17], [105, 108, 22, 121], [5, 122, 51, 113], [79, 117, 2, 81], [87, 114, 83, 1], []], ![[65, 0, 73, 98, 21, 50], [124, 114, 39, 55, 100, 84], [20, 66, 10, 53, 53, 73], [63, 94, 56, 60, 34, 25], [118, 47, 28, 62, 117, 62], [90, 56, 32, 0, 24, 64]], ![[45, 20, 14, 109, 38, 67], [36, 107, 63, 96, 30, 55], [120, 56, 4, 109, 98, 95], [116, 6, 104, 22, 101, 96], [113, 60, 63, 115, 6, 118], [11, 105, 117, 105, 1, 102]], ![[119, 76, 58, 124, 5, 40], [118, 47, 5, 83, 66, 78], [60, 112, 114, 68, 56, 20], [4, 65, 43, 3, 103, 45], [48, 23, 18, 26, 49, 90], [112, 51, 110, 80, 124, 27]]]
 h' := ![![[125, 61, 2, 47], [49, 23, 97, 115], [87, 9, 11, 116], [3, 121, 105, 85], [66, 43, 57, 9], [0, 0, 0, 1], [0, 1]], ![[102, 91, 39, 23], [109, 85, 125, 38], [23, 42, 22, 48], [90, 104, 1, 51], [46, 95, 71, 50], [34, 72, 85, 72], [125, 61, 2, 47]], ![[110, 101, 86, 57], [63, 76, 112, 5], [68, 111, 73, 41], [41, 32, 91, 112], [94, 47, 6, 77], [35, 25, 81, 37], [102, 91, 39, 23]], ![[0, 1], [84, 70, 47, 96], [57, 92, 21, 49], [33, 124, 57, 6], [26, 69, 120, 118], [33, 30, 88, 17], [110, 101, 86, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [87, 1, 114], []]
 b := ![[], [], [104, 113, 63, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [8, 8, 44, 44, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![950219983, 2361732526, -907412296, -3106347622, -132307293]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![54362584, 90479809, -6103189, 10961420, -132307293]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-313, -520, 167, -75, 63]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-313, -520, 167, -75, 63]] 
 ![![127, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![114, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![-313, -520, 167, -75, 63], ![378, 632, -196, 93, -75], ![-450, -747, 251, -105, 93], ![318, 531, -169, 77, -64], ![120, 204, -53, 33, -22]]]
  hmulB := by decide  
  f := ![![![-103, -14, 9, -75, 9]], ![![-75, -10, 7, -54, 6]], ![![-96, -21, 11, -57, 9]], ![![-63, -3, 2, -58, 7]], ![![-39, 24, -4, -72, -1]]]
  g := ![![![245, -520, 167, -75, 63], ![-306, 632, -196, 93, -75], ![339, -747, 251, -105, 93], ![-252, 531, -169, 77, -64], ![-111, 204, -53, 33, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-103, -14, 9, -75, 9]] ![![-313, -520, 167, -75, 63]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, -1, -5, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-1, 0, -1, -5, 1]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![71, 41, 1, 0, 0], ![47, 126, 0, 1, 0], ![43, 16, 0, 0, 1]] where
  M :=![![![-1, 0, -1, -5, 1], ![6, 14, -2, -9, -5], ![-30, -69, 37, 105, -9], ![6, 7, -23, -41, 22], ![120, 288, -141, -429, 16]]]
  hmulB := by decide  
  f := ![![![-347, -226, 81, -25, 31]], ![![186, 118, -82, 3, -25]], ![![-131, -87, 18, -13, 9]], ![![55, 33, -50, -6, -13]], ![![-91, -60, 16, -8, 7]]]
  g := ![![![2, 5, -1, -5, 1], ![6, 10, -2, -9, -5], ![-55, -112, 37, 105, -9], ![20, 44, -23, -41, 22], ![226, 457, -141, -429, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [97, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 130], [0, 1]]
 g := ![![[19, 101], [40, 60], [129], [89], [44], [81], [1]], ![[27, 30], [24, 71], [129], [89], [44], [81], [1]]]
 h' := ![![[122, 130], [50, 25], [21, 45], [58, 103], [62, 58], [111, 100], [34, 122], [0, 1]], ![[0, 1], [87, 106], [9, 86], [48, 28], [64, 73], [128, 31], [115, 9], [122, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [105, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [97, 9, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-743, -2288, 642, 2366, 1080]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1557, -2626, 642, 2366, 1080]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 21, -3, -38, -6]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![5, 21, -3, -38, -6]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![27, 122, 1, 0, 0], ![27, 61, 0, 1, 0], ![33, 95, 0, 0, 1]] where
  M :=![![![5, 21, -3, -38, -6], ![-36, -85, 74, 204, -38], ![-228, -606, 85, 516, 204], ![318, 775, -323, -1043, -16], ![630, 1797, 29, -1134, -887]]]
  hmulB := by decide  
  f := ![![![1256587, 670139, -296979, 54146, -106488]], ![![-638928, -340733, 151008, -27528, 54146]], ![![-333561, -177881, 78838, -14370, 28268]], ![![-39975, -21315, 9450, -1721, 3388]], ![![-147933, -78887, 34966, -6372, 12537]]]
  g := ![![![10, 25, -3, -38, -6], ![-48, -137, 74, 204, -38], ![-177, -472, 85, 516, 204], ![288, 804, -323, -1043, -16], ![456, 1158, 29, -1134, -887]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [94, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 130], [0, 1]]
 g := ![![[40, 46], [41, 74], [91], [41], [7], [80], [1]], ![[0, 85], [45, 57], [91], [41], [7], [80], [1]]]
 h' := ![![[39, 130], [76, 35], [26, 104], [117, 109], [33, 33], [6, 111], [37, 39], [0, 1]], ![[0, 1], [0, 96], [21, 27], [45, 22], [10, 98], [12, 20], [117, 92], [39, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [126, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [94, 92, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2797, 2652, -2706, -6072, 1209]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1526, 4491, -2706, -6072, 1209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, 258, 247, 123, 43]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![91, 258, 247, 123, 43]] 
 ![![131, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![91, 258, 247, 123, 43], ![258, 736, 704, 339, 123], ![738, 2103, 2017, 993, 339], ![-30, -81, -41, 7, -4], ![624, 1770, 1699, 819, 334]]]
  hmulB := by decide  
  f := ![![![16171481, 8624340, -3821979, 696831, -1370447]], ![![12158427, 6484156, -2873531, 523908, -1030362]], ![![2994630, 1597053, -707753, 129039, -253779]], ![![14301122, 7626867, -3379937, 616237, -1211944]], ![![2824685, 1506420, -667588, 121716, -239377]]]
  g := ![![![-356, 258, 247, 123, 43], ![-1005, 736, 704, 339, 123], ![-2892, 2103, 2017, 993, 339], ![63, -81, -41, 7, -4], ![-2428, 1770, 1699, 819, 334]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-1, 0, -1, -5, 1]] ![![5, 21, -3, -38, -6]]
  ![![-737, -1493, 1562, 3603, -1005]] where
 M := ![![![-737, -1493, 1562, 3603, -1005]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-737, -1493, 1562, 3603, -1005]] ![![91, 258, 247, 123, 43]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-34715, -74801, 62225, 156414, -35894]]]
 hmul := by decide  
 g := ![![![![-265, -571, 475, 1194, -274]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0, 0, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] where
  M :=![![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 5 2 7 [85, 63, 47, 123, 39, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 30, 3, 93, 18], [31, 50, 34, 62, 109], [59, 78, 73, 3, 61], [59, 115, 27, 116, 86], [0, 1]]
 g := ![![[28, 61, 21, 112, 130], [86, 125, 125, 61], [14, 93, 88, 61], [46, 102, 21, 135, 8], [96, 28, 98, 1], [], []], ![[96, 42, 91, 33, 52, 117, 81, 88], [89, 106, 91, 65], [94, 117, 8, 9], [105, 104, 42, 77, 113, 29, 130, 59], [73, 27, 27, 63], [15, 39, 26, 115], [53, 8, 28, 50]], ![[103, 120, 19, 20, 120, 72, 107, 135], [57, 45, 26, 73], [73, 101, 2, 129], [73, 53, 100, 84, 103, 65, 107, 2], [76, 13, 12, 87], [120, 74, 60, 93], [115, 106, 65, 99]], ![[14, 13, 46, 84, 82, 15, 58, 73], [0, 136, 106, 38], [89, 82, 60, 17], [30, 105, 91, 116, 115, 56, 131, 36], [123, 70, 102, 19], [41, 122, 88, 37], [4, 52, 56, 22]], ![[43, 12, 54, 39, 36, 47, 21, 57], [38, 39, 123, 30], [116, 28, 126, 136], [78, 18, 130, 64, 55, 33, 123, 42], [3, 78, 104, 44], [89, 66, 45, 109], [127, 129, 28, 135]]]
 h' := ![![[86, 30, 3, 93, 18], [102, 118, 68, 37, 33], [39, 86, 44, 57, 46], [63, 115, 13, 70, 46], [60, 66, 53, 71, 62], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[31, 50, 34, 62, 109], [39, 41, 106, 84, 9], [84, 53, 84, 71, 32], [26, 127, 5, 37, 3], [112, 21, 118, 43, 19], [17, 14, 59, 103, 36], [14, 45, 14, 116, 72], [86, 30, 3, 93, 18]], ![[59, 78, 73, 3, 61], [24, 6, 118, 94, 7], [38, 58, 113, 25, 115], [30, 70, 84, 113, 35], [117, 20, 34, 4, 122], [136, 126, 78, 86, 19], [91, 134, 15, 130, 40], [31, 50, 34, 62, 109]], ![[59, 115, 27, 116, 86], [59, 129, 90, 92, 71], [123, 18, 46, 100, 60], [4, 16, 16, 20, 90], [50, 102, 18, 99, 119], [40, 116, 1, 2, 108], [127, 11, 35, 120, 96], [59, 78, 73, 3, 61]], ![[0, 1], [42, 117, 29, 104, 17], [126, 59, 124, 21, 21], [81, 83, 19, 34, 100], [33, 65, 51, 57, 89], [39, 18, 136, 83, 110], [84, 84, 72, 45, 66], [59, 115, 27, 116, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 75, 2, 33], [], [], []]
 b := ![[], [44, 27, 3, 33, 21], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 5
  hpos := by decide
  P := [85, 63, 47, 123, 39, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![601203128, 1540785433, -449721543, -1784401025, -243308986]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4388344, 11246609, -3282639, -13024825, -1775978]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 48261724457 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀

instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-407, -476, 163, -63, 61]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-407, -476, 163, -63, 61]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![47, 120, 47, 1, 0], ![92, 66, 74, 0, 1]] where
  M :=![![![-407, -476, 163, -63, 61], ![366, 508, -168, 69, -63], ![-378, -579, 187, -81, 69], ![258, 399, -129, 61, -48], ![108, 156, -57, 9, -14]]]
  hmulB := by decide  
  f := ![![![-5, -10, -7, -3, -1]], ![![-6, -20, -24, -15, -3]], ![![-18, -51, -65, -45, -15]], ![![-13, -38, -45, -29, -8]], ![![-16, -44, -51, -33, -10]]]
  g := ![![![-22, 22, -10, -63, 61], ![21, -26, 9, 69, -63], ![-21, 33, -8, -81, 69], ![13, -27, 4, 61, -48], ![7, 0, 4, 9, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [50, 37, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 117, 99], [32, 21, 40], [0, 1]]
 g := ![![[120, 75, 51], [124, 128, 100], [129, 46], [43, 48, 4], [122, 129], [9, 1], []], ![[108, 32, 22, 29], [86, 26, 104, 91], [7, 31], [3, 133, 44, 29], [32, 83], [28, 24], [36, 71]], ![[66, 53, 132, 2], [8, 8, 87, 12], [134, 65], [53, 89, 19, 22], [116, 69], [42, 67], [95, 71]]]
 h' := ![![[116, 117, 99], [55, 133, 32], [138, 122, 129], [74, 89, 121], [132, 136, 137], [106, 34, 44], [0, 0, 1], [0, 1]], ![[32, 21, 40], [109, 2, 78], [34, 15, 53], [55, 9, 93], [102, 22, 78], [112, 81, 120], [119, 22, 21], [116, 117, 99]], ![[0, 1], [32, 4, 29], [19, 2, 96], [73, 41, 64], [121, 120, 63], [19, 24, 114], [27, 117, 117], [32, 21, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 81], []]
 b := ![[], [101, 36, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [50, 37, 130, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![122282, 314096, -54816, -333888, -29560]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![133342, 304544, 128240, -333888, -29560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-455699, -243026, 107700, -19636, 38618]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-455699, -243026, 107700, -19636, 38618]] 
 ![![139, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![106, 0, 0, 0, 1]] where
  M :=![![![-455699, -243026, 107700, -19636, 38618], ![231708, 123571, -54762, 9984, -19636], ![-117816, -62832, 27845, -5076, 9984], ![68892, 36740, -16282, 2969, -5838], ![53832, 28710, -12724, 2316, -4561]]]
  hmulB := by decide  
  f := ![![![2383, 7198, 7680, 3620, 1366]], ![![659, 1977, 2086, 988, 370]], ![![602, 1796, 1877, 892, 332]], ![![1147, 3462, 3690, 1741, 656]], ![![1954, 5878, 6232, 2948, 1107]]]
  g := ![![![17785, -243026, 107700, -19636, 38618], ![-9043, 123571, -54762, 9984, -19636], ![4598, -62832, 27845, -5076, 9984], ![-2689, 36740, -16282, 2969, -5838], ![-2100, 28710, -12724, 2316, -4561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![632479, 337277, -149512, 27239, -53605]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![632479, 337277, -149512, 27239, -53605]] 
 ![![139, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![100, 0, 0, 1, 0], ![102, 0, 0, 0, 1]] where
  M :=![![![632479, 337277, -149512, 27239, -53605], ![-321630, -171596, 75922, -13899, 27239], ![163434, 86955, -38887, 6927, -13899], ![-95616, -50986, 22604, -4117, 8104], ![-74790, -40059, 17452, -3321, 6296]]]
  hmulB := by decide  
  f := ![![![3337, 8385, -3026, -10765, -689]], ![![2443, 6163, -2150, -7786, -588]], ![![1792, 4479, -1701, -5905, -275]], ![![2824, 7028, -2732, -9347, -362]], ![![4056, 10377, -3142, -12261, -1516]]]
  g := ![![![-124526, 337277, -149512, 27239, -53605], ![63508, -171596, 75922, -13899, 27239], ![-31745, 86955, -38887, 6927, -13899], ![18822, -50986, 22604, -4117, 8104], ![15113, -40059, 17452, -3321, 6296]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-407, -476, 163, -63, 61]] ![![-455699, -243026, 107700, -19636, 38618]]
  ![![54916033, 29286860, -12978851, 2366309, -4653825]] where
 M := ![![![54916033, 29286860, -12978851, 2366309, -4653825]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![54916033, 29286860, -12978851, 2366309, -4653825]] ![![632479, 337277, -149512, 27239, -53605]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![23314321890079, 12433609789877, -5510110867403, 1004608513542, -1975760033440]]]
 hmul := by decide  
 g := ![![![![167728934461, 89450430143, -39641085377, 7227399378, -14214100960]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -73, 41, 118, -10]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-31, -73, 41, 118, -10]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![73, 122, 1, 0, 0], ![143, 78, 0, 1, 0], ![23, 72, 0, 0, 1]] where
  M :=![![![-31, -73, 41, 118, -10], ![-60, -181, -28, 72, 118], ![708, 1710, -809, -2508, 72], ![-282, -557, 655, 1483, -454], ![-2862, -7053, 2897, 9594, 193]]]
  hmulB := by decide  
  f := ![![![2521, 31, -241, -118, -76]], ![![-456, 1381, -270, 276, -118]], ![![857, 1131, -334, 166, -132]], ![![2185, 764, -376, 33, -136]], ![![169, 676, -168, 116, -69]]]
  g := ![![![-132, -91, 41, 118, -10], ![-74, -73, -28, 72, 118], ![2797, 1952, -809, -2508, 72], ![-1676, -1097, 655, 1483, -454], ![-10676, -7535, 2897, 9594, 193]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [11, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 148], [0, 1]]
 g := ![![[139, 30], [67], [2, 33], [4], [40, 127], [31], [1]], ![[12, 119], [67], [56, 116], [4], [4, 22], [31], [1]]]
 h' := ![![[110, 148], [45, 46], [127, 31], [5, 114], [7, 147], [78, 96], [138, 110], [0, 1]], ![[0, 1], [39, 103], [110, 118], [29, 35], [85, 2], [59, 53], [20, 39], [110, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [3, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [11, 39, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![705, 1413, -1140, -3021, 1021]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3305, 2031, -1140, -3021, 1021]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1991, -1011, 536, -57, 181]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-1991, -1011, 536, -57, 181]] 
 ![![149, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![119, 0, 0, 1, 0], ![131, 0, 0, 0, 1]] where
  M :=![![![-1991, -1011, 536, -57, 181], ![1086, 724, -70, 129, -57], ![-342, 231, 613, 219, 129], ![300, 150, -84, 7, -28], ![390, 561, 364, 219, 52]]]
  hmulB := by decide  
  f := ![![![-172999, -289137, 91834, -42003, 34795]], ![![-18337, -30647, 9734, -4452, 3688]], ![![-12141, -20292, 6445, -2946, 2442]], ![![-136981, -228939, 72714, -33260, 27551]], ![![-151663, -253476, 80508, -36828, 30503]]]
  g := ![![![-44, -1011, 536, -57, 181], ![-124, 724, -70, 129, -57], ![-354, 231, 613, 219, 129], ![9, 150, -84, 7, -28], ![-304, 561, 364, 219, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9607, -5124, 2270, -414, 814]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-9607, -5124, 2270, -414, 814]] 
 ![![149, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![122, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![-9607, -5124, 2270, -414, 814], ![4884, 2603, -1156, 210, -414], ![-2484, -1326, 581, -114, 210], ![1452, 774, -342, 65, -124], ![1128, 588, -266, 66, -97]]]
  hmulB := by decide  
  f := ![![![-453731, -758340, 240858, -110130, 91258]], ![![-185126, -309409, 98272, -44934, 37234]], ![![-95790, -160098, 50849, -23250, 19266]], ![![-368402, -615726, 195562, -89419, 74096]], ![![-403867, -675000, 214388, -98028, 81229]]]
  g := ![![![1223, -5124, 2270, -414, 814], ![-620, 2603, -1156, 210, -414], ![324, -1326, 581, -114, 210], ![-186, 774, -342, 65, -124], ![-151, 588, -266, 66, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2

def I149N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-391025, -209081, 92556, -16945, 33193]] i)))

def SI149N3: IdealEqSpanCertificate' Table ![![-391025, -209081, 92556, -16945, 33193]] 
 ![![149, 0, 0, 0, 0], ![97, 1, 0, 0, 0], ![127, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![129, 0, 0, 0, 1]] where
  M :=![![![-391025, -209081, 92556, -16945, 33193], ![199158, 106870, -47240, 8697, -16945], ![-101670, -55017, 24233, -4521, 8697], ![59532, 32306, -14214, 2663, -5102], ![46314, 24903, -11000, 2031, -3946]]]
  hmulB := by decide  
  f := ![![![767, 2789, 1626, 925, -3137]], ![![373, 1505, 1188, 1028, -2036]], ![![691, 2344, 1013, 176, -2248]], ![![505, 1443, 20, -920, -715]], ![![33, 1326, 3296, 4734, -4273]]]
  g := ![![![28022, -209081, 92556, -16945, 33193], ![-14410, 106870, -47240, 8697, -16945], ![7526, -55017, 24233, -4521, 8697], ![-4439, 32306, -14214, 2663, -5102], ![-3368, 24903, -11000, 2031, -3946]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N3 : Nat.card (O ⧸ I149N3) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N3)

lemma isPrimeI149N3 : Ideal.IsPrime I149N3 := prime_ideal_of_norm_prime hp149.out _ NI149N3
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-31, -73, 41, 118, -10]] ![![-1991, -1011, 536, -57, 181]]
  ![![-79, 50, 75, -35, 15]] where
 M := ![![![-79, 50, 75, -35, 15]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-79, 50, 75, -35, 15]] ![![-9607, -5124, 2270, -414, 814]]
  ![![782953, 417226, -185575, 33371, -66371]] where
 M := ![![![782953, 417226, -185575, 33371, -66371]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N2 : IdealMulLeCertificate' Table 
  ![![782953, 417226, -185575, 33371, -66371]] ![![-391025, -209081, 92556, -16945, 33193]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-205280154989, -109476627285, 48515948259, -8845472016, 17396359708]]]
 hmul := by decide  
 g := ![![![![-1377719161, -734742465, 325610391, -59365584, 116754092]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2, I149N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
    exact isPrimeI149N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1 ⊙ MulI149N2)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![857, 2006, -1127, -3225, 281]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![857, 2006, -1127, -3225, 281]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![103, 113, 104, 132, 1]] where
  M :=![![![857, 2006, -1127, -3225, 281], ![1686, 5072, 726, -2145, -3225], ![-19350, -46689, 22295, 68841, -2145], ![7530, 14757, -17825, -40111, 12546], ![78516, 193302, -79971, -263937, -4618]]]
  hmulB := by decide  
  f := ![![![417215, 222508, -98605, 17979, -35357]], ![![-212142, -113140, 50142, -9141, 17979]], ![![107874, 57543, -25489, 4653, -9141]], ![![-63078, -33645, 14909, -2719, 5346]], ![![144665, 77156, -34182, 6237, -12258]]]
  g := ![![![-186, -197, -201, -267, 281], ![2211, 2447, 2226, 2805, -3225], ![1335, 1296, 1625, 2331, -2145], ![-8508, -9291, -8759, -11233, 12546], ![3670, 4736, 2651, 2289, -4618]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [87, 12, 146, 90, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 138, 12, 38], [123, 49, 83, 81], [55, 114, 56, 32], [0, 1]]
 g := ![![[43, 133, 125, 74], [109, 16, 144, 136], [18, 65, 64, 76], [78, 1, 47], [118, 63, 34, 97], [1], []], ![[102, 51, 94, 30, 65, 105], [125, 47, 135, 135, 91, 68], [87, 148, 103, 76, 92, 136], [9, 102, 40], [148, 107, 43, 53, 134, 10], [19, 141, 58], [38, 57, 85]], ![[34, 31, 139, 86, 89, 1], [108, 59, 70, 4, 48, 128], [142, 59, 80, 111, 13, 137], [137, 81, 29], [24, 45, 64, 21, 27, 116], [58, 5, 125], [144, 78, 68]], ![[96, 46, 30, 38, 40, 121], [89, 133, 104, 54, 25, 45], [73, 130, 71, 27, 17, 76], [125, 21, 39], [109, 88, 42, 65, 115, 29], [9, 24, 124], [96, 61, 118]]]
 h' := ![![[34, 138, 12, 38], [30, 134, 101, 136], [95, 36, 37, 49], [13, 4, 91, 23], [2, 68, 21, 54], [64, 139, 5, 61], [0, 0, 1], [0, 1]], ![[123, 49, 83, 81], [97, 142, 6, 32], [136, 136, 27, 140], [3, 11, 26, 98], [129, 53, 26, 77], [96, 113, 34, 77], [115, 43, 42, 80], [34, 138, 12, 38]], ![[55, 114, 56, 32], [76, 54, 48, 84], [72, 46, 81, 108], [41, 58, 24, 11], [129, 86, 138, 123], [36, 103, 137, 23], [34, 67, 77, 27], [123, 49, 83, 81]], ![[0, 1], [8, 123, 147, 50], [90, 84, 6, 5], [33, 78, 10, 19], [6, 95, 117, 48], [75, 98, 126, 141], [109, 41, 31, 44], [55, 114, 56, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [46, 118, 142], []]
 b := ![[], [], [62, 72, 25, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [87, 12, 146, 90, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5571, -30892, 22867, 63678, -10369]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7036, 7555, 7293, 9486, -10369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-417215, -222508, 98605, -17979, 35357]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-417215, -222508, 98605, -17979, 35357]] 
 ![![151, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-417215, -222508, 98605, -17979, 35357], ![212142, 113140, -50142, 9141, -17979], ![-107874, -57543, 25489, -4653, 9141], ![63078, 33645, -14909, 2719, -5346], ![49284, 26280, -11655, 2121, -4178]]]
  hmulB := by decide  
  f := ![![![-857, -2006, 1127, 3225, -281]], ![![-119, -286, 137, 420, -14]], ![![-394, -913, 539, 1509, -157]], ![![-135, -297, 230, 586, -111]], ![![-537, -1320, 552, 1812, 25]]]
  g := ![![![-33759, -222508, 98605, -17979, 35357], ![17168, 113140, -50142, 9141, -17979], ![-8723, -57543, 25489, -4653, 9141], ![5104, 33645, -14909, 2719, -5346], ![3993, 26280, -11655, 2121, -4178]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![857, 2006, -1127, -3225, 281]] ![![-417215, -222508, 98605, -17979, 35357]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB1556I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1556I3 : PrimesBelowBoundCertificateInterval O 103 151 1556 where
  m := 9
  g := ![3, 2, 3, 2, 3, 1, 3, 4, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1556I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1, I149N2, I149N3]
    · exact ![I151N0, I151N1]
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
    · exact ![1225043, 107, 107]
    · exact ![141158161, 109]
    · exact ![12769, 12769, 113]
    · exact ![260144641, 127]
    · exact ![17161, 17161, 131]
    · exact ![48261724457]
    · exact ![2685619, 139, 139]
    · exact ![22201, 149, 149, 149]
    · exact ![519885601, 151]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
      exact NI149N3
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I107N2, I109N1, I113N2, I127N1, I131N2, I139N1, I139N2, I149N1, I149N2, I149N3, I151N1]
  Il := ![[I107N1, I107N2], [I109N1], [I113N2], [I127N1], [I131N2], [], [I139N1, I139N2], [I149N1, I149N2, I149N3], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
