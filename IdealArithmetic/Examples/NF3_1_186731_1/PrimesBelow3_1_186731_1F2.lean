
import IdealArithmetic.Examples.NF3_1_186731_1.RI3_1_186731_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7350997, -576417, 712546]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![7350997, -576417, 712546]] 
 ![![83, 0, 0], ![0, 83, 0], ![44, 81, 1]] where
  M :=![![![7350997, -576417, 712546], ![-60870569, 4773071, -5900299], ![67081353, -5260080, 6502322]]]
  hmulB := by decide  
  f := ![![![-2326, -282, -1]], ![![-763, -2888, -2537]], ![![-1696, -2961, -2501]]]
  g := ![![![-289169, -702321, 712546], ![2394489, 5815630, -5900299], ![-2638805, -6409014, 6502322]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [63, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 82], [0, 1]]
 g := ![![[42, 29], [32, 30], [23], [77], [72, 17], [1]], ![[0, 54], [0, 53], [23], [77], [76, 66], [1]]]
 h' := ![![[10, 82], [59, 19], [57, 69], [57, 43], [29, 49], [20, 10], [0, 1]], ![[0, 1], [0, 64], [0, 14], [72, 40], [21, 34], [37, 73], [10, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [60, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [63, 73, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2274, -1617, -1059]
  a := ![-4, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![534, 1014, -1059]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2326, 282, 1]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![2326, 282, 1]] 
 ![![83, 0, 0], ![19, 1, 0], ![39, 0, 1]] where
  M :=![![![2326, 282, 1], ![763, 2888, 2537], ![-23379, -573, 2042]]]
  hmulB := by decide  
  f := ![![![-7350997, 576417, -712546]], ![![-949378, 74444, -92025]], ![![-4262292, 334221, -413152]]]
  g := ![![![-37, 282, 1], ![-1844, 2888, 2537], ![-1110, -573, 2042]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![7350997, -576417, 712546]] ![![2326, 282, 1]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![32, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![32, 1, 0]] 
 ![![89, 0, 0], ![32, 1, 0], ![8, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![32, 1, 0], ![3, 34, 9], ![-83, -2, 31]]]
  hmulB := by decide  
  f := ![![![7937, 106578, 28224], ![4094, -279104, 0]], ![![2837, 38301, 10143], ![1514, -100303, 0]], ![![712, 9580, 2537], ![372, -25088, 0]]]
  g := ![![![1, 0, 0], ![-32, 89, 0], ![-8, 0, 89]], ![![0, 1, 0], ![-13, 34, 9], ![-3, -2, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-30, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-30, 1, 0]] 
 ![![89, 0, 0], ![59, 1, 0], ![85, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-30, 1, 0], ![3, -28, 9], ![-83, -2, -31]]]
  hmulB := by decide  
  f := ![![![3133, -33696, 10836], ![-1424, -107156, 0]], ![![2095, -22334, 7182], ![-889, -71022, 0]], ![![3005, -32182, 10349], ![-1322, -102340, 0]]]
  g := ![![![1, 0, 0], ![-59, 89, 0], ![-85, 0, 89]], ![![-1, 1, 0], ![10, -28, 9], ![30, -2, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1189949, -93308, 115344]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![1189949, -93308, 115344]] 
 ![![89, 0, 0], ![86, 1, 0], ![0, 0, 1]] where
  M :=![![![1189949, -93308, 115344], ![-9853476, 772645, -955116], ![10858852, -851480, 1052569]]]
  hmulB := by decide  
  f := ![![![3325, -868, -1152]], ![![4258, -795, -1188]], ![![460, 136, 73]]]
  g := ![![![103533, -93308, 115344], ![-857314, 772645, -955116], ![944788, -851480, 1052569]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![32, 1, 0]] ![![89, 0, 0], ![-30, 1, 0]]
  ![![-3325, 868, 1152]] where
 M := ![![![7921, 0, 0], ![-2670, 89, 0]], ![![2848, 89, 0], ![-957, 4, 9]]]
 hmul := by decide  
 g := ![![![![-105905461, 8304412, -10265616]], ![![45551946, -3571885, 4415436]]], ![![![-28224892, 2213211, -2735892]], ![![12140061, -951944, 1176759]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-3325, 868, 1152]] ![![1189949, -93308, 115344]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, 8, -6]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![121, 8, -6]] 
 ![![97, 0, 0], ![24, 1, 0], ![28, 0, 1]] where
  M :=![![![121, 8, -6], ![522, 149, 78], ![-826, 38, 125]]]
  hmulB := by decide  
  f := ![![![15661, -1228, 1518]], ![![2538, -199, 246]], ![![5994, -470, 581]]]
  g := ![![![1, 8, -6], ![-54, 149, 78], ![-54, 38, 125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![34, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![34, 1, 0]] 
 ![![97, 0, 0], ![34, 1, 0], ![26, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![34, 1, 0], ![3, 36, 9], ![-83, -2, 33]]]
  hmulB := by decide  
  f := ![![![-4763, -66936, -16740], ![-2328, 180420, 0]], ![![-1681, -23428, -5859], ![-775, 63147, 0]], ![![-1290, -17942, -4487], ![-586, 48360, 0]]]
  g := ![![![1, 0, 0], ![-34, 97, 0], ![-26, 0, 97]], ![![0, 1, 0], ![-15, 36, 9], ![-9, -2, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![38, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![38, 1, 0]] 
 ![![97, 0, 0], ![38, 1, 0], ![47, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![38, 1, 0], ![3, 40, 9], ![-83, -2, 37]]]
  hmulB := by decide  
  f := ![![![-4938, -80012, -18009], ![-2716, 194097, 0]], ![![-1931, -31309, -7047], ![-1066, 75951, 0]], ![![-2404, -38769, -8726], ![-1287, 94047, 0]]]
  g := ![![![1, 0, 0], ![-38, 97, 0], ![-47, 0, 97]], ![![0, 1, 0], ![-20, 40, 9], ![-18, -2, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![121, 8, -6]] ![![97, 0, 0], ![34, 1, 0]]
  ![![97, 0, 0], ![-6, 39, 1]] where
 M := ![![![11737, 776, -582], ![4636, 421, -126]]]
 hmul := by decide  
 g := ![![![![121, 8, -6], ![0, 0, 0]], ![![52, -23, -2], ![68, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-6, 39, 1]] ![![97, 0, 0], ![38, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3686, 97, 0]], ![![-582, 3783, 97], ![-194, 1552, 388]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![38, 1, 0]]], ![![![-6, 39, 1]], ![![-2, 16, 4]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![4, -33, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![4, -33, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![4, 68, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![4, -33, 1], ![-182, -64, -298], ![2766, 57, 35]]]
  hmulB := by decide  
  f := ![![![-3, 33, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -68, 101]], ![![0, -1, 1], ![10, 200, -298], ![26, -23, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [33, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 100], [0, 1]]
 g := ![![[98, 49], [79], [31, 81], [5], [33], [99, 1]], ![[0, 52], [79], [71, 20], [5], [33], [97, 100]]]
 h' := ![![[99, 100], [87, 94], [88, 68], [50, 9], [35, 45], [66, 72], [0, 1]], ![[0, 1], [0, 7], [53, 33], [32, 92], [46, 56], [23, 29], [99, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [30, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [33, 2, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![316, -1597, -224]
  a := ![4, 2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 135, -224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-5, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-5, 1, 0]] 
 ![![101, 0, 0], ![96, 1, 0], ![66, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-5, 1, 0], ![3, -3, 9], ![-83, -2, -6]]]
  hmulB := by decide  
  f := ![![![-5559, 5576, -16740], ![404, 187860, 0]], ![![-5280, 5297, -15903], ![405, 178467, 0]], ![![-3634, 3644, -10939], ![236, 122760, 0]]]
  g := ![![![1, 0, 0], ![-96, 101, 0], ![-66, 0, 101]], ![![-1, 1, 0], ![-3, -3, 9], ![5, -2, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![4, -33, 1]] ![![101, 0, 0], ![-5, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-505, 101, 0]], ![![404, -3333, 101], ![-202, 101, -303]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-5, 1, 0]]], ![![![4, -33, 1]], ![![-2, 1, -3]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [98, 49, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 33, 62], [97, 69, 41], [0, 1]]
 g := ![![[88, 40, 29], [102, 48, 4], [91, 20, 83], [28, 4], [46, 72], [1]], ![[42, 20, 48, 70], [8, 20, 77, 53], [101, 50, 41, 77], [29, 97], [54, 7], [72, 14, 75, 89]], ![[1, 49, 73, 50], [54, 35, 95, 64], [0, 57, 34, 28], [24, 23], [29, 46], [32, 90, 32, 14]]]
 h' := ![![[28, 33, 62], [98, 78, 82], [43, 93, 2], [69, 62, 17], [49, 88, 2], [5, 54, 22], [0, 1]], ![[97, 69, 41], [78, 82, 91], [71, 79, 33], [97, 12, 73], [40, 17, 32], [64, 101, 25], [28, 33, 62]], ![[0, 1], [11, 46, 33], [52, 34, 68], [36, 29, 13], [88, 101, 69], [47, 51, 56], [97, 69, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 91], []]
 b := ![[], [98, 36, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [98, 49, 81, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-109257398732, -2815328046, 3282648110]
  a := ![-194, -129, -518]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1060751444, -27333282, 31870370]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![31, -25, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![31, -25, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![31, 82, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![31, -25, 1], ![-158, -21, -226], ![2102, 41, 54]]]
  hmulB := by decide  
  f := ![![![-30, 25, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -82, 107]], ![![0, -1, 1], ![64, 173, -226], ![4, -41, 54]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [64, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 106], [0, 1]]
 g := ![![[8, 102], [1, 25], [102], [47, 87], [85], [23, 1]], ![[0, 5], [41, 82], [102], [15, 20], [85], [46, 106]]]
 h' := ![![[23, 106], [43, 40], [36, 102], [95, 40], [51, 27], [26, 37], [0, 1]], ![[0, 1], [0, 67], [28, 5], [52, 67], [30, 80], [21, 70], [23, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [82, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [64, 84, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1360, -2700, -1711]
  a := ![-5, -3, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![483, 1286, -1711]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![12, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![12, 1, 0]] 
 ![![107, 0, 0], ![12, 1, 0], ![53, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![12, 1, 0], ![3, 14, 9], ![-83, -2, 11]]]
  hmulB := by decide  
  f := ![![![-878, -4157, -2673], ![-107, 31779, 0]], ![![-99, -462, -297], ![1, 3531, 0]], ![![-434, -2059, -1324], ![-61, 15741, 0]]]
  g := ![![![1, 0, 0], ![-12, 107, 0], ![-53, 0, 107]], ![![0, 1, 0], ![-6, 14, 9], ![-6, -2, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![31, -25, 1]] ![![107, 0, 0], ![12, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![1284, 107, 0]], ![![3317, -2675, 107], ![214, -321, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![12, 1, 0]]], ![![![31, -25, 1]], ![![2, -3, -2]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![3, 33, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![3, 33, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![3, 33, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![3, 33, 1], ![16, 67, 296], ![-2712, -75, -32]]]
  hmulB := by decide  
  f := ![![![-2, -33, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -33, 109]], ![![0, 0, 1], ![-8, -89, 296], ![-24, 9, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [60, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 108], [0, 1]]
 g := ![![[80, 20], [64], [104, 89], [45, 5], [83], [105, 1]], ![[0, 89], [64], [75, 20], [25, 104], [83], [101, 108]]]
 h' := ![![[105, 108], [50, 67], [82, 101], [25, 31], [82, 21], [22, 65], [0, 1]], ![[0, 1], [0, 42], [5, 8], [10, 78], [107, 88], [89, 44], [105, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [37, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [60, 4, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2001, -1410, -231]
  a := ![-4, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, 57, -231]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![31, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![31, 1, 0]] 
 ![![109, 0, 0], ![31, 1, 0], ![32, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![31, 1, 0], ![3, 33, 9], ![-83, -2, 30]]]
  hmulB := by decide  
  f := ![![![29395, 360054, 98226], ![11772, -1189626, 0]], ![![8348, 102368, 27927], ![3380, -338227, 0]], ![![8632, 105704, 28837], ![3448, -349248, 0]]]
  g := ![![![1, 0, 0], ![-31, 109, 0], ![-32, 0, 109]], ![![0, 1, 0], ![-12, 33, 9], ![-9, -2, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![3, 33, 1]] ![![109, 0, 0], ![31, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3379, 109, 0]], ![![327, 3597, 109], ![109, 1090, 327]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![31, 1, 0]]], ![![![3, 33, 1]], ![![1, 10, 3]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![41, 11, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![41, 11, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![41, 11, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![41, 11, 1], ![-50, 61, 98], ![-886, -31, 28]]]
  hmulB := by decide  
  f := ![![![-40, -11, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -11, 113]], ![![0, 0, 1], ![-36, -9, 98], ![-18, -3, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [90, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 112], [0, 1]]
 g := ![![[20, 83], [18], [91], [95], [21, 111], [8, 1]], ![[6, 30], [18], [91], [95], [5, 2], [16, 112]]]
 h' := ![![[8, 112], [90, 14], [44, 73], [95, 59], [31, 78], [71, 87], [0, 1]], ![[0, 1], [89, 99], [63, 40], [2, 54], [90, 35], [89, 26], [8, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [58, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [90, 105, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![187, -705, -927]
  a := ![-3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![338, 84, -927]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![15, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![15, 1, 0]] 
 ![![113, 0, 0], ![15, 1, 0], ![85, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![15, 1, 0], ![3, 17, 9], ![-83, -2, 14]]]
  hmulB := by decide  
  f := ![![![8890, 51631, 27342], ![1695, -343294, 0]], ![![1179, 6849, 3627], ![227, -45539, 0]], ![![6680, 38837, 20567], ![1329, -258230, 0]]]
  g := ![![![1, 0, 0], ![-15, 113, 0], ![-85, 0, 113]], ![![0, 1, 0], ![-9, 17, 9], ![-11, -2, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![41, 11, 1]] ![![113, 0, 0], ![15, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![1695, 113, 0]], ![![4633, 1243, 113], ![565, 226, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![15, 1, 0]]], ![![![41, 11, 1]], ![![5, 2, 1]]]]
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


lemma PB123I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 122 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 122 (by omega)

def PB123I2 : PrimesBelowBoundCertificateInterval O 79 122 123 where
  m := 8
  g := ![2, 3, 3, 2, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB123I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
  β := ![I83N1, I89N0, I89N1, I89N2, I97N0, I97N1, I97N2, I101N1, I107N1, I109N1, I113N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N0, I97N1, I97N2], [I101N1], [], [I107N1], [I109N1], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
