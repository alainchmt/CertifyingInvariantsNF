
import IdealArithmetic.Examples.NF3_1_484300_1.RI3_1_484300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-656, -17, 76]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-656, -17, 76]] 
 ![![83, 0, 0], ![0, 83, 0], ![70, 38, 1]] where
  M :=![![![-656, -17, 76], ![-9289, -1872, 25], ![-1422, -3224, -1889]]]
  hmulB := by decide  
  f := ![![![-43576, 3339, -1709]], ![![211837, -16232, 8308]], ![![56274, -4312, 2207]]]
  g := ![![![-72, -35, 76], ![-133, -34, 25], ![1576, 826, -1889]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [61, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 82], [0, 1]]
 g := ![![[22, 49], [71, 11], [51], [27], [43, 30], [1]], ![[0, 34], [0, 72], [51], [27], [38, 53], [1]]]
 h' := ![![[69, 82], [68, 76], [74, 29], [23, 36], [33, 44], [22, 69], [0, 1]], ![[0, 1], [0, 7], [0, 54], [17, 47], [81, 39], [52, 14], [69, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [66, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [61, 14, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1097, -522, -171]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![131, 72, -171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43576, 3339, -1709]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-43576, 3339, -1709]] 
 ![![83, 0, 0], ![51, 1, 0], ![74, 0, 1]] where
  M :=![![![-43576, 3339, -1709], ![211837, -16232, 8308], ![-328744, 25190, -12893]]]
  hmulB := by decide  
  f := ![![![-656, -17, 76]], ![![-515, -33, 47]], ![![-602, -54, 45]]]
  g := ![![![-1053, 3339, -1709], ![5119, -16232, 8308], ![-7944, 25190, -12893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-656, -17, 76]] ![![-43576, 3339, -1709]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -4, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-29, -4, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![60, 85, 1]] where
  M :=![![![-29, -4, 1], ![-126, -45, -11], ![442, 18, -49]]]
  hmulB := by decide  
  f := ![![![-27, 2, -1]], ![![124, -11, 5]], ![![98, -9, 4]]]
  g := ![![![-1, -1, 1], ![6, 10, -11], ![38, 47, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [39, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 88], [0, 1]]
 g := ![![[18, 16], [47], [10], [82, 1], [42, 11], [1]], ![[0, 73], [47], [10], [3, 88], [63, 78], [1]]]
 h' := ![![[10, 88], [40, 85], [2, 15], [6, 30], [53, 88], [50, 10], [0, 1]], ![[0, 1], [0, 4], [63, 74], [39, 59], [43, 1], [61, 79], [10, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [3, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [39, 79, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1367, -1972, -219]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![163, 187, -219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -2, 1]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![27, -2, 1]] 
 ![![89, 0, 0], ![11, 1, 0], ![49, 0, 1]] where
  M :=![![![27, -2, 1], ![-124, 11, -5], ![198, -14, 9]]]
  hmulB := by decide  
  f := ![![![29, 4, -1]], ![![5, 1, 0]], ![![11, 2, 0]]]
  g := ![![![0, -2, 1], ![0, 11, -5], ![-1, -14, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-29, -4, 1]] ![![27, -2, 1]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![32, -20, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![32, -20, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![32, 77, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![32, -20, 1], ![-142, 16, -59], ![2394, 274, -4]]]
  hmulB := by decide  
  f := ![![![-31, 20, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -77, 97]], ![![0, -1, 1], ![18, 47, -59], ![26, 6, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [28, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 96], [0, 1]]
 g := ![![[88, 73], [88], [62], [1], [86], [58, 1]], ![[54, 24], [88], [62], [1], [86], [19, 96]]]
 h' := ![![[58, 96], [25, 49], [8, 66], [80, 81], [60, 1], [25, 38], [0, 1]], ![[0, 1], [54, 48], [53, 31], [25, 16], [21, 96], [95, 59], [58, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [62, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [28, 39, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-591, -1995, -1040]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![337, 805, -1040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-38, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-38, 1, 0]] 
 ![![97, 0, 0], ![59, 1, 0], ![4, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-38, 1, 0], ![1, -38, 3], ![-122, -16, -37]]]
  hmulB := by decide  
  f := ![![![4583, -236165, 18648], ![-4171, -602952, 0]], ![![2793, -143614, 11340], ![-2521, -366660, 0]], ![![198, -9739, 769], ![-149, -24864, 0]]]
  g := ![![![1, 0, 0], ![-59, 97, 0], ![-4, 0, 97]], ![![-1, 1, 0], ![23, -38, 3], ![10, -16, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![32, -20, 1]] ![![97, 0, 0], ![-38, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3686, 97, 0]], ![![3104, -1940, 97], ![-1358, 776, -97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-38, 1, 0]]], ![![![32, -20, 1]], ![![-14, 8, -1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [51, 98, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 57, 17], [13, 43, 84], [0, 1]]
 g := ![![[44, 47, 16], [93, 79], [34, 11, 85], [98, 84], [25, 81], [1]], ![[47, 49, 55, 19], [86, 5], [40, 80, 67, 96], [86, 68], [69, 79], [81, 12, 51, 65]], ![[90, 31, 85, 100], [54, 43], [91, 26, 45, 92], [98, 78], [79, 47], [92, 82, 92, 36]]]
 h' := ![![[79, 57, 17], [91, 87, 4], [84, 3, 33], [19, 61, 61], [13, 82, 36], [50, 3, 92], [0, 1]], ![[13, 43, 84], [25, 28, 35], [13, 67, 56], [94, 65, 24], [95, 89, 13], [68, 80, 68], [79, 57, 17]], ![[0, 1], [25, 87, 62], [70, 31, 12], [56, 76, 16], [2, 31, 52], [30, 18, 42], [13, 43, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 21], []]
 b := ![[], [14, 23, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [51, 98, 9, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-228159, -47268, -909]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2259, -468, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![17, 24, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![17, 24, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![17, 24, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![17, 24, 1], ![-98, 1, 73], ![-2974, -430, 25]]]
  hmulB := by decide  
  f := ![![![-16, -24, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -24, 103]], ![![0, 0, 1], ![-13, -17, 73], ![-33, -10, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [89, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 102], [0, 1]]
 g := ![![[22, 4], [63, 81], [73, 76], [8], [19], [102, 1]], ![[18, 99], [85, 22], [100, 27], [8], [19], [101, 102]]]
 h' := ![![[102, 102], [58, 2], [95, 94], [37, 73], [50, 76], [89, 15], [0, 1]], ![[0, 1], [56, 101], [1, 9], [67, 30], [77, 27], [74, 88], [102, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [56, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [89, 1, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23874, -4095, 898]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-380, -249, 898]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![30, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![30, 1, 0]] 
 ![![103, 0, 0], ![30, 1, 0], ![78, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![30, 1, 0], ![1, 30, 3], ![-122, -16, 31]]]
  hmulB := by decide  
  f := ![![![-5487, -194307, -19434], ![-3399, 667234, 0]], ![![-1616, -56571, -5658], ![-926, 194258, 0]], ![![-4152, -147145, -14717], ![-2585, 505284, 0]]]
  g := ![![![1, 0, 0], ![-30, 103, 0], ![-78, 0, 103]], ![![0, 1, 0], ![-11, 30, 3], ![-20, -16, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![17, 24, 1]] ![![103, 0, 0], ![30, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3090, 103, 0]], ![![1751, 2472, 103], ![412, 721, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![30, 1, 0]]], ![![![17, 24, 1]], ![![4, 7, 1]]]]
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
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [101, 78, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 33, 69], [68, 73, 38], [0, 1]]
 g := ![![[104, 33, 13], [27, 100, 76], [21, 36], [80, 2, 52], [35, 39], [1]], ![[25, 42, 97, 29], [99, 36, 103, 48], [16, 34], [9, 70, 100, 44], [94, 79], [93, 102, 98, 19]], ![[80, 95, 100, 2], [4, 89, 16, 95], [0, 61], [2, 101, 34, 15], [94, 44], [101, 46, 64, 88]]]
 h' := ![![[89, 33, 69], [55, 49, 21], [48, 66, 66], [52, 39, 6], [32, 99, 42], [6, 29, 50], [0, 1]], ![[68, 73, 38], [8, 61, 99], [78, 85, 63], [93, 17, 26], [27, 48, 53], [76, 75, 87], [89, 33, 69]], ![[0, 1], [95, 104, 94], [90, 63, 85], [82, 51, 75], [73, 67, 12], [30, 3, 77], [68, 73, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 27], []]
 b := ![[], [91, 45, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [101, 78, 57, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-227268, -153973, -68587]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2124, -1439, -641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![45, 50, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![45, 50, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![45, 50, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![45, 50, 1], ![-72, 29, 151], ![-6146, -846, 79]]]
  hmulB := by decide  
  f := ![![![-44, -50, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -50, 109]], ![![0, 0, 1], ![-63, -69, 151], ![-89, -44, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [39, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 108], [0, 1]]
 g := ![![[32, 4], [93], [7, 61], [43, 81], [97], [60, 1]], ![[54, 105], [93], [70, 48], [107, 28], [97], [11, 108]]]
 h' := ![![[60, 108], [52, 107], [54, 23], [67, 37], [17, 9], [58, 73], [0, 1]], ![[0, 1], [41, 2], [17, 86], [107, 72], [12, 100], [78, 36], [60, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [68, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [39, 49, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2978, -1795, -243]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, 95, -243]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-42, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-42, 1, 0]] 
 ![![109, 0, 0], ![67, 1, 0], ![30, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-42, 1, 0], ![1, -42, 3], ![-122, -16, -41]]]
  hmulB := by decide  
  f := ![![![1105, -60472, 4320], ![-872, -156960, 0]], ![![676, -37165, 2655], ![-544, -96465, 0]], ![![318, -16644, 1189], ![-204, -43200, 0]]]
  g := ![![![1, 0, 0], ![-67, 109, 0], ![-30, 0, 109]], ![![-1, 1, 0], ![25, -42, 3], ![20, -16, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![45, 50, 1]] ![![109, 0, 0], ![-42, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-4578, 109, 0]], ![![4905, 5450, 109], ![-1962, -2071, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-42, 1, 0]]], ![![![45, 50, 1]], ![![-18, -19, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [65, 35, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 24, 7], [17, 88, 106], [0, 1]]
 g := ![![[6, 78, 41], [80, 51], [6, 106], [68, 97], [88, 27, 26], [1]], ![[4, 67, 51, 112], [3, 91], [47, 2], [2, 87], [10, 85, 71, 13], [33, 97, 2, 4]], ![[62, 86, 23, 18], [75, 7], [37, 77], [50, 25], [101, 80, 36, 87], [106, 4, 77, 109]]]
 h' := ![![[62, 24, 7], [85, 25, 43], [55, 25, 86], [28, 101, 85], [43, 68, 53], [48, 78, 79], [0, 1]], ![[17, 88, 106], [15, 56, 4], [60, 77, 59], [105, 82, 51], [110, 68, 55], [13, 29, 40], [62, 24, 7]], ![[0, 1], [12, 32, 66], [49, 11, 81], [9, 43, 90], [78, 90, 5], [57, 6, 107], [17, 88, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 16], []]
 b := ![[], [112, 61, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [65, 35, 34, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6434785, -1559400, -192100]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56945, -13800, -1700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-25, 23, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-25, 23, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![102, 23, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-25, 23, 1], ![-99, -41, 70], ![-2852, -414, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -23, 127]], ![![-1, 0, 1], ![-57, -13, 70], ![-8, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [90, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 126], [0, 1]]
 g := ![![[70, 104], [93, 41], [24, 25], [4, 44], [18, 9], [50, 1]], ![[63, 23], [111, 86], [4, 102], [45, 83], [87, 118], [100, 126]]]
 h' := ![![[50, 126], [12, 72], [126, 26], [21, 122], [31, 67], [72, 124], [0, 1]], ![[0, 1], [56, 55], [29, 101], [25, 5], [79, 60], [49, 3], [50, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [111, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [90, 77, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20314, -2250, -650]
  a := ![4, -10, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![682, 100, -650]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![57, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![57, 1, 0]] 
 ![![127, 0, 0], ![57, 1, 0], ![18, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![57, 1, 0], ![1, 57, 3], ![-122, -16, 58]]]
  hmulB := by decide  
  f := ![![![-6302, -537911, -28314], ![-6985, 1198626, 0]], ![![-2867, -241371, -12705], ![-3047, 537845, 0]], ![![-930, -76240, -4013], ![-908, 169884, 0]]]
  g := ![![![1, 0, 0], ![-57, 127, 0], ![-18, 0, 127]], ![![0, 1, 0], ![-26, 57, 3], ![-2, -16, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-25, 23, 1]] ![![127, 0, 0], ![57, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![7239, 127, 0]], ![![-3175, 2921, 127], ![-1524, 1270, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![57, 1, 0]]], ![![![-25, 23, 1]], ![![-12, 10, 1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-62, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-62, 1, 0]] 
 ![![131, 0, 0], ![69, 1, 0], ![29, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-62, 1, 0], ![1, -62, 3], ![-122, -16, -61]]]
  hmulB := by decide  
  f := ![![![-610, 64783, -3135], ![917, 136895, 0]], ![![-301, 34096, -1650], ![525, 72050, 0]], ![![-118, 14341, -694], ![239, 30305, 0]]]
  g := ![![![1, 0, 0], ![-69, 131, 0], ![-29, 0, 131]], ![![-1, 1, 0], ![32, -62, 3], ![21, -16, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-39, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-39, 1, 0]] 
 ![![131, 0, 0], ![92, 1, 0], ![61, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-39, 1, 0], ![1, -39, 3], ![-122, -16, -38]]]
  hmulB := by decide  
  f := ![![![-1230, 58649, -4512], ![917, 197024, 0]], ![![-860, 41179, -3168], ![656, 138336, 0]], ![![-579, 27310, -2101], ![406, 91744, 0]]]
  g := ![![![1, 0, 0], ![-92, 131, 0], ![-61, 0, 131]], ![![-1, 1, 0], ![26, -39, 3], ![28, -16, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-31, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-31, 1, 0]] 
 ![![131, 0, 0], ![100, 1, 0], ![73, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-31, 1, 0], ![1, -31, 3], ![-122, -16, -30]]]
  hmulB := by decide  
  f := ![![![-628, 22379, -2166], ![393, 94582, 0]], ![![-488, 17079, -1653], ![263, 72181, 0]], ![![-358, 12471, -1207], ![185, 52706, 0]]]
  g := ![![![1, 0, 0], ![-100, 131, 0], ![-73, 0, 131]], ![![-1, 1, 0], ![22, -31, 3], ![28, -16, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-62, 1, 0]] ![![131, 0, 0], ![-39, 1, 0]]
  ![![131, 0, 0], ![64, 10, 1]] where
 M := ![![![17161, 0, 0], ![-5109, 131, 0]], ![![-8122, 131, 0], ![2419, -101, 3]]]
 hmul := by decide  
 g := ![![![![67, -10, -1], ![131, 0, 0]], ![![-39, 1, 0], ![0, 0, 0]]], ![![![-62, 1, 0], ![0, 0, 0]], ![![-47, -11, -1], ![134, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![64, 10, 1]] ![![131, 0, 0], ![-31, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-4061, 131, 0]], ![![8384, 1310, 131], ![-2096, -262, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-31, 1, 0]]], ![![![64, 10, 1]], ![![-16, -2, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-435, -60, 19]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-435, -60, 19]] 
 ![![137, 0, 0], ![0, 137, 0], ![42, 105, 1]] where
  M :=![![![-435, -60, 19], ![-2378, -739, -161], ![6446, 86, -799]]]
  hmulB := by decide  
  f := ![![![4411, -338, 173]], ![![-21444, 1643, -841]], ![![-14840, 1137, -582]]]
  g := ![![![-9, -15, 19], ![32, 118, -161], ![292, 613, -799]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [23, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 136], [0, 1]]
 g := ![![[], [], [60], [], [], [], [1]], ![[], [], [60], [], [], [], [1]]]
 h' := ![![[0, 136], [100], [127], [0, 34], [87], [118], [114], [0, 1]], ![[0, 1], [100], [127], [0, 103], [87], [118], [114], [0, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [0, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [23, 0, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31390, -37786, -12699]
  a := ![14, -1, 29]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3664, 9457, -12699]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4411, 338, -173]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-4411, 338, -173]] 
 ![![137, 0, 0], ![95, 1, 0], ![6, 0, 1]] where
  M :=![![![-4411, 338, -173], ![21444, -1643, 841], ![-33278, 2550, -1305]]]
  hmulB := by decide  
  f := ![![![435, 60, -19]], ![![319, 47, -12]], ![![-28, 2, 5]]]
  g := ![![![-259, 338, -173], ![1259, -1643, 841], ![-1954, 2550, -1305]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-435, -60, 19]] ![![-4411, 338, -173]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB197I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB197I2 : PrimesBelowBoundCertificateInterval O 79 137 197 where
  m := 11
  g := ![2, 2, 2, 1, 2, 1, 2, 1, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB197I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1]
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
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
    · exact ![18769, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
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
  β := ![I83N1, I89N1, I97N1, I103N1, I109N1, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [], [I103N1], [], [I109N1], [], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
