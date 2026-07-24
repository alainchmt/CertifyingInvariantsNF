
import IdealArithmetic.Examples.NF3_3_701244_1.RI3_3_701244_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1187249, -260665, 60338]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-1187249, -260665, 60338]] 
 ![![83, 0, 0], ![0, 83, 0], ![61, 15, 1]] where
  M :=![![![-1187249, -260665, 60338], ![10257460, 2252017, -521330], ![-44313050, -9729175, 2252017]]]
  hmulB := by decide  
  f := ![![![-6388367, -204215, 123888]], ![![21060960, 673249, -408430]], ![![-1307139, -41785, 25349]]]
  g := ![![![-58649, -14045, 60338], ![506730, 121349, -521330], ![-2188989, -524210, 2252017]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [21, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 82], [0, 1]]
 g := ![![[30, 4], [23, 75], [7], [44], [28, 77], [1]], ![[0, 79], [0, 8], [7], [44], [73, 6], [1]]]
 h' := ![![[34, 82], [15, 2], [52, 18], [38, 67], [76, 25], [62, 34], [0, 1]], ![[0, 1], [0, 81], [0, 65], [75, 16], [13, 58], [56, 49], [34, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [7, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [21, 49, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![361, 150, 10]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 0, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6388367, 204215, -123888]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![6388367, 204215, -123888]] 
 ![![83, 0, 0], ![53, 1, 0], ![48, 0, 1]] where
  M :=![![![6388367, 204215, -123888], ![-21060960, -673249, 408430], ![34716550, 1109775, -673249]]]
  hmulB := by decide  
  f := ![![![1187249, 260665, -60338]], ![![634539, 139316, -32248]], ![![1220494, 267965, -62027]]]
  g := ![![![18212, 204215, -123888], ![-60041, -673249, 408430], ![98969, 1109775, -673249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-1187249, -260665, 60338]] ![![6388367, 204215, -123888]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-349750393, -11180364, 6782622]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-349750393, -11180364, 6782622]] 
 ![![89, 0, 0], ![0, 89, 0], ![14, 76, 1]] where
  M :=![![![-349750393, -11180364, 6782622], ![1153045740, 36859061, -22360728], ![-1900661880, -60757878, 36859061]]]
  hmulB := by decide  
  f := ![![![67567, 14808, -3450]], ![![-586500, -129083, 29616]], ![![-461918, -101710, 23297]]]
  g := ![![![-4996709, -5917524, 6782622], ![16472988, 19508701, -22360728], ![-27153806, -32157826, 36859061]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [61, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 88], [0, 1]]
 g := ![![[44, 2], [53], [49], [0, 8], [32, 18], [1]], ![[16, 87], [53], [49], [66, 81], [47, 71], [1]]]
 h' := ![![[75, 88], [5, 25], [37, 26], [0, 82], [6, 39], [28, 75], [0, 1]], ![[0, 1], [11, 64], [29, 63], [9, 7], [83, 50], [46, 14], [75, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [4, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [61, 14, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1992, 57, 557]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-110, -475, 557]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67567, 14808, -3450]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![67567, 14808, -3450]] 
 ![![89, 0, 0], ![26, 1, 0], ![18, 0, 1]] where
  M :=![![![67567, 14808, -3450], ![-586500, -129083, 29616], ![2517360, 550806, -129083]]]
  hmulB := by decide  
  f := ![![![-349750393, -11180364, 6782622]], ![![-89218702, -2852027, 1730196]], ![![-92091786, -2943870, 1785913]]]
  g := ![![![-2869, 14808, -3450], ![25130, -129083, 29616], ![-106518, 550806, -129083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-349750393, -11180364, 6782622]] ![![67567, 14808, -3450]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [66, 67, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 81, 88], [88, 15, 9], [0, 1]]
 g := ![![[53, 46, 6], [59, 49], [70, 79], [77, 61], [90, 31], [1]], ![[95, 57, 88, 32], [88, 86], [96, 66], [96, 31], [96, 3], [25, 49, 63, 47]], ![[47, 76, 73, 35], [16, 85], [8, 47], [42, 75], [2, 43], [96, 84, 82, 50]]]
 h' := ![![[91, 81, 88], [84, 30, 54], [1, 68, 90], [16, 57, 51], [65, 89, 35], [31, 30, 82], [0, 1]], ![[88, 15, 9], [13, 93, 55], [1, 61, 59], [41, 1, 58], [13, 9, 15], [74, 56, 87], [91, 81, 88]], ![[0, 1], [60, 71, 85], [90, 65, 45], [91, 39, 85], [27, 96, 47], [16, 11, 25], [88, 15, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 46], []]
 b := ![[], [26, 78, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [66, 67, 15, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-129786, 15229, -23959]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1338, 157, -247]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-944889, -30205, 18324]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-944889, -30205, 18324]] 
 ![![101, 0, 0], ![20, 1, 0], ![2, 0, 1]] where
  M :=![![![-944889, -30205, 18324], ![3115080, 99579, -60410], ![-5134850, -164145, 99579]]]
  hmulB := by decide  
  f := ![![![-22209, -9285, -1546]], ![![-7000, -2931, -490]], ![![-16068, -6725, -1123]]]
  g := ![![![-3737, -30205, 18324], ![12320, 99579, -60410], ![-20308, -164145, 99579]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18383571, -587662, 356508]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-18383571, -587662, 356508]] 
 ![![101, 0, 0], ![87, 1, 0], ![3, 0, 1]] where
  M :=![![![-18383571, -587662, 356508], ![60606360, 1937385, -1175324], ![-99902540, -3193554, 1937385]]]
  hmulB := by decide  
  f := ![![![-23271, -5562, 908]], ![![-18517, -4509, 672]], ![![-10053, -2540, 309]]]
  g := ![![![313599, -587662, 356508], ![-1033863, 1937385, -1175324], ![1704203, -3193554, 1937385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9880909, -315860, 191618]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-9880909, -315860, 191618]] 
 ![![101, 0, 0], ![95, 1, 0], ![83, 0, 1]] where
  M :=![![![-9880909, -315860, 191618], ![32575060, 1041317, -631720], ![-53696200, -1716490, 1041317]]]
  hmulB := by decide  
  f := ![![![-31689, -6800, 1706]], ![![-26935, -5747, 1470]], ![![-37487, -7990, 2051]]]
  g := ![![![41797, -315860, 191618], ![-137795, 1041317, -631720], ![227139, -1716490, 1041317]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-944889, -30205, 18324]] ![![-18383571, -587662, 356508]]
  ![![13709204771859, 438237962097, -265859183452]] where
 M := ![![![13709204771859, 438237962097, -265859183452]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![13709204771859, 438237962097, -265859183452]] ![![-9880909, -315860, 191618]]
  ![![101, 0, 0]] where
 M := ![![![-106908149017041756611, -3417500149458898511, 2073243027223474738]]]
 hmul := by decide  
 g := ![![![![-1058496524921205511, -33836635143157411, 20527158685380938]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, 5, -12]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![491, 5, -12]] 
 ![![103, 0, 0], ![0, 103, 0], ![2, 94, 1]] where
  M :=![![![491, 5, -12], ![-2040, -193, 10], ![850, -735, -193]]]
  hmulB := by decide  
  f := ![![![433, 95, -22]], ![![-3740, -821, 190]], ![![-3248, -713, 165]]]
  g := ![![![5, 11, -12], ![-20, -11, 10], ![12, 169, -193]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [95, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 102], [0, 1]]
 g := ![![[72, 26], [94, 63], [4, 79], [83], [29], [61, 1]], ![[10, 77], [23, 40], [85, 24], [83], [29], [19, 102]]]
 h' := ![![[61, 102], [31, 52], [32, 75], [69, 39], [34, 17], [76, 21], [0, 1]], ![[0, 1], [10, 51], [75, 28], [79, 64], [41, 86], [18, 82], [61, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [54, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [95, 42, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-882, 467, 383]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -345, 383]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 95, -22]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![433, 95, -22]] 
 ![![103, 0, 0], ![18, 1, 0], ![44, 0, 1]] where
  M :=![![![433, 95, -22], ![-3740, -821, 190], ![16150, 3545, -821]]]
  hmulB := by decide  
  f := ![![![491, 5, -12]], ![![66, -1, -2]], ![![218, -5, -7]]]
  g := ![![![-3, 95, -22], ![26, -821, 190], ![-112, 3545, -821]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![491, 5, -12]] ![![433, 95, -22]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2719, 261, -342]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![2719, 261, -342]] 
 ![![107, 0, 0], ![0, 107, 0], ![3, 64, 1]] where
  M :=![![![2719, 261, -342], ![-58140, -16775, 522], ![44370, -14193, -16775]]]
  hmulB := by decide  
  f := ![![![2699153, 86283, -52344]], ![![-8898480, -284455, 172566]], ![![-5109693, -163340, 99091]]]
  g := ![![![35, 207, -342], ![-558, -469, 522], ![885, 9901, -16775]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [59, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 106], [0, 1]]
 g := ![![[6, 41], [52, 53], [41], [0, 75], [102], [74, 1]], ![[44, 66], [15, 54], [41], [93, 32], [102], [41, 106]]]
 h' := ![![[74, 106], [35, 24], [42, 38], [0, 24], [94, 90], [21, 67], [0, 1]], ![[0, 1], [99, 83], [72, 69], [64, 83], [13, 17], [57, 40], [74, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [11, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [59, 33, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![399, 166, 26]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -14, 26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2699153, 86283, -52344]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![2699153, 86283, -52344]] 
 ![![107, 0, 0], ![86, 1, 0], ![47, 0, 1]] where
  M :=![![![2699153, 86283, -52344], ![-8898480, -284455, 172566], ![14668110, 468891, -284455]]]
  hmulB := by decide  
  f := ![![![2719, 261, -342]], ![![1642, 53, -270]], ![![1609, -18, -307]]]
  g := ![![![-21131, 86283, -52344], ![69664, -284455, 172566], ![-114833, 468891, -284455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![2719, 261, -342]] ![![2699153, 86283, -52344]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8406691, 268729, -163028]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![8406691, 268729, -163028]] 
 ![![109, 0, 0], ![0, 109, 0], ![20, 86, 1]] where
  M :=![![![8406691, 268729, -163028], ![-27714760, -885905, 537458], ![45683930, 1460173, -885905]]]
  hmulB := by decide  
  f := ![![![422099, 176889, 29638]], ![![5038460, 2111465, 353778]], ![![4328630, 1813997, 303937]]]
  g := ![![![107039, 131093, -163028], ![-352880, -432177, 537458], ![581670, 712367, -885905]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [96, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 108], [0, 1]]
 g := ![![[87, 27], [29], [69, 83], [19, 46], [102], [41, 1]], ![[104, 82], [29], [93, 26], [52, 63], [102], [82, 108]]]
 h' := ![![[41, 108], [21, 38], [25, 62], [29, 44], [53, 41], [97, 59], [0, 1]], ![[0, 1], [53, 71], [60, 47], [89, 65], [99, 68], [9, 50], [41, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [26, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [96, 68, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6625, 3581, 849]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-95, -637, 849]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![422099, 176889, 29638]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![422099, 176889, 29638]] 
 ![![109, 0, 0], ![46, 1, 0], ![32, 0, 1]] where
  M :=![![![422099, 176889, 29638], ![5038460, 2111465, 353778], ![30071130, 12601903, 2111465]]]
  hmulB := by decide  
  f := ![![![8406691, 268729, -163028]], ![![3293514, 105281, -63870]], ![![2887138, 92289, -55989]]]
  g := ![![![-79479, 176889, 29638], ![-948714, 2111465, 353778], ![-5662232, 12601903, 2111465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![8406691, 268729, -163028]] ![![422099, 176889, 29638]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2164503, 69194, -41976]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![2164503, 69194, -41976]] 
 ![![113, 0, 0], ![0, 113, 0], ![45, 27, 1]] where
  M :=![![![2164503, 69194, -41976], ![-7135920, -228129, 138388], ![11762980, 376098, -228129]]]
  hmulB := by decide  
  f := ![![![40791, 17094, 2864]], ![![486880, 204039, 34188]], ![![158295, 66337, 11115]]]
  g := ![![![35871, 10642, -41976], ![-118260, -35085, 138388], ![194945, 57837, -228129]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [17, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 112], [0, 1]]
 g := ![![[17, 112], [1], [31], [77], [13, 9], [50, 1]], ![[80, 1], [1], [31], [77], [11, 104], [100, 112]]]
 h' := ![![[50, 112], [107, 98], [24, 1], [72, 12], [5, 23], [54, 110], [0, 1]], ![[0, 1], [35, 15], [74, 112], [107, 101], [25, 90], [17, 3], [50, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [20, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [17, 63, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1065, -74, 14]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, -4, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40791, -17094, -2864]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-40791, -17094, -2864]] 
 ![![113, 0, 0], ![59, 1, 0], ![11, 0, 1]] where
  M :=![![![-40791, -17094, -2864], ![-486880, -204039, -34188], ![-2905980, -1217798, -204039]]]
  hmulB := by decide  
  f := ![![![-2164503, -69194, 41976]], ![![-1066989, -34109, 20692]], ![![-314801, -10064, 6105]]]
  g := ![![![8843, -17094, -2864], ![105553, -204039, -34188], ![629987, -1217798, -204039]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![2164503, 69194, -41976]] ![![-40791, -17094, -2864]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106613, 23411, -5416]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![106613, 23411, -5416]] 
 ![![127, 0, 0], ![0, 127, 0], ![86, 32, 1]] where
  M :=![![![106613, 23411, -5416], ![-920720, -202099, 46822], ![3979870, 874067, -202099]]]
  hmulB := by decide  
  f := ![![![642199, 20529, -12454]], ![![-2117180, -67679, 41058]], ![![-71108, -2273, 1379]]]
  g := ![![![4507, 1549, -5416], ![-38956, -13389, 46822], ![168192, 57805, -202099]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [79, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 126], [0, 1]]
 g := ![![[98, 82], [1, 76], [17, 22], [50, 117], [90, 122], [5, 1]], ![[0, 45], [0, 51], [0, 105], [0, 10], [65, 5], [10, 126]]]
 h' := ![![[5, 126], [48, 92], [54, 40], [114, 28], [2, 25], [113, 73], [0, 1]], ![[0, 1], [0, 35], [0, 87], [0, 99], [0, 102], [97, 54], [5, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [120, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [79, 122, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![759, 690, 474]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-315, -114, 474]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![642199, 20529, -12454]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![642199, 20529, -12454]] 
 ![![127, 0, 0], ![63, 1, 0], ![111, 0, 1]] where
  M :=![![![642199, 20529, -12454], ![-2117180, -67679, 41058], ![3489930, 111563, -67679]]]
  hmulB := by decide  
  f := ![![![106613, 23411, -5416]], ![![45637, 10022, -2318]], ![![124519, 27344, -6325]]]
  g := ![![![5758, 20529, -12454], ![-18983, -67679, 41058], ![31290, 111563, -67679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![106613, 23411, -5416]] ![![642199, 20529, -12454]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20853, 4578, -1060]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![20853, 4578, -1060]] 
 ![![131, 0, 0], ![64, 1, 0], ![48, 0, 1]] where
  M :=![![![20853, 4578, -1060], ![-180200, -39567, 9156], ![778260, 170846, -39567]]]
  hmulB := by decide  
  f := ![![![-1281513, -40966, 24852]], ![![-593832, -18983, 11516]], ![![-522724, -16710, 10137]]]
  g := ![![![-1689, 4578, -1060], ![14600, -39567, 9156], ![-63028, 170846, -39567]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34237, 14384, 2426]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![34237, 14384, 2426]] 
 ![![131, 0, 0], ![70, 1, 0], ![39, 0, 1]] where
  M :=![![![34237, 14384, 2426], ![412420, 172519, 28768], ![2445280, 1026098, 172519]]]
  hmulB := by decide  
  f := ![![![-244018097, -7800452, 4732182]], ![![-124250350, -3971873, 2409556]], ![![-82769333, -2645862, 1605125]]]
  g := ![![![-8147, 14384, 2426], ![-97602, 172519, 28768], ![-580991, 1026098, 172519]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9101, 3865, 670]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![9101, 3865, 670]] 
 ![![131, 0, 0], ![128, 1, 0], ![61, 0, 1]] where
  M :=![![![9101, 3865, 670], ![113900, 47291, 7730], ![657050, 277255, 47291]]]
  hmulB := by decide  
  f := ![![![93257531, 2981135, -1808520]], ![![88774928, 2837841, -1721590]], ![![47293911, 1511830, -917159]]]
  g := ![![![-4019, 3865, 670], ![-48938, 47291, 7730], ![-287911, 277255, 47291]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![20853, 4578, -1060]] ![![34237, 14384, 2426]]
  ![![10006121, 2077654, -580858]] where
 M := ![![![10006121, 2077654, -580858]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![10006121, 2077654, -580858]] ![![9101, 3865, 670]]
  ![![131, 0, 0]] where
 M := ![![![-53942251079, -24117791811, -4704989188]]]
 hmul := by decide  
 g := ![![![![-411772909, -184105281, -35915948]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [115, 116, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 124, 130], [60, 12, 7], [0, 1]]
 g := ![![[120, 36, 77], [85, 65], [3, 118], [71, 107, 103], [28, 118], [97, 1], []], ![[9, 10, 3, 17], [48, 36], [49, 49], [108, 113, 58, 118], [9, 78], [43, 7], [3, 49]], ![[68, 129, 105, 103], [58, 128], [65, 78], [19, 71, 114, 118], [56, 69], [86, 32], [126, 49]]]
 h' := ![![[37, 124, 130], [127, 13, 25], [77, 134, 32], [55, 58, 23], [7, 117, 69], [79, 4, 114], [0, 0, 1], [0, 1]], ![[60, 12, 7], [41, 59, 72], [128, 13, 131], [134, 75, 7], [53, 7, 9], [102, 78, 107], [65, 42, 12], [37, 124, 130]], ![[0, 1], [54, 65, 40], [82, 127, 111], [76, 4, 107], [75, 13, 59], [79, 55, 53], [70, 95, 124], [60, 12, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 89], []]
 b := ![[], [21, 127, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [115, 116, 40, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1699485, -416480, 94256]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12405, -3040, 688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB187I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB187I2 : PrimesBelowBoundCertificateInterval O 79 137 187 where
  m := 11
  g := ![2, 2, 1, 3, 2, 2, 2, 2, 2, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB187I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0]
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
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
    · exact ![2571353]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
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
  β := ![I83N1, I89N1, I101N0, I101N1, I101N2, I103N1, I107N1, I109N1, I113N1, I127N1, I131N0, I131N1, I131N2]
  Il := ![[I83N1], [I89N1], [], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N1], [I113N1], [I127N1], [I131N0, I131N1, I131N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
