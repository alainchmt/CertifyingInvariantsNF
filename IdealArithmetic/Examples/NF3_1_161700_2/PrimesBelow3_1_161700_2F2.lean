
import IdealArithmetic.Examples.NF3_1_161700_2.RI3_1_161700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-240, -29, -23]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-240, -29, -23]] 
 ![![83, 0, 0], ![0, 83, 0], ![79, 59, 1]] where
  M :=![![![-240, -29, -23], ![-1794, -223, -174], ![-1963, -241, -194]]]
  hmulB := by decide  
  f := ![![![-16, 1, 1]], ![![78, -17, 6]], ![![41, -11, 5]]]
  g := ![![![19, 16, -23], ![144, 121, -174], ![161, 135, -194]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [42, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 82], [0, 1]]
 g := ![![[43, 75], [62, 81], [7], [69], [12, 68], [1]], ![[49, 8], [22, 2], [7], [69], [44, 15], [1]]]
 h' := ![![[20, 82], [52, 65], [61, 9], [43, 67], [77, 61], [41, 20], [0, 1]], ![[0, 1], [24, 18], [75, 74], [55, 16], [52, 22], [26, 63], [20, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [33, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [42, 63, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1901, 1363, -911]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![890, 664, -911]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 1, 1]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-16, 1, 1]] 
 ![![83, 0, 0], ![61, 1, 0], ![6, 0, 1]] where
  M :=![![![-16, 1, 1], ![78, -17, 6], ![65, 11, -18]]]
  hmulB := by decide  
  f := ![![![-240, -29, -23]], ![![-198, -24, -19]], ![![-41, -5, -4]]]
  g := ![![![-1, 1, 1], ![13, -17, 6], ![-6, 11, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-240, -29, -23]] ![![-16, 1, 1]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-36, 12, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-36, 12, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![53, 12, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-36, 12, 1], ![78, -26, 72], ![923, -11, -38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -12, 89]], ![![-1, 0, 1], ![-42, -10, 72], ![33, 5, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [76, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 88], [0, 1]]
 g := ![![[29, 4], [49], [53], [41, 40], [17, 85], [1]], ![[24, 85], [49], [53], [80, 49], [22, 4], [1]]]
 h' := ![![[21, 88], [53, 2], [67, 82], [88, 26], [43, 29], [13, 21], [0, 1]], ![[0, 1], [6, 87], [9, 7], [11, 63], [29, 60], [9, 68], [21, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [6, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [76, 68, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![425, 867, 406]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-237, -45, 406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![17, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![17, 1, 0]] 
 ![![89, 0, 0], ![17, 1, 0], ![38, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![17, 1, 0], ![0, 18, 6], ![78, -2, 17]]]
  hmulB := by decide  
  f := ![![![324, 19, 0], ![-1691, 0, 0]], ![![34, 2, 0], ![-177, 0, 0]], ![![120, 4, -1], ![-626, 15, 0]]]
  g := ![![![1, 0, 0], ![-17, 89, 0], ![-38, 0, 89]], ![![0, 1, 0], ![-6, 18, 6], ![-6, -2, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-36, 12, 1]] ![![89, 0, 0], ![17, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![1513, 89, 0]], ![![-3204, 1068, 89], ![-534, 178, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![17, 1, 0]]], ![![![-36, 12, 1]], ![![-6, 2, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1104208, -6485, -127143]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![1104208, -6485, -127143]] 
 ![![97, 0, 0], ![42, 1, 0], ![87, 0, 1]] where
  M :=![![![1104208, -6485, -127143], ![-9917154, 1352009, -38910], ![1147029, -1639889, 1358494]]]
  hmulB := by decide  
  f := ![![![-1772888033456, -217310240717, -172150811637]], ![![-906072790854, -111061100629, -87981397248]], ![![-1741788630261, -213498257858, -169131000233]]]
  g := ![![![128227, -6485, -127143], ![-652746, 1352009, -38910], ![-496563, -1639889, 1358494]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![267, 2, -34]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![267, 2, -34]] 
 ![![97, 0, 0], ![74, 1, 0], ![45, 0, 1]] where
  M :=![![![267, 2, -34], ![-2652, 337, 12], ![598, -446, 335]]]
  hmulB := by decide  
  f := ![![![118247, 14494, 11482]], ![![99442, 12189, 9656]], ![![64973, 7964, 6309]]]
  g := ![![![17, 2, -34], ![-290, 337, 12], ![191, -446, 335]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-122540879, 5603870, 9652088]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-122540879, 5603870, 9652088]] 
 ![![97, 0, 0], ![77, 1, 0], ![66, 0, 1]] where
  M :=![![![-122540879, 5603870, 9652088], ![752862864, -136241185, 33623220], ![311624716, 114269404, -141845055]]]
  hmulB := by decide  
  f := ![![![-15483033069629295, -1897819591478402, -1503432060705680]], ![![-13499600485530915, -1654702031789003, -1310836971373276]], ![![-11859438081872938, -1453660522100944, -1151574071698895]]]
  g := ![![![-12279141, 5603870, 9652088], ![93034037, -136241185, 33623220], ![9017054, 114269404, -141845055]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![1104208, -6485, -127143]] ![![267, 2, -34]]
  ![![235990242, 56728749, -80213797]] where
 M := ![![![235990242, 56728749, -80213797]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![235990242, 56728749, -80213797]] ![![-122540879, 5603870, 9652088]]
  ![![97, 0, 0]] where
 M := ![![![-11206084956232234, -15572316125658013, 15563132238100911]]]
 hmul := by decide  
 g := ![![![![-115526649033322, -160539341501629, 160444662248463]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [83, 77, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 47, 26], [54, 53, 75], [0, 1]]
 g := ![![[9, 3, 47], [17, 96], [14, 85, 70], [77, 24], [83, 95], [1]], ![[22, 20, 29, 83], [79, 14], [47, 64, 94, 50], [6, 45], [20, 82], [29, 27, 0, 2]], ![[94, 70, 83, 55], [1, 24], [15, 25, 19, 69], [47, 20], [17, 45], [39, 37, 93, 99]]]
 h' := ![![[61, 47, 26], [79, 92, 42], [50, 24, 46], [73, 58, 75], [0, 21, 78], [18, 24, 14], [0, 1]], ![[54, 53, 75], [85, 41, 73], [73, 25, 32], [21, 34, 29], [32, 74, 34], [51, 37, 53], [61, 47, 26]], ![[0, 1], [95, 69, 87], [73, 52, 23], [47, 9, 98], [3, 6, 90], [0, 40, 34], [54, 53, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 80], []]
 b := ![[], [30, 52, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [83, 77, 87, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![89688, -1313, -1010]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![888, -13, -10]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-1, -13, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-1, -13, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![102, 90, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-1, -13, 1], ![78, -16, -78], ![-1027, 39, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -90, 103]], ![![-1, -1, 1], ![78, 68, -78], ![-7, 3, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [93, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 102], [0, 1]]
 g := ![![[99, 72], [88, 64], [71, 61], [2], [2], [63, 1]], ![[0, 31], [0, 39], [0, 42], [2], [2], [23, 102]]]
 h' := ![![[63, 102], [56, 22], [92, 95], [33, 24], [61, 38], [12, 65], [0, 1]], ![[0, 1], [0, 81], [0, 8], [0, 79], [86, 65], [90, 38], [63, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [5, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [93, 40, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1993, 2013, -860]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![871, 771, -860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-25, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-25, 1, 0]] 
 ![![103, 0, 0], ![78, 1, 0], ![3, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-25, 1, 0], ![0, -24, 6], ![78, -2, -25]]]
  hmulB := by decide  
  f := ![![![1376, -55, 0], ![5665, 0, 0]], ![![1076, -43, 0], ![4430, 0, 0]], ![![76, 17, -5], ![313, 86, 0]]]
  g := ![![![1, 0, 0], ![-78, 103, 0], ![-3, 0, 103]], ![![-1, 1, 0], ![18, -24, 6], ![3, -2, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-1, -13, 1]] ![![103, 0, 0], ![-25, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2575, 103, 0]], ![![-103, -1339, 103], ![103, 309, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-25, 1, 0]]], ![![![-1, -13, 1]], ![![1, 3, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-41, 31, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-41, 31, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![66, 31, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-41, 31, 1], ![78, -12, 186], ![2405, -49, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -31, 107]], ![![-1, 0, 1], ![-114, -54, 186], ![49, 12, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [90, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 106], [0, 1]]
 g := ![![[28, 44], [16, 100], [57], [70, 13], [19], [48, 1]], ![[0, 63], [1, 7], [57], [52, 94], [19], [96, 106]]]
 h' := ![![[48, 106], [58, 30], [68, 97], [13, 59], [104, 21], [67, 74], [0, 1]], ![[0, 1], [0, 77], [16, 10], [63, 48], [42, 86], [88, 33], [48, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [74, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [90, 59, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1949, 1371, -867]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![553, 264, -867]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![28, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![28, 1, 0]] 
 ![![107, 0, 0], ![28, 1, 0], ![43, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![28, 1, 0], ![0, 29, 6], ![78, -2, 28]]]
  hmulB := by decide  
  f := ![![![1373, 49, 0], ![-5243, 0, 0]], ![![364, 13, 0], ![-1390, 0, 0]], ![![557, 15, -1], ![-2127, 18, 0]]]
  g := ![![![1, 0, 0], ![-28, 107, 0], ![-43, 0, 107]], ![![0, 1, 0], ![-10, 29, 6], ![-10, -2, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-41, 31, 1]] ![![107, 0, 0], ![28, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2996, 107, 0]], ![![-4387, 3317, 107], ![-1070, 856, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![28, 1, 0]]], ![![![-41, 31, 1]], ![![-10, 8, 2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![11, 21, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![11, 21, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![11, 21, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![11, 21, 1], ![78, 30, 126], ![1625, -29, 9]]]
  hmulB := by decide  
  f := ![![![-10, -21, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -21, 109]], ![![0, 0, 1], ![-12, -24, 126], ![14, -2, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [60, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 108], [0, 1]]
 g := ![![[29, 20], [64], [5, 89], [64, 5], [83], [4, 1]], ![[0, 89], [64], [34, 20], [84, 104], [83], [8, 108]]]
 h' := ![![[4, 108], [50, 42], [27, 101], [84, 31], [82, 88], [87, 65], [0, 1]], ![[0, 1], [0, 67], [104, 8], [99, 78], [107, 21], [20, 44], [4, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [72, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [60, 105, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182673, 127073, -7195]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2402, 2552, -7195]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-17, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-17, 1, 0]] 
 ![![109, 0, 0], ![92, 1, 0], ![100, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-17, 1, 0], ![0, -16, 6], ![78, -2, -17]]]
  hmulB := by decide  
  f := ![![![1446, -85, 0], ![9265, 0, 0]], ![![1208, -71, 0], ![7740, 0, 0]], ![![1316, -64, -5], ![8432, 91, 0]]]
  g := ![![![1, 0, 0], ![-92, 109, 0], ![-100, 0, 109]], ![![-1, 1, 0], ![8, -16, 6], ![18, -2, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![11, 21, 1]] ![![109, 0, 0], ![-17, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1853, 109, 0]], ![![1199, 2289, 109], ![-109, -327, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-17, 1, 0]]], ![![![11, 21, 1]], ![![-1, -3, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![279485195855, 34257659842, 27138545920]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![279485195855, 34257659842, 27138545920]] 
 ![![113, 0, 0], ![0, 113, 0], ![7, 18, 1]] where
  M :=![![![279485195855, 34257659842, 27138545920], ![2116806581760, 259465763857, 205545959052], ![2319296370716, 284285777276, 225208104015]]]
  hmulB := by decide  
  f := ![![![-39969, -52670, 52888]], ![![4125264, -198415, -316020]], ![![612205, -27852, -48353]]]
  g := ![![![792171455, -4019789086, 27138545920], ![5999866092, -30445676983, 205545959052], ![6573802147, -33358053938, 225208104015]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [1, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 112], [0, 1]]
 g := ![![[71, 1], [18], [32], [63], [12, 104], [42, 1]], ![[0, 112], [18], [32], [63], [86, 9], [84, 112]]]
 h' := ![![[42, 112], [42, 112], [88, 40], [81, 91], [101, 17], [71, 68], [0, 1]], ![[0, 1], [0, 1], [73, 73], [61, 22], [24, 96], [102, 45], [42, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [98, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [1, 71, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1686, 1123, 483]
  a := ![-1, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, -67, 483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39969, -52670, 52888]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-39969, -52670, 52888]] 
 ![![113, 0, 0], ![5, 1, 0], ![108, 0, 1]] where
  M :=![![![-39969, -52670, 52888], ![4125264, -198415, -316020], ![-4795804, 792884, -145745]]]
  hmulB := by decide  
  f := ![![![279485195855, 34257659842, 27138545920]], ![![31099403195, 3811982859, 3019811404]], ![![287643340912, 35257637524, 27930717375]]]
  g := ![![![-48571, -52670, 52888], ![347323, -198415, -316020], ![61772, 792884, -145745]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![279485195855, 34257659842, 27138545920]] ![![-39969, -52670, 52888]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB114I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 113 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 113 (by omega)

def PB114I2 : PrimesBelowBoundCertificateInterval O 79 113 114 where
  m := 8
  g := ![2, 2, 3, 1, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB114I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
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
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I103N1, I107N1, I109N1, I113N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [], [I103N1], [I107N1], [I109N1], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
