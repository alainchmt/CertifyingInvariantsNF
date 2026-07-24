
import IdealArithmetic.Examples.NF3_1_730732_1.RI3_1_730732_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![18, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![18, 1, 0]] 
 ![![83, 0, 0], ![18, 1, 0], ![46, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![18, 1, 0], ![1, 18, 2], ![-106, -36, 19]]]
  hmulB := by decide  
  f := ![![![-119, -2160, -240], ![0, 9960, 0]], ![![-26, -468, -52], ![1, 2158, 0]], ![![-64, -1197, -133], ![-9, 5520, 0]]]
  g := ![![![1, 0, 0], ![-18, 83, 0], ![-46, 0, 83]], ![![0, 1, 0], ![-5, 18, 2], ![-4, -36, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49014, -2187, 1201]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![49014, -2187, 1201]] 
 ![![83, 0, 0], ![46, 1, 0], ![63, 0, 1]] where
  M :=![![![49014, -2187, 1201], ![-129493, 5778, -3173], ![146551, -6539, 3591]]]
  hmulB := by decide  
  f := ![![![551, 178, -27]], ![![342, 117, -11]], ![![214, 81, 0]]]
  g := ![![![891, -2187, 1201], ![-2354, 5778, -3173], ![2664, -6539, 3591]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![18, 1, 0]] ![![83, 0, 0], ![18, 1, 0]]
  ![![551, 178, -27]] where
 M := ![![![6889, 0, 0], ![1494, 83, 0]], ![![1494, 83, 0], ![325, 36, 2]]]
 hmul := by decide  
 g := ![![![![4068162, -181521, 99683]], ![![752759, -33588, 18445]]], ![![![752759, -33588, 18445]], ![![139288, -6215, 3413]]]]
 hle2 := by decide  
def MulI83N1 : IdealMulLeCertificate' Table 
  ![![551, 178, -27]] ![![49014, -2187, 1201]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [5, 18, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 79, 55], [75, 9, 34], [0, 1]]
 g := ![![[76, 49, 10], [76, 85], [3, 45], [6, 0, 44], [2, 51, 1], []], ![[55, 47, 10, 20], [4, 64], [66, 53], [3, 26, 20, 39], [9, 2, 32, 5], [6, 88]], ![[66, 40, 44, 16], [13, 80], [35, 71], [29, 86, 61, 64], [84, 18, 78, 18], [27, 88]]]
 h' := ![![[65, 79, 55], [1, 24, 59], [84, 23, 68], [59, 81, 32], [79, 65, 69], [0, 0, 1], [0, 1]], ![[75, 9, 34], [44, 20, 71], [81, 41, 8], [12, 40, 26], [59, 87, 13], [12, 21, 9], [65, 79, 55]], ![[0, 1], [60, 45, 48], [83, 25, 13], [76, 57, 31], [85, 26, 7], [61, 68, 79], [75, 9, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 28], []]
 b := ![[], [62, 2, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [5, 18, 38, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-149253, -69598, -11392]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1677, -782, -128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-729047, 32530, -17864]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-729047, 32530, -17864]] 
 ![![97, 0, 0], ![26, 1, 0], ![2, 0, 1]] where
  M :=![![![-729047, 32530, -17864], ![1926114, -85943, 47196], ![-2179836, 97264, -53413]]]
  hmulB := by decide  
  f := ![![![-1715, -794, -128]], ![![-328, -183, -52]], ![![926, 372, 19]]]
  g := ![![![-15867, 32530, -17864], ![41920, -85943, 47196], ![-47442, 97264, -53413]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![27, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![27, 1, 0]] 
 ![![97, 0, 0], ![27, 1, 0], ![24, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![27, 1, 0], ![1, 27, 2], ![-106, -36, 28]]]
  hmulB := by decide  
  f := ![![![811, 26238, 1944], ![582, -94284, 0]], ![![216, 7288, 540], ![195, -26190, 0]], ![![204, 6492, 481], ![132, -23328, 0]]]
  g := ![![![1, 0, 0], ![-27, 97, 0], ![-24, 0, 97]], ![![0, 1, 0], ![-8, 27, 2], ![2, -36, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![43, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![43, 1, 0]] 
 ![![97, 0, 0], ![43, 1, 0], ![46, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![43, 1, 0], ![1, 43, 2], ![-106, -36, 44]]]
  hmulB := by decide  
  f := ![![![-4093, -261050, -12144], ![-4462, 588984, 0]], ![![-1831, -115693, -5382], ![-1939, 261027, 0]], ![![-1945, -123797, -5759], ![-2107, 279312, 0]]]
  g := ![![![1, 0, 0], ![-43, 97, 0], ![-46, 0, 97]], ![![0, 1, 0], ![-20, 43, 2], ![-6, -36, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-729047, 32530, -17864]] ![![97, 0, 0], ![27, 1, 0]]
  ![![97, 0, 0], ![12, -22, 1]] where
 M := ![![![-70717559, 3155410, -1732808], ![-17758155, 792367, -435132]]]
 hmul := by decide  
 g := ![![![![-717719, 11762, -16920], ![-91568, 0, 0]], ![![-180231, 2957, -4249], ![-22979, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![12, -22, 1]] ![![97, 0, 0], ![43, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4171, 97, 0]], ![![1164, -2134, 97], ![388, -970, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![43, 1, 0]]], ![![![12, -22, 1]], ![![4, -10, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![1, -6, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![1, -6, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![1, 95, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![1, -6, 1], ![-112, -35, -11], ![565, 145, -41]]]
  hmulB := by decide  
  f := ![![![0, 6, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -95, 101]], ![![0, -1, 1], ![-1, 10, -11], ![6, 40, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [88, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 100], [0, 1]]
 g := ![![[72, 31], [88], [51, 78], [70], [13], [27, 1]], ![[0, 70], [88], [36, 23], [70], [13], [54, 100]]]
 h' := ![![[27, 100], [50, 58], [57, 47], [79, 49], [49, 75], [48, 35], [0, 1]], ![[0, 1], [0, 43], [13, 54], [89, 52], [54, 26], [84, 66], [27, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [100, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [88, 74, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![589, -1211, -522]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 479, -522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![11, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![11, 1, 0]] 
 ![![101, 0, 0], ![11, 1, 0], ![41, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![11, 1, 0], ![1, 11, 2], ![-106, -36, 12]]]
  hmulB := by decide  
  f := ![![![-1173, -13154, -2392], ![-202, 120796, 0]], ![![-130, -1430, -260], ![1, 13130, 0]], ![![-479, -5340, -971], ![-56, 49036, 0]]]
  g := ![![![1, 0, 0], ![-11, 101, 0], ![-41, 0, 101]], ![![0, 1, 0], ![-2, 11, 2], ![-2, -36, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![1, -6, 1]] ![![101, 0, 0], ![11, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1111, 101, 0]], ![![101, -606, 101], ![-101, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![11, 1, 0]]], ![![![1, -6, 1]], ![![-1, -1, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-22, -5, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-22, -5, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![81, 98, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-22, -5, 1], ![-111, -58, -9], ![459, 109, -63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -98, 103]], ![![-1, -1, 1], ![6, 8, -9], ![54, 61, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [50, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 102], [0, 1]]
 g := ![![[7, 68], [6, 38], [95, 28], [8], [83], [62, 1]], ![[0, 35], [96, 65], [80, 75], [8], [83], [21, 102]]]
 h' := ![![[62, 102], [9, 58], [91, 55], [71, 53], [70, 27], [93, 86], [0, 1]], ![[0, 1], [0, 45], [102, 48], [61, 50], [96, 76], [69, 17], [62, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [28, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [50, 41, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-293673, -304613, -151072]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![115953, 140781, -151072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![9, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![9, 1, 0]] 
 ![![103, 0, 0], ![9, 1, 0], ![63, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![9, 1, 0], ![1, 9, 2], ![-106, -36, 10]]]
  hmulB := by decide  
  f := ![![![-1835, -16764, -3726], ![-309, 191889, 0]], ![![-162, -1458, -324], ![1, 16686, 0]], ![![-1125, -10254, -2279], ![-159, 117369, 0]]]
  g := ![![![1, 0, 0], ![-9, 103, 0], ![-63, 0, 103]], ![![0, 1, 0], ![-2, 9, 2], ![-4, -36, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-22, -5, 1]] ![![103, 0, 0], ![9, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![927, 103, 0]], ![![-2266, -515, 103], ![-309, -103, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![9, 1, 0]]], ![![![-22, -5, 1]], ![![-3, -1, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![73, 15, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![73, 15, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![73, 15, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![73, 15, 1], ![-91, 37, 31], ![-1661, -611, 52]]]
  hmulB := by decide  
  f := ![![![-72, -15, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -15, 107]], ![![0, 0, 1], ![-22, -4, 31], ![-51, -13, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [88, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 106], [0, 1]]
 g := ![![[59, 47], [27, 52], [29], [59, 85], [29], [51, 1]], ![[102, 60], [4, 55], [29], [7, 22], [29], [102, 106]]]
 h' := ![![[51, 106], [85, 58], [49, 42], [51, 52], [52, 70], [6, 52], [0, 1]], ![[0, 1], [47, 49], [51, 65], [28, 55], [91, 37], [90, 55], [51, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [79, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [88, 56, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-734, -1363, -1168]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![790, 151, -1168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-31, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-31, 1, 0]] 
 ![![107, 0, 0], ![76, 1, 0], ![55, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-31, 1, 0], ![1, -31, 2], ![-106, -36, -30]]]
  hmulB := by decide  
  f := ![![![-3526, 130457, -8418], ![2354, 450363, 0]], ![![-2523, 92644, -5978], ![1606, 319823, 0]], ![![-1802, 67057, -4327], ![1246, 231495, 0]]]
  g := ![![![1, 0, 0], ![-76, 107, 0], ![-55, 0, 107]], ![![-1, 1, 0], ![21, -31, 2], ![40, -36, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![73, 15, 1]] ![![107, 0, 0], ![-31, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3317, 107, 0]], ![![7811, 1605, 107], ![-2354, -428, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-31, 1, 0]]], ![![![73, 15, 1]], ![![-22, -4, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-54, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-54, 1, 0]] 
 ![![109, 0, 0], ![55, 1, 0], ![14, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-54, 1, 0], ![1, -54, 2], ![-106, -36, -53]]]
  hmulB := by decide  
  f := ![![![-19, 3995, -148], ![109, 8066, 0]], ![![18, 1997, -74], ![110, 4033, 0]], ![![4, 513, -19], ![27, 1036, 0]]]
  g := ![![![1, 0, 0], ![-55, 109, 0], ![-14, 0, 109]], ![![-1, 1, 0], ![27, -54, 2], ![24, -36, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 2, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![5, 2, 0]] 
 ![![109, 0, 0], ![57, 1, 0], ![11, 0, 1]] where
  M :=![![![5, 2, 0], ![2, 5, 4], ![-212, -72, 7]]]
  hmulB := by decide  
  f := ![![![-323, 14, -8]], ![![-161, 7, -4]], ![![-41, 2, -1]]]
  g := ![![![-1, 2, 0], ![-3, 5, 4], ![35, -72, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-4, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-4, 1, 0]] 
 ![![109, 0, 0], ![105, 1, 0], ![47, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-4, 1, 0], ![1, -4, 2], ![-106, -36, -3]]]
  hmulB := by decide  
  f := ![![![-2745, 11014, -5508], ![218, 300186, 0]], ![![-2643, 10606, -5304], ![219, 289068, 0]], ![![-1183, 4749, -2375], ![111, 129438, 0]]]
  g := ![![![1, 0, 0], ![-105, 109, 0], ![-47, 0, 109]], ![![-1, 1, 0], ![3, -4, 2], ![35, -36, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-54, 1, 0]] ![![5, 2, 0]]
  ![![109, 0, 0], ![42, -53, 1]] where
 M := ![![![545, 218, 0]], ![![-268, -103, 4]]]
 hmul := by decide  
 g := ![![![![-37, 55, -1], ![109, 0, 0]]], ![![![-4, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![42, -53, 1]] ![![109, 0, 0], ![-4, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-436, 109, 0]], ![![4578, -5777, 109], ![-327, 218, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-4, 1, 0]]], ![![![42, -53, 1]], ![![-3, 2, -1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![1, 6, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![1, 6, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![1, 6, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![1, 6, 1], ![-100, -35, 13], ![-707, -287, -29]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![13, -1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -6, 113]], ![![0, 0, 1], ![-1, -1, 13], ![-6, -1, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [103, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 112], [0, 1]]
 g := ![![[100, 56], [82], [98], [99], [73, 18], [96, 1]], ![[52, 57], [82], [98], [99], [106, 95], [79, 112]]]
 h' := ![![[96, 112], [3, 100], [58, 46], [78, 95], [52, 41], [56, 73], [0, 1]], ![[0, 1], [111, 13], [67, 67], [45, 18], [33, 72], [58, 40], [96, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [13, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [103, 17, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-620, -443, -168]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, 5, -168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-13, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-13, 1, 0]] 
 ![![113, 0, 0], ![100, 1, 0], ![29, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-13, 1, 0], ![1, -13, 2], ![-106, -36, -12]]]
  hmulB := by decide  
  f := ![![![-727, 9800, -1508], ![226, 85202, 0]], ![![-640, 8669, -1334], ![227, 75371, 0]], ![![-186, 2515, -387], ![63, 21866, 0]]]
  g := ![![![1, 0, 0], ![-100, 113, 0], ![-29, 0, 113]], ![![-1, 1, 0], ![11, -13, 2], ![34, -36, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![1, 6, 1]] ![![113, 0, 0], ![-13, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1469, 113, 0]], ![![113, 678, 113], ![-113, -113, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-13, 1, 0]]], ![![![1, 6, 1]], ![![-1, -1, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![825164, 412875, 88842]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![825164, 412875, 88842]] 
 ![![127, 0, 0], ![28, 1, 0], ![53, 0, 1]] where
  M :=![![![825164, 412875, 88842], ![-9004377, -2373148, 914592], ![-50072532, -21171282, -1960273]]]
  hmulB := by decide  
  f := ![![![-24015103096348, 1071551320569, -588447386616]], ![![-4795085924377, 213956218880, -117495051738]], ![![-10587442044386, 472410526767, -259426435813]]]
  g := ![![![-121606, 412875, 88842], ![70633, -2373148, 914592], ![5091479, -21171282, -1960273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12080, -539, 296]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![12080, -539, 296]] 
 ![![127, 0, 0], ![38, 1, 0], ![104, 0, 1]] where
  M :=![![![12080, -539, 296], ![-31915, 1424, -782], ![36118, -1612, 885]]]
  hmulB := by decide  
  f := ![![![-344, -137, -6]], ![![-99, -42, -4]], ![![-164, -70, -7]]]
  g := ![![![14, -539, 296], ![-37, 1424, -782], ![42, -1612, 885]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1668984475, 74469908, -40895496]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-1668984475, 74469908, -40895496]] 
 ![![127, 0, 0], ![60, 1, 0], ![42, 0, 1]] where
  M :=![![![-1668984475, 74469908, -40895496], ![4409392484, -196746619, 108044320], ![-4990230032, 222663528, -122276711]]]
  hmulB := by decide  
  f := ![![![-129149, -42700, 5464]], ![![-65912, -22739, 1952]], ![![-10126, -5072, -1095]]]
  g := ![![![-34799749, 74469908, -40895496], ![91939592, -196746619, 108044320], ![-104050550, 222663528, -122276711]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![825164, 412875, 88842]] ![![12080, -539, 296]]
  ![![-129149, -42700, 5464]] where
 M := ![![![-129149, -42700, 5464]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-129149, -42700, 5464]] ![![-1668984475, 74469908, -40895496]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [72, 73, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 34, 3], [114, 96, 128], [0, 1]]
 g := ![![[57, 97, 20], [35, 24, 112], [], [105, 62], [64, 100], [71, 1], []], ![[23, 121, 112, 46], [101, 125, 16, 77], [106, 65], [121, 43], [76, 15], [9, 46], [57, 9]], ![[40, 69, 91, 19], [22, 54, 102, 8], [62, 65], [96, 35], [114, 41], [80, 108], [63, 9]]]
 h' := ![![[88, 34, 3], [100, 44, 46], [129, 88, 80], [103, 92], [117, 8, 18], [128, 116, 121], [0, 0, 1], [0, 1]], ![[114, 96, 128], [64, 2, 94], [0, 52, 84], [77, 115, 14], [55, 69, 49], [5, 54, 43], [103, 127, 96], [88, 34, 3]], ![[0, 1], [97, 85, 122], [128, 122, 98], [111, 55, 117], [39, 54, 64], [16, 92, 98], [76, 4, 34], [114, 96, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 30], []]
 b := ![[], [90, 121, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [72, 73, 60, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-537493, -488761, -242350]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4103, -3731, -1850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![368, 111, -25]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![368, 111, -25]] 
 ![![137, 0, 0], ![0, 137, 0], ![62, 12, 1]] where
  M :=![![![368, 111, -25], ![2761, 1268, 197], ![-9991, -2221, 1379]]]
  hmulB := by decide  
  f := ![![![-15957, 712, -391]], ![![42158, -1881, 1033]], ![![-3877, 173, -95]]]
  g := ![![![14, 3, -25], ![-69, -8, 197], ![-697, -137, 1379]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [80, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 136], [0, 1]]
 g := ![![[103, 60], [59], [15], [135, 25], [25], [126], [1]], ![[136, 77], [59], [15], [46, 112], [25], [126], [1]]]
 h' := ![![[117, 136], [134, 34], [14, 14], [23, 120], [5, 132], [19, 132], [57, 117], [0, 1]], ![[0, 1], [2, 103], [8, 123], [89, 17], [105, 5], [119, 5], [46, 20], [117, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [34, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [80, 20, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1322, 57, -372]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![178, 33, -372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15957, -712, 391]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![15957, -712, 391]] 
 ![![137, 0, 0], ![112, 1, 0], ![99, 0, 1]] where
  M :=![![![15957, -712, 391], ![-42158, 1881, -1033], ![47711, -2129, 1169]]]
  hmulB := by decide  
  f := ![![![-368, -111, 25]], ![![-321, -100, 19]], ![![-193, -64, 8]]]
  g := ![![![416, -712, 391], ![-1099, 1881, -1033], ![1244, -2129, 1169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![368, 111, -25]] ![![15957, -712, 391]]
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


lemma PB242I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB242I2 : PrimesBelowBoundCertificateInterval O 79 137 242 where
  m := 11
  g := ![3, 1, 3, 2, 2, 2, 3, 2, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB242I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
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
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
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
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I97N0, I97N1, I97N2, I101N1, I103N1, I107N1, I109N0, I109N1, I109N2, I113N1, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N0, I83N0, I83N1], [], [I97N0, I97N1, I97N2], [I101N1], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [I113N1], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
