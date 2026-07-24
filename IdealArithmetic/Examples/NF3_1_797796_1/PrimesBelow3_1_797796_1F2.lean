
import IdealArithmetic.Examples.NF3_1_797796_1.RI3_1_797796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![24, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![24, 1, 0]] 
 ![![83, 0, 0], ![24, 1, 0], ![44, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![24, 1, 0], ![0, 24, 2], ![710, 117, 24]]]
  hmulB := by decide  
  f := ![![![745, 31, 0], ![-2573, 0, 0]], ![![216, 9, 0], ![-746, 0, 0]], ![![388, 4, -1], ![-1340, 42, 0]]]
  g := ![![![1, 0, 0], ![-24, 83, 0], ![-44, 0, 83]], ![![0, 1, 0], ![-8, 24, 2], ![-38, 117, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![35, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![35, 1, 0]] 
 ![![83, 0, 0], ![35, 1, 0], ![10, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![35, 1, 0], ![0, 35, 2], ![710, 117, 35]]]
  hmulB := by decide  
  f := ![![![526, 15, 0], ![-1245, 0, 0]], ![![210, 6, 0], ![-497, 0, 0]], ![![60, -16, -1], ![-142, 42, 0]]]
  g := ![![![1, 0, 0], ![-35, 83, 0], ![-10, 0, 83]], ![![0, 1, 0], ![-15, 35, 2], ![-45, 117, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![24, 1, 0]] ![![83, 0, 0], ![24, 1, 0]]
  ![![83, 0, 0], ![-44, 24, 1]] where
 M := ![![![6889, 0, 0], ![1992, 83, 0]], ![![1992, 83, 0], ![576, 48, 2]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![24, 1, 0], ![0, 0, 0]]], ![![![24, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-44, 24, 1]] ![![83, 0, 0], ![35, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2905, 83, 0]], ![![-3652, 1992, 83], ![-830, 913, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![35, 1, 0]]], ![![![-44, 24, 1]], ![![-10, 11, 1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![32, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![32, 1, 0]] 
 ![![89, 0, 0], ![32, 1, 0], ![22, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![32, 1, 0], ![0, 32, 2], ![710, 117, 32]]]
  hmulB := by decide  
  f := ![![![1089, 34, 0], ![-3026, 0, 0]], ![![352, 11, 0], ![-978, 0, 0]], ![![262, -8, -1], ![-728, 45, 0]]]
  g := ![![![1, 0, 0], ![-32, 89, 0], ![-22, 0, 89]], ![![0, 1, 0], ![-12, 32, 2], ![-42, 117, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-16, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-16, 1, 0]] 
 ![![89, 0, 0], ![73, 1, 0], ![50, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-16, 1, 0], ![0, -16, 2], ![710, 117, -16]]]
  hmulB := by decide  
  f := ![![![753, -47, 0], ![4183, 0, 0]], ![![641, -40, 0], ![3561, 0, 0]], ![![450, -20, -1], ![2500, 45, 0]]]
  g := ![![![1, 0, 0], ![-73, 89, 0], ![-50, 0, 89]], ![![-1, 1, 0], ![12, -16, 2], ![-79, 117, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![32, 1, 0]] ![![89, 0, 0], ![-16, 1, 0]]
  ![![89, 0, 0], ![-78, 8, 1]] where
 M := ![![![7921, 0, 0], ![-1424, 89, 0]], ![![2848, 89, 0], ![-512, 16, 2]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![62, -7, -1], ![89, 0, 0]]], ![![![32, 1, 0], ![0, 0, 0]], ![![74, -8, -1], ![91, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-78, 8, 1]] ![![89, 0, 0], ![-16, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1424, 89, 0]], ![![-6942, 712, 89], ![1958, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-16, 1, 0]]], ![![![-78, 8, 1]], ![![22, -1, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-118, -40, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-118, -40, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![76, 57, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-118, -40, 1], ![710, -1, -80], ![-28400, -4325, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-76, -57, 97]], ![![-2, -1, 1], ![70, 47, -80], ![-292, -44, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [77, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 96], [0, 1]]
 g := ![![[57, 8], [8], [24], [25], [2], [73, 1]], ![[59, 89], [8], [24], [25], [2], [49, 96]]]
 h' := ![![[73, 96], [72, 28], [3, 69], [69, 11], [65, 92], [5, 14], [0, 1]], ![[0, 1], [79, 69], [93, 28], [96, 86], [88, 5], [57, 83], [73, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [39, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [77, 24, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1497, 565, 95]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-59, -50, 95]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-17, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-17, 1, 0]] 
 ![![97, 0, 0], ![80, 1, 0], ![1, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-17, 1, 0], ![0, -17, 2], ![710, 117, -17]]]
  hmulB := by decide  
  f := ![![![817, -48, 0], ![4656, 0, 0]], ![![698, -41, 0], ![3978, 0, 0]], ![![27, 7, -1], ![154, 49, 0]]]
  g := ![![![1, 0, 0], ![-80, 97, 0], ![-1, 0, 97]], ![![-1, 1, 0], ![14, -17, 2], ![-89, 117, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-118, -40, 1]] ![![97, 0, 0], ![-17, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1649, 97, 0]], ![![-11446, -3880, 97], ![2716, 679, -97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-17, 1, 0]]], ![![![-118, -40, 1]], ![![28, 7, -1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-73, -27, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-73, -27, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![28, 74, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-73, -27, 1], ![710, 44, -54], ![-19170, -2804, 44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -74, 101]], ![![-1, -1, 1], ![22, 40, -54], ![-202, -60, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [70, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 100], [0, 1]]
 g := ![![[80, 13], [96], [51, 85], [43], [84], [56, 1]], ![[0, 88], [96], [64, 16], [43], [84], [11, 100]]]
 h' := ![![[56, 100], [60, 35], [66, 46], [3, 40], [36, 12], [19, 36], [0, 1]], ![[0, 1], [0, 66], [16, 55], [21, 61], [1, 89], [15, 65], [56, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [2, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [70, 45, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8494, 1705, 1190]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-414, -855, 1190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-47, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-47, 1, 0]] 
 ![![101, 0, 0], ![54, 1, 0], ![57, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-47, 1, 0], ![0, -47, 2], ![710, 117, -47]]]
  hmulB := by decide  
  f := ![![![2962, -63, 0], ![6363, 0, 0]], ![![1646, -35, 0], ![3536, 0, 0]], ![![1680, -12, -1], ![3609, 51, 0]]]
  g := ![![![1, 0, 0], ![-54, 101, 0], ![-57, 0, 101]], ![![-1, 1, 0], ![24, -47, 2], ![-29, 117, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-73, -27, 1]] ![![101, 0, 0], ![-47, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4747, 101, 0]], ![![-7373, -2727, 101], ![4141, 1313, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-47, 1, 0]]], ![![![-73, -27, 1]], ![![41, 13, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-94, 28, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-94, 28, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![9, 28, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-94, 28, 1], ![710, 23, 56], ![19880, 3631, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -28, 103]], ![![-1, 0, 1], ![2, -15, 56], ![191, 29, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [54, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 102], [0, 1]]
 g := ![![[55, 14], [62, 19], [90, 15], [66], [17], [17, 1]], ![[87, 89], [76, 84], [36, 88], [66], [17], [34, 102]]]
 h' := ![![[17, 102], [51, 80], [84, 15], [4, 18], [90, 90], [9, 29], [0, 1]], ![[0, 1], [72, 23], [30, 88], [1, 85], [75, 13], [90, 74], [17, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [99, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [54, 86, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2774, 79, 161]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41, -43, 161]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![47, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![47, 1, 0]] 
 ![![103, 0, 0], ![47, 1, 0], ![80, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![47, 1, 0], ![0, 47, 2], ![710, 117, 47]]]
  hmulB := by decide  
  f := ![![![1552, 33, 0], ![-3399, 0, 0]], ![![658, 14, 0], ![-1441, 0, 0]], ![![1210, 2, -1], ![-2650, 52, 0]]]
  g := ![![![1, 0, 0], ![-47, 103, 0], ![-80, 0, 103]], ![![0, 1, 0], ![-23, 47, 2], ![-83, 117, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-94, 28, 1]] ![![103, 0, 0], ![47, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![4841, 103, 0]], ![![-9682, 2884, 103], ![-3708, 1339, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![47, 1, 0]]], ![![![-94, 28, 1]], ![![-36, 13, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-95, -15, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-95, -15, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![12, 92, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-95, -15, 1], ![710, 22, -30], ![-10650, -1400, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -92, 107]], ![![-1, -1, 1], ![10, 26, -30], ![-102, -32, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [63, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 106], [0, 1]]
 g := ![![[103, 3], [26, 83], [40], [22, 1], [100], [38, 1]], ![[3, 104], [77, 24], [40], [60, 106], [100], [76, 106]]]
 h' := ![![[38, 106], [74, 18], [73, 46], [5, 88], [8, 106], [67, 97], [0, 1]], ![[0, 1], [9, 89], [2, 61], [32, 19], [77, 1], [8, 10], [38, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [81, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [63, 69, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4127, 2564, 842]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-133, -700, 842]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![30, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![30, 1, 0]] 
 ![![107, 0, 0], ![30, 1, 0], ![85, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![30, 1, 0], ![0, 30, 2], ![710, 117, 30]]]
  hmulB := by decide  
  f := ![![![631, 21, 0], ![-2247, 0, 0]], ![![150, 5, 0], ![-534, 0, 0]], ![![485, 1, -1], ![-1727, 54, 0]]]
  g := ![![![1, 0, 0], ![-30, 107, 0], ![-85, 0, 107]], ![![0, 1, 0], ![-10, 30, 2], ![-50, 117, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-95, -15, 1]] ![![107, 0, 0], ![30, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![3210, 107, 0]], ![![-10165, -1605, 107], ![-2140, -428, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![30, 1, 0]]], ![![![-95, -15, 1]], ![![-20, -4, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [33, 98, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 20, 42], [105, 88, 67], [0, 1]]
 g := ![![[40, 81, 104], [5, 36], [89, 62, 94], [67, 6, 3], [21, 38], [1]], ![[67, 17, 89, 14], [], [91, 47, 30, 51], [28, 72, 78, 40], [87, 26], [3, 27, 77, 77]], ![[2, 2, 12, 76], [50, 36], [48, 84, 79, 24], [104, 73, 52, 13], [91, 34], [65, 39, 81, 32]]]
 h' := ![![[97, 20, 42], [89, 102, 70], [6, 3, 6], [78, 68, 58], [69, 104, 60], [76, 11, 93], [0, 1]], ![[105, 88, 67], [5, 103, 89], [21, 31], [82, 26, 3], [94, 46, 56], [26, 43, 35], [97, 20, 42]], ![[0, 1], [16, 13, 59], [85, 75, 103], [68, 15, 48], [18, 68, 102], [80, 55, 90], [105, 88, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 39], []]
 b := ![[], [20, 108, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [33, 98, 16, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-479927, -117175, -14715]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4403, -1075, -135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [82, 69, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 22, 28], [80, 90, 85], [0, 1]]
 g := ![![[16, 98, 14], [12, 30], [99, 82], [95, 104], [9, 39, 8], [1]], ![[39, 0, 36, 22], [37, 97], [110, 60], [50, 88], [30, 42, 74, 91], [9, 50, 94, 30]], ![[78, 16, 47, 50], [21, 13], [26, 102], [32, 49], [49, 94, 67, 41], [47, 12, 40, 83]]]
 h' := ![![[44, 22, 28], [3, 13, 50], [99, 96, 16], [104, 64, 67], [53, 80, 45], [31, 44, 11], [0, 1]], ![[80, 90, 85], [73, 99, 5], [13, 95, 60], [28, 102, 25], [25, 21, 75], [35, 111, 75], [44, 22, 28]], ![[0, 1], [17, 1, 58], [65, 35, 37], [84, 60, 21], [83, 12, 106], [98, 71, 27], [80, 90, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 45], []]
 b := ![[], [54, 76, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [82, 69, 102, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17559974, 3746628, 395952]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![155398, 33156, 3504]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [52, 29, 110, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 28, 71], [49, 98, 56], [0, 1]]
 g := ![![[69, 20, 41], [2, 54, 19], [90, 28, 61], [71, 105, 1], [47, 117, 35], [1]], ![[70, 58, 63, 113], [67, 99, 19, 13], [87, 31, 106, 122], [87, 47, 67, 121], [79, 96, 3, 64], [104, 5, 70, 25]], ![[69, 90, 71, 92], [107, 98, 80, 95], [47, 67, 37, 3], [25, 117, 45, 119], [104, 116, 78, 3], [16, 46, 47, 102]]]
 h' := ![![[95, 28, 71], [23, 35, 101], [19, 79, 20], [118, 46, 76], [96, 83, 126], [75, 98, 17], [0, 1]], ![[49, 98, 56], [105, 90, 64], [54, 44, 76], [105, 60, 46], [36, 121, 80], [51, 63, 115], [95, 28, 71]], ![[0, 1], [118, 2, 89], [105, 4, 31], [54, 21, 5], [66, 50, 48], [104, 93, 122], [49, 98, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 32], []]
 b := ![[], [103, 67, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [52, 29, 110, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78232, -10414, 1016]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![616, -82, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [37, 89, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 108, 51], [112, 22, 80], [0, 1]]
 g := ![![[1, 91, 25], [4, 117, 101], [128, 34], [112, 25], [97, 108], [75, 1], []], ![[83, 41, 104, 29], [126, 46, 11, 82], [104, 59], [82, 33], [80, 113], [115, 91], [28, 112]], ![[68, 120, 101, 7], [88, 92, 78, 33], [44, 28], [82, 63], [63, 38], [41, 5], [130, 112]]]
 h' := ![![[94, 108, 51], [114, 5, 5], [57, 102, 106], [48, 111, 54], [0, 125, 5], [107, 100, 34], [0, 0, 1], [0, 1]], ![[112, 22, 80], [22, 105, 103], [10, 91, 67], [37, 85, 37], [53, 96, 66], [0, 113, 84], [71, 44, 22], [94, 108, 51]], ![[0, 1], [44, 21, 23], [90, 69, 89], [43, 66, 40], [8, 41, 60], [80, 49, 13], [5, 87, 108], [112, 22, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 86], []]
 b := ![[], [91, 29, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [37, 89, 56, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3173737, 939139, 145934]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24227, 7169, 1114]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-109, -2, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-109, -2, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![28, 135, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-109, -2, 1], ![710, 8, -4], ![-1420, 121, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -135, 137]], ![![-1, -1, 1], ![6, 4, -4], ![-12, -7, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [63, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 136], [0, 1]]
 g := ![![[113, 87], [30], [56], [126, 14], [68], [25], [1]], ![[0, 50], [30], [56], [59, 123], [68], [25], [1]]]
 h' := ![![[5, 136], [42, 19], [98, 21], [8, 78], [78, 39], [65, 43], [74, 5], [0, 1]], ![[0, 1], [0, 118], [66, 116], [124, 59], [136, 98], [6, 94], [99, 132], [5, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [38, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [63, 132, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28069, -4620, 940]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-397, -960, 940]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![4, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![4, 1, 0]] 
 ![![137, 0, 0], ![4, 1, 0], ![129, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![4, 1, 0], ![0, 4, 2], ![710, 117, 4]]]
  hmulB := by decide  
  f := ![![![389, 97, 0], ![-13289, 0, 0]], ![![4, 1, 0], ![-136, 0, 0]], ![![365, 89, -1], ![-12469, 69, 0]]]
  g := ![![![1, 0, 0], ![-4, 137, 0], ![-129, 0, 137]], ![![0, 1, 0], ![-2, 4, 2], ![-2, 117, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-109, -2, 1]] ![![137, 0, 0], ![4, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![548, 137, 0]], ![![-14933, -274, 137], ![274, 0, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![4, 1, 0]]], ![![![-109, -2, 1]], ![![2, 0, 0]]]]
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


lemma PB253I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB253I2 : PrimesBelowBoundCertificateInterval O 79 137 253 where
  m := 11
  g := ![3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB253I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0]
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
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![2048383]
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
      exact NI89N1
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I89N0, I89N1, I97N1, I101N1, I103N1, I107N1, I137N1]
  Il := ![[I83N0, I83N0, I83N1], [I89N0, I89N1, I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [], [], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
