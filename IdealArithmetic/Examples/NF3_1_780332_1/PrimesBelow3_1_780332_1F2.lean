
import IdealArithmetic.Examples.NF3_1_780332_1.RI3_1_780332_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-61, -35, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-61, -35, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![22, 48, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-61, -35, 1], ![558, 63, -35], ![-19530, -3782, 63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -48, 83]], ![![-1, -1, 1], ![16, 21, -35], ![-252, -82, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [31, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 82], [0, 1]]
 g := ![![[66, 75], [57, 61], [30], [78], [15, 11], [1]], ![[0, 8], [0, 22], [30], [78], [2, 72], [1]]]
 h' := ![![[29, 82], [59, 18], [67, 12], [82, 14], [33, 59], [52, 29], [0, 1]], ![[0, 1], [0, 65], [0, 71], [73, 69], [1, 24], [63, 54], [29, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [35, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [31, 54, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1147, 752, 71]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -32, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![35, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![35, 1, 0]] 
 ![![83, 0, 0], ![35, 1, 0], ![20, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![35, 1, 0], ![0, 35, 1], ![558, 124, 35]]]
  hmulB := by decide  
  f := ![![![526, 15, 0], ![-1245, 0, 0]], ![![210, 6, 0], ![-497, 0, 0]], ![![120, 3, 0], ![-284, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 83, 0], ![-20, 0, 83]], ![![0, 1, 0], ![-15, 35, 1], ![-54, 124, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-61, -35, 1]] ![![83, 0, 0], ![35, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2905, 83, 0]], ![![-5063, -2905, 83], ![-1577, -1162, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![35, 1, 0]]], ![![![-61, -35, 1]], ![![-19, -14, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![16, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![16, 1, 0]] 
 ![![89, 0, 0], ![16, 1, 0], ![11, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![16, 1, 0], ![0, 16, 1], ![558, 124, 16]]]
  hmulB := by decide  
  f := ![![![529, 33, 0], ![-2937, 0, 0]], ![![80, 5, 0], ![-444, 0, 0]], ![![51, 3, 0], ![-283, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 89, 0], ![-11, 0, 89]], ![![0, 1, 0], ![-3, 16, 1], ![-18, 124, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![25, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![25, 1, 0]] 
 ![![89, 0, 0], ![25, 1, 0], ![87, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![25, 1, 0], ![0, 25, 1], ![558, 124, 25]]]
  hmulB := by decide  
  f := ![![![926, 37, 0], ![-3293, 0, 0]], ![![250, 10, 0], ![-889, 0, 0]], ![![908, 36, 0], ![-3229, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 89, 0], ![-87, 0, 89]], ![![0, 1, 0], ![-8, 25, 1], ![-53, 124, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-41, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-41, 1, 0]] 
 ![![89, 0, 0], ![48, 1, 0], ![10, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-41, 1, 0], ![0, -41, 1], ![558, 124, -41]]]
  hmulB := by decide  
  f := ![![![3527, -86, 0], ![7654, 0, 0]], ![![1928, -47, 0], ![4184, 0, 0]], ![![470, -11, 0], ![1020, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 89, 0], ![-10, 0, 89]], ![![-1, 1, 0], ![22, -41, 1], ![-56, 124, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![16, 1, 0]] ![![89, 0, 0], ![25, 1, 0]]
  ![![89, 0, 0], ![-45, -48, 1]] where
 M := ![![![7921, 0, 0], ![2225, 89, 0]], ![![1424, 89, 0], ![400, 41, 1]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-45, -48, 1]] ![![89, 0, 0], ![-41, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3649, 89, 0]], ![![-4005, -4272, 89], ![2403, 2047, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-41, 1, 0]]], ![![![-45, -48, 1]], ![![27, 23, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [34, 74, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 70, 26], [55, 26, 71], [0, 1]]
 g := ![![[54, 93, 16], [], [65, 24], [22, 43], [38, 61], [1]], ![[33, 25, 31, 41], [55, 12], [38, 91], [70, 18], [90, 53], [83, 32, 63, 19]], ![[61, 52, 89, 46], [41, 12], [19, 61], [47, 95], [68, 32], [15, 28, 43, 78]]]
 h' := ![![[7, 70, 26], [27, 76, 93], [30, 53], [94, 72, 11], [58, 49, 72], [63, 23, 62], [0, 1]], ![[55, 26, 71], [45, 26, 29], [13, 24, 20], [23, 53, 24], [50, 73, 42], [43, 53, 76], [7, 70, 26]], ![[0, 1], [25, 92, 72], [35, 20, 77], [83, 69, 62], [41, 72, 80], [92, 21, 56], [55, 26, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 67], []]
 b := ![[], [72, 13, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [34, 74, 35, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4451718, 3038234, 425345]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45894, 31322, 4385]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [74, 55, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 42, 68], [61, 58, 33], [0, 1]]
 g := ![![[60, 75, 71], [85, 88], [36, 83, 84], [53, 45], [27, 84], [1]], ![[24, 19, 26, 45], [21, 9], [95, 100, 48, 87], [9, 81], [6, 92], [3, 82, 79, 19]], ![[24, 28, 19, 82], [23, 17], [77, 63, 22, 4], [12, 31], [74, 36], [51, 51, 88, 82]]]
 h' := ![![[4, 42, 68], [2, 99, 24], [63, 3, 54], [34, 67, 36], [44, 35, 34], [27, 46, 65], [0, 1]], ![[61, 58, 33], [38, 9, 44], [73, 7, 3], [65, 75, 79], [78, 11, 9], [44, 25, 30], [4, 42, 68]], ![[0, 1], [20, 94, 33], [56, 91, 44], [89, 60, 87], [88, 55, 58], [98, 30, 6], [61, 58, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 96], []]
 b := ![[], [1, 19, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [74, 55, 36, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47268, -134431, -41309]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-468, -1331, -409]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-61, 28, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-61, 28, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![42, 28, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-61, 28, 1], ![558, 63, 28], ![15624, 4030, 63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -28, 103]], ![![-1, 0, 1], ![-6, -7, 28], ![126, 22, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [15, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 102], [0, 1]]
 g := ![![[25, 55], [73, 66], [], [15], [19], [37, 1]], ![[0, 48], [43, 37], [], [15], [19], [74, 102]]]
 h' := ![![[37, 102], [38, 63], [0, 13], [42], [79, 18], [63, 15], [0, 1]], ![[0, 1], [0, 40], [69, 90], [42], [24, 85], [0, 88], [37, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [64, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [15, 66, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3266, 4346, 913]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-404, -206, 913]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-28, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-28, 1, 0]] 
 ![![103, 0, 0], ![75, 1, 0], ![40, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-28, 1, 0], ![0, -28, 1], ![558, 124, -28]]]
  hmulB := by decide  
  f := ![![![2745, -98, 0], ![10094, 0, 0]], ![![1989, -71, 0], ![7314, 0, 0]], ![![1072, -38, 0], ![3942, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 103, 0], ![-40, 0, 103]], ![![-1, 1, 0], ![20, -28, 1], ![-74, 124, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-61, 28, 1]] ![![103, 0, 0], ![-28, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2884, 103, 0]], ![![-6283, 2884, 103], ![2266, -721, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-28, 1, 0]]], ![![![-61, 28, 1]], ![![22, -7, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![38, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![38, 1, 0]] 
 ![![107, 0, 0], ![38, 1, 0], ![54, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![38, 1, 0], ![0, 38, 1], ![558, 124, 38]]]
  hmulB := by decide  
  f := ![![![951, 25, 0], ![-2675, 0, 0]], ![![342, 9, 0], ![-962, 0, 0]], ![![470, 12, 0], ![-1322, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 107, 0], ![-54, 0, 107]], ![![0, 1, 0], ![-14, 38, 1], ![-58, 124, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-21, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-21, 1, 0]] 
 ![![107, 0, 0], ![86, 1, 0], ![94, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-21, 1, 0], ![0, -21, 1], ![558, 124, -21]]]
  hmulB := by decide  
  f := ![![![1324, -63, 0], ![6741, 0, 0]], ![![1072, -51, 0], ![5458, 0, 0]], ![![1160, -55, 0], ![5906, 1, 0]]]
  g := ![![![1, 0, 0], ![-86, 107, 0], ![-94, 0, 107]], ![![-1, 1, 0], ![16, -21, 1], ![-76, 124, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-17, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-17, 1, 0]] 
 ![![107, 0, 0], ![90, 1, 0], ![32, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-17, 1, 0], ![0, -17, 1], ![558, 124, -17]]]
  hmulB := by decide  
  f := ![![![1242, -73, 0], ![7811, 0, 0]], ![![1038, -61, 0], ![6528, 0, 0]], ![![394, -23, 0], ![2478, 1, 0]]]
  g := ![![![1, 0, 0], ![-90, 107, 0], ![-32, 0, 107]], ![![-1, 1, 0], ![14, -17, 1], ![-94, 124, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![38, 1, 0]] ![![107, 0, 0], ![-21, 1, 0]]
  ![![107, 0, 0], ![-49, 17, 1]] where
 M := ![![![11449, 0, 0], ![-2247, 107, 0]], ![![4066, 107, 0], ![-798, 17, 1]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![28, -16, -1], ![107, 0, 0]]], ![![![38, 1, 0], ![0, 0, 0]], ![![42, -17, -1], ![108, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-49, 17, 1]] ![![107, 0, 0], ![-17, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1819, 107, 0]], ![![-5243, 1819, 107], ![1391, -214, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-17, 1, 0]]], ![![![-49, 17, 1]], ![![13, -2, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [96, 62, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 25, 72], [42, 83, 37], [0, 1]]
 g := ![![[28, 5, 27], [58, 21], [51, 105, 48], [13, 77, 88], [46, 28], [1]], ![[65, 44, 66, 99], [26, 43], [42, 32, 19, 51], [46, 64, 42, 11], [65, 48], [13, 54, 18, 32]], ![[29, 9, 38, 62], [29, 3], [15, 21, 35, 101], [12, 58, 15, 101], [21, 64], [107, 48, 17, 77]]]
 h' := ![![[37, 25, 72], [72, 28, 71], [9, 59, 28], [60, 102, 22], [4, 42, 57], [13, 47, 79], [0, 1]], ![[42, 83, 37], [7, 108, 61], [66, 41, 32], [77, 53, 14], [103, 85, 16], [28, 2, 22], [37, 25, 72]], ![[0, 1], [2, 82, 86], [72, 9, 49], [103, 63, 73], [40, 91, 36], [51, 60, 8], [42, 83, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 17], []]
 b := ![[], [57, 90, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [96, 62, 30, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-485922, -162192, -13734]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4458, -1488, -126]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-122, -62, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-122, -62, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![104, 51, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-122, -62, 1], ![558, 2, -62], ![-34596, -7130, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -51, 113]], ![![-2, -1, 1], ![62, 28, -62], ![-308, -64, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [85, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 112], [0, 1]]
 g := ![![[59, 4], [36], [112], [104], [104, 15], [70, 1]], ![[0, 109], [36], [112], [104], [24, 98], [27, 112]]]
 h' := ![![[70, 112], [86, 2], [78, 107], [85, 15], [87, 68], [39, 69], [0, 1]], ![[0, 1], [0, 111], [110, 6], [5, 98], [101, 45], [10, 44], [70, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [30, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [85, 43, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21333, 6125, 530]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-299, -185, 530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-51, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-51, 1, 0]] 
 ![![113, 0, 0], ![62, 1, 0], ![111, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-51, 1, 0], ![0, -51, 1], ![558, 124, -51]]]
  hmulB := by decide  
  f := ![![![5101, -100, 0], ![11300, 0, 0]], ![![2806, -55, 0], ![6216, 0, 0]], ![![4971, -97, 0], ![11012, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 113, 0], ![-111, 0, 113]], ![![-1, 1, 0], ![27, -51, 1], ![-13, 124, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-122, -62, 1]] ![![113, 0, 0], ![-51, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5763, 113, 0]], ![![-13786, -7006, 113], ![6780, 3164, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-51, 1, 0]]], ![![![-122, -62, 1]], ![![60, 28, -1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-82, -13, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-82, -13, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![45, 114, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-82, -13, 1], ![558, 42, -13], ![-7254, -1054, 42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -114, 127]], ![![-1, -1, 1], ![9, 12, -13], ![-72, -46, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [81, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 126], [0, 1]]
 g := ![![[104, 69], [68, 50], [62, 68], [83, 22], [95, 8], [85, 1]], ![[0, 58], [0, 77], [0, 59], [48, 105], [13, 119], [43, 126]]]
 h' := ![![[85, 126], [80, 14], [58, 80], [8, 103], [52, 28], [100, 32], [0, 1]], ![[0, 1], [0, 113], [0, 47], [0, 24], [19, 99], [26, 95], [85, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [64, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [81, 42, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3308, -66, 93]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-59, -84, 93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![13, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![13, 1, 0]] 
 ![![127, 0, 0], ![13, 1, 0], ![85, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![13, 1, 0], ![0, 13, 1], ![558, 124, 13]]]
  hmulB := by decide  
  f := ![![![963, 74, 0], ![-9398, 0, 0]], ![![91, 7, 0], ![-888, 0, 0]], ![![639, 49, 0], ![-6236, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 127, 0], ![-85, 0, 127]], ![![0, 1, 0], ![-2, 13, 1], ![-17, 124, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-82, -13, 1]] ![![127, 0, 0], ![13, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![1651, 127, 0]], ![![-10414, -1651, 127], ![-508, -127, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![13, 1, 0]]], ![![![-82, -13, 1]], ![![-4, -1, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [115, 130, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 4, 85], [75, 126, 46], [0, 1]]
 g := ![![[100, 109, 81], [130, 18, 129], [103, 28], [102, 21], [127, 1], [103, 1], []], ![[116, 119, 58, 66], [96, 101, 9, 26], [111, 99], [20, 46], [68, 41], [127, 25], [120, 20]], ![[110, 5, 28, 80], [127, 118, 31, 121], [106, 48], [85, 81], [55, 107], [4, 16], [28, 20]]]
 h' := ![![[28, 4, 85], [115, 52, 9], [114, 4, 28], [13, 115, 91], [79, 22, 105], [76, 119, 130], [0, 0, 1], [0, 1]], ![[75, 126, 46], [100, 27, 52], [89, 6, 69], [4, 100, 19], [83, 116, 35], [49, 74, 33], [84, 9, 126], [28, 4, 85]], ![[0, 1], [115, 52, 70], [27, 121, 34], [77, 47, 21], [114, 124, 122], [46, 69, 99], [47, 122, 4], [75, 126, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 15], []]
 b := ![[], [127, 26, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [115, 130, 28, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3384385, 1371570, 144624]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25835, 10470, 1104]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-46, -30, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-46, -30, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![91, 107, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-46, -30, 1], ![558, 78, -30], ![-16740, -3162, 78]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -107, 137]], ![![-1, -1, 1], ![24, 24, -30], ![-174, -84, 78]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [38, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 136], [0, 1]]
 g := ![![[107, 119], [130], [59], [33, 44], [135], [18], [1]], ![[0, 18], [130], [59], [51, 93], [135], [18], [1]]]
 h' := ![![[44, 136], [118, 16], [117, 33], [116, 123], [84, 27], [75, 51], [99, 44], [0, 1]], ![[0, 1], [0, 121], [62, 104], [48, 14], [39, 110], [127, 86], [117, 93], [44, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [106, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [38, 93, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22092, -3698, 790]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-686, -644, 790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![30, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![30, 1, 0]] 
 ![![137, 0, 0], ![30, 1, 0], ![59, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![30, 1, 0], ![0, 30, 1], ![558, 124, 30]]]
  hmulB := by decide  
  f := ![![![841, 28, 0], ![-3836, 0, 0]], ![![150, 5, 0], ![-684, 0, 0]], ![![367, 12, 0], ![-1674, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 137, 0], ![-59, 0, 137]], ![![0, 1, 0], ![-7, 30, 1], ![-36, 124, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-46, -30, 1]] ![![137, 0, 0], ![30, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![4110, 137, 0]], ![![-6302, -4110, 137], ![-822, -822, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![30, 1, 0]]], ![![![-46, -30, 1]], ![![-6, -6, 0]]]]
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


lemma PB250I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB250I2 : PrimesBelowBoundCertificateInterval O 79 137 250 where
  m := 11
  g := ![2, 3, 1, 1, 2, 3, 1, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB250I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
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
      exact NI107N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I89N2, I103N1, I107N0, I107N1, I107N2, I113N1, I127N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [], [], [I103N1], [I107N0, I107N1, I107N2], [], [I113N1], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
