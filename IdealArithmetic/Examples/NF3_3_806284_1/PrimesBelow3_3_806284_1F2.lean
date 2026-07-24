
import IdealArithmetic.Examples.NF3_3_806284_1.RI3_3_806284_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![3, -10, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![3, -10, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![3, 73, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![3, -10, 1], ![103, 44, -21], ![-1133, -484, 65]]]
  hmulB := by decide  
  f := ![![![-2, 10, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -73, 83]], ![![0, -1, 1], ![2, 19, -21], ![-16, -63, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [11, 73, 1] where
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
 g := ![![[67, 68], [71, 51], [64], [59], [33, 17], [1]], ![[0, 15], [0, 32], [64], [59], [37, 66], [1]]]
 h' := ![![[10, 82], [49, 20], [28, 47], [63, 75], [52, 15], [72, 10], [0, 1]], ![[0, 1], [0, 63], [0, 36], [66, 8], [36, 68], [6, 73], [10, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [15, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [11, 73, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![320, 704, 245]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -207, 245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![21, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![21, 1, 0]] 
 ![![83, 0, 0], ![21, 1, 0], ![18, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![21, 1, 0], ![0, 22, 2], ![103, 51, 20]]]
  hmulB := by decide  
  f := ![![![43, 2, 0], ![-166, 0, 0]], ![![-21, -1, 0], ![84, 0, 0]], ![![-18, -12, -1], ![72, 42, 0]]]
  g := ![![![1, 0, 0], ![-21, 83, 0], ![-18, 0, 83]], ![![0, 1, 0], ![-6, 22, 2], ![-16, 51, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![3, -10, 1]] ![![83, 0, 0], ![21, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1743, 83, 0]], ![![249, -830, 83], ![166, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![21, 1, 0]]], ![![![3, -10, 1]], ![![2, -2, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70, -44, -7]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-70, -44, -7]] 
 ![![89, 0, 0], ![0, 89, 0], ![10, 19, 1]] where
  M :=![![![-70, -44, -7], ![-721, -471, -81], ![-3811, -2426, -390]]]
  hmulB := by decide  
  f := ![![![-144, -2, 3]], ![![309, 7, -7]], ![![44, 1, -1]]]
  g := ![![![0, 1, -7], ![1, 12, -81], ![1, 56, -390]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [50, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 88], [0, 1]]
 g := ![![[12, 73], [50], [17], [3, 57], [77, 84], [1]], ![[0, 16], [50], [17], [68, 32], [51, 5], [1]]]
 h' := ![![[23, 88], [76, 47], [23, 36], [28, 62], [66, 71], [39, 23], [0, 1]], ![[0, 1], [0, 42], [50, 53], [30, 27], [8, 18], [34, 66], [23, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [42, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [50, 66, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-839, 889, 1082]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-131, -221, 1082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-144, -2, 3]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-144, -2, 3]] 
 ![![89, 0, 0], ![52, 1, 0], ![46, 0, 1]] where
  M :=![![![-144, -2, 3], ![309, 7, -7], ![-515, -24, 14]]]
  hmulB := by decide  
  f := ![![![-70, -44, -7]], ![![-49, -31, -5]], ![![-79, -50, -8]]]
  g := ![![![-2, -2, 3], ![3, 7, -7], ![1, -24, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-70, -44, -7]] ![![-144, -2, 3]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-67, 20, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-67, 20, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![30, 20, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-67, 20, 1], ![103, 4, 39], ![1957, 1046, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -20, 97]], ![![-1, 0, 1], ![-11, -8, 39], ![31, 18, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [72, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 96], [0, 1]]
 g := ![![[1, 31], [91], [61], [16], [65], [25, 1]], ![[0, 66], [91], [61], [16], [65], [50, 96]]]
 h' := ![![[25, 96], [13, 15], [58, 24], [45, 62], [79, 4], [43, 68], [0, 1]], ![[0, 1], [0, 82], [76, 73], [43, 35], [82, 93], [94, 29], [25, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [87, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [72, 72, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-543, 26, 108]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, -22, 108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-39, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-39, 1, 0]] 
 ![![97, 0, 0], ![58, 1, 0], ![35, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-39, 1, 0], ![0, -38, 2], ![103, 51, -40]]]
  hmulB := by decide  
  f := ![![![820, -21, 0], ![2037, 0, 0]], ![![508, -13, 0], ![1262, 0, 0]], ![![320, 11, -1], ![795, 49, 0]]]
  g := ![![![1, 0, 0], ![-58, 97, 0], ![-35, 0, 97]], ![![-1, 1, 0], ![22, -38, 2], ![-15, 51, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-67, 20, 1]] ![![97, 0, 0], ![-39, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3783, 97, 0]], ![![-6499, 1940, 97], ![2716, -776, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-39, 1, 0]]], ![![![-67, 20, 1]], ![![28, -8, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![11, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![11, 1, 0]] 
 ![![101, 0, 0], ![11, 1, 0], ![35, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![11, 1, 0], ![0, 12, 2], ![103, 51, 10]]]
  hmulB := by decide  
  f := ![![![419, 38, 0], ![-3838, 0, 0]], ![![33, 3, 0], ![-302, 0, 0]], ![![133, 6, -1], ![-1218, 51, 0]]]
  g := ![![![1, 0, 0], ![-11, 101, 0], ![-35, 0, 101]], ![![0, 1, 0], ![-2, 12, 2], ![-8, 51, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-9, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-9, 1, 0]] 
 ![![101, 0, 0], ![92, 1, 0], ![65, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-9, 1, 0], ![0, -8, 2], ![103, 51, -10]]]
  hmulB := by decide  
  f := ![![![442, -49, 0], ![4949, 0, 0]], ![![406, -45, 0], ![4546, 0, 0]], ![![298, -29, -1], ![3337, 51, 0]]]
  g := ![![![1, 0, 0], ![-92, 101, 0], ![-65, 0, 101]], ![![-1, 1, 0], ![6, -8, 2], ![-39, 51, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-2, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-2, 1, 0]] 
 ![![101, 0, 0], ![99, 1, 0], ![100, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-2, 1, 0], ![0, -1, 2], ![103, 51, -3]]]
  hmulB := by decide  
  f := ![![![3, 49, -100], ![101, 5050, 0]], ![![1, 49, -98], ![1, 4949, 0]], ![![2, 49, -99], ![51, 5000, 0]]]
  g := ![![![1, 0, 0], ![-99, 101, 0], ![-100, 0, 101]], ![![-1, 1, 0], ![-1, -1, 2], ![-46, 51, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![11, 1, 0]] ![![101, 0, 0], ![-9, 1, 0]]
  ![![101, 0, 0], ![1, -49, 1]] where
 M := ![![![10201, 0, 0], ![-909, 101, 0]], ![![1111, 101, 0], ![-99, 3, 2]]]
 hmul := by decide  
 g := ![![![![100, 49, -1], ![101, 0, 0]], ![![-9, 1, 0], ![0, 0, 0]]], ![![![11, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![1, -49, 1]] ![![101, 0, 0], ![-2, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-202, 101, 0]], ![![101, -4949, 101], ![101, 101, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-2, 1, 0]]], ![![![1, -49, 1]], ![![1, 1, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![0, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![0, 1, 0]] 
 ![![103, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![0, 1, 0], ![0, 1, 2], ![103, 51, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![51, 52, 0]]]
  g := ![![![1, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![0, 1, 0], ![0, 1, 2], ![1, 51, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![0, 1, 0]] ![![103, 0, 0], ![0, 1, 0]]
  ![![103, 0, 0], ![0, -51, 1]] where
 M := ![![![10609, 0, 0], ![0, 103, 0]], ![![0, 103, 0], ![0, 1, 2]]]
 hmul := by decide  
 g := ![![![![68, 0, 35], ![0, 35, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![0, -51, 1]] ![![103, 0, 0], ![0, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![0, 103, 0]], ![![0, -5253, 103], ![103, 0, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![0, 1, 0]]], ![![![0, -51, 1]], ![![1, 0, -1]]]]
 hle2 := by decide  

def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N0, I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N0
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [46, 7, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 74, 32], [84, 32, 75], [0, 1]]
 g := ![![[106, 53, 1], [103, 12, 16], [36, 69], [5, 90, 13], [75, 101], [1]], ![[73, 101, 76, 22], [2, 77, 18, 7], [103, 62], [36, 53, 28, 106], [88, 101], [60, 49, 16, 26]], ![[1, 60, 68, 27], [16, 20, 64, 92], [69, 69], [18, 50, 52, 48], [], [95, 92, 15, 81]]]
 h' := ![![[46, 74, 32], [77, 92, 106], [98, 98, 103], [91, 37, 47], [57, 74, 21], [61, 100, 23], [0, 1]], ![[84, 32, 75], [74, 90, 23], [78, 68, 12], [106, 52, 13], [55, 71, 44], [95, 23, 84], [46, 74, 32]], ![[0, 1], [76, 32, 85], [98, 48, 99], [94, 18, 47], [57, 69, 42], [48, 91], [84, 32, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 5], []]
 b := ![[], [79, 69, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [46, 7, 84, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-508785, -582722, -216889]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4755, -5446, -2027]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-5, 12, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-5, 12, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![104, 12, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-5, 12, 1], ![103, 58, 23], ![1133, 638, 35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -12, 109]], ![![-1, 0, 1], ![-21, -2, 23], ![-23, 2, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [68, 49, 1] where
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
 g := ![![[44, 71], [63], [67, 84], [36, 21], [83], [60, 1]], ![[53, 38], [63], [93, 25], [97, 88], [83], [11, 108]]]
 h' := ![![[60, 108], [15, 92], [22, 45], [59, 53], [53, 81], [62, 44], [0, 1]], ![[0, 1], [85, 17], [106, 64], [78, 56], [8, 28], [86, 65], [60, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [95, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [68, 49, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![377, 752, 317]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-299, -28, 317]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-23, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-23, 1, 0]] 
 ![![109, 0, 0], ![86, 1, 0], ![74, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-23, 1, 0], ![0, -22, 2], ![103, 51, -24]]]
  hmulB := by decide  
  f := ![![![484, -21, 0], ![2289, 0, 0]], ![![392, -17, 0], ![1854, 0, 0]], ![![348, -4, -1], ![1646, 55, 0]]]
  g := ![![![1, 0, 0], ![-86, 109, 0], ![-74, 0, 109]], ![![-1, 1, 0], ![16, -22, 2], ![-23, 51, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-5, 12, 1]] ![![109, 0, 0], ![-23, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2507, 109, 0]], ![![-545, 1308, 109], ![218, -218, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-23, 1, 0]]], ![![![-5, 12, 1]], ![![2, -2, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, -4, -5]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![8, -4, -5]] 
 ![![113, 0, 0], ![0, 113, 0], ![21, 46, 1]] where
  M :=![![![8, -4, -5], ![-515, -251, -3], ![103, -334, -248]]]
  hmulB := by decide  
  f := ![![![542, 6, -11]], ![![-1133, -13, 23]], ![![-345, -4, 7]]]
  g := ![![![1, 2, -5], ![-4, -1, -3], ![47, 98, -248]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [90, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 112], [0, 1]]
 g := ![![[10, 8], [25], [61], [112], [39, 52], [4, 1]], ![[42, 105], [25], [61], [112], [21, 61], [8, 112]]]
 h' := ![![[4, 112], [1, 102], [45, 108], [26, 93], [106, 98], [92, 39], [0, 1]], ![[0, 1], [70, 11], [25, 5], [59, 20], [46, 15], [22, 74], [4, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [67, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [90, 109, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41297, 56926, 25223]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4322, -9764, 25223]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-542, -6, 11]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-542, -6, 11]] 
 ![![113, 0, 0], ![22, 1, 0], ![86, 0, 1]] where
  M :=![![![-542, -6, 11], ![1133, 13, -23], ![-1751, -20, 36]]]
  hmulB := by decide  
  f := ![![![-8, 4, 5]], ![![3, 3, 1]], ![![-7, 6, 6]]]
  g := ![![![-12, -6, 11], ![25, 13, -23], ![-39, -20, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![8, -4, -5]] ![![-542, -6, 11]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [2, 103, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 87, 65], [32, 39, 62], [0, 1]]
 g := ![![[93, 106, 15], [45, 18, 2], [51, 88, 25], [89, 49, 122], [32, 103, 94], [1]], ![[18, 92, 36, 51], [95, 54, 111, 114], [78, 12, 91, 118], [102, 7, 20, 83], [124, 44, 103, 65], [90, 12, 4, 51]], ![[17, 108, 72, 38], [6, 21, 31, 122], [21, 87, 94, 124], [7, 45, 78, 68], [22, 21, 24, 94], [112, 26, 21, 76]]]
 h' := ![![[68, 87, 65], [37, 18, 53], [25, 93, 111], [76, 38, 122], [63, 58, 54], [125, 24, 100], [0, 1]], ![[32, 39, 62], [126, 47, 62], [114, 19, 87], [21, 85, 116], [47, 31, 34], [54, 87, 126], [68, 87, 65]], ![[0, 1], [3, 62, 12], [106, 15, 56], [46, 4, 16], [85, 38, 39], [32, 16, 28], [32, 39, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 69], []]
 b := ![[], [105, 92, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [2, 103, 27, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37211, 25908, 5207]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![293, 204, 41]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-22, 19, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-22, 19, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![109, 19, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-22, 19, 1], ![103, 48, 37], ![1854, 995, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -19, 131]], ![![-1, 0, 1], ![-30, -5, 37], ![5, 6, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [107, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 130], [0, 1]]
 g := ![![[20, 60], [17, 62], [38], [13], [11], [102], [1]], ![[0, 71], [40, 69], [38], [13], [11], [102], [1]]]
 h' := ![![[87, 130], [15, 45], [22, 113], [114, 13], [123, 119], [11, 81], [24, 87], [0, 1]], ![[0, 1], [0, 86], [28, 18], [66, 118], [127, 12], [115, 50], [126, 44], [87, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [58, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [107, 44, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![622, 2321, 1508]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1250, -201, 1508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-37, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-37, 1, 0]] 
 ![![131, 0, 0], ![94, 1, 0], ![120, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-37, 1, 0], ![0, -36, 2], ![103, 51, -38]]]
  hmulB := by decide  
  f := ![![![3812, -103, 0], ![13493, 0, 0]], ![![2702, -73, 0], ![9564, 0, 0]], ![![3484, -76, -1], ![12332, 66, 0]]]
  g := ![![![1, 0, 0], ![-94, 131, 0], ![-120, 0, 131]], ![![-1, 1, 0], ![24, -36, 2], ![-1, 51, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-22, 19, 1]] ![![131, 0, 0], ![-37, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-4847, 131, 0]], ![![-2882, 2489, 131], ![917, -655, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-37, 1, 0]]], ![![![-22, 19, 1]], ![![7, -5, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3077, -32, 62]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-3077, -32, 62]] 
 ![![137, 0, 0], ![47, 1, 0], ![105, 0, 1]] where
  M :=![![![-3077, -32, 62], ![6386, 53, -126], ![-9682, -20, 179]]]
  hmulB := by decide  
  f := ![![![6967, 4488, 746]], ![![2951, 1901, 316]], ![![8153, 5252, 873]]]
  g := ![![![-59, -32, 62], ![125, 53, -126], ![-201, -20, 179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1771, -20, 36]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-1771, -20, 36]] 
 ![![137, 0, 0], ![104, 1, 0], ![20, 0, 1]] where
  M :=![![![-1771, -20, 36], ![3708, 45, -76], ![-5768, -84, 121]]]
  hmulB := by decide  
  f := ![![![-939, -604, -100]], ![![-788, -507, -84]], ![![-516, -332, -55]]]
  g := ![![![-3, -20, 36], ![4, 45, -76], ![4, -84, 121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 2, -4]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![199, 2, -4]] 
 ![![137, 0, 0], ![123, 1, 0], ![46, 0, 1]] where
  M :=![![![199, 2, -4], ![-412, -3, 8], ![618, -2, -11]]]
  hmulB := by decide  
  f := ![![![-49, -30, -4]], ![![-47, -29, -4]], ![![-36, -22, -3]]]
  g := ![![![1, 2, -4], ![-3, -3, 8], ![10, -2, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-3077, -32, 62]] ![![-1771, -20, 36]]
  ![![4973095, 54892, -100838]] where
 M := ![![![4973095, 54892, -100838]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![4973095, 54892, -100838]] ![![199, 2, -4]]
  ![![137, 0, 0]] where
 M := ![![![904712517, 9983190, -18344026]]]
 hmul := by decide  
 g := ![![![![6603741, 72870, -133898]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB200I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB200I2 : PrimesBelowBoundCertificateInterval O 79 137 200 where
  m := 11
  g := ![2, 2, 2, 3, 3, 1, 2, 2, 1, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB200I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N0, I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![101, 101, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![137, 137, 137]
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
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N0
      exact NI103N0
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
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I89N1, I97N1, I101N0, I101N1, I101N2, I103N0, I109N1, I113N1, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [I103N0, I103N0, I103N0], [], [I109N1], [I113N1], [], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
