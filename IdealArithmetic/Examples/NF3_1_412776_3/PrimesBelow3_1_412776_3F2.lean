
import IdealArithmetic.Examples.NF3_1_412776_3.RI3_1_412776_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-23, 12, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-23, 12, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![60, 12, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-23, 12, 1], ![112, -44, 24], ![1344, -196, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -12, 83]], ![![-1, 0, 1], ![-16, -4, 24], ![48, 4, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [39, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 82], [0, 1]]
 g := ![![[42, 65], [18, 49], [29], [63], [51, 69], [1]], ![[61, 18], [17, 34], [29], [63], [75, 14], [1]]]
 h' := ![![[22, 82], [45, 27], [52, 76], [42, 19], [3, 35], [44, 22], [0, 1]], ![[0, 1], [58, 56], [64, 7], [45, 64], [26, 48], [30, 61], [22, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [36, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [39, 61, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![263, -47, -80]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![61, 11, -80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-24, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-24, 1, 0]] 
 ![![83, 0, 0], ![59, 1, 0], ![44, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-24, 1, 0], ![0, -24, 2], ![112, -21, -24]]]
  hmulB := by decide  
  f := ![![![1369, -57, 0], ![4731, 0, 0]], ![![961, -40, 0], ![3321, 0, 0]], ![![724, -18, -1], ![2502, 42, 0]]]
  g := ![![![1, 0, 0], ![-59, 83, 0], ![-44, 0, 83]], ![![-1, 1, 0], ![16, -24, 2], ![29, -21, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-23, 12, 1]] ![![83, 0, 0], ![-24, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1992, 83, 0]], ![![-1909, 996, 83], ![664, -332, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-24, 1, 0]]], ![![![-23, 12, 1]], ![![8, -4, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-23, 44, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-23, 44, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![66, 44, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-23, 44, 1], ![112, -44, 88], ![4928, -868, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -44, 89]], ![![-1, 0, 1], ![-64, -44, 88], ![88, 12, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [84, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 88], [0, 1]]
 g := ![![[36, 71], [42], [53], [88, 55], [28, 4], [1]], ![[0, 18], [42], [53], [20, 34], [36, 85], [1]]]
 h' := ![![[2, 88], [27, 31], [23, 24], [84, 26], [51, 12], [5, 2], [0, 1]], ![[0, 1], [0, 58], [71, 65], [47, 63], [75, 77], [9, 87], [2, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [52, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [84, 87, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1346, 586, 74]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70, -30, 74]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![1, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![1, 1, 0]] 
 ![![89, 0, 0], ![1, 1, 0], ![44, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![1, 1, 0], ![0, 1, 2], ![112, -21, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![89, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![44, -44, 0]]]
  g := ![![![1, 0, 0], ![-1, 89, 0], ![-44, 0, 89]], ![![0, 1, 0], ![-1, 1, 2], ![1, -21, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-23, 44, 1]] ![![89, 0, 0], ![1, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![89, 89, 0]], ![![-2047, 3916, 89], ![89, 0, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![1, 1, 0]]], ![![![-23, 44, 1]], ![![1, 0, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![10, 25, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![10, 25, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![10, 25, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![10, 25, 1], ![112, -11, 50], ![2800, -469, -11]]]
  hmulB := by decide  
  f := ![![![-9, -25, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -25, 97]], ![![0, 0, 1], ![-4, -13, 50], ![30, -2, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [15, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 96], [0, 1]]
 g := ![![[68, 65], [3], [11], [62], [11], [47, 1]], ![[19, 32], [3], [11], [62], [11], [94, 96]]]
 h' := ![![[47, 96], [3, 68], [40, 10], [37, 60], [26, 16], [71, 60], [0, 1]], ![[0, 1], [95, 29], [25, 87], [44, 37], [2, 81], [78, 37], [47, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [29, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [15, 50, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![687, 20, 59]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -15, 59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![47, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![47, 1, 0]] 
 ![![97, 0, 0], ![47, 1, 0], ![11, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![47, 1, 0], ![0, 47, 2], ![112, -21, 47]]]
  hmulB := by decide  
  f := ![![![1411, 30, 0], ![-2910, 0, 0]], ![![611, 13, 0], ![-1260, 0, 0]], ![![129, -21, -1], ![-266, 49, 0]]]
  g := ![![![1, 0, 0], ![-47, 97, 0], ![-11, 0, 97]], ![![0, 1, 0], ![-23, 47, 2], ![6, -21, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![10, 25, 1]] ![![97, 0, 0], ![47, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4559, 97, 0]], ![![970, 2425, 97], ![582, 1164, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![47, 1, 0]]], ![![![10, 25, 1]], ![![6, 12, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![60, -26, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![60, -26, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![60, 75, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![60, -26, 1], ![112, 39, -52], ![-2912, 602, 39]]]
  hmulB := by decide  
  f := ![![![-59, 26, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -75, 101]], ![![0, -1, 1], ![32, 39, -52], ![-52, -23, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [24, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 100], [0, 1]]
 g := ![![[76, 80], [82], [58, 22], [45], [43], [95, 1]], ![[0, 21], [82], [27, 79], [45], [43], [89, 100]]]
 h' := ![![[95, 100], [31, 22], [22, 53], [11, 27], [9, 67], [43, 12], [0, 1]], ![[0, 1], [0, 79], [7, 48], [51, 74], [11, 34], [72, 89], [95, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [91, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [24, 6, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-641, 638, -211]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![119, 163, -211]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-49, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-49, 1, 0]] 
 ![![101, 0, 0], ![52, 1, 0], ![62, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-49, 1, 0], ![0, -49, 2], ![112, -21, -49]]]
  hmulB := by decide  
  f := ![![![2500, -51, 0], ![5151, 0, 0]], ![![1324, -27, 0], ![2728, 0, 0]], ![![1556, -7, -1], ![3206, 51, 0]]]
  g := ![![![1, 0, 0], ![-52, 101, 0], ![-62, 0, 101]], ![![-1, 1, 0], ![24, -49, 2], ![42, -21, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![60, -26, 1]] ![![101, 0, 0], ![-49, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4949, 101, 0]], ![![6060, -2626, 101], ![-2828, 1313, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-49, 1, 0]]], ![![![60, -26, 1]], ![![-28, 13, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![15, -10, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![15, -10, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![15, 93, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![15, -10, 1], ![112, -6, -20], ![-1120, 266, -6]]]
  hmulB := by decide  
  f := ![![![-14, 10, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -93, 103]], ![![0, -1, 1], ![4, 18, -20], ![-10, 8, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [40, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 102], [0, 1]]
 g := ![![[82, 55], [11, 61], [63, 100], [8], [100], [16, 1]], ![[35, 48], [60, 42], [15, 3], [8], [100], [32, 102]]]
 h' := ![![[16, 102], [75, 40], [55, 24], [82, 93], [89, 27], [81, 10], [0, 1]], ![[0, 1], [97, 63], [27, 79], [25, 10], [6, 76], [35, 93], [16, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [86, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [40, 87, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![264, -73, -106]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 95, -106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![20, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![20, 1, 0]] 
 ![![103, 0, 0], ![20, 1, 0], ![6, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![20, 1, 0], ![0, 20, 2], ![112, -21, 20]]]
  hmulB := by decide  
  f := ![![![981, 49, 0], ![-5047, 0, 0]], ![![180, 9, 0], ![-926, 0, 0]], ![![42, -8, -1], ![-216, 52, 0]]]
  g := ![![![1, 0, 0], ![-20, 103, 0], ![-6, 0, 103]], ![![0, 1, 0], ![-4, 20, 2], ![4, -21, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![15, -10, 1]] ![![103, 0, 0], ![20, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![2060, 103, 0]], ![![1545, -1030, 103], ![412, -206, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![20, 1, 0]]], ![![![15, -10, 1]], ![![4, -2, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [100, 43, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 68, 22], [19, 38, 85], [0, 1]]
 g := ![![[7, 23, 56], [12, 15, 27], [1, 14], [103, 93, 52], [103, 23], [1]], ![[34, 69, 1, 104], [32, 4, 15, 54], [71, 4], [96, 9, 15, 74], [9, 19], [64, 102, 77, 55]], ![[4, 36, 91, 41], [43, 72, 1, 9], [59, 62], [0, 56], [104, 36], [91, 58, 76, 52]]]
 h' := ![![[49, 68, 22], [84, 69, 85], [42, 105, 54], [79, 87, 96], [21, 52, 42], [7, 64, 68], [0, 1]], ![[19, 38, 85], [86, 76, 40], [67, 37, 82], [31, 77, 105], [61, 92, 65], [76, 60, 33], [49, 68, 22]], ![[0, 1], [61, 69, 89], [10, 72, 78], [102, 50, 13], [15, 70], [6, 90, 6], [19, 38, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 72], []]
 b := ![[], [5, 0, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [100, 43, 39, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1587559, -172805, -9095]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14837, -1615, -85]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-50, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-50, 1, 0]] 
 ![![109, 0, 0], ![59, 1, 0], ![58, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-50, 1, 0], ![0, -50, 2], ![112, -21, -50]]]
  hmulB := by decide  
  f := ![![![2001, -40, 0], ![4360, 0, 0]], ![![1051, -21, 0], ![2290, 0, 0]], ![![1062, 4, -1], ![2314, 55, 0]]]
  g := ![![![1, 0, 0], ![-59, 109, 0], ![-58, 0, 109]], ![![-1, 1, 0], ![26, -50, 2], ![39, -21, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-38, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-38, 1, 0]] 
 ![![109, 0, 0], ![71, 1, 0], ![41, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-38, 1, 0], ![0, -38, 2], ![112, -21, -38]]]
  hmulB := by decide  
  f := ![![![3193, -84, 0], ![9156, 0, 0]], ![![2091, -55, 0], ![5996, 0, 0]], ![![1185, -12, -1], ![3398, 55, 0]]]
  g := ![![![1, 0, 0], ![-71, 109, 0], ![-41, 0, 109]], ![![-1, 1, 0], ![24, -38, 2], ![29, -21, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-21, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-21, 1, 0]] 
 ![![109, 0, 0], ![88, 1, 0], ![52, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-21, 1, 0], ![0, -21, 2], ![112, -21, -21]]]
  hmulB := by decide  
  f := ![![![715, -34, 0], ![3706, 0, 0]], ![![568, -27, 0], ![2944, 0, 0]], ![![370, -7, -1], ![1918, 55, 0]]]
  g := ![![![1, 0, 0], ![-88, 109, 0], ![-52, 0, 109]], ![![-1, 1, 0], ![16, -21, 2], ![28, -21, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-50, 1, 0]] ![![109, 0, 0], ![-38, 1, 0]]
  ![![109, 0, 0], ![-31, -44, 1]] where
 M := ![![![11881, 0, 0], ![-4142, 109, 0]], ![![-5450, 109, 0], ![1900, -88, 2]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![-7, 45, -1], ![109, 0, 0]]], ![![![-19, 45, -1], ![109, 0, 0]], ![![18, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-31, -44, 1]] ![![109, 0, 0], ![-21, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2289, 109, 0]], ![![-3379, -4796, 109], ![763, 872, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-21, 1, 0]]], ![![![-31, -44, 1]], ![![7, 8, -1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [39, 51, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 78, 11], [28, 34, 102], [0, 1]]
 g := ![![[20, 69, 81], [27, 62], [5, 85], [24, 85], [70, 84, 52], [1]], ![[72, 108, 42, 64], [58, 52], [100, 49], [53, 11], [16, 10, 24, 91], [48, 107, 106, 88]], ![[96, 72, 78, 15], [111, 64], [44, 14], [28, 72], [19, 93, 104, 62], [87, 23, 96, 25]]]
 h' := ![![[11, 78, 11], [25, 21, 104], [93, 108, 47], [66, 33, 56], [95, 99, 57], [74, 62, 39], [0, 1]], ![[28, 34, 102], [112, 34, 38], [112, 89, 74], [82, 24, 7], [62, 102, 89], [24, 110, 87], [11, 78, 11]], ![[0, 1], [77, 58, 84], [15, 29, 105], [6, 56, 50], [9, 25, 80], [27, 54, 100], [28, 34, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 50], []]
 b := ![[], [18, 71, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [39, 51, 74, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69043, 14803, 1582]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-611, 131, 14]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4467, 305, 156]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![4467, 305, 156]] 
 ![![127, 0, 0], ![0, 127, 0], ![119, 120, 1]] where
  M :=![![![4467, 305, 156], ![17472, 1191, 610], ![34160, 2331, 1191]]]
  hmulB := by decide  
  f := ![![![-27, 3, 2]], ![![224, -69, 6]], ![![189, -62, 7]]]
  g := ![![![-111, -145, 156], ![-434, -567, 610], ![-847, -1107, 1191]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [16, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [115, 126], [0, 1]]
 g := ![![[96, 8], [103, 98], [23, 32], [81, 1], [118, 1], [115, 1]], ![[0, 119], [70, 29], [20, 95], [69, 126], [106, 126], [103, 126]]]
 h' := ![![[115, 126], [3, 32], [13, 15], [101, 63], [17, 126], [65, 1], [0, 1]], ![[0, 1], [0, 95], [87, 112], [107, 64], [29, 1], [53, 126], [115, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [57, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [16, 12, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![464, 152, -58]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![58, 56, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -3, -2]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![27, -3, -2]] 
 ![![127, 0, 0], ![14, 1, 0], ![29, 0, 1]] where
  M :=![![![27, -3, -2], ![-224, 69, -6], ![-336, -49, 69]]]
  hmulB := by decide  
  f := ![![![-4467, -305, -156]], ![![-630, -43, -22]], ![![-1289, -88, -45]]]
  g := ![![![1, -3, -2], ![-8, 69, -6], ![-13, -49, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![4467, 305, 156]] ![![27, -3, -2]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![18, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![18, 1, 0]] 
 ![![131, 0, 0], ![18, 1, 0], ![100, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![18, 1, 0], ![0, 18, 2], ![112, -21, 18]]]
  hmulB := by decide  
  f := ![![![811, 45, 0], ![-5895, 0, 0]], ![![90, 5, 0], ![-654, 0, 0]], ![![596, 24, -1], ![-4332, 66, 0]]]
  g := ![![![1, 0, 0], ![-18, 131, 0], ![-100, 0, 131]], ![![0, 1, 0], ![-4, 18, 2], ![-10, -21, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![25, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![25, 1, 0]] 
 ![![131, 0, 0], ![25, 1, 0], ![15, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![25, 1, 0], ![0, 25, 2], ![112, -21, 25]]]
  hmulB := by decide  
  f := ![![![476, 19, 0], ![-2489, 0, 0]], ![![50, 2, 0], ![-261, 0, 0]], ![![40, -11, -1], ![-209, 66, 0]]]
  g := ![![![1, 0, 0], ![-25, 131, 0], ![-15, 0, 131]], ![![0, 1, 0], ![-5, 25, 2], ![2, -21, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-43, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-43, 1, 0]] 
 ![![131, 0, 0], ![88, 1, 0], ![58, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-43, 1, 0], ![0, -43, 2], ![112, -21, -43]]]
  hmulB := by decide  
  f := ![![![3613, -84, 0], ![11004, 0, 0]], ![![2452, -57, 0], ![7468, 0, 0]], ![![1620, -16, -1], ![4934, 66, 0]]]
  g := ![![![1, 0, 0], ![-88, 131, 0], ![-58, 0, 131]], ![![-1, 1, 0], ![28, -43, 2], ![34, -21, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![18, 1, 0]] ![![131, 0, 0], ![25, 1, 0]]
  ![![131, 0, 0], ![-37, -44, 1]] where
 M := ![![![17161, 0, 0], ![3275, 131, 0]], ![![2358, 131, 0], ![450, 43, 2]]]
 hmul := by decide  
 g := ![![![![131, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![18, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-37, -44, 1]] ![![131, 0, 0], ![-43, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-5633, 131, 0]], ![![-4847, -5764, 131], ![1703, 1834, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-43, 1, 0]]], ![![![-37, -44, 1]], ![![13, 14, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![71, -5, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![71, -5, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![71, 132, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![71, -5, 1], ![112, 50, -10], ![-560, 161, 50]]]
  hmulB := by decide  
  f := ![![![-70, 5, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -132, 137]], ![![0, -1, 1], ![6, 10, -10], ![-30, -47, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [28, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 136], [0, 1]]
 g := ![![[81, 93], [119], [32], [84, 87], [87], [22], [1]], ![[0, 44], [119], [32], [48, 50], [87], [22], [1]]]
 h' := ![![[61, 136], [111, 97], [44, 121], [114, 13], [32, 19], [31, 118], [109, 61], [0, 1]], ![[0, 1], [0, 40], [27, 16], [85, 124], [95, 118], [105, 19], [131, 76], [61, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [80, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [28, 76, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![961, -4, 83]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -80, 83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![10, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![10, 1, 0]] 
 ![![137, 0, 0], ![10, 1, 0], ![87, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![10, 1, 0], ![0, 10, 2], ![112, -21, 10]]]
  hmulB := by decide  
  f := ![![![861, 86, 0], ![-11782, 0, 0]], ![![50, 5, 0], ![-684, 0, 0]], ![![531, 48, -1], ![-7266, 69, 0]]]
  g := ![![![1, 0, 0], ![-10, 137, 0], ![-87, 0, 137]], ![![0, 1, 0], ![-2, 10, 2], ![-4, -21, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![71, -5, 1]] ![![137, 0, 0], ![10, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![1370, 137, 0]], ![![9727, -685, 137], ![822, 0, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![10, 1, 0]]], ![![![71, -5, 1]], ![![6, 0, 0]]]]
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


lemma PB182I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB182I2 : PrimesBelowBoundCertificateInterval O 79 137 182 where
  m := 11
  g := ![2, 2, 2, 2, 2, 1, 3, 1, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB182I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
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
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![109, 109, 109]
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
      exact NI101N1
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
      exact NI109N2
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
  β := ![I83N1, I89N1, I97N1, I101N1, I103N1, I109N0, I109N1, I109N2, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [], [I109N0, I109N1, I109N2], [], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
