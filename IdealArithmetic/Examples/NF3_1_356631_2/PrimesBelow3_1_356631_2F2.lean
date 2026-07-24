
import IdealArithmetic.Examples.NF3_1_356631_2.RI3_1_356631_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![1, -20, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![1, -20, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![1, 63, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![1, -20, 1], ![189, 38, -60], ![-3780, -677, 38]]]
  hmulB := by decide  
  f := ![![![0, 20, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -63, 83]], ![![0, -1, 1], ![3, 46, -60], ![-46, -37, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [64, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 82], [0, 1]]
 g := ![![[43, 48], [78, 37], [70], [23], [48, 3], [1]], ![[0, 35], [12, 46], [70], [23], [9, 80], [1]]]
 h' := ![![[70, 82], [71, 31], [33, 55], [23, 30], [82, 43], [19, 70], [0, 1]], ![[0, 1], [0, 52], [65, 28], [48, 53], [21, 40], [22, 13], [70, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [24, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [64, 13, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![442, 124, 27]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -19, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-23, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-23, 1, 0]] 
 ![![83, 0, 0], ![60, 1, 0], ![45, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-23, 1, 0], ![0, -23, 3], ![189, 37, -23]]]
  hmulB := by decide  
  f := ![![![1680, -73, 0], ![6059, 0, 0]], ![![1220, -53, 0], ![4400, 0, 0]], ![![938, -33, -1], ![3383, 28, 0]]]
  g := ![![![1, 0, 0], ![-60, 83, 0], ![-45, 0, 83]], ![![-1, 1, 0], ![15, -23, 3], ![-12, 37, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![1, -20, 1]] ![![83, 0, 0], ![-23, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1909, 83, 0]], ![![83, -1660, 83], ![166, 498, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-23, 1, 0]]], ![![![1, -20, 1]], ![![2, 6, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![33, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![33, 1, 0]] 
 ![![89, 0, 0], ![33, 1, 0], ![82, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![33, 1, 0], ![0, 33, 3], ![189, 37, 33]]]
  hmulB := by decide  
  f := ![![![694, 21, 0], ![-1869, 0, 0]], ![![264, 8, 0], ![-711, 0, 0]], ![![632, 8, -1], ![-1702, 30, 0]]]
  g := ![![![1, 0, 0], ![-33, 89, 0], ![-82, 0, 89]], ![![0, 1, 0], ![-15, 33, 3], ![-42, 37, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2252, -621, -149]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-2252, -621, -149]] 
 ![![89, 0, 0], ![70, 1, 0], ![28, 0, 1]] where
  M :=![![![-2252, -621, -149], ![-28161, -7765, -1863], ![-117369, -32364, -7765]]]
  hmulB := by decide  
  f := ![![![-1093, -171, 62]], ![![-728, -121, 43]], ![![-707, -81, 33]]]
  g := ![![![510, -621, -149], ![6377, -7765, -1863], ![26579, -32364, -7765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-14, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-14, 1, 0]] 
 ![![89, 0, 0], ![75, 1, 0], ![83, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-14, 1, 0], ![0, -14, 3], ![189, 37, -14]]]
  hmulB := by decide  
  f := ![![![1065, -76, 0], ![6764, 0, 0]], ![![883, -63, 0], ![5608, 0, 0]], ![![991, -66, -1], ![6294, 30, 0]]]
  g := ![![![1, 0, 0], ![-75, 89, 0], ![-83, 0, 89]], ![![-1, 1, 0], ![9, -14, 3], ![-16, 37, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![33, 1, 0]] ![![-2252, -621, -149]]
  ![![89, 0, 0], ![-31, -25, 1]] where
 M := ![![![-200428, -55269, -13261]], ![![-102477, -28258, -6780]]]
 hmul := by decide  
 g := ![![![![-1973, -396, -158], ![801, 0, 0]]], ![![![-1002, -197, -81], ![429, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-31, -25, 1]] ![![89, 0, 0], ![-14, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1246, 89, 0]], ![![-2759, -2225, 89], ![623, 356, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-14, 1, 0]]], ![![![-31, -25, 1]], ![![7, 4, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-34, 1, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-34, 1, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![63, 1, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-34, 1, 1], ![189, 3, 3], ![189, 100, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-63, -1, 97]], ![![-1, 0, 1], ![0, 0, 3], ![0, 1, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [48, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 96], [0, 1]]
 g := ![![[46, 95], [95], [79], [31], [16], [23, 1]], ![[0, 2], [95], [79], [31], [16], [46, 96]]]
 h' := ![![[23, 96], [3, 80], [2, 80], [37, 46], [19, 82], [60, 93], [0, 1]], ![[0, 1], [0, 17], [96, 17], [28, 51], [62, 15], [65, 4], [23, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [49, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [48, 74, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2293, -21, 561]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-388, -6, 561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-3, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-3, 1, 0]] 
 ![![97, 0, 0], ![94, 1, 0], ![94, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-3, 1, 0], ![0, -3, 3], ![189, 37, -3]]]
  hmulB := by decide  
  f := ![![![202, -67, 0], ![6499, 0, 0]], ![![196, -65, 0], ![6306, 0, 0]], ![![196, -63, -2], ![6306, 65, 0]]]
  g := ![![![1, 0, 0], ![-94, 97, 0], ![-94, 0, 97]], ![![-1, 1, 0], ![0, -3, 3], ![-31, 37, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-34, 1, 1]] ![![97, 0, 0], ![-3, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-291, 97, 0]], ![![-3298, 97, 97], ![291, 0, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-3, 1, 0]]], ![![![-34, 1, 1]], ![![3, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![42, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![42, 1, 0]] 
 ![![101, 0, 0], ![42, 1, 0], ![18, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![42, 1, 0], ![0, 42, 3], ![189, 37, 42]]]
  hmulB := by decide  
  f := ![![![1387, 33, 0], ![-3333, 0, 0]], ![![546, 13, 0], ![-1312, 0, 0]], ![![174, -10, -1], ![-418, 34, 0]]]
  g := ![![![1, 0, 0], ![-42, 101, 0], ![-18, 0, 101]], ![![0, 1, 0], ![-18, 42, 3], ![-21, 37, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-21, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-21, 1, 0]] 
 ![![101, 0, 0], ![80, 1, 0], ![55, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-21, 1, 0], ![0, -21, 3], ![189, 37, -21]]]
  hmulB := by decide  
  f := ![![![1786, -85, 0], ![8585, 0, 0]], ![![1408, -67, 0], ![6768, 0, 0]], ![![968, -39, -1], ![4653, 34, 0]]]
  g := ![![![1, 0, 0], ![-80, 101, 0], ![-55, 0, 101]], ![![-1, 1, 0], ![15, -21, 3], ![-16, 37, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![42, 1, 0]] ![![101, 0, 0], ![-21, 1, 0]]
  ![![101, 0, 0], ![9, 7, 1]] where
 M := ![![![10201, 0, 0], ![-2121, 101, 0]], ![![4242, 101, 0], ![-882, 21, 3]]]
 hmul := by decide  
 g := ![![![![92, -7, -1], ![101, 0, 0]], ![![-21, 1, 0], ![0, 0, 0]]], ![![![33, -6, -1], ![101, 0, 0]], ![![-9, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![9, 7, 1]] ![![101, 0, 0], ![-21, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2121, 101, 0]], ![![909, 707, 101], ![0, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-21, 1, 0]]], ![![![9, 7, 1]], ![![0, -1, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [84, 101, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 38, 25], [50, 64, 78], [0, 1]]
 g := ![![[43, 33, 79], [35, 57, 13], [2, 54, 60], [53, 19], [60, 98], [1]], ![[71, 35, 12, 38], [70, 24, 17, 9], [46, 45, 53, 52], [3, 91], [64, 29], [61, 8, 83, 72]], ![[102, 55, 12, 73], [98, 20, 68, 102], [60, 50, 39, 54], [26, 25], [82, 79], [34, 88, 102, 31]]]
 h' := ![![[96, 38, 25], [47, 22, 64], [38, 82, 61], [59, 25, 36], [59, 101, 88], [19, 2, 43], [0, 1]], ![[50, 64, 78], [3, 43, 11], [42, 99, 83], [36, 34, 45], [44, 31, 20], [95, 92, 21], [96, 38, 25]], ![[0, 1], [46, 38, 28], [100, 25, 62], [91, 44, 22], [3, 74, 98], [89, 9, 39], [50, 64, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 89], []]
 b := ![[], [32, 75, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [84, 101, 60, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36771, 5150, -11124]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![357, 50, -108]
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


def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![12, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![12, 1, 0]] 
 ![![107, 0, 0], ![12, 1, 0], ![59, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![12, 1, 0], ![0, 12, 3], ![189, 37, 12]]]
  hmulB := by decide  
  f := ![![![85, 7, 0], ![-749, 0, 0]], ![![-12, -1, 0], ![108, 0, 0]], ![![37, -1, -1], ![-325, 36, 0]]]
  g := ![![![1, 0, 0], ![-12, 107, 0], ![-59, 0, 107]], ![![0, 1, 0], ![-3, 12, 3], ![-9, 37, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-24, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-24, 1, 0]] 
 ![![107, 0, 0], ![83, 1, 0], ![22, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-24, 1, 0], ![0, -24, 3], ![189, 37, -24]]]
  hmulB := by decide  
  f := ![![![1681, -70, 0], ![7490, 0, 0]], ![![1321, -55, 0], ![5886, 0, 0]], ![![386, -8, -1], ![1720, 36, 0]]]
  g := ![![![1, 0, 0], ![-83, 107, 0], ![-22, 0, 107]], ![![-1, 1, 0], ![18, -24, 3], ![-22, 37, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![12, 1, 0]] ![![107, 0, 0], ![12, 1, 0]]
  ![![107, 0, 0], ![-59, 8, 1]] where
 M := ![![![11449, 0, 0], ![1284, 107, 0]], ![![1284, 107, 0], ![144, 24, 3]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![12, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-59, 8, 1]] ![![107, 0, 0], ![-24, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-2568, 107, 0]], ![![-6313, 856, 107], ![1605, -214, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-24, 1, 0]]], ![![![-59, 8, 1]], ![![15, -2, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-6, 44, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-6, 44, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![103, 44, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-6, 44, 1], ![189, 31, 132], ![8316, 1691, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-103, -44, 109]], ![![-1, 0, 1], ![-123, -53, 132], ![47, 3, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [68, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 108], [0, 1]]
 g := ![![[108, 46], [20], [82, 104], [88, 84], [48], [68, 1]], ![[75, 63], [20], [69, 5], [23, 25], [48], [27, 108]]]
 h' := ![![[68, 108], [19, 41], [92, 42], [11, 39], [51, 56], [63, 87], [0, 1]], ![[0, 1], [82, 68], [5, 67], [47, 70], [44, 53], [93, 22], [68, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [46, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [68, 41, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1024, 388, 207]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-205, -80, 207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-23, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-23, 1, 0]] 
 ![![109, 0, 0], ![86, 1, 0], ![78, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-23, 1, 0], ![0, -23, 3], ![189, 37, -23]]]
  hmulB := by decide  
  f := ![![![622, -27, 0], ![2943, 0, 0]], ![![484, -21, 0], ![2290, 0, 0]], ![![424, -3, -2], ![2006, 73, 0]]]
  g := ![![![1, 0, 0], ![-86, 109, 0], ![-78, 0, 109]], ![![-1, 1, 0], ![16, -23, 3], ![-11, 37, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-6, 44, 1]] ![![109, 0, 0], ![-23, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2507, 109, 0]], ![![-654, 4796, 109], ![327, -981, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-23, 1, 0]]], ![![![-6, 44, 1]], ![![3, -9, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-25, 2, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-25, 2, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![88, 2, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-25, 2, 1], ![189, 12, 6], ![378, 137, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -2, 113]], ![![-1, 0, 1], ![-3, 0, 6], ![-6, 1, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [22, 56, 1] where
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
 g := ![![[95, 36], [36], [85], [50], [90, 14], [57, 1]], ![[0, 77], [36], [85], [50], [97, 99], [1, 112]]]
 h' := ![![[57, 112], [3, 107], [2, 107], [8, 57], [54, 84], [102, 63], [0, 1]], ![[0, 1], [0, 6], [112, 6], [93, 56], [96, 29], [77, 50], [57, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [94, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [22, 56, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![400, 81, -16]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 1, -16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-6, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-6, 1, 0]] 
 ![![113, 0, 0], ![107, 1, 0], ![101, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-6, 1, 0], ![0, -6, 3], ![189, 37, -6]]]
  hmulB := by decide  
  f := ![![![127, -21, 0], ![2373, 0, 0]], ![![121, -20, 0], ![2261, 0, 0]], ![![115, -17, -1], ![2149, 38, 0]]]
  g := ![![![1, 0, 0], ![-107, 113, 0], ![-101, 0, 113]], ![![-1, 1, 0], ![3, -6, 3], ![-28, 37, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-25, 2, 1]] ![![113, 0, 0], ![-6, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-678, 113, 0]], ![![-2825, 226, 113], ![339, 0, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-6, 1, 0]]], ![![![-25, 2, 1]], ![![3, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![38, 5, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![38, 5, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![38, 5, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![38, 5, 1], ![189, 75, 15], ![945, 248, 75]]]
  hmulB := by decide  
  f := ![![![-37, -5, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -5, 127]], ![![0, 0, 1], ![-3, 0, 15], ![-15, -1, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [114, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 126], [0, 1]]
 g := ![![[27, 31], [68, 32], [40, 31], [46, 52], [68, 68], [97, 1]], ![[113, 96], [124, 95], [126, 96], [10, 75], [60, 59], [67, 126]]]
 h' := ![![[97, 126], [122, 44], [12, 64], [90, 83], [122, 68], [118, 24], [0, 1]], ![[0, 1], [72, 83], [124, 63], [13, 44], [114, 59], [33, 103], [97, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [60, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [114, 30, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7327, 2077, 1152]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-287, -29, 1152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-15, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-15, 1, 0]] 
 ![![127, 0, 0], ![112, 1, 0], ![52, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-15, 1, 0], ![0, -15, 3], ![189, 37, -15]]]
  hmulB := by decide  
  f := ![![![316, -21, 0], ![2667, 0, 0]], ![![286, -19, 0], ![2414, 0, 0]], ![![136, 1, -2], ![1148, 85, 0]]]
  g := ![![![1, 0, 0], ![-112, 127, 0], ![-52, 0, 127]], ![![-1, 1, 0], ![12, -15, 3], ![-25, 37, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![38, 5, 1]] ![![127, 0, 0], ![-15, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1905, 127, 0]], ![![4826, 635, 127], ![-381, 0, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-15, 1, 0]]], ![![![38, 5, 1]], ![![-3, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-36, 31, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-36, 31, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![95, 31, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-36, 31, 1], ![189, 1, 93], ![5859, 1210, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -31, 131]], ![![-1, 0, 1], ![-66, -22, 93], ![44, 9, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [65, 92, 1] where
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
 g := ![![[78, 129], [88, 75], [48], [80], [94], [80], [1]], ![[0, 2], [0, 56], [48], [80], [94], [80], [1]]]
 h' := ![![[39, 130], [44, 103], [57, 59], [65, 110], [5, 92], [73, 15], [66, 39], [0, 1]], ![[0, 1], [0, 28], [0, 72], [32, 21], [56, 39], [3, 116], [15, 92], [39, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [50, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [65, 92, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1160, 111, -26]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 7, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![38, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![38, 1, 0]] 
 ![![131, 0, 0], ![38, 1, 0], ![130, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![38, 1, 0], ![0, 38, 3], ![189, 37, 38]]]
  hmulB := by decide  
  f := ![![![2205, 58, 0], ![-7598, 0, 0]], ![![646, 17, 0], ![-2226, 0, 0]], ![![2158, 44, -1], ![-7436, 44, 0]]]
  g := ![![![1, 0, 0], ![-38, 131, 0], ![-130, 0, 131]], ![![0, 1, 0], ![-14, 38, 3], ![-47, 37, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-36, 31, 1]] ![![131, 0, 0], ![38, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![4978, 131, 0]], ![![-4716, 4061, 131], ![-1179, 1179, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![38, 1, 0]]], ![![![-36, 31, 1]], ![![-9, 9, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![86, 5, -3]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![86, 5, -3]] 
 ![![137, 0, 0], ![0, 137, 0], ![17, 44, 1]] where
  M :=![![![86, 5, -3], ![-567, -25, 15], ![945, -4, -25]]]
  hmulB := by decide  
  f := ![![![-5, -1, 0]], ![![0, -5, -3]], ![![-2, -2, -1]]]
  g := ![![![1, 1, -3], ![-6, -5, 15], ![10, 8, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [7, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 136], [0, 1]]
 g := ![![[111, 98], [56], [112], [82, 99], [8], [107], [1]], ![[0, 39], [56], [112], [16, 38], [8], [107], [1]]]
 h' := ![![[45, 136], [38, 57], [29, 78], [111, 48], [32, 28], [122, 75], [130, 45], [0, 1]], ![[0, 1], [0, 80], [114, 59], [79, 89], [59, 109], [72, 62], [100, 92], [45, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [63, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [7, 92, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![763, 492, 335]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -104, 335]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![137, 0, 0], ![5, 1, 0], ![83, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 3], ![189, 37, 5]]]
  hmulB := by decide  
  f := ![![![-86, -5, 3]], ![![1, 0, 0]], ![![-59, -3, 2]]]
  g := ![![![0, 1, 0], ![-2, 5, 3], ![-3, 37, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![86, 5, -3]] ![![5, 1, 0]]
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


lemma PB169I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB169I2 : PrimesBelowBoundCertificateInterval O 79 137 169 where
  m := 11
  g := ![2, 3, 2, 3, 1, 3, 2, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB169I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
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
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I89N2, I97N1, I101N0, I101N1, I107N0, I107N1, I109N1, I113N1, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N1], [I101N0, I101N1, I101N1], [], [I107N0, I107N0, I107N1], [I109N1], [I113N1], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
