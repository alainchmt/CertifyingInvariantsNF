
import IdealArithmetic.Examples.NF3_1_959928_1.RI3_1_959928_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-4, -10, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-4, -10, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![79, 73, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-4, -10, 1], ![246, 34, -20], ![-2583, -357, 44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -73, 83]], ![![-1, -1, 1], ![22, 18, -20], ![-73, -43, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [16, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 82], [0, 1]]
 g := ![![[2, 26], [42, 48], [16], [37], [45, 28], [1]], ![[0, 57], [0, 35], [16], [37], [62, 55], [1]]]
 h' := ![![[51, 82], [75, 62], [4, 52], [54, 79], [27, 28], [67, 51], [0, 1]], ![[0, 1], [0, 21], [0, 31], [16, 4], [44, 55], [12, 32], [51, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [47, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [16, 32, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1861, 1623, 344]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-305, -283, 344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![20, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![20, 1, 0]] 
 ![![83, 0, 0], ![20, 1, 0], ![39, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![20, 1, 0], ![0, 21, 2], ![246, 48, 20]]]
  hmulB := by decide  
  f := ![![![1041, 52, 0], ![-4316, 0, 0]], ![![220, 11, 0], ![-912, 0, 0]], ![![493, 14, -1], ![-2044, 42, 0]]]
  g := ![![![1, 0, 0], ![-20, 83, 0], ![-39, 0, 83]], ![![0, 1, 0], ![-6, 21, 2], ![-18, 48, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-4, -10, 1]] ![![83, 0, 0], ![20, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1660, 83, 0]], ![![-332, -830, 83], ![166, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![20, 1, 0]]], ![![![-4, -10, 1]], ![![2, -2, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-46, 7, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-46, 7, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![43, 7, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-46, 7, 1], ![246, 9, 14], ![1599, 459, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -7, 89]], ![![-1, 0, 1], ![-4, -1, 14], ![17, 5, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [38, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 88], [0, 1]]
 g := ![![[35, 21], [2], [5], [47, 44], [12, 25], [1]], ![[51, 68], [2], [5], [0, 45], [48, 64], [1]]]
 h' := ![![[5, 88], [55, 56], [24, 64], [83, 19], [78, 20], [51, 5], [0, 1]], ![[0, 1], [68, 33], [77, 25], [0, 70], [0, 69], [76, 84], [5, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [35, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [38, 84, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45, 2435, 1098]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-531, -59, 1098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-14, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-14, 1, 0]] 
 ![![89, 0, 0], ![75, 1, 0], ![87, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-14, 1, 0], ![0, -13, 2], ![246, 48, -14]]]
  hmulB := by decide  
  f := ![![![1037, -74, 0], ![6586, 0, 0]], ![![883, -63, 0], ![5608, 0, 0]], ![![1003, -65, -1], ![6370, 45, 0]]]
  g := ![![![1, 0, 0], ![-75, 89, 0], ![-87, 0, 89]], ![![-1, 1, 0], ![9, -13, 2], ![-24, 48, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-46, 7, 1]] ![![89, 0, 0], ![-14, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1246, 89, 0]], ![![-4094, 623, 89], ![890, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-14, 1, 0]]], ![![![-46, 7, 1]], ![![10, -1, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [40, 37, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 9, 85], [77, 87, 12], [0, 1]]
 g := ![![[94, 33, 88], [36, 81], [4, 27], [24, 95], [96, 9], [1]], ![[18, 70, 11, 6], [36, 73], [43, 72], [44, 4], [57, 94], [6, 41, 62, 18]], ![[93, 16, 25, 2], [4, 48], [50, 95], [34, 70], [85, 65], [86, 61, 88, 79]]]
 h' := ![![[23, 9, 85], [65, 26, 31], [70, 37, 9], [91, 32, 67], [88, 18, 17], [57, 60, 3], [0, 1]], ![[77, 87, 12], [64, 73, 57], [90, 86, 48], [8, 12, 13], [64, 8, 2], [93, 5, 26], [23, 9, 85]], ![[0, 1], [69, 95, 9], [61, 71, 40], [86, 53, 17], [31, 71, 78], [6, 32, 68], [77, 87, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 35], []]
 b := ![[], [86, 27, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [40, 37, 94, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![108252, -23862, -7178]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1116, -246, -74]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![12, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![12, 1, 0]] 
 ![![101, 0, 0], ![12, 1, 0], ![23, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![12, 1, 0], ![0, 13, 2], ![246, 48, 12]]]
  hmulB := by decide  
  f := ![![![565, 47, 0], ![-4747, 0, 0]], ![![60, 5, 0], ![-504, 0, 0]], ![![127, 4, -1], ![-1067, 51, 0]]]
  g := ![![![1, 0, 0], ![-12, 101, 0], ![-23, 0, 101]], ![![0, 1, 0], ![-2, 13, 2], ![-6, 48, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![25, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![25, 1, 0]] 
 ![![101, 0, 0], ![25, 1, 0], ![79, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![25, 1, 0], ![0, 26, 2], ![246, 48, 25]]]
  hmulB := by decide  
  f := ![![![1976, 79, 0], ![-7979, 0, 0]], ![![450, 18, 0], ![-1817, 0, 0]], ![![1554, 49, -1], ![-6275, 51, 0]]]
  g := ![![![1, 0, 0], ![-25, 101, 0], ![-79, 0, 101]], ![![0, 1, 0], ![-8, 26, 2], ![-29, 48, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-38, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-38, 1, 0]] 
 ![![101, 0, 0], ![63, 1, 0], ![4, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-38, 1, 0], ![0, -37, 2], ![246, 48, -38]]]
  hmulB := by decide  
  f := ![![![1901, -50, 0], ![5050, 0, 0]], ![![1255, -33, 0], ![3334, 0, 0]], ![![140, 15, -1], ![372, 51, 0]]]
  g := ![![![1, 0, 0], ![-63, 101, 0], ![-4, 0, 101]], ![![-1, 1, 0], ![23, -37, 2], ![-26, 48, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![12, 1, 0]] ![![101, 0, 0], ![25, 1, 0]]
  ![![101, 0, 0], ![-52, 19, 1]] where
 M := ![![![10201, 0, 0], ![2525, 101, 0]], ![![1212, 101, 0], ![300, 38, 2]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-52, 19, 1]] ![![101, 0, 0], ![-38, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3838, 101, 0]], ![![-5252, 1919, 101], ![2222, -707, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-38, 1, 0]]], ![![![-52, 19, 1]], ![![22, -7, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [60, 3, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 62, 17], [44, 40, 86], [0, 1]]
 g := ![![[7, 69, 76], [0, 77, 28], [70, 44, 76], [100, 19], [90, 60], [1]], ![[48, 60, 70, 36], [46, 6, 66, 50], [81, 7, 35, 4], [63, 19], [25, 28], [1, 67, 5, 72]], ![[90, 69, 50, 77], [8, 82, 93, 42], [73, 68, 34, 21], [17, 76], [52, 83], [22, 47, 55, 31]]]
 h' := ![![[95, 62, 17], [0, 29, 73], [23, 70, 50], [6, 65, 30], [54, 95, 88], [43, 100, 36], [0, 1]], ![[44, 40, 86], [43, 71, 14], [69, 77, 100], [35, 92, 39], [101, 31, 88], [46, 53, 50], [95, 62, 17]], ![[0, 1], [102, 3, 16], [47, 59, 56], [23, 49, 34], [42, 80, 30], [22, 53, 17], [44, 40, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 59], []]
 b := ![[], [82, 94, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [60, 3, 67, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4690105, -1557566, -231441]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45535, -15122, -2247]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [96, 92, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 85, 55], [57, 21, 52], [0, 1]]
 g := ![![[56, 34, 105], [81, 59, 33], [39, 3], [15, 70, 48], [12, 105], [1]], ![[27, 71, 48, 74], [92, 89, 34, 2], [64, 35], [98, 56, 96, 67], [4, 56], [61, 51, 23, 97]], ![[15, 77, 8, 53], [19, 49, 64, 92], [1, 83], [5, 13, 57, 81], [85, 81], [28, 89, 104, 10]]]
 h' := ![![[81, 85, 55], [35, 102, 76], [48, 43, 51], [58, 55, 89], [39, 60, 72], [11, 15, 31], [0, 1]], ![[57, 21, 52], [106, 13, 37], [66, 4, 12], [2, 66, 79], [45, 103, 104], [1, 88, 85], [81, 85, 55]], ![[0, 1], [11, 99, 101], [9, 60, 44], [31, 93, 46], [57, 51, 38], [70, 4, 98], [57, 21, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 63], []]
 b := ![[], [88, 38, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [96, 92, 76, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1158810, -326564, -42479]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10830, -3052, -397]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![27, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![27, 1, 0]] 
 ![![109, 0, 0], ![27, 1, 0], ![58, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![27, 1, 0], ![0, 28, 2], ![246, 48, 27]]]
  hmulB := by decide  
  f := ![![![1864, 69, 0], ![-7521, 0, 0]], ![![432, 16, 0], ![-1743, 0, 0]], ![![976, 22, -1], ![-3938, 55, 0]]]
  g := ![![![1, 0, 0], ![-27, 109, 0], ![-58, 0, 109]], ![![0, 1, 0], ![-8, 28, 2], ![-24, 48, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-23, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-23, 1, 0]] 
 ![![109, 0, 0], ![86, 1, 0], ![74, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-23, 1, 0], ![0, -22, 2], ![246, 48, -23]]]
  hmulB := by decide  
  f := ![![![484, -21, 0], ![2289, 0, 0]], ![![392, -17, 0], ![1854, 0, 0]], ![![348, -4, -1], ![1646, 55, 0]]]
  g := ![![![1, 0, 0], ![-86, 109, 0], ![-74, 0, 109]], ![![-1, 1, 0], ![16, -22, 2], ![-20, 48, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2548540664, 769508345, 126269917]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![2548540664, 769508345, 126269917]] 
 ![![109, 0, 0], ![104, 1, 0], ![99, 0, 1]] where
  M :=![![![2548540664, 769508345, 126269917], ![31062399582, 9379005025, 1539016690], ![173767853079, 52467600351, 8609496680]]]
  hmulB := by decide  
  f := ![![![1958810, 146267, -54875]], ![![1745110, 134705, -49674]], ![![2171133, 135336, -56035]]]
  g := ![![![-825514211, 769508345, 126269917], ![-10061621792, 9379005025, 1539016690], ![-56286263805, 52467600351, 8609496680]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![27, 1, 0]] ![![109, 0, 0], ![-23, 1, 0]]
  ![![-1958810, -146267, 54875]] where
 M := ![![![11881, 0, 0], ![-2507, 109, 0]], ![![2943, 109, 0], ![-621, 5, 2]]]
 hmul := by decide  
 g := ![![![![-277790932376, -83876409605, -13763420953]], ![![27554035690, 8319686910, 1365191401]]], ![![![-99872997510, -30155730340, -4948304449]], ![![9906385764, 2991141802, 490821483]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-1958810, -146267, 54875]] ![![2548540664, 769508345, 126269917]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-42, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-42, 1, 0]] 
 ![![113, 0, 0], ![71, 1, 0], ![43, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-42, 1, 0], ![0, -41, 2], ![246, 48, -42]]]
  hmulB := by decide  
  f := ![![![3403, -81, 0], ![9153, 0, 0]], ![![2185, -52, 0], ![5877, 0, 0]], ![![1289, -10, -1], ![3467, 57, 0]]]
  g := ![![![1, 0, 0], ![-71, 113, 0], ![-43, 0, 113]], ![![-1, 1, 0], ![25, -41, 2], ![-12, 48, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-39, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-39, 1, 0]] 
 ![![113, 0, 0], ![74, 1, 0], ![50, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-39, 1, 0], ![0, -38, 2], ![246, 48, -39]]]
  hmulB := by decide  
  f := ![![![1210, -31, 0], ![3503, 0, 0]], ![![820, -21, 0], ![2374, 0, 0]], ![![592, 4, -1], ![1714, 57, 0]]]
  g := ![![![1, 0, 0], ![-74, 113, 0], ![-50, 0, 113]], ![![-1, 1, 0], ![24, -38, 2], ![-12, 48, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-33, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-33, 1, 0]] 
 ![![113, 0, 0], ![80, 1, 0], ![37, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-33, 1, 0], ![0, -32, 2], ![246, 48, -33]]]
  hmulB := by decide  
  f := ![![![1519, -46, 0], ![5198, 0, 0]], ![![1090, -33, 0], ![3730, 0, 0]], ![![533, 0, -1], ![1824, 57, 0]]]
  g := ![![![1, 0, 0], ![-80, 113, 0], ![-37, 0, 113]], ![![-1, 1, 0], ![22, -32, 2], ![-21, 48, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-42, 1, 0]] ![![113, 0, 0], ![-39, 1, 0]]
  ![![113, 0, 0], ![-85, -40, 1]] where
 M := ![![![12769, 0, 0], ![-4407, 113, 0]], ![![-4746, 113, 0], ![1638, -80, 2]]]
 hmul := by decide  
 g := ![![![![113, 0, 0], ![0, 0, 0]], ![![46, 41, -1], ![113, 0, 0]]], ![![![43, 41, -1], ![113, 0, 0]], ![![16, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-85, -40, 1]] ![![113, 0, 0], ![-33, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-3729, 113, 0]], ![![-9605, -4520, 113], ![3051, 1243, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-33, 1, 0]]], ![![![-85, -40, 1]], ![![27, 11, -1]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-45, -62, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-45, -62, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![82, 65, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-45, -62, 1], ![246, -59, -124], ![-15375, -2853, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -65, 127]], ![![-1, -1, 1], ![82, 63, -124], ![-123, -24, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [87, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 126], [0, 1]]
 g := ![![[32, 73], [40, 18], [80, 9], [90, 25], [25, 42], [10, 1]], ![[0, 54], [93, 109], [43, 118], [86, 102], [64, 85], [20, 126]]]
 h' := ![![[10, 126], [76, 94], [25, 48], [44, 124], [111, 5], [19, 13], [0, 1]], ![[0, 1], [0, 33], [124, 79], [14, 3], [34, 122], [22, 114], [10, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [44, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [87, 117, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![152602, 97343, 24467]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14596, -11756, 24467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-3, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-3, 1, 0]] 
 ![![127, 0, 0], ![124, 1, 0], ![124, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-3, 1, 0], ![0, -2, 2], ![246, 48, -3]]]
  hmulB := by decide  
  f := ![![![262, -87, 0], ![11049, 0, 0]], ![![256, -85, 0], ![10796, 0, 0]], ![![256, -84, -1], ![10796, 64, 0]]]
  g := ![![![1, 0, 0], ![-124, 127, 0], ![-124, 0, 127]], ![![-1, 1, 0], ![0, -2, 2], ![-42, 48, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-45, -62, 1]] ![![127, 0, 0], ![-3, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-381, 127, 0]], ![![-5715, -7874, 127], ![381, 127, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-3, 1, 0]]], ![![![-45, -62, 1]], ![![3, 1, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-62, -21, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-62, -21, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![69, 110, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-62, -21, 1], ![246, -35, -42], ![-5289, -885, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -110, 131]], ![![-1, -1, 1], ![24, 35, -42], ![-33, 5, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [26, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 130], [0, 1]]
 g := ![![[53, 3], [60, 20], [112], [1], [41], [39], [1]], ![[111, 128], [10, 111], [112], [1], [41], [39], [1]]]
 h' := ![![[63, 130], [12, 38], [70, 85], [10, 51], [125, 1], [55, 98], [105, 63], [0, 1]], ![[0, 1], [48, 93], [54, 46], [79, 80], [57, 130], [72, 33], [13, 68], [63, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [126, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [26, 68, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![820, 451, 122]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-58, -99, 122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![42, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![42, 1, 0]] 
 ![![131, 0, 0], ![42, 1, 0], ![14, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![42, 1, 0], ![0, 43, 2], ![246, 48, 42]]]
  hmulB := by decide  
  f := ![![![2269, 54, 0], ![-7074, 0, 0]], ![![714, 17, 0], ![-2226, 0, 0]], ![![238, -16, -1], ![-742, 66, 0]]]
  g := ![![![1, 0, 0], ![-42, 131, 0], ![-14, 0, 131]], ![![0, 1, 0], ![-14, 43, 2], ![-18, 48, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-62, -21, 1]] ![![131, 0, 0], ![42, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![5502, 131, 0]], ![![-8122, -2751, 131], ![-2358, -917, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![42, 1, 0]]], ![![![-62, -21, 1]], ![![-18, -7, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-32, 9, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-32, 9, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![105, 9, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-32, 9, 1], ![246, 25, 18], ![2091, 555, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -9, 137]], ![![-1, 0, 1], ![-12, -1, 18], ![3, 3, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [92, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 136], [0, 1]]
 g := ![![[93, 105], [105], [81], [44, 100], [112], [8], [1]], ![[22, 32], [105], [81], [9, 37], [112], [8], [1]]]
 h' := ![![[75, 136], [128, 67], [91, 67], [62, 9], [93, 10], [56, 89], [45, 75], [0, 1]], ![[0, 1], [84, 70], [47, 70], [52, 128], [21, 127], [18, 48], [53, 62], [75, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [74, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [92, 62, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4397, 4710, 1528]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1139, -66, 1528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-18, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-18, 1, 0]] 
 ![![137, 0, 0], ![119, 1, 0], ![121, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-18, 1, 0], ![0, -17, 2], ![246, 48, -18]]]
  hmulB := by decide  
  f := ![![![1963, -109, 0], ![14933, 0, 0]], ![![1693, -94, 0], ![12879, 0, 0]], ![![1739, -88, -1], ![13229, 69, 0]]]
  g := ![![![1, 0, 0], ![-119, 137, 0], ![-121, 0, 137]], ![![-1, 1, 0], ![13, -17, 2], ![-24, 48, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-32, 9, 1]] ![![137, 0, 0], ![-18, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-2466, 137, 0]], ![![-4384, 1233, 137], ![822, -137, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-18, 1, 0]]], ![![![-32, 9, 1]], ![![6, -1, 0]]]]
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


lemma PB278I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB278I2 : PrimesBelowBoundCertificateInterval O 79 137 278 where
  m := 11
  g := ![2, 2, 1, 3, 1, 1, 3, 3, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB278I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
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
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![113, 113, 113]
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
      exact NI113N1
      exact NI113N2
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
  β := ![I83N1, I89N1, I101N0, I101N1, I101N2, I109N0, I109N1, I109N2, I113N0, I113N1, I113N2, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N0, I101N1, I101N2], [], [], [I109N0, I109N1, I109N2], [I113N0, I113N1, I113N2], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
