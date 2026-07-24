
import IdealArithmetic.Examples.NF3_1_557179_1.RI3_1_557179_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2071, -188, 156]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![2071, -188, 156]] 
 ![![83, 0, 0], ![21, 1, 0], ![4, 0, 1]] where
  M :=![![![2071, -188, 156], ![-22464, 2039, -1692], ![29568, -2684, 2227]]]
  hmulB := by decide  
  f := ![![![-475, -28, 12]], ![![-141, -13, 0]], ![![28, -4, -5]]]
  g := ![![![65, -188, 156], ![-705, 2039, -1692], ![928, -2684, 2227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-11, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-11, 1, 0]] 
 ![![83, 0, 0], ![72, 1, 0], ![80, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-11, 1, 0], ![0, -10, 9], ![-144, 1, -11]]]
  hmulB := by decide  
  f := ![![![771, -70, 0], ![5810, 0, 0]], ![![672, -61, 0], ![5064, 0, 0]], ![![754, -64, -4], ![5682, 37, 0]]]
  g := ![![![1, 0, 0], ![-72, 83, 0], ![-80, 0, 83]], ![![-1, 1, 0], ![0, -10, 9], ![8, 1, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![2071, -188, 156]] ![![83, 0, 0], ![-11, 1, 0]]
  ![![83, 0, 0], ![2, -8, 1]] where
 M := ![![![171893, -15604, 12948], ![-45245, 4107, -3408]]]
 hmul := by decide  
 g := ![![![![2069, -180, 155], ![83, 0, 0]], ![![-545, 49, -41], ![-5, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![2, -8, 1]] ![![83, 0, 0], ![-11, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-913, 83, 0]], ![![166, -664, 83], ![-166, 83, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-11, 1, 0]]], ![![![2, -8, 1]], ![![-2, 1, -1]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-35, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-35, 1, 0]] 
 ![![89, 0, 0], ![54, 1, 0], ![26, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-35, 1, 0], ![0, -34, 9], ![-144, 1, -35]]]
  hmulB := by decide  
  f := ![![![1891, -54, 0], ![4806, 0, 0]], ![![1156, -33, 0], ![2938, 0, 0]], ![![554, -12, -1], ![1408, 10, 0]]]
  g := ![![![1, 0, 0], ![-54, 89, 0], ![-26, 0, 89]], ![![-1, 1, 0], ![18, -34, 9], ![8, 1, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-32, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-32, 1, 0]] 
 ![![89, 0, 0], ![57, 1, 0], ![48, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-32, 1, 0], ![0, -31, 9], ![-144, 1, -32]]]
  hmulB := by decide  
  f := ![![![2177, -68, 0], ![6052, 0, 0]], ![![1441, -45, 0], ![4006, 0, 0]], ![![1200, -34, -1], ![3336, 10, 0]]]
  g := ![![![1, 0, 0], ![-57, 89, 0], ![-48, 0, 89]], ![![-1, 1, 0], ![15, -31, 9], ![15, 1, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-23, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-23, 1, 0]] 
 ![![89, 0, 0], ![66, 1, 0], ![13, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-23, 1, 0], ![0, -22, 9], ![-144, 1, -23]]]
  hmulB := by decide  
  f := ![![![1312, -57, 0], ![5073, 0, 0]], ![![990, -43, 0], ![3828, 0, 0]], ![![218, -7, -1], ![843, 10, 0]]]
  g := ![![![1, 0, 0], ![-66, 89, 0], ![-13, 0, 89]], ![![-1, 1, 0], ![15, -22, 9], ![1, 1, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-35, 1, 0]] ![![89, 0, 0], ![-32, 1, 0]]
  ![![89, 0, 0], ![-14, -37, 1]] where
 M := ![![![7921, 0, 0], ![-2848, 89, 0]], ![![-3115, 89, 0], ![1120, -66, 9]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![-18, 38, -1], ![89, 0, 0]]], ![![![-21, 38, -1], ![89, 0, 0]], ![![14, 3, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-14, -37, 1]] ![![89, 0, 0], ![-23, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2047, 89, 0]], ![![-1246, -3293, 89], ![178, 801, -356]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-23, 1, 0]]], ![![![-14, -37, 1]], ![![2, 9, -4]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [73, 69, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 60, 11], [10, 36, 86], [0, 1]]
 g := ![![[87, 31, 18], [30, 89], [91, 53], [18, 12], [22, 35], [1]], ![[94, 74, 73, 43], [50, 16], [93, 49], [17, 25], [33, 33], [30, 74, 54, 70]], ![[5, 9, 50, 53], [92, 86], [73, 8], [11, 31], [35, 6], [73, 7, 68, 27]]]
 h' := ![![[51, 60, 11], [9, 0, 55], [68, 58, 63], [55, 24, 76], [37, 84, 20], [24, 28, 61], [0, 1]], ![[10, 36, 86], [24, 28, 40], [45, 43, 93], [74, 96, 90], [32, 15, 92], [93, 55, 79], [51, 60, 11]], ![[0, 1], [52, 69, 2], [50, 93, 38], [74, 74, 28], [2, 95, 82], [36, 14, 54], [10, 36, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 29], []]
 b := ![[], [47, 61, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [73, 69, 36, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11324071, 20564, 174794]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-116743, 212, 1802]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![17, 5, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![17, 5, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![17, 5, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![17, 5, 1], ![-144, 23, 45], ![-704, -11, 18]]]
  hmulB := by decide  
  f := ![![![-16, -5, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -5, 101]], ![![0, 0, 1], ![-9, -2, 45], ![-10, -1, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [60, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 100], [0, 1]]
 g := ![![[34, 80], [47], [90, 33], [43], [56], [81, 1]], ![[50, 21], [47], [36, 68], [43], [56], [61, 100]]]
 h' := ![![[81, 100], [96, 79], [54, 59], [100, 29], [16, 12], [89, 37], [0, 1]], ![[0, 1], [31, 22], [86, 42], [25, 72], [79, 89], [56, 64], [81, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [63, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [60, 20, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1191, -1895, 328]
  a := ![-1, 1, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-67, -35, 328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-45, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-45, 1, 0]] 
 ![![101, 0, 0], ![56, 1, 0], ![83, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-45, 1, 0], ![0, -44, 9], ![-144, 1, -45]]]
  hmulB := by decide  
  f := ![![![2296, -51, 0], ![5151, 0, 0]], ![![1306, -29, 0], ![2930, 0, 0]], ![![1918, -23, -4], ![4303, 45, 0]]]
  g := ![![![1, 0, 0], ![-56, 101, 0], ![-83, 0, 101]], ![![-1, 1, 0], ![17, -44, 9], ![35, 1, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![17, 5, 1]] ![![101, 0, 0], ![-45, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4545, 101, 0]], ![![1717, 505, 101], ![-909, -202, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-45, 1, 0]]], ![![![17, 5, 1]], ![![-9, -2, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![14, 43, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![14, 43, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![14, 43, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![14, 43, 1], ![-144, 58, 387], ![-6176, 27, 15]]]
  hmulB := by decide  
  f := ![![![-13, -43, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -43, 103]], ![![0, 0, 1], ![-54, -161, 387], ![-62, -6, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [45, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 102], [0, 1]]
 g := ![![[14, 64], [42, 32], [86, 26], [91], [16], [91, 1]], ![[70, 39], [70, 71], [83, 77], [91], [16], [79, 102]]]
 h' := ![![[91, 102], [67, 95], [44, 54], [89, 52], [8, 20], [25, 99], [0, 1]], ![[0, 1], [60, 8], [14, 49], [83, 51], [77, 83], [73, 4], [91, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [69, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [45, 12, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3389, -16, 117]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, -49, 117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![25, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![25, 1, 0]] 
 ![![103, 0, 0], ![25, 1, 0], ![88, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![25, 1, 0], ![0, 26, 9], ![-144, 1, 25]]]
  hmulB := by decide  
  f := ![![![776, 31, 0], ![-3193, 0, 0]], ![![150, 6, 0], ![-617, 0, 0]], ![![646, 20, -2], ![-2658, 23, 0]]]
  g := ![![![1, 0, 0], ![-25, 103, 0], ![-88, 0, 103]], ![![0, 1, 0], ![-14, 26, 9], ![-23, 1, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![14, 43, 1]] ![![103, 0, 0], ![25, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![2575, 103, 0]], ![![1442, 4429, 103], ![206, 1133, 412]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![25, 1, 0]]], ![![![14, 43, 1]], ![![2, 11, 4]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![21, 40, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![21, 40, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![21, 40, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![21, 40, 1], ![-144, 62, 360], ![-5744, 24, 22]]]
  hmulB := by decide  
  f := ![![![-20, -40, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -40, 107]], ![![0, 0, 1], ![-72, -134, 360], ![-58, -8, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [96, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 106], [0, 1]]
 g := ![![[100, 34], [59, 57], [85], [91, 76], [29], [30, 1]], ![[50, 73], [57, 50], [85], [17, 31], [29], [60, 106]]]
 h' := ![![[30, 106], [7, 26], [25, 59], [38, 70], [79, 41], [9, 55], [0, 1]], ![[0, 1], [38, 81], [83, 48], [105, 37], [25, 66], [54, 52], [30, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [66, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [96, 77, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4994, -5854, -1104]
  a := ![1, -2, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![170, 358, -1104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-39, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-39, 1, 0]] 
 ![![107, 0, 0], ![68, 1, 0], ![85, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-39, 1, 0], ![0, -38, 9], ![-144, 1, -39]]]
  hmulB := by decide  
  f := ![![![1132, -29, 0], ![3103, 0, 0]], ![![742, -19, 0], ![2034, 0, 0]], ![![908, -19, -1], ![2489, 12, 0]]]
  g := ![![![1, 0, 0], ![-68, 107, 0], ![-85, 0, 107]], ![![-1, 1, 0], ![17, -38, 9], ![29, 1, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![21, 40, 1]] ![![107, 0, 0], ![-39, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4173, 107, 0]], ![![2247, 4280, 107], ![-963, -1498, 321]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-39, 1, 0]]], ![![![21, 40, 1]], ![![-9, -14, 3]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![47, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![47, 1, 0]] 
 ![![109, 0, 0], ![47, 1, 0], ![40, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![47, 1, 0], ![0, 48, 9], ![-144, 1, 47]]]
  hmulB := by decide  
  f := ![![![2257, 48, 0], ![-5232, 0, 0]], ![![893, 19, 0], ![-2070, 0, 0]], ![![786, -26, -8], ![-1822, 97, 0]]]
  g := ![![![1, 0, 0], ![-47, 109, 0], ![-40, 0, 109]], ![![0, 1, 0], ![-24, 48, 9], ![-19, 1, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-44, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-44, 1, 0]] 
 ![![109, 0, 0], ![65, 1, 0], ![32, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-44, 1, 0], ![0, -43, 9], ![-144, 1, -44]]]
  hmulB := by decide  
  f := ![![![3565, -81, 0], ![8829, 0, 0]], ![![2113, -48, 0], ![5233, 0, 0]], ![![1112, 13, -8], ![2754, 97, 0]]]
  g := ![![![1, 0, 0], ![-65, 109, 0], ![-32, 0, 109]], ![![-1, 1, 0], ![23, -43, 9], ![11, 1, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-4, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-4, 1, 0]] 
 ![![109, 0, 0], ![105, 1, 0], ![35, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-4, 1, 0], ![0, -3, 9], ![-144, 1, -4]]]
  hmulB := by decide  
  f := ![![![337, -84, 0], ![9156, 0, 0]], ![![325, -81, 0], ![8830, 0, 0]], ![![111, -25, -8], ![3016, 97, 0]]]
  g := ![![![1, 0, 0], ![-105, 109, 0], ![-35, 0, 109]], ![![-1, 1, 0], ![0, -3, 9], ![-1, 1, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![47, 1, 0]] ![![109, 0, 0], ![-44, 1, 0]]
  ![![109, 0, 0], ![-36, -48, 1]] where
 M := ![![![11881, 0, 0], ![-4796, 109, 0]], ![![5123, 109, 0], ![-2068, 4, 9]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![-8, 49, -1], ![109, 0, 0]]], ![![![47, 1, 0], ![0, 0, 0]], ![![-16, 4, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-36, -48, 1]] ![![109, 0, 0], ![-4, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-436, 109, 0]], ![![-3924, -5232, 109], ![0, 109, -436]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-4, 1, 0]]], ![![![-36, -48, 1]], ![![0, 1, -4]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-7, -30, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-7, -30, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![106, 83, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-7, -30, 1], ![-144, -36, -270], ![4336, -46, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-106, -83, 113]], ![![-1, -1, 1], ![252, 198, -270], ![44, 4, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [68, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 112], [0, 1]]
 g := ![![[], [], [], [62], [0, 104], [0, 1]], ![[], [], [], [62], [0, 9], [0, 112]]]
 h' := ![![[0, 112], [98], [95], [78], [0, 47], [0, 45], [0, 1]], ![[0, 1], [98], [95], [78], [0, 66], [0, 68], [0, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [0, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [68, 0, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5100, -4552, 325]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-350, -279, 325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![44, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![44, 1, 0]] 
 ![![113, 0, 0], ![44, 1, 0], ![6, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![44, 1, 0], ![0, 45, 9], ![-144, 1, 44]]]
  hmulB := by decide  
  f := ![![![265, 6, 0], ![-678, 0, 0]], ![![44, 1, 0], ![-112, 0, 0]], ![![-42, -36, -7], ![108, 88, 0]]]
  g := ![![![1, 0, 0], ![-44, 113, 0], ![-6, 0, 113]], ![![0, 1, 0], ![-18, 45, 9], ![-4, 1, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-7, -30, 1]] ![![113, 0, 0], ![44, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![4972, 113, 0]], ![![-791, -3390, 113], ![-452, -1356, -226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![44, 1, 0]]], ![![![-7, -30, 1]], ![![-4, -12, -2]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![39, -46, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![39, -46, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![39, 81, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![39, -46, 1], ![-144, -6, -414], ![6640, -62, 40]]]
  hmulB := by decide  
  f := ![![![-38, 46, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -81, 127]], ![![0, -1, 1], ![126, 264, -414], ![40, -26, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [122, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 126], [0, 1]]
 g := ![![[5, 76], [54, 8], [33, 19], [27, 4], [10, 25], [25, 1]], ![[0, 51], [0, 119], [0, 108], [0, 123], [0, 102], [50, 126]]]
 h' := ![![[25, 126], [16, 40], [38, 95], [8, 20], [50, 125], [125, 122], [0, 1]], ![[0, 1], [0, 87], [0, 32], [0, 107], [0, 2], [0, 5], [25, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [66, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [122, 102, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-512399, -405816, 46265]
  a := ![1, 20, 161]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18242, -32703, 46265]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![33, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![33, 1, 0]] 
 ![![127, 0, 0], ![33, 1, 0], ![87, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![33, 1, 0], ![0, 34, 9], ![-144, 1, 33]]]
  hmulB := by decide  
  f := ![![![1816, 55, 0], ![-6985, 0, 0]], ![![462, 14, 0], ![-1777, 0, 0]], ![![1230, 7, -8], ![-4731, 113, 0]]]
  g := ![![![1, 0, 0], ![-33, 127, 0], ![-87, 0, 127]], ![![0, 1, 0], ![-15, 34, 9], ![-24, 1, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![39, -46, 1]] ![![127, 0, 0], ![33, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![4191, 127, 0]], ![![4953, -5842, 127], ![1143, -1524, -381]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![33, 1, 0]]], ![![![39, -46, 1]], ![![9, -12, -3]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-32, -65, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-32, -65, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![99, 66, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-32, -65, 1], ![-144, -96, -585], ![9376, -81, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -66, 131]], ![![-1, -1, 1], ![441, 294, -585], ![95, 15, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [12, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 130], [0, 1]]
 g := ![![[25, 11], [71, 7], [114], [4], [13], [3], [1]], ![[0, 120], [67, 124], [114], [4], [13], [3], [1]]]
 h' := ![![[93, 130], [65, 81], [51, 20], [90, 30], [111, 2], [108, 12], [119, 93], [0, 1]], ![[0, 1], [0, 50], [77, 111], [129, 101], [35, 129], [45, 119], [122, 38], [93, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [94, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [12, 38, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5065, -3464, 801]
  a := ![-1, 2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-644, -430, 801]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![61, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![61, 1, 0]] 
 ![![131, 0, 0], ![61, 1, 0], ![31, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![61, 1, 0], ![0, 62, 9], ![-144, 1, 61]]]
  hmulB := by decide  
  f := ![![![1099, 18, 0], ![-2358, 0, 0]], ![![549, 9, 0], ![-1178, 0, 0]], ![![261, -44, -7], ![-560, 102, 0]]]
  g := ![![![1, 0, 0], ![-61, 131, 0], ![-31, 0, 131]], ![![0, 1, 0], ![-31, 62, 9], ![-16, 1, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-32, -65, 1]] ![![131, 0, 0], ![61, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![7991, 131, 0]], ![![-4192, -8515, 131], ![-2096, -4061, -524]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![61, 1, 0]]], ![![![-32, -65, 1]], ![![-16, -31, -4]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-54, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-54, 1, 0]] 
 ![![137, 0, 0], ![83, 1, 0], ![93, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-54, 1, 0], ![0, -53, 9], ![-144, 1, -54]]]
  hmulB := by decide  
  f := ![![![4699, -87, 0], ![11919, 0, 0]], ![![2917, -54, 0], ![7399, 0, 0]], ![![3219, -36, -4], ![8165, 61, 0]]]
  g := ![![![1, 0, 0], ![-83, 137, 0], ![-93, 0, 137]], ![![-1, 1, 0], ![26, -53, 9], ![35, 1, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-30, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-30, 1, 0]] 
 ![![137, 0, 0], ![107, 1, 0], ![86, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-30, 1, 0], ![0, -29, 9], ![-144, 1, -30]]]
  hmulB := by decide  
  f := ![![![1501, -50, 0], ![6850, 0, 0]], ![![1171, -39, 0], ![5344, 0, 0]], ![![958, -19, -4], ![4372, 61, 0]]]
  g := ![![![1, 0, 0], ![-107, 137, 0], ![-86, 0, 137]], ![![-1, 1, 0], ![17, -29, 9], ![17, 1, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-54, 1, 0]] ![![137, 0, 0], ![-54, 1, 0]]
  ![![137, 0, 0], ![50, 49, 1]] where
 M := ![![![18769, 0, 0], ![-7398, 137, 0]], ![![-7398, 137, 0], ![2916, -107, 9]]]
 hmul := by decide  
 g := ![![![![87, -49, -1], ![137, 0, 0]], ![![-54, 1, 0], ![0, 0, 0]]], ![![![-54, 1, 0], ![0, 0, 0]], ![![18, -4, 0], ![9, 0, 0]]]]
 hle2 := by decide  
def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![50, 49, 1]] ![![137, 0, 0], ![-30, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-4110, 137, 0]], ![![6850, 6713, 137], ![-1644, -1370, 411]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-30, 1, 0]]], ![![![50, 49, 1]], ![![-12, -10, 3]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB212I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB212I2 : PrimesBelowBoundCertificateInterval O 79 137 212 where
  m := 11
  g := ![3, 3, 1, 2, 2, 2, 3, 2, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB212I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N0, I137N1]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I89N0, I89N1, I89N2, I101N1, I103N1, I107N1, I109N0, I109N1, I109N2, I113N1, I127N1, I131N1, I137N0, I137N1]
  Il := ![[I83N0, I83N1, I83N1], [I89N0, I89N1, I89N2], [], [I101N1], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [I113N1], [I127N1], [I131N1], [I137N0, I137N0, I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
