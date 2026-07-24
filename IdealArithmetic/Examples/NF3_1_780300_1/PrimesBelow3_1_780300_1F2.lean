
import IdealArithmetic.Examples.NF3_1_780300_1.RI3_1_780300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![19, 28, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![19, 28, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![19, 28, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![19, 28, 1], ![170, 19, 140], ![4760, 34, 19]]]
  hmulB := by decide  
  f := ![![![-18, -28, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -28, 83]], ![![0, 0, 1], ![-30, -47, 140], ![53, -6, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [37, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 82], [0, 1]]
 g := ![![[63, 9], [23, 27], [28], [81], [9, 49], [1]], ![[0, 74], [0, 56], [28], [81], [81, 34], [1]]]
 h' := ![![[76, 82], [62, 80], [24, 39], [75, 32], [82, 74], [46, 76], [0, 1]], ![[0, 1], [0, 3], [0, 44], [17, 51], [62, 9], [12, 7], [76, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [16, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [37, 7, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![377, 27, -2]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 1, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![26, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![26, 1, 0]] 
 ![![83, 0, 0], ![26, 1, 0], ![64, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![26, 1, 0], ![0, 26, 5], ![170, 0, 26]]]
  hmulB := by decide  
  f := ![![![365, 14, 0], ![-1162, 0, 0]], ![![78, 3, 0], ![-248, 0, 0]], ![![252, -6, -3], ![-802, 50, 0]]]
  g := ![![![1, 0, 0], ![-26, 83, 0], ![-64, 0, 83]], ![![0, 1, 0], ![-12, 26, 5], ![-18, 0, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![19, 28, 1]] ![![83, 0, 0], ![26, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2158, 83, 0]], ![![1577, 2324, 83], ![664, 747, 166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![26, 1, 0]]], ![![![19, 28, 1]], ![![8, 9, 2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-21, -44, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-21, -44, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![68, 45, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-21, -44, 1], ![170, -21, -220], ![-7480, 34, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -45, 89]], ![![-1, -1, 1], ![170, 111, -220], ![-68, 11, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [52, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 88], [0, 1]]
 g := ![![[9, 78], [16], [17], [68, 20], [15, 84], [1]], ![[84, 11], [16], [17], [53, 69], [41, 5], [1]]]
 h' := ![![[66, 88], [48, 16], [48, 4], [24, 62], [21, 38], [37, 66], [0, 1]], ![[0, 1], [36, 73], [45, 85], [22, 27], [37, 51], [32, 23], [66, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [21, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [52, 23, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2010, 264, 83]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86, -39, 83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![42, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![42, 1, 0]] 
 ![![89, 0, 0], ![42, 1, 0], ![21, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![42, 1, 0], ![0, 42, 5], ![170, 0, 42]]]
  hmulB := by decide  
  f := ![![![1135, 27, 0], ![-2403, 0, 0]], ![![546, 13, 0], ![-1156, 0, 0]], ![![231, -3, -1], ![-489, 18, 0]]]
  g := ![![![1, 0, 0], ![-42, 89, 0], ![-21, 0, 89]], ![![0, 1, 0], ![-21, 42, 5], ![-8, 0, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-21, -44, 1]] ![![89, 0, 0], ![42, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3738, 89, 0]], ![![-1869, -3916, 89], ![-712, -1869, -178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![42, 1, 0]]], ![![![-21, -44, 1]], ![![-8, -21, -2]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [81, 91, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 59, 33], [55, 37, 64], [0, 1]]
 g := ![![[27, 44, 73], [53, 25], [42, 9], [31, 36], [32, 4], [1]], ![[5, 82, 50, 33], [18, 27], [16, 73], [93, 47], [34, 70], [47, 82, 11, 47]], ![[71, 7, 35, 16], [4, 61], [64, 85], [64, 36], [29, 95], [16, 68, 20, 50]]]
 h' := ![![[44, 59, 33], [39, 5, 48], [89, 87, 92], [75, 93, 94], [89, 60, 91], [16, 6, 2], [0, 1]], ![[55, 37, 64], [88, 65, 1], [73, 20, 67], [37, 33, 48], [95, 4, 12], [91, 13, 78], [44, 59, 33]], ![[0, 1], [89, 27, 48], [5, 87, 35], [57, 68, 52], [10, 33, 91], [82, 78, 17], [55, 37, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 18], []]
 b := ![[], [60, 61, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [81, 91, 95, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149283, -3589, -194]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1539, -37, -2]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![45, 3, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![45, 3, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![45, 3, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![45, 3, 1], ![170, 45, 15], ![510, 34, 45]]]
  hmulB := by decide  
  f := ![![![-44, -3, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -3, 101]], ![![0, 0, 1], ![-5, 0, 15], ![-15, -1, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [93, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 100], [0, 1]]
 g := ![![[91, 25], [70], [37, 37], [70], [5], [21, 1]], ![[10, 76], [70], [6, 64], [70], [5], [42, 100]]]
 h' := ![![[21, 100], [3, 96], [94, 26], [8, 80], [85, 75], [67, 45], [0, 1]], ![[0, 1], [100, 5], [34, 75], [72, 21], [44, 26], [2, 56], [21, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [53, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [93, 80, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-846, 388, -241]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99, 11, -241]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-15, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-15, 1, 0]] 
 ![![101, 0, 0], ![86, 1, 0], ![56, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-15, 1, 0], ![0, -15, 5], ![170, 0, -15]]]
  hmulB := by decide  
  f := ![![![496, -33, 0], ![3333, 0, 0]], ![![436, -29, 0], ![2930, 0, 0]], ![![286, -7, -4], ![1922, 81, 0]]]
  g := ![![![1, 0, 0], ![-86, 101, 0], ![-56, 0, 101]], ![![-1, 1, 0], ![10, -15, 5], ![10, 0, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![45, 3, 1]] ![![101, 0, 0], ![-15, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1515, 101, 0]], ![![4545, 303, 101], ![-505, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-15, 1, 0]]], ![![![45, 3, 1]], ![![-5, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [38, 5, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 8, 11], [32, 94, 92], [0, 1]]
 g := ![![[93, 46, 64], [82, 51, 83], [47, 69, 82], [48, 7], [], [1]], ![[72, 13, 50, 53], [88, 14, 57, 62], [15, 64, 65, 96], [77, 33], [74, 38], [94, 12, 20, 95]], ![[64, 73, 56, 66], [45, 25, 45, 18], [33, 42, 73, 91], [30, 30], [6, 38], [11, 45, 29, 8]]]
 h' := ![![[71, 8, 11], [77, 10, 95], [68, 50, 86], [34, 87, 59], [2, 71, 25], [65, 98], [0, 1]], ![[32, 94, 92], [58, 2, 79], [99, 54, 85], [90, 61, 14], [21, 65, 41], [19, 63, 48], [71, 8, 11]], ![[0, 1], [73, 91, 32], [1, 102, 35], [6, 58, 30], [42, 70, 37], [8, 45, 55], [32, 94, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 33], []]
 b := ![[], [55, 97, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [38, 5, 0, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6592, -515, -515]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -5, -5]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![6, -30, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![6, -30, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![6, 77, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![6, -30, 1], ![170, 6, -150], ![-5100, 34, 6]]]
  hmulB := by decide  
  f := ![![![-5, 30, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -77, 107]], ![![0, -1, 1], ![10, 108, -150], ![-48, -4, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [102, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 106], [0, 1]]
 g := ![![[77, 64], [26, 23], [76], [60, 36], [48], [64, 1]], ![[0, 43], [0, 84], [76], [10, 71], [48], [21, 106]]]
 h' := ![![[64, 106], [23, 8], [72, 39], [86, 41], [27, 6], [106, 35], [0, 1]], ![[0, 1], [0, 99], [0, 68], [35, 66], [90, 101], [99, 72], [64, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [104, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [102, 43, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6606, 889, 1850]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -1323, 1850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![43, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![43, 1, 0]] 
 ![![107, 0, 0], ![43, 1, 0], ![101, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![43, 1, 0], ![0, 43, 5], ![170, 0, 43]]]
  hmulB := by decide  
  f := ![![![130, 3, 0], ![-321, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![142, -14, -2], ![-351, 43, 0]]]
  g := ![![![1, 0, 0], ![-43, 107, 0], ![-101, 0, 107]], ![![0, 1, 0], ![-22, 43, 5], ![-39, 0, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![6, -30, 1]] ![![107, 0, 0], ![43, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4601, 107, 0]], ![![642, -3210, 107], ![428, -1284, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![43, 1, 0]]], ![![![6, -30, 1]], ![![4, -12, -1]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [57, 7, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 97, 10], [66, 11, 99], [0, 1]]
 g := ![![[93, 57, 89], [0, 105], [53, 70, 78], [105, 43, 83], [15, 9], [1]], ![[74, 105, 83, 19], [60, 21], [93, 63, 104, 96], [105, 58, 77, 95], [49, 36], [41, 17, 49, 19]], ![[95, 20, 99, 85], [12, 27], [75, 57, 41, 69], [10, 70, 14, 11], [64, 9], [44, 19, 87, 90]]]
 h' := ![![[40, 97, 10], [89, 44, 78], [31, 99, 66], [10, 100, 80], [105, 71, 65], [52, 102, 106], [0, 1]], ![[66, 11, 99], [106, 26, 99], [93, 27, 81], [101, 25, 27], [21, 82, 8], [78, 4, 6], [40, 97, 10]], ![[0, 1], [95, 39, 41], [105, 92, 71], [91, 93, 2], [87, 65, 36], [62, 3, 106], [66, 11, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 37], []]
 b := ![[], [106, 61, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [57, 7, 3, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17222, -4578, 1526]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![158, -42, 14]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-10, -26, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-10, -26, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![103, 87, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-10, -26, 1], ![170, -10, -130], ![-4420, 34, -10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-103, -87, 113]], ![![-1, -1, 1], ![120, 100, -130], ![-30, 8, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [10, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 112], [0, 1]]
 g := ![![[98, 105], [11], [82], [98], [34, 9], [37, 1]], ![[28, 8], [11], [82], [98], [28, 104], [74, 112]]]
 h' := ![![[37, 112], [94, 61], [59, 89], [38, 46], [112, 95], [82, 3], [0, 1]], ![[0, 1], [91, 52], [75, 24], [45, 67], [11, 18], [80, 110], [37, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [7, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [10, 76, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![690, 212, 157]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-137, -119, 157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![17, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![17, 1, 0]] 
 ![![113, 0, 0], ![17, 1, 0], ![10, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![17, 1, 0], ![0, 17, 5], ![170, 0, 17]]]
  hmulB := by decide  
  f := ![![![307, 18, 0], ![-2034, 0, 0]], ![![17, 1, 0], ![-112, 0, 0]], ![![4, -10, -3], ![-26, 68, 0]]]
  g := ![![![1, 0, 0], ![-17, 113, 0], ![-10, 0, 113]], ![![0, 1, 0], ![-3, 17, 5], ![0, 0, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-10, -26, 1]] ![![113, 0, 0], ![17, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![1921, 113, 0]], ![![-1130, -2938, 113], ![0, -452, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![17, 1, 0]]], ![![![-10, -26, 1]], ![![0, -4, -1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [16, 52, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 107, 115], [109, 19, 12], [0, 1]]
 g := ![![[62, 126, 60], [18, 64, 38], [76, 52, 8], [49, 48, 41], [97, 100, 36], [1]], ![[122, 96, 33, 73], [122, 85, 10, 34], [122, 106, 45, 62], [113, 84, 67, 52], [44, 57, 75, 73], [28, 97, 42, 50]], ![[14, 118, 19, 108], [63, 123, 53, 91], [42, 68, 70, 58], [60, 66, 104, 23], [80, 125, 51, 78], [74, 23, 34, 77]]]
 h' := ![![[24, 107, 115], [93, 67, 21], [54, 18, 66], [105, 8, 32], [99, 89, 26], [111, 75, 6], [0, 1]], ![[109, 19, 12], [109, 57, 103], [109, 21, 22], [18, 94, 4], [16, 125, 61], [41, 24, 103], [24, 107, 115]], ![[0, 1], [67, 3, 3], [64, 88, 39], [96, 25, 91], [91, 40, 40], [96, 28, 18], [109, 19, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 67], []]
 b := ![[], [116, 99, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [16, 52, 121, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1666748, 113792, 44196]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13124, 896, 348]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-23, 27, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-23, 27, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![108, 27, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-23, 27, 1], ![170, -23, 135], ![4590, 34, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-108, -27, 131]], ![![-1, 0, 1], ![-110, -28, 135], ![54, 5, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [56, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 130], [0, 1]]
 g := ![![[109, 64], [69, 20], [27], [77], [7], [58], [1]], ![[95, 67], [81, 111], [27], [77], [7], [58], [1]]]
 h' := ![![[53, 130], [66, 123], [72, 85], [55, 114], [100, 83], [19, 20], [75, 53], [0, 1]], ![[0, 1], [35, 8], [123, 46], [71, 17], [45, 48], [31, 111], [2, 78], [53, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [122, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [56, 78, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![899, -70, 109]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83, -23, 109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-4, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-4, 1, 0]] 
 ![![131, 0, 0], ![127, 1, 0], ![23, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-4, 1, 0], ![0, -4, 5], ![170, 0, -4]]]
  hmulB := by decide  
  f := ![![![141, -35, 0], ![4585, 0, 0]], ![![137, -34, 0], ![4455, 0, 0]], ![![25, -3, -4], ![813, 105, 0]]]
  g := ![![![1, 0, 0], ![-127, 131, 0], ![-23, 0, 131]], ![![-1, 1, 0], ![3, -4, 5], ![2, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-23, 27, 1]] ![![131, 0, 0], ![-4, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-524, 131, 0]], ![![-3013, 3537, 131], ![262, -131, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-4, 1, 0]]], ![![![-23, 27, 1]], ![![2, -1, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-23, -67, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-23, -67, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![114, 70, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-23, -67, 1], ![170, -23, -335], ![-11390, 34, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-114, -70, 137]], ![![-1, -1, 1], ![280, 171, -335], ![-64, 12, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [72, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 136], [0, 1]]
 g := ![![[17, 59], [100], [121], [2, 8], [87], [81], [1]], ![[0, 78], [100], [121], [74, 129], [87], [81], [1]]]
 h' := ![![[9, 136], [126, 123], [105, 10], [130, 126], [37, 62], [37, 118], [65, 9], [0, 1]], ![[0, 1], [0, 14], [58, 127], [31, 11], [47, 75], [3, 19], [9, 128], [9, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [131, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [72, 128, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1561, -486, -50]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![53, 22, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![61, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![61, 1, 0]] 
 ![![137, 0, 0], ![61, 1, 0], ![23, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![61, 1, 0], ![0, 61, 5], ![170, 0, 61]]]
  hmulB := by decide  
  f := ![![![428, 7, 0], ![-959, 0, 0]], ![![122, 2, 0], ![-273, 0, 0]], ![![30, -24, -2], ![-67, 55, 0]]]
  g := ![![![1, 0, 0], ![-61, 137, 0], ![-23, 0, 137]], ![![0, 1, 0], ![-28, 61, 5], ![-9, 0, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-23, -67, 1]] ![![137, 0, 0], ![61, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8357, 137, 0]], ![![-3151, -9179, 137], ![-1233, -4110, -274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![61, 1, 0]]], ![![![-23, -67, 1]], ![![-9, -30, -2]]]]
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
  g := ![2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB250I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![2048383]
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
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
  β := ![I83N1, I89N1, I101N1, I107N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [], [I107N1], [], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
