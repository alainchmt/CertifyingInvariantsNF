
import IdealArithmetic.Examples.NF3_1_280904_4.RI3_1_280904_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [13, 28, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 21, 46], [51, 61, 37], [0, 1]]
 g := ![![[34, 51, 40], [18, 42, 33], [16, 59], [22, 40], [50, 24, 1], []], ![[51, 70, 12, 20], [28, 81, 15, 35], [67, 21], [19, 65], [24, 23, 57, 20], [11, 41]], ![[67, 46, 31, 3], [4, 25, 6, 41], [70, 65], [78, 17], [12, 44, 82, 49], [20, 41]]]
 h' := ![![[56, 21, 46], [15, 78, 66], [7, 47, 45], [76, 64, 15], [14, 31, 17], [0, 0, 1], [0, 1]], ![[51, 61, 37], [65, 21, 61], [42, 9, 10], [0, 22, 41], [9, 27, 56], [5, 17, 61], [56, 21, 46]], ![[0, 1], [52, 67, 39], [15, 27, 28], [26, 80, 27], [58, 25, 10], [17, 66, 21], [51, 61, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 44], []]
 b := ![[], [70, 69, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [13, 28, 59, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85739, -18592, 830]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1033, -224, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![16, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![16, 1, 0]] 
 ![![89, 0, 0], ![16, 1, 0], ![6, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![16, 1, 0], ![1, 16, 2], ![-99, -7, 17]]]
  hmulB := by decide  
  f := ![![![-1144, -19340, -2418], ![-356, 107601, 0]], ![![-217, -3472, -434], ![1, 19313, 0]], ![![-80, -1304, -163], ![-8, 7254, 0]]]
  g := ![![![1, 0, 0], ![-16, 89, 0], ![-6, 0, 89]], ![![0, 1, 0], ![-3, 16, 2], ![-1, -7, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![25, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![25, 1, 0]] 
 ![![89, 0, 0], ![25, 1, 0], ![44, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![25, 1, 0], ![1, 25, 2], ![-99, -7, 26]]]
  hmulB := by decide  
  f := ![![![-3122, -91179, -7296], ![-1869, 324672, 0]], ![![-874, -25594, -2048], ![-533, 91136, 0]], ![![-1562, -45078, -3607], ![-858, 160512, 0]]]
  g := ![![![1, 0, 0], ![-25, 89, 0], ![-44, 0, 89]], ![![0, 1, 0], ![-8, 25, 2], ![-12, -7, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-42, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-42, 1, 0]] 
 ![![89, 0, 0], ![47, 1, 0], ![53, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-42, 1, 0], ![1, -42, 2], ![-99, -7, -41]]]
  hmulB := by decide  
  f := ![![![-161, 12093, -576], ![267, 25632, 0]], ![![-67, 6382, -304], ![179, 13528, 0]], ![![-77, 7201, -343], ![199, 15264, 0]]]
  g := ![![![1, 0, 0], ![-47, 89, 0], ![-53, 0, 89]], ![![-1, 1, 0], ![21, -42, 2], ![27, -7, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![16, 1, 0]] ![![89, 0, 0], ![25, 1, 0]]
  ![![89, 0, 0], ![-22, -24, 1]] where
 M := ![![![7921, 0, 0], ![2225, 89, 0]], ![![1424, 89, 0], ![401, 41, 2]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-22, -24, 1]] ![![89, 0, 0], ![-42, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3738, 89, 0]], ![![-1958, -2136, 89], ![801, 979, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-42, 1, 0]]], ![![![-22, -24, 1]], ![![9, 11, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![27, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![27, 1, 0]] 
 ![![97, 0, 0], ![27, 1, 0], ![24, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![27, 1, 0], ![1, 27, 2], ![-99, -7, 28]]]
  hmulB := by decide  
  f := ![![![811, 26238, 1944], ![582, -94284, 0]], ![![216, 7288, 540], ![195, -26190, 0]], ![![204, 6492, 481], ![132, -23328, 0]]]
  g := ![![![1, 0, 0], ![-27, 97, 0], ![-24, 0, 97]], ![![0, 1, 0], ![-8, 27, 2], ![-6, -7, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-17, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-17, 1, 0]] 
 ![![97, 0, 0], ![80, 1, 0], ![50, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-17, 1, 0], ![1, -17, 2], ![-99, -7, -16]]]
  hmulB := by decide  
  f := ![![![-3158, 57159, -6726], ![1164, 326211, 0]], ![![-2602, 47131, -5546], ![971, 268981, 0]], ![![-1621, 29463, -3467], ![639, 168150, 0]]]
  g := ![![![1, 0, 0], ![-80, 97, 0], ![-50, 0, 97]], ![![-1, 1, 0], ![13, -17, 2], ![13, -7, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, 6, -2]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-43, 6, -2]] 
 ![![97, 0, 0], ![86, 1, 0], ![37, 0, 1]] where
  M :=![![![-43, 6, -2], ![204, -29, 10], ![-488, 64, -23]]]
  hmulB := by decide  
  f := ![![![-27, -10, -2]], ![![-22, -9, -2]], ![![1, -2, -1]]]
  g := ![![![-5, 6, -2], ![24, -29, 10], ![-53, 64, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![27, 1, 0]] ![![97, 0, 0], ![-17, 1, 0]]
  ![![27, 10, 2]] where
 M := ![![![9409, 0, 0], ![-1649, 97, 0]], ![![2619, 97, 0], ![-458, 10, 2]]]
 hmul := by decide  
 g := ![![![![4171, -582, 194]], ![![-935, 131, -44]]], ![![![957, -133, 44]], ![![-214, 30, -10]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![27, 10, 2]] ![![-43, 6, -2]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![34, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![34, 1, 0]] 
 ![![101, 0, 0], ![34, 1, 0], ![79, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![34, 1, 0], ![1, 34, 2], ![-99, -7, 35]]]
  hmulB := by decide  
  f := ![![![197, 8974, 528], ![202, -26664, 0]], ![![54, 2991, 176], ![102, -8888, 0]], ![![145, 7019, 413], ![185, -20856, 0]]]
  g := ![![![1, 0, 0], ![-34, 101, 0], ![-79, 0, 101]], ![![0, 1, 0], ![-13, 34, 2], ![-26, -7, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-21, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-21, 1, 0]] 
 ![![101, 0, 0], ![80, 1, 0], ![83, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-21, 1, 0], ![1, -21, 2], ![-99, -7, -20]]]
  hmulB := by decide  
  f := ![![![-194, 4535, -432], ![101, 21816, 0]], ![![-149, 3590, -342], ![102, 17271, 0]], ![![-143, 3726, -355], ![162, 17928, 0]]]
  g := ![![![1, 0, 0], ![-80, 101, 0], ![-83, 0, 101]], ![![-1, 1, 0], ![15, -21, 2], ![21, -7, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-14, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-14, 1, 0]] 
 ![![101, 0, 0], ![87, 1, 0], ![54, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-14, 1, 0], ![1, -14, 2], ![-99, -7, -13]]]
  hmulB := by decide  
  f := ![![![-3423, 49886, -7128], ![1010, 359964, 0]], ![![-2942, 42957, -6138], ![910, 309969, 0]], ![![-1820, 26671, -3811], ![613, 192456, 0]]]
  g := ![![![1, 0, 0], ![-87, 101, 0], ![-54, 0, 101]], ![![-1, 1, 0], ![11, -14, 2], ![12, -7, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![34, 1, 0]] ![![101, 0, 0], ![-21, 1, 0]]
  ![![101, 0, 0], ![-3, -44, 1]] where
 M := ![![![10201, 0, 0], ![-2121, 101, 0]], ![![3434, 101, 0], ![-713, 13, 2]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![-18, 45, -1], ![101, 0, 0]]], ![![![34, 1, 0], ![0, 0, 0]], ![![-7, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-3, -44, 1]] ![![101, 0, 0], ![-14, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1414, 101, 0]], ![![-303, -4444, 101], ![-101, 606, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-14, 1, 0]]], ![![![-3, -44, 1]], ![![-1, 6, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![27, 19, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![27, 19, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![27, 19, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![27, 19, 1], ![-80, 20, 39], ![-1934, -186, 39]]]
  hmulB := by decide  
  f := ![![![-26, -19, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -19, 103]], ![![0, 0, 1], ![-11, -7, 39], ![-29, -9, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [69, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 102], [0, 1]]
 g := ![![[40, 23], [15, 4], [26, 29], [60], [55], [21, 1]], ![[8, 80], [99, 99], [17, 74], [60], [55], [42, 102]]]
 h' := ![![[21, 102], [98, 34], [60, 2], [85, 82], [65, 67], [96, 63], [0, 1]], ![[0, 1], [91, 69], [102, 101], [56, 21], [30, 36], [80, 40], [21, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [2, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [69, 82, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![896, -1357, 243]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55, -58, 243]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-39, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-39, 1, 0]] 
 ![![103, 0, 0], ![64, 1, 0], ![64, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-39, 1, 0], ![1, -39, 2], ![-99, -7, -38]]]
  hmulB := by decide  
  f := ![![![2548, -131253, 6732], ![-2163, -346698, 0]], ![![1585, -81536, 4182], ![-1338, -215373, 0]], ![![1573, -81555, 4183], ![-1371, -215424, 0]]]
  g := ![![![1, 0, 0], ![-64, 103, 0], ![-64, 0, 103]], ![![-1, 1, 0], ![23, -39, 2], ![27, -7, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![27, 19, 1]] ![![103, 0, 0], ![-39, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4017, 103, 0]], ![![2781, 1957, 103], ![-1133, -721, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-39, 1, 0]]], ![![![27, 19, 1]], ![![-11, -7, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![49, -28, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![49, -28, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![49, 79, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![49, -28, 1], ![-127, 42, -55], ![2719, 143, 14]]]
  hmulB := by decide  
  f := ![![![-48, 28, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -79, 107]], ![![0, -1, 1], ![24, 41, -55], ![19, -9, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [28, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 106], [0, 1]]
 g := ![![[36, 40], [92, 35], [25], [49, 14], [12], [62, 1]], ![[55, 67], [15, 72], [25], [61, 93], [12], [17, 106]]]
 h' := ![![[62, 106], [99, 19], [89, 28], [19, 5], [26, 11], [83, 71], [0, 1]], ![[0, 1], [100, 88], [6, 79], [8, 102], [66, 96], [98, 36], [62, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [94, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [28, 45, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-216471, -230029, -25012]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9431, 16317, -25012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-52, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-52, 1, 0]] 
 ![![107, 0, 0], ![55, 1, 0], ![93, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-52, 1, 0], ![1, -52, 2], ![-99, -7, -51]]]
  hmulB := by decide  
  f := ![![![1973, -164713, 6336], ![-2461, -338976, 0]], ![![1057, -84645, 3256], ![-1176, -174196, 0]], ![![1727, -143162, 5507], ![-2114, -294624, 0]]]
  g := ![![![1, 0, 0], ![-55, 107, 0], ![-93, 0, 107]], ![![-1, 1, 0], ![25, -52, 2], ![47, -7, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![49, -28, 1]] ![![107, 0, 0], ![-52, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-5564, 107, 0]], ![![5243, -2996, 107], ![-2675, 1498, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-52, 1, 0]]], ![![![49, -28, 1]], ![![-25, 14, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-42, -16, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-42, -16, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![67, 93, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-42, -16, 1], ![-115, -49, -31], ![1531, 59, -65]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -93, 109]], ![![-1, -1, 1], ![18, 26, -31], ![54, 56, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [37, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 108], [0, 1]]
 g := ![![[68, 108], [83], [58, 7], [66, 1], [83], [100, 1]], ![[77, 1], [83], [104, 102], [57, 108], [83], [91, 108]]]
 h' := ![![[100, 108], [47, 76], [34, 65], [65, 94], [17, 108], [6, 44], [0, 1]], ![[0, 1], [17, 33], [103, 44], [91, 15], [26, 1], [46, 65], [100, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [101, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [37, 9, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-311, -1250, -208]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![125, 166, -208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![31, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![31, 1, 0]] 
 ![![109, 0, 0], ![31, 1, 0], ![65, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![31, 1, 0], ![1, 31, 2], ![-99, -7, 32]]]
  hmulB := by decide  
  f := ![![![-3734, -135945, -8772], ![-2289, 478074, 0]], ![![-1061, -38651, -2494], ![-653, 135923, 0]], ![![-2254, -81069, -5231], ![-1269, 285090, 0]]]
  g := ![![![1, 0, 0], ![-31, 109, 0], ![-65, 0, 109]], ![![0, 1, 0], ![-10, 31, 2], ![-18, -7, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-42, -16, 1]] ![![109, 0, 0], ![31, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3379, 109, 0]], ![![-4578, -1744, 109], ![-1417, -545, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![31, 1, 0]]], ![![![-42, -16, 1]], ![![-13, -5, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [4, 60, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 20, 42], [6, 92, 71], [0, 1]]
 g := ![![[52, 103, 77], [85, 13], [41, 30], [22, 83], [80, 96, 11], [1]], ![[25, 84, 64, 67], [106, 8], [11, 13], [108, 106], [63, 28, 62, 108], [71, 71, 16, 73]], ![[80, 80, 83, 38], [71, 111], [17, 97], [2, 69], [97, 2, 80, 29], [84, 74, 3, 40]]]
 h' := ![![[18, 20, 42], [7, 6, 90], [11, 29, 37], [47, 53, 97], [19, 30, 99], [109, 53, 24], [0, 1]], ![[6, 92, 71], [12, 25, 57], [60, 45, 102], [45, 85, 76], [5, 100, 85], [11, 93, 27], [18, 20, 42]], ![[0, 1], [54, 82, 79], [15, 39, 87], [14, 88, 53], [19, 96, 42], [106, 80, 62], [6, 92, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 33], []]
 b := ![[], [92, 38, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [4, 60, 89, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103960, -25764, 226]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-920, -228, 2]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2395, 306, -82]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![2395, 306, -82]] 
 ![![127, 0, 0], ![0, 127, 0], ![25, 83, 1]] where
  M :=![![![2395, 306, -82], ![8424, 2969, 530], ![-25948, 2204, 3275]]]
  hmulB := by decide  
  f := ![![![67365, -9314, 3194]], ![![-325520, 45007, -15434]], ![![-193553, 26761, -9177]]]
  g := ![![![35, 56, -82], ![-38, -323, 530], ![-849, -2123, 3275]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [27, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 126], [0, 1]]
 g := ![![[73, 11], [7, 73], [32, 124], [87, 2], [103, 121], [61, 1]], ![[109, 116], [15, 54], [103, 3], [82, 125], [118, 6], [122, 126]]]
 h' := ![![[61, 126], [65, 97], [25, 33], [64, 88], [13, 111], [4, 11], [0, 1]], ![[0, 1], [13, 30], [6, 94], [98, 39], [53, 16], [40, 116], [61, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [59, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [27, 66, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11239, 55, 983]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-282, -642, 983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67365, -9314, 3194]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![67365, -9314, 3194]] 
 ![![127, 0, 0], ![87, 1, 0], ![26, 0, 1]] where
  M :=![![![67365, -9314, 3194], ![-325520, 45007, -15434], ![752804, -104084, 35693]]]
  hmulB := by decide  
  f := ![![![2395, 306, -82]], ![![1707, 233, -52]], ![![286, 80, 9]]]
  g := ![![![6257, -9314, 3194], ![-30235, 45007, -15434], ![69922, -104084, 35693]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![2395, 306, -82]] ![![67365, -9314, 3194]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![6, 1, 0]] 
 ![![131, 0, 0], ![6, 1, 0], ![48, 0, 1]] where
  M :=![![![6, 1, 0], ![1, 6, 2], ![-99, -7, 7]]]
  hmulB := by decide  
  f := ![![![56, -7, 2]], ![![1, 0, 0]], ![![25, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 6, 2], ![-3, -7, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![51, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![51, 1, 0]] 
 ![![131, 0, 0], ![51, 1, 0], ![10, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![51, 1, 0], ![1, 51, 2], ![-99, -7, 52]]]
  hmulB := by decide  
  f := ![![![22, 3671, 144], ![131, -9432, 0]], ![![-23, 1427, 56], ![132, -3668, 0]], ![![-10, 280, 11], ![40, -720, 0]]]
  g := ![![![1, 0, 0], ![-51, 131, 0], ![-10, 0, 131]], ![![0, 1, 0], ![-20, 51, 2], ![-2, -7, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-58, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-58, 1, 0]] 
 ![![131, 0, 0], ![73, 1, 0], ![87, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-58, 1, 0], ![1, -58, 2], ![-99, -7, -57]]]
  hmulB := by decide  
  f := ![![![-4059, 353185, -12180], ![4585, 797790, 0]], ![![-2232, 196774, -6786], ![2621, 444483, 0]], ![![-2697, 234558, -8089], ![3042, 529830, 0]]]
  g := ![![![1, 0, 0], ![-73, 131, 0], ![-87, 0, 131]], ![![-1, 1, 0], ![31, -58, 2], ![41, -7, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![6, 1, 0]] ![![131, 0, 0], ![51, 1, 0]]
  ![![131, 0, 0], ![-43, -37, 1]] where
 M := ![![![786, 131, 0], ![307, 57, 2]]]
 hmul := by decide  
 g := ![![![![6, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-43, -37, 1]] ![![131, 0, 0], ![-58, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-7598, 131, 0]], ![![-5633, -4847, 131], ![2358, 2096, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-58, 1, 0]]], ![![![-43, -37, 1]], ![![18, 16, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-10, -61, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-10, -61, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![127, 76, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-10, -61, 1], ![-160, -17, -121], ![5986, 374, -78]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -76, 137]], ![![-1, -1, 1], ![111, 67, -121], ![116, 46, -78]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [54, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 136], [0, 1]]
 g := ![![[7, 68], [38], [107], [67, 103], [37], [130], [1]], ![[59, 69], [38], [107], [41, 34], [37], [130], [1]]]
 h' := ![![[33, 136], [17, 43], [98, 77], [81, 92], [93, 69], [6, 41], [83, 33], [0, 1]], ![[0, 1], [66, 94], [36, 60], [103, 45], [41, 68], [126, 96], [76, 104], [33, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [49, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [54, 104, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1164, -51, -363]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![345, 201, -363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-16, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-16, 1, 0]] 
 ![![137, 0, 0], ![121, 1, 0], ![78, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-16, 1, 0], ![1, -16, 2], ![-99, -7, -15]]]
  hmulB := by decide  
  f := ![![![-2091, 34492, -4312], ![548, 295372, 0]], ![![-1839, 30460, -3808], ![549, 260848, 0]], ![![-1178, 19637, -2455], ![419, 168168, 0]]]
  g := ![![![1, 0, 0], ![-121, 137, 0], ![-78, 0, 137]], ![![-1, 1, 0], ![13, -16, 2], ![14, -7, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-10, -61, 1]] ![![137, 0, 0], ![-16, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-2192, 137, 0]], ![![-1370, -8357, 137], ![0, 959, -137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-16, 1, 0]]], ![![![-10, -61, 1]], ![![0, 7, -1]]]]
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


lemma PB150I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB150I2 : PrimesBelowBoundCertificateInterval O 79 137 150 where
  m := 11
  g := ![1, 3, 3, 3, 2, 2, 2, 1, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB150I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
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
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![97, 97, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
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
  β := ![I89N0, I89N1, I89N2, I97N0, I97N1, I97N2, I101N0, I101N1, I101N2, I103N1, I107N1, I109N1, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[], [I89N0, I89N1, I89N2], [I97N0, I97N1, I97N2], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N1], [], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
