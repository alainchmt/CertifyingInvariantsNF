
import IdealArithmetic.Examples.NF3_1_808623_1.RI3_1_808623_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [34, 31, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 31, 22], [10, 5, 15], [0, 1]]
 g := ![![[8, 23, 34], [4, 21], [18, 22, 3], [34, 1], []], ![[15, 6, 29, 35], [3, 25], [1, 1, 16, 19], [32, 25], [23, 3]], ![[12, 8, 10, 20], [30, 28], [32, 3, 26, 13], [13, 36], [30, 3]]]
 h' := ![![[24, 31, 22], [5, 25, 21], [17, 33, 24], [28, 22, 15], [0, 0, 1], [0, 1]], ![[10, 5, 15], [16, 34, 26], [9, 7, 32], [19, 10, 4], [16, 7, 5], [24, 31, 22]], ![[0, 1], [27, 15, 27], [23, 34, 18], [27, 5, 18], [5, 30, 31], [10, 5, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 8], []]
 b := ![[], [26, 5, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [34, 31, 3, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-910533, -121767, -29600]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24609, -3291, -800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![13, 1, 0]] 
 ![![41, 0, 0], ![13, 1, 0], ![18, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, 1, 0], ![-2, 15, 5], ![177, 11, 11]]]
  hmulB := by decide  
  f := ![![![621, -4847, -1615], ![82, 13243, 0]], ![![191, -1531, -510], ![42, 4182, 0]], ![![272, -2128, -709], ![38, 5814, 0]]]
  g := ![![![1, 0, 0], ![-13, 41, 0], ![-18, 0, 41]], ![![0, 1, 0], ![-7, 15, 5], ![-4, 11, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-10, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-10, 1, 0]] 
 ![![41, 0, 0], ![31, 1, 0], ![0, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-10, 1, 0], ![-2, -8, 5], ![177, 11, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![6, 6, -4], ![18, 33, 0]]]
  g := ![![![1, 0, 0], ![-31, 41, 0], ![0, 0, 41]], ![![-1, 1, 0], ![6, -8, 5], ![-4, 11, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-3, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-3, 1, 0]] 
 ![![41, 0, 0], ![38, 1, 0], ![40, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-3, 1, 0], ![-2, -1, 5], ![177, 11, -5]]]
  hmulB := by decide  
  f := ![![![916, 460, -2295], ![-41, 18819, 0]], ![![848, 426, -2125], ![-40, 17425, 0]], ![![893, 449, -2239], ![-49, 18360, 0]]]
  g := ![![![1, 0, 0], ![-38, 41, 0], ![-40, 0, 41]], ![![-1, 1, 0], ![-4, -1, 5], ![-1, 11, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![13, 1, 0]] ![![41, 0, 0], ![-10, 1, 0]]
  ![![41, 0, 0], ![-10, 1, 1]] where
 M := ![![![1681, 0, 0], ![-410, 41, 0]], ![![533, 41, 0], ![-132, 5, 5]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![0, 0, -1], ![41, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-10, 1, 1]] ![![41, 0, 0], ![-3, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-123, 41, 0]], ![![-410, 41, 41], ![205, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-3, 1, 0]]], ![![![-10, 1, 1]], ![![5, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [20, 14, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 36, 27], [28, 6, 16], [0, 1]]
 g := ![![[20, 12, 21], [20, 19, 24], [16, 35], [39, 15, 1], []], ![[37, 36, 42, 33], [5, 22, 24, 32], [24, 24], [40, 36, 9, 26], [22, 41]], ![[38, 8, 25, 31], [31, 17, 30, 21], [15, 23], [12, 25, 14, 10], [33, 41]]]
 h' := ![![[30, 36, 27], [30, 16, 8], [17, 26, 29], [37, 14, 11], [0, 0, 1], [0, 1]], ![[28, 6, 16], [19, 17, 7], [33, 33, 16], [13, 31, 14], [30, 0, 6], [30, 36, 27]], ![[0, 1], [8, 10, 28], [41, 27, 41], [30, 41, 18], [38, 0, 36], [28, 6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 9], []]
 b := ![[], [12, 4, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [20, 14, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7926749, 1427170, 73616]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![184343, 33190, 1712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![18, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![18, 1, 0]] 
 ![![47, 0, 0], ![18, 1, 0], ![31, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![18, 1, 0], ![-2, 20, 5], ![177, 11, 16]]]
  hmulB := by decide  
  f := ![![![509, -5442, -1360], ![94, 12784, 0]], ![![190, -2081, -520], ![48, 4888, 0]], ![![325, -3590, -897], ![90, 8432, 0]]]
  g := ![![![1, 0, 0], ![-18, 47, 0], ![-31, 0, 47]], ![![0, 1, 0], ![-11, 20, 5], ![-11, 11, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-16, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-16, 1, 0]] 
 ![![47, 0, 0], ![31, 1, 0], ![30, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-16, 1, 0], ![-2, -14, 5], ![177, 11, -18]]]
  hmulB := by decide  
  f := ![![![3329, 24652, -8800], ![-564, 82720, 0]], ![![2193, 16248, -5800], ![-375, 54520, 0]], ![![2130, 15735, -5617], ![-345, 52800, 0]]]
  g := ![![![1, 0, 0], ![-31, 47, 0], ![-30, 0, 47]], ![![-1, 1, 0], ![6, -14, 5], ![8, 11, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-2, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-2, 1, 0]] 
 ![![47, 0, 0], ![45, 1, 0], ![9, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-2, 1, 0], ![-2, 0, 5], ![177, 11, -4]]]
  hmulB := by decide  
  f := ![![![-2111, -2, 5290], ![94, -49726, 0]], ![![-2019, -2, 5060], ![95, -47564, 0]], ![![-403, -1, 1013], ![47, -9522, 0]]]
  g := ![![![1, 0, 0], ![-45, 47, 0], ![-9, 0, 47]], ![![-1, 1, 0], ![-1, 0, 5], ![-6, 11, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![18, 1, 0]] ![![47, 0, 0], ![-16, 1, 0]]
  ![![47, 0, 0], ![-11, -18, 1]] where
 M := ![![![2209, 0, 0], ![-752, 47, 0]], ![![846, 47, 0], ![-290, 4, 5]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![-5, 19, -1], ![47, 0, 0]]], ![![![18, 1, 0], ![0, 0, 0]], ![![-5, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-11, -18, 1]] ![![47, 0, 0], ![-2, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-94, 47, 0]], ![![-517, -846, 47], ![235, 0, -94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-2, 1, 0]]], ![![![-11, -18, 1]], ![![5, 0, -2]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![123, 1, -6]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![123, 1, -6]] 
 ![![53, 0, 0], ![0, 53, 0], ![6, 44, 1]] where
  M :=![![![123, 1, -6], ![-1064, 59, 17], ![1053, -175, 43]]]
  hmulB := by decide  
  f := ![![![-104, -19, -7]], ![![-1201, -219, -81]], ![![-1053, -192, -71]]]
  g := ![![![3, 5, -6], ![-22, -13, 17], ![15, -39, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [48, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 52], [0, 1]]
 g := ![![[15, 29], [11], [47, 7], [38], [22, 1]], ![[17, 24], [11], [42, 46], [38], [44, 52]]]
 h' := ![![[22, 52], [1, 33], [23, 45], [47, 31], [4, 12], [0, 1]], ![[0, 1], [38, 20], [6, 8], [40, 22], [3, 41], [22, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [44, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [48, 31, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3303256, 1774420, 453959]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10934, -343392, 453959]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104, 19, 7]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![104, 19, 7]] 
 ![![53, 0, 0], ![47, 1, 0], ![16, 0, 1]] where
  M :=![![![104, 19, 7], ![1201, 219, 81], ![2341, 426, 157]]]
  hmulB := by decide  
  f := ![![![-123, -1, 6]], ![![-89, -2, 5]], ![![-57, 3, 1]]]
  g := ![![![-17, 19, 7], ![-196, 219, 81], ![-381, 426, 157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![123, 1, -6]] ![![104, 19, 7]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-23, -21, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-23, -21, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![36, 38, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-23, -21, 1], ![219, -54, -107], ![-3863, -200, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -38, 59]], ![![-1, -1, 1], ![69, 68, -107], ![-85, -24, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [22, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 58], [0, 1]]
 g := ![![[50, 51], [1, 21], [16], [50, 36], [21, 1]], ![[0, 8], [29, 38], [16], [39, 23], [42, 58]]]
 h' := ![![[21, 58], [37, 46], [30, 32], [21, 4], [10, 6], [0, 1]], ![[0, 1], [0, 13], [53, 27], [46, 55], [18, 53], [21, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [38, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [22, 38, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8061, 5130, 1197]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-867, -684, 1197]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-11, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-11, 1, 0]] 
 ![![59, 0, 0], ![48, 1, 0], ![27, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-11, 1, 0], ![-2, -9, 5], ![177, 11, -13]]]
  hmulB := by decide  
  f := ![![![-553, -2594, 1440], ![118, -16992, 0]], ![![-456, -2107, 1170], ![60, -13806, 0]], ![![-254, -1187, 659], ![49, -7776, 0]]]
  g := ![![![1, 0, 0], ![-48, 59, 0], ![-27, 0, 59]], ![![-1, 1, 0], ![5, -9, 5], ![0, 11, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-23, -21, 1]] ![![59, 0, 0], ![-11, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-649, 59, 0]], ![![-1357, -1239, 59], ![472, 177, -118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-11, 1, 0]]], ![![![-23, -21, 1]], ![![8, 3, -2]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![12, 18, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![12, 18, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![12, 18, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![12, 18, 1], ![141, 59, 88], ![3040, 229, -11]]]
  hmulB := by decide  
  f := ![![![-11, -18, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -18, 61]], ![![0, 0, 1], ![-15, -25, 88], ![52, 7, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [36, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 60], [0, 1]]
 g := ![![[33, 39], [3], [22, 12], [18, 22], [32, 1]], ![[0, 22], [3], [40, 49], [51, 39], [3, 60]]]
 h' := ![![[32, 60], [15, 51], [1, 8], [23, 16], [7, 12], [0, 1]], ![[0, 1], [0, 10], [13, 53], [47, 45], [25, 49], [32, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [20, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [36, 29, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1740, 1024, 145]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -26, 145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 1, 0]] 
 ![![61, 0, 0], ![34, 1, 0], ![11, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 1, 0], ![-2, -25, 5], ![177, 11, -29]]]
  hmulB := by decide  
  f := ![![![577, 7877, -1575], ![-122, 19215, 0]], ![![324, 4376, -875], ![-60, 10675, 0]], ![![116, 1420, -284], ![5, 3465, 0]]]
  g := ![![![1, 0, 0], ![-34, 61, 0], ![-11, 0, 61]], ![![-1, 1, 0], ![13, -25, 5], ![2, 11, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![12, 18, 1]] ![![61, 0, 0], ![-27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1647, 61, 0]], ![![732, 1098, 61], ![-183, -427, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-27, 1, 0]]], ![![![12, 18, 1]], ![![-3, -7, 1]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![3, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![3, 1, 0]] 
 ![![67, 0, 0], ![3, 1, 0], ![10, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![3, 1, 0], ![-2, 5, 5], ![177, 11, 1]]]
  hmulB := by decide  
  f := ![![![4948, -12376, -12375], ![67, 165825, 0]], ![![217, -551, -550], ![68, 7370, 0]], ![![736, -1848, -1847], ![66, 24750, 0]]]
  g := ![![![1, 0, 0], ![-3, 67, 0], ![-10, 0, 67]], ![![0, 1, 0], ![-1, 5, 5], ![2, 11, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![32, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![32, 1, 0]] 
 ![![67, 0, 0], ![32, 1, 0], ![50, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![32, 1, 0], ![-2, 34, 5], ![177, 11, 30]]]
  hmulB := by decide  
  f := ![![![2241, -41895, -6160], ![469, 82544, 0]], ![![1048, -19996, -2940], ![269, 39396, 0]], ![![1670, -31265, -4597], ![355, 61600, 0]]]
  g := ![![![1, 0, 0], ![-32, 67, 0], ![-50, 0, 67]], ![![0, 1, 0], ![-20, 34, 5], ![-25, 11, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![3, 1, 0]] ![![67, 0, 0], ![32, 1, 0]]
  ![![67, 0, 0], ![-8, -6, 1]] where
 M := ![![![4489, 0, 0], ![2144, 67, 0]], ![![201, 67, 0], ![94, 37, 5]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![32, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-8, -6, 1]] ![![67, 0, 0], ![32, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2144, 67, 0]], ![![-536, -402, 67], ![-67, -201, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![32, 1, 0]]], ![![![-8, -6, 1]], ![![-1, -3, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3421, 143, -226]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![3421, 143, -226]] 
 ![![71, 0, 0], ![0, 71, 0], ![70, 60, 1]] where
  M :=![![![3421, 143, -226], ![-40288, 1221, 1167], ![58307, -5433, 197]]]
  hmulB := by decide  
  f := ![![![92688, 16897, 6237]], ![![1070155, 195089, 72011]], ![![1025037, 186864, 68975]]]
  g := ![![![271, 193, -226], ![-1718, -969, 1167], ![627, -243, 197]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [22, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 70], [0, 1]]
 g := ![![[25, 36], [56, 9], [32, 60], [1], [40], [1]], ![[34, 35], [5, 62], [47, 11], [1], [40], [1]]]
 h' := ![![[18, 70], [46, 65], [6, 3], [26, 29], [30, 70], [49, 18], [0, 1]], ![[0, 1], [9, 6], [60, 68], [51, 42], [12, 1], [18, 53], [18, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [44, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [22, 53, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54606, 8171, 3117]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2304, -2519, 3117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-92688, -16897, -6237]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-92688, -16897, -6237]] 
 ![![71, 0, 0], ![57, 1, 0], ![37, 0, 1]] where
  M :=![![![-92688, -16897, -6237], ![-1070155, -195089, -72011], ![-2080167, -379214, -139975]]]
  hmulB := by decide  
  f := ![![![-3421, -143, 226]], ![![-2179, -132, 165]], ![![-2604, 2, 115]]]
  g := ![![![15510, -16897, -6237], ![179075, -195089, -72011], ![348086, -379214, -139975]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![3421, 143, -226]] ![![-92688, -16897, -6237]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [34, 44, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 62, 66], [42, 10, 7], [0, 1]]
 g := ![![[56, 46, 57], [18, 9], [49, 12], [10, 4, 48], [36, 1], []], ![[24, 49, 70, 5], [57, 46], [4, 35], [38, 23, 34, 5], [69, 27], [20, 49]], ![[9, 12, 28, 15], [19, 41], [2, 48], [26, 2, 68, 58], [12, 48], [6, 49]]]
 h' := ![![[67, 62, 66], [41, 37, 38], [54, 22, 3], [25, 5, 42], [17, 61, 11], [0, 0, 1], [0, 1]], ![[42, 10, 7], [21, 60, 48], [34, 35, 22], [30, 27, 20], [13, 4, 48], [13, 68, 10], [67, 62, 66]], ![[0, 1], [66, 49, 60], [37, 16, 48], [55, 41, 11], [29, 8, 14], [27, 5, 62], [42, 10, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 63], []]
 b := ![[], [18, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [34, 44, 37, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2558431, -297402, 28470]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35047, -4074, 390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [71, 69, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 14, 13], [21, 64, 66], [0, 1]]
 g := ![![[16, 47, 40], [63, 63, 50], [75, 39, 9], [25, 54, 65], [70, 1], []], ![[12, 69, 42, 22], [2, 42, 46, 23], [44, 24, 14, 51], [30, 32, 74, 25], [48, 67], [28, 11]], ![[39, 53, 36, 74], [57, 65, 38, 70], [70, 14, 45, 47], [69, 48, 29, 71], [76, 38], [54, 11]]]
 h' := ![![[49, 14, 13], [30, 25, 35], [47, 61, 45], [42, 20, 3], [7, 76, 12], [0, 0, 1], [0, 1]], ![[21, 64, 66], [68, 25, 37], [54, 75, 39], [49, 49, 57], [76, 61, 18], [18, 2, 64], [49, 14, 13]], ![[0, 1], [63, 29, 7], [7, 22, 74], [0, 10, 19], [71, 21, 49], [4, 77, 14], [21, 64, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 13], []]
 b := ![[], [53, 43, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [71, 69, 9, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6766350, 959850, 195525]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85650, 12150, 2475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB255I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB255I1 : PrimesBelowBoundCertificateInterval O 31 79 255 where
  m := 11
  g := ![1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB255I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N0, I41N1, I41N2, I47N0, I47N1, I47N2, I53N1, I59N1, I61N1, I67N0, I67N1, I71N1]
  Il := ![[], [I41N0, I41N1, I41N2], [], [I47N0, I47N1, I47N2], [I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N1], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
