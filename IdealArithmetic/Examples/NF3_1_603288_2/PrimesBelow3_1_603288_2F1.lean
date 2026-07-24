
import IdealArithmetic.Examples.NF3_1_603288_2.RI3_1_603288_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [33, 26, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 7, 11], [27, 29, 26], [0, 1]]
 g := ![![[13, 12, 33], [5, 34], [1, 35, 1], [5, 1], []], ![[8, 5, 4, 16], [30, 21], [21, 26, 33, 3], [6, 27], [19, 10]], ![[9, 18, 36, 3], [26, 27], [32, 36, 1, 10], [35, 12], [4, 10]]]
 h' := ![![[15, 7, 11], [36, 11, 25], [4, 33, 16], [20, 22, 36], [0, 0, 1], [0, 1]], ![[27, 29, 26], [30, 8, 32], [24, 27, 13], [12, 28, 28], [5, 15, 29], [15, 7, 11]], ![[0, 1], [14, 18, 17], [13, 14, 8], [17, 24, 10], [5, 22, 7], [27, 29, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 6], []]
 b := ![[], [16, 31, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [33, 26, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7733, 2109, -1369]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![209, 57, -37]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, 18, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![13, 18, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![13, 18, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, 18, 1], ![140, -8, 36], ![2520, -308, -8]]]
  hmulB := by decide  
  f := ![![![-12, -18, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -18, 41]], ![![0, 0, 1], ![-8, -16, 36], ![64, -4, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [36, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40], [0, 1]]
 g := ![![[10, 8], [25], [39], [40, 40], [1]], ![[0, 33], [25], [39], [31, 1], [1]]]
 h' := ![![[9, 40], [22, 34], [15, 36], [36, 11], [5, 9], [0, 1]], ![[0, 1], [0, 7], [11, 5], [12, 30], [4, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [35, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [36, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1675, 822, -91]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, 60, -91]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![5, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![5, 1, 0]] 
 ![![41, 0, 0], ![5, 1, 0], ![8, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![5, 1, 0], ![0, 5, 2], ![140, -21, 5]]]
  hmulB := by decide  
  f := ![![![126, 25, 0], ![-1025, 0, 0]], ![![10, 2, 0], ![-81, 0, 0]], ![![18, 1, -1], ![-146, 21, 0]]]
  g := ![![![1, 0, 0], ![-5, 41, 0], ![-8, 0, 41]], ![![0, 1, 0], ![-1, 5, 2], ![5, -21, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![13, 18, 1]] ![![41, 0, 0], ![5, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![205, 41, 0]], ![![533, 738, 41], ![205, 82, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![5, 1, 0]]], ![![![13, 18, 1]], ![![5, 2, 1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![33, -7, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![33, -7, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![33, 36, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![33, -7, 1], ![140, 12, -14], ![-980, 217, 12]]]
  hmulB := by decide  
  f := ![![![-32, 7, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -36, 43]], ![![0, -1, 1], ![14, 12, -14], ![-32, -5, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [7, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 42], [0, 1]]
 g := ![![[27, 24], [41, 17], [10], [12, 31], [1]], ![[6, 19], [10, 26], [10], [1, 12], [1]]]
 h' := ![![[26, 42], [14, 14], [20, 19], [2, 15], [36, 26], [0, 1]], ![[0, 1], [34, 29], [41, 24], [5, 28], [24, 17], [26, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [23, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [7, 17, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2735, 1, 92]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -77, 92]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![14, 1, 0]] 
 ![![43, 0, 0], ![14, 1, 0], ![31, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![14, 1, 0], ![0, 14, 2], ![140, -21, 14]]]
  hmulB := by decide  
  f := ![![![253, 18, 0], ![-774, 0, 0]], ![![70, 5, 0], ![-214, 0, 0]], ![![157, 4, -1], ![-480, 22, 0]]]
  g := ![![![1, 0, 0], ![-14, 43, 0], ![-31, 0, 43]], ![![0, 1, 0], ![-6, 14, 2], ![0, -21, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![33, -7, 1]] ![![43, 0, 0], ![14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![602, 43, 0]], ![![1419, -301, 43], ![602, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![14, 1, 0]]], ![![![33, -7, 1]], ![![14, -2, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![8, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![8, 1, 0]] 
 ![![47, 0, 0], ![8, 1, 0], ![15, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![8, 1, 0], ![0, 8, 2], ![140, -21, 8]]]
  hmulB := by decide  
  f := ![![![33, 4, 0], ![-188, 0, 0]], ![![-8, -1, 0], ![48, 0, 0]], ![![1, -4, -1], ![-4, 24, 0]]]
  g := ![![![1, 0, 0], ![-8, 47, 0], ![-15, 0, 47]], ![![0, 1, 0], ![-2, 8, 2], ![4, -21, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-6, 1, 0]] 
 ![![47, 0, 0], ![41, 1, 0], ![29, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-6, 1, 0], ![0, -6, 2], ![140, -21, -6]]]
  hmulB := by decide  
  f := ![![![61, -10, 0], ![470, 0, 0]], ![![55, -9, 0], ![424, 0, 0]], ![![43, -4, -1], ![332, 24, 0]]]
  g := ![![![1, 0, 0], ![-41, 47, 0], ![-29, 0, 47]], ![![-1, 1, 0], ![4, -6, 2], ![25, -21, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-2, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-2, 1, 0]] 
 ![![47, 0, 0], ![45, 1, 0], ![45, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-2, 1, 0], ![0, -2, 2], ![140, -21, -2]]]
  hmulB := by decide  
  f := ![![![53, -26, 0], ![1222, 0, 0]], ![![51, -25, 0], ![1176, 0, 0]], ![![51, -24, -1], ![1176, 24, 0]]]
  g := ![![![1, 0, 0], ![-45, 47, 0], ![-45, 0, 47]], ![![-1, 1, 0], ![0, -2, 2], ![25, -21, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![8, 1, 0]] ![![47, 0, 0], ![-6, 1, 0]]
  ![![47, 0, 0], ![23, 1, 1]] where
 M := ![![![2209, 0, 0], ![-282, 47, 0]], ![![376, 47, 0], ![-48, 2, 2]]]
 hmul := by decide  
 g := ![![![![24, -1, -1], ![47, 0, 0]], ![![-6, 1, 0], ![0, 0, 0]]], ![![![-15, 0, -1], ![47, 0, 0]], ![![-2, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![23, 1, 1]] ![![47, 0, 0], ![-2, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-94, 47, 0]], ![![1081, 47, 47], ![94, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-2, 1, 0]]], ![![![23, 1, 1]], ![![2, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [4, 14, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 44, 37], [48, 8, 16], [0, 1]]
 g := ![![[46, 40, 49], [17, 1], [37, 13, 4], [22, 52], [1]], ![[35, 15, 43, 9], [32, 9], [18, 17, 10, 44], [35, 44], [27, 4, 4, 38]], ![[34, 29, 19, 38], [40, 16], [49, 0, 34, 15], [50, 49], [8, 28, 23, 15]]]
 h' := ![![[28, 44, 37], [0, 36, 46], [11, 3, 52], [34, 20, 2], [49, 39, 23], [0, 1]], ![[48, 8, 16], [14, 25, 4], [6, 38, 50], [30, 8, 14], [8, 9, 37], [28, 44, 37]], ![[0, 1], [10, 45, 3], [8, 12, 4], [16, 25, 37], [2, 5, 46], [48, 8, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [36, 20, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [4, 14, 30, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-371371, 115010, -14151]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7007, 2170, -267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [40, 4, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 48, 25], [13, 10, 34], [0, 1]]
 g := ![![[45, 43, 1], [28, 6, 57], [15, 19], [9, 2, 53], [1]], ![[33, 24, 51, 45], [58, 15, 10, 45], [16, 27], [21, 55, 42, 49], [25, 54, 18, 49]], ![[3, 35, 25, 44], [12, 58, 4, 38], [25, 26], [2, 4, 56, 52], [44, 46, 54, 10]]]
 h' := ![![[29, 48, 25], [1, 29, 58], [26, 16, 36], [53, 9, 45], [19, 55, 42], [0, 1]], ![[13, 10, 34], [44, 30, 7], [13, 4, 52], [57, 8, 26], [25, 18, 25], [29, 48, 25]], ![[0, 1], [10, 0, 53], [30, 39, 30], [33, 42, 47], [24, 45, 51], [13, 10, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 42], []]
 b := ![[], [55, 22, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [40, 4, 17, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3540, 1711, -1062]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![60, 29, -18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![32, 6, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![32, 6, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![32, 6, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![32, 6, 1], ![140, 11, 12], ![840, -56, 11]]]
  hmulB := by decide  
  f := ![![![-31, -6, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -6, 61]], ![![0, 0, 1], ![-4, -1, 12], ![8, -2, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [21, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 60], [0, 1]]
 g := ![![[22, 25], [27], [3, 25], [33, 12], [26, 1]], ![[1, 36], [27], [43, 36], [40, 49], [52, 60]]]
 h' := ![![[26, 60], [47, 5], [59, 37], [39, 5], [3, 45], [0, 1]], ![[0, 1], [55, 56], [45, 24], [47, 56], [14, 16], [26, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [46, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [21, 35, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5377, -25, 738]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-299, -73, 738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-12, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-12, 1, 0]] 
 ![![61, 0, 0], ![49, 1, 0], ![50, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-12, 1, 0], ![0, -12, 2], ![140, -21, -12]]]
  hmulB := by decide  
  f := ![![![697, -58, 0], ![3538, 0, 0]], ![![565, -47, 0], ![2868, 0, 0]], ![![578, -42, -1], ![2934, 31, 0]]]
  g := ![![![1, 0, 0], ![-49, 61, 0], ![-50, 0, 61]], ![![-1, 1, 0], ![8, -12, 2], ![29, -21, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![32, 6, 1]] ![![61, 0, 0], ![-12, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-732, 61, 0]], ![![1952, 366, 61], ![-244, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-12, 1, 0]]], ![![![32, 6, 1]], ![![-4, -1, 0]]]]
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
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [14, 55, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 12, 52], [28, 54, 15], [0, 1]]
 g := ![![[4, 53, 19], [10, 65, 21], [59, 35], [56, 64], [39, 1], []], ![[36, 49, 48, 34], [21, 56, 52, 18], [23, 17], [53, 36], [3, 35], [40, 24]], ![[0, 43, 64, 40], [57, 56, 54, 19], [10, 39], [43, 62], [45, 10], [10, 24]]]
 h' := ![![[11, 12, 52], [61, 6, 32], [40, 33, 17], [53, 9, 54], [57, 52, 59], [0, 0, 1], [0, 1]], ![[28, 54, 15], [15, 63, 30], [42, 29, 21], [30, 30, 34], [54, 40, 61], [30, 6, 54], [11, 12, 52]], ![[0, 1], [0, 65, 5], [53, 5, 29], [40, 28, 46], [46, 42, 14], [41, 61, 12], [28, 54, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 41], []]
 b := ![[], [54, 46, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [14, 55, 28, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49714, 6901, 1876]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-742, 103, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-18, 4, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-18, 4, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![53, 4, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-18, 4, 1], ![140, -39, 8], ![560, -14, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -4, 71]], ![![-1, 0, 1], ![-4, -1, 8], ![37, 2, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [57, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 70], [0, 1]]
 g := ![![[70, 5], [17, 57], [46, 54], [2], [54], [1]], ![[0, 66], [0, 14], [0, 17], [2], [54], [1]]]
 h' := ![![[57, 70], [25, 17], [5, 46], [17, 57], [29, 59], [14, 57], [0, 1]], ![[0, 1], [0, 54], [0, 25], [0, 14], [55, 12], [68, 14], [57, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [67, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [57, 14, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![617, 210, -54]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49, 6, -54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-8, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-8, 1, 0]] 
 ![![71, 0, 0], ![63, 1, 0], ![39, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-8, 1, 0], ![0, -8, 2], ![140, -21, -8]]]
  hmulB := by decide  
  f := ![![![89, -11, 0], ![781, 0, 0]], ![![81, -10, 0], ![711, 0, 0]], ![![57, -3, -1], ![501, 36, 0]]]
  g := ![![![1, 0, 0], ![-63, 71, 0], ![-39, 0, 71]], ![![-1, 1, 0], ![6, -8, 2], ![25, -21, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-18, 4, 1]] ![![71, 0, 0], ![-8, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-568, 71, 0]], ![![-1278, 284, 71], ![284, -71, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-8, 1, 0]]], ![![![-18, 4, 1]], ![![4, -1, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![9, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![9, 1, 0]] 
 ![![73, 0, 0], ![9, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![9, 1, 0], ![0, 9, 2], ![140, -21, 9]]]
  hmulB := by decide  
  f := ![![![442, 49, 0], ![-3577, 0, 0]], ![![54, 6, 0], ![-437, 0, 0]], ![![420, 42, -1], ![-3399, 37, 0]]]
  g := ![![![1, 0, 0], ![-9, 73, 0], ![-69, 0, 73]], ![![0, 1, 0], ![-3, 9, 2], ![-4, -21, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![27, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![27, 1, 0]] 
 ![![73, 0, 0], ![27, 1, 0], ![37, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![27, 1, 0], ![0, 27, 2], ![140, -21, 27]]]
  hmulB := by decide  
  f := ![![![703, 26, 0], ![-1898, 0, 0]], ![![243, 9, 0], ![-656, 0, 0]], ![![343, -1, -1], ![-926, 37, 0]]]
  g := ![![![1, 0, 0], ![-27, 73, 0], ![-37, 0, 73]], ![![0, 1, 0], ![-11, 27, 2], ![-4, -21, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-36, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-36, 1, 0]] 
 ![![73, 0, 0], ![37, 1, 0], ![9, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-36, 1, 0], ![0, -36, 2], ![140, -21, -36]]]
  hmulB := by decide  
  f := ![![![2629, -73, 0], ![5329, 0, 0]], ![![1369, -38, 0], ![2775, 0, 0]], ![![333, 9, -1], ![675, 37, 0]]]
  g := ![![![1, 0, 0], ![-37, 73, 0], ![-9, 0, 73]], ![![-1, 1, 0], ![18, -36, 2], ![17, -21, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![9, 1, 0]] ![![73, 0, 0], ![27, 1, 0]]
  ![![73, 0, 0], ![12, 18, 1]] where
 M := ![![![5329, 0, 0], ![1971, 73, 0]], ![![657, 73, 0], ![243, 36, 2]]]
 hmul := by decide  
 g := ![![![![61, -18, -1], ![73, 0, 0]], ![![15, -17, -1], ![73, 0, 0]]], ![![![-3, -17, -1], ![73, 0, 0]], ![![3, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![12, 18, 1]] ![![73, 0, 0], ![-36, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2628, 73, 0]], ![![876, 1314, 73], ![-292, -657, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-36, 1, 0]]], ![![![12, 18, 1]], ![![-4, -9, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-18, 40, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-18, 40, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![61, 40, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-18, 40, 1], ![140, -39, 80], ![5600, -770, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -40, 79]], ![![-1, 0, 1], ![-60, -41, 80], ![101, 10, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [34, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 78], [0, 1]]
 g := ![![[23, 64], [28, 18], [56, 2], [2, 76], [64], [1]], ![[61, 15], [14, 61], [72, 77], [57, 3], [64], [1]]]
 h' := ![![[8, 78], [75, 71], [71, 27], [11, 9], [7, 47], [45, 8], [0, 1]], ![[0, 1], [11, 8], [50, 52], [4, 70], [67, 32], [30, 71], [8, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [35, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [34, 71, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5420, 370, 266]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-274, -130, 266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-1, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-1, 1, 0]] 
 ![![79, 0, 0], ![78, 1, 0], ![39, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-1, 1, 0], ![0, -1, 2], ![140, -21, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![237, 0, 0]], ![![2, -1, 0], ![80, 0, 0]], ![![2, -1, -1], ![119, 40, 0]]]
  g := ![![![1, 0, 0], ![-78, 79, 0], ![-39, 0, 79]], ![![-1, 1, 0], ![0, -1, 2], ![23, -21, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-18, 40, 1]] ![![79, 0, 0], ![-1, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-79, 79, 0]], ![![-1422, 3160, 79], ![158, -79, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-1, 1, 0]]], ![![![-18, 40, 1]], ![![2, -1, 1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB220I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB220I1 : PrimesBelowBoundCertificateInterval O 31 79 220 where
  m := 11
  g := ![1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB220I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N1, I43N1, I47N0, I47N1, I47N2, I61N1, I71N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [], [], [I61N1], [], [I71N1], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
