
import IdealArithmetic.Examples.NF3_1_936091_1.RI3_1_936091_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [31, 4, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10, 36], [31, 26, 1], [0, 1]]
 g := ![![[32, 31, 21], [34, 28], [3, 34, 9], [1, 1], []], ![[30, 33, 15, 3], [1, 12], [6, 0, 9, 1], [10, 10], [18, 1]], ![[34, 29, 1, 27], [1, 10], [33, 28, 15, 7], [26, 26], [16, 1]]]
 h' := ![![[7, 10, 36], [10, 26, 13], [18, 6, 19], [6, 2, 34], [0, 0, 1], [0, 1]], ![[31, 26, 1], [13, 1, 16], [9, 23, 7], [30, 20, 31], [9, 0, 26], [7, 10, 36]], ![[0, 1], [16, 10, 8], [11, 8, 11], [5, 15, 9], [21, 0, 10], [31, 26, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 21], []]
 b := ![[], [13, 35, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [31, 4, 36, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40515, 1221, 1221]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1095, 33, 33]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![8, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![8, 1, 0]] 
 ![![41, 0, 0], ![8, 1, 0], ![18, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![8, 1, 0], ![0, 8, 1], ![-194, 17, 9]]]
  hmulB := by decide  
  f := ![![![193, 24, 0], ![-984, 0, 0]], ![![24, 3, 0], ![-122, 0, 0]], ![![82, 10, 0], ![-418, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 41, 0], ![-18, 0, 41]], ![![0, 1, 0], ![-2, 8, 1], ![-12, 17, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 1, 0]] 
 ![![41, 0, 0], ![34, 1, 0], ![33, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 1, 0], ![0, -7, 1], ![-194, 17, -6]]]
  hmulB := by decide  
  f := ![![![57, -8, 0], ![328, 0, 0]], ![![50, -7, 0], ![288, 0, 0]], ![![51, -7, 0], ![294, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 41, 0], ![-33, 0, 41]], ![![-1, 1, 0], ![5, -7, 1], ![-14, 17, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-2, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-2, 1, 0]] 
 ![![41, 0, 0], ![39, 1, 0], ![37, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-2, 1, 0], ![0, -2, 1], ![-194, 17, -1]]]
  hmulB := by decide  
  f := ![![![47, -23, 0], ![943, 0, 0]], ![![45, -22, 0], ![903, 0, 0]], ![![43, -21, 0], ![863, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 41, 0], ![-37, 0, 41]], ![![-1, 1, 0], ![1, -2, 1], ![-20, 17, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![8, 1, 0]] ![![41, 0, 0], ![-7, 1, 0]]
  ![![41, 0, 0], ![-15, 1, 1]] where
 M := ![![![1681, 0, 0], ![-287, 41, 0]], ![![328, 41, 0], ![-56, 1, 1]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![8, 0, -1], ![41, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-15, 1, 1]] ![![41, 0, 0], ![-2, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-82, 41, 0]], ![![-615, 41, 41], ![-164, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-2, 1, 0]]], ![![![-15, 1, 1]], ![![-4, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-30, -6, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-30, -6, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![13, 37, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-30, -6, 1], ![-194, -13, -5], ![970, -279, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -37, 43]], ![![-1, -1, 1], ![-3, 4, -5], ![28, 9, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [13, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 42], [0, 1]]
 g := ![![[12, 10], [35, 4], [6], [25, 41], [1]], ![[0, 33], [13, 39], [6], [36, 2], [1]]]
 h' := ![![[16, 42], [18, 15], [25, 2], [19, 36], [30, 16], [0, 1]], ![[0, 1], [0, 28], [14, 41], [36, 7], [28, 27], [16, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [22, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [13, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![569, -1847, 229]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -240, 229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![5, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![5, 1, 0]] 
 ![![43, 0, 0], ![5, 1, 0], ![18, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![5, 1, 0], ![0, 5, 1], ![-194, 17, 6]]]
  hmulB := by decide  
  f := ![![![111, 22, 0], ![-946, 0, 0]], ![![5, 1, 0], ![-42, 0, 0]], ![![46, 9, 0], ![-392, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 43, 0], ![-18, 0, 43]], ![![0, 1, 0], ![-1, 5, 1], ![-9, 17, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-30, -6, 1]] ![![43, 0, 0], ![5, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![215, 43, 0]], ![![-1290, -258, 43], ![-344, -43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![5, 1, 0]]], ![![![-30, -6, 1]], ![![-8, -1, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [26, 3, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 30, 26], [41, 16, 21], [0, 1]]
 g := ![![[41, 10, 16], [6, 43, 4], [14, 35, 34], [31, 9, 1], []], ![[5, 28, 39, 33], [45, 27, 9, 5], [22, 7, 16, 10], [11, 45, 4, 29], [30, 18]], ![[16, 36, 1, 25], [26, 40, 10, 9], [31, 8, 36, 42], [18, 12, 1, 6], [35, 18]]]
 h' := ![![[15, 30, 26], [32, 42, 4], [12, 37, 2], [40, 2, 38], [0, 0, 1], [0, 1]], ![[41, 16, 21], [40, 43, 28], [21, 8, 7], [36, 37, 2], [9, 13, 16], [15, 30, 26]], ![[0, 1], [44, 9, 15], [16, 2, 38], [45, 8, 7], [19, 34, 30], [41, 16, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 22], []]
 b := ![[], [2, 28, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [26, 3, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-177472, 47000, -10528]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3776, 1000, -224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![2, 8, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![2, 8, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![2, 8, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![2, 8, 1], ![-194, 19, 9], ![-1746, -41, 28]]]
  hmulB := by decide  
  f := ![![![-1, -8, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -8, 53]], ![![0, 0, 1], ![-4, -1, 9], ![-34, -5, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [5, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 52], [0, 1]]
 g := ![![[16, 11], [40], [40, 10], [6], [26, 1]], ![[37, 42], [40], [35, 43], [6], [52, 52]]]
 h' := ![![[26, 52], [50, 45], [12, 27], [16, 13], [29, 35], [0, 1]], ![[0, 1], [1, 8], [25, 26], [36, 40], [38, 18], [26, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [49, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [5, 27, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-549, -1666, 70]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, -42, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-9, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-9, 1, 0]] 
 ![![53, 0, 0], ![44, 1, 0], ![25, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-9, 1, 0], ![0, -9, 1], ![-194, 17, -8]]]
  hmulB := by decide  
  f := ![![![73, -8, 0], ![424, 0, 0]], ![![64, -7, 0], ![372, 0, 0]], ![![47, -5, 0], ![274, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 53, 0], ![-25, 0, 53]], ![![-1, 1, 0], ![7, -9, 1], ![-14, 17, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![2, 8, 1]] ![![53, 0, 0], ![-9, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-477, 53, 0]], ![![106, 424, 53], ![-212, -53, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-9, 1, 0]]], ![![![2, 8, 1]], ![![-4, -1, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![28, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![28, 1, 0]] 
 ![![59, 0, 0], ![28, 1, 0], ![42, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![28, 1, 0], ![0, 28, 1], ![-194, 17, 29]]]
  hmulB := by decide  
  f := ![![![365, 13, 0], ![-767, 0, 0]], ![![140, 5, 0], ![-294, 0, 0]], ![![238, 8, 0], ![-500, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 59, 0], ![-42, 0, 59]], ![![0, 1, 0], ![-14, 28, 1], ![-32, 17, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-28, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-28, 1, 0]] 
 ![![59, 0, 0], ![31, 1, 0], ![42, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-28, 1, 0], ![0, -28, 1], ![-194, 17, -27]]]
  hmulB := by decide  
  f := ![![![813, -29, 0], ![1711, 0, 0]], ![![449, -16, 0], ![945, 0, 0]], ![![630, -22, 0], ![1326, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 59, 0], ![-42, 0, 59]], ![![-1, 1, 0], ![14, -28, 1], ![7, 17, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-1, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-1, 1, 0]] 
 ![![59, 0, 0], ![58, 1, 0], ![58, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-1, 1, 0], ![0, -1, 1], ![-194, 17, 0]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![177, 0, 0]], ![![2, -1, 0], ![60, 0, 0]], ![![2, -1, 0], ![60, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 59, 0], ![-58, 0, 59]], ![![-1, 1, 0], ![0, -1, 1], ![-20, 17, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![28, 1, 0]] ![![59, 0, 0], ![-28, 1, 0]]
  ![![59, 0, 0], ![-17, 0, 1]] where
 M := ![![![3481, 0, 0], ![-1652, 59, 0]], ![![1652, 59, 0], ![-784, 0, 1]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![-11, 1, -1], ![59, 0, 0]]], ![![![28, 1, 0], ![0, 0, 0]], ![![4, 0, -1], ![60, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-17, 0, 1]] ![![59, 0, 0], ![-1, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-59, 59, 0]], ![![-1003, 0, 59], ![-177, 0, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-1, 1, 0]]], ![![![-17, 0, 1]], ![![-3, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [42, 5, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 47], [22, 13], [0, 1]]
 g := ![![[13, 39, 1], [31, 14], [35, 33, 36], [60, 3, 15], [1]], ![[17, 41, 13], [12, 48], [31, 52, 41], [21, 40, 12], [1]], ![[13, 42, 47], [34, 60], [7, 37, 45], [5, 18, 34], [1]]]
 h' := ![![[3, 47], [15, 54, 60], [55, 20, 21], [42, 57, 55], [19, 56, 25], [0, 1]], ![[22, 13], [46, 60, 48], [60, 30, 29], [37, 11, 44], [46, 44, 20], [3, 47]], ![[0, 1], [48, 8, 14], [45, 11, 11], [39, 54, 23], [53, 22, 16], [22, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25], []]
 b := ![[], [57, 40, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [42, 5, 36, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40504, 1220, 1220]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-664, 20, 20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![12, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![12, 1, 0]] 
 ![![67, 0, 0], ![12, 1, 0], ![57, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![12, 1, 0], ![0, 12, 1], ![-194, 17, 13]]]
  hmulB := by decide  
  f := ![![![265, 22, 0], ![-1474, 0, 0]], ![![36, 3, 0], ![-200, 0, 0]], ![![243, 20, 0], ![-1352, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 67, 0], ![-57, 0, 67]], ![![0, 1, 0], ![-3, 12, 1], ![-17, 17, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![16, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![16, 1, 0]] 
 ![![67, 0, 0], ![16, 1, 0], ![12, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![16, 1, 0], ![0, 16, 1], ![-194, 17, 17]]]
  hmulB := by decide  
  f := ![![![273, 17, 0], ![-1139, 0, 0]], ![![48, 3, 0], ![-200, 0, 0]], ![![36, 2, 0], ![-150, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 67, 0], ![-12, 0, 67]], ![![0, 1, 0], ![-4, 16, 1], ![-10, 17, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-29, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-29, 1, 0]] 
 ![![67, 0, 0], ![38, 1, 0], ![30, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-29, 1, 0], ![0, -29, 1], ![-194, 17, -28]]]
  hmulB := by decide  
  f := ![![![1480, -51, 0], ![3417, 0, 0]], ![![842, -29, 0], ![1944, 0, 0]], ![![680, -23, 0], ![1570, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 67, 0], ![-30, 0, 67]], ![![-1, 1, 0], ![16, -29, 1], ![0, 17, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![12, 1, 0]] ![![67, 0, 0], ![16, 1, 0]]
  ![![67, 0, 0], ![-9, 28, 1]] where
 M := ![![![4489, 0, 0], ![1072, 67, 0]], ![![804, 67, 0], ![192, 28, 1]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![16, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-9, 28, 1]] ![![67, 0, 0], ![-29, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1943, 67, 0]], ![![-603, 1876, 67], ![67, -804, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-29, 1, 0]]], ![![![-9, 28, 1]], ![![1, -12, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![5, 17, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![5, 17, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![5, 17, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![5, 17, 1], ![-194, 22, 18], ![-3492, 112, 40]]]
  hmulB := by decide  
  f := ![![![-4, -17, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -17, 71]], ![![0, 0, 1], ![-4, -4, 18], ![-52, -8, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [30, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 70], [0, 1]]
 g := ![![[44, 45], [43, 48], [], [], [60], [1]], ![[0, 26], [15, 23], [], [], [60], [1]]]
 h' := ![![[29, 70], [59, 20], [0, 30], [32], [23], [41, 29], [0, 1]], ![[0, 1], [0, 51], [18, 41], [32], [23], [30, 42], [29, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [22, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [30, 42, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7493, 1305, 461]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-138, -92, 461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-18, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-18, 1, 0]] 
 ![![71, 0, 0], ![53, 1, 0], ![31, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-18, 1, 0], ![0, -18, 1], ![-194, 17, -17]]]
  hmulB := by decide  
  f := ![![![109, -6, 0], ![426, 0, 0]], ![![91, -5, 0], ![356, 0, 0]], ![![77, -4, 0], ![302, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 71, 0], ![-31, 0, 71]], ![![-1, 1, 0], ![13, -18, 1], ![-8, 17, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![5, 17, 1]] ![![71, 0, 0], ![-18, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1278, 71, 0]], ![![355, 1207, 71], ![-284, -284, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-18, 1, 0]]], ![![![5, 17, 1]], ![![-4, -4, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [20, 64, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 23, 55], [37, 49, 18], [0, 1]]
 g := ![![[62, 34, 72], [39, 2], [59, 65], [55, 55, 49], [38, 1], []], ![[38, 60, 40, 38], [20, 61], [69, 72], [29, 23, 62, 67], [22, 65], [23, 32]], ![[58, 25, 8, 37], [68, 49], [58, 46], [48, 40, 63, 24], [17, 18], [60, 32]]]
 h' := ![![[1, 23, 55], [46, 50, 27], [13, 4, 41], [68, 3, 24], [43, 30, 66], [0, 0, 1], [0, 1]], ![[37, 49, 18], [40, 45, 58], [32, 66, 39], [5, 52, 27], [1, 41, 66], [52, 51, 49], [1, 23, 55]], ![[0, 1], [35, 51, 61], [9, 3, 66], [1, 18, 22], [43, 2, 14], [23, 22, 23], [37, 49, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 37], []]
 b := ![[], [36, 40, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [20, 64, 35, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31244, 3504, -1168]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-428, 48, -16]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 8, -1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-39, 8, -1]] 
 ![![79, 0, 0], ![0, 79, 0], ![39, 71, 1]] where
  M :=![![![-39, 8, -1], ![194, -56, 7], ![-1358, 313, -49]]]
  hmulB := by decide  
  f := ![![![-7, -1, 0]], ![![0, -7, -1]], ![![-1, -7, -1]]]
  g := ![![![0, 1, -1], ![-1, -7, 7], ![7, 48, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [32, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 78], [0, 1]]
 g := ![![[50, 42], [76, 67], [40, 2], [24, 25], [5], [1]], ![[0, 37], [0, 12], [0, 77], [77, 54], [5], [1]]]
 h' := ![![[59, 78], [17, 68], [63, 15], [22, 9], [74, 74], [47, 59], [0, 1]], ![[0, 1], [0, 11], [0, 64], [0, 70], [16, 5], [52, 20], [59, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [22, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [32, 20, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1520, -620, 117]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -113, 117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![7, 1, 0]] 
 ![![79, 0, 0], ![7, 1, 0], ![30, 0, 1]] where
  M :=![![![7, 1, 0], ![0, 7, 1], ![-194, 17, 8]]]
  hmulB := by decide  
  f := ![![![39, -8, 1]], ![![1, 0, 0]], ![![32, -7, 1]]]
  g := ![![![0, 1, 0], ![-1, 7, 1], ![-7, 17, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-39, 8, -1]] ![![7, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB274I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB274I1 : PrimesBelowBoundCertificateInterval O 31 79 274 where
  m := 11
  g := ![1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB274I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![389017]
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
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
      exact NI79N1
  β := ![I41N0, I41N1, I41N2, I43N1, I53N1, I59N0, I59N1, I59N2, I67N0, I67N1, I67N2, I71N1, I79N1]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N1], [], [I53N1], [I59N0, I59N1, I59N2], [], [I67N0, I67N1, I67N2], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
