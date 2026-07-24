
import IdealArithmetic.Examples.NF3_1_623807_1.RI3_1_623807_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![5, 12, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![5, 12, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![5, 12, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![5, 12, 1], ![152, 17, 23], ![1672, 76, -6]]]
  hmulB := by decide  
  f := ![![![-4, -12, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -12, 37]], ![![0, 0, 1], ![1, -7, 23], ![46, 4, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [18, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[13, 33], [30], [10, 1], [33], [1]], ![[24, 4], [30], [35, 36], [33], [1]]]
 h' := ![![[25, 36], [3, 25], [5, 20], [26, 36], [19, 25], [0, 1]], ![[0, 1], [36, 12], [24, 17], [1, 1], [15, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [18, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![474, 664, -31]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 28, -31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![6, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![0, 15, 2], ![152, 0, 13]]]
  hmulB := by decide  
  f := ![![![85, 6, 0], ![-222, 0, 0]], ![![14, 1, 0], ![-36, 0, 0]], ![![10, -7, -1], ![-26, 19, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-6, 0, 37]], ![![0, 1, 0], ![-6, 15, 2], ![2, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![5, 12, 1]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![185, 444, 37], ![222, 185, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![14, 1, 0]]], ![![![5, 12, 1]], ![![6, 5, 1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![3, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![3, 1, 0]] 
 ![![41, 0, 0], ![3, 1, 0], ![35, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![3, 1, 0], ![0, 4, 2], ![152, 0, 2]]]
  hmulB := by decide  
  f := ![![![31, 10, 0], ![-410, 0, 0]], ![![-3, -1, 0], ![42, 0, 0]], ![![31, 8, -1], ![-412, 21, 0]]]
  g := ![![![1, 0, 0], ![-3, 41, 0], ![-35, 0, 41]], ![![0, 1, 0], ![-2, 4, 2], ![2, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![18, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![0, 15, 2], ![152, 0, 13]]]
  hmulB := by decide  
  f := ![![![15, 1, 0], ![-41, 0, 0]], ![![-14, -1, 0], ![42, 0, 0]], ![![10, -7, -1], ![-28, 21, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-18, 0, 41]], ![![0, 1, 0], ![-6, 15, 2], ![-2, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-17, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-17, 1, 0]] 
 ![![41, 0, 0], ![24, 1, 0], ![28, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-17, 1, 0], ![0, -16, 2], ![152, 0, -18]]]
  hmulB := by decide  
  f := ![![![562, -33, 0], ![1353, 0, 0]], ![![324, -19, 0], ![780, 0, 0]], ![![378, -14, -1], ![910, 21, 0]]]
  g := ![![![1, 0, 0], ![-24, 41, 0], ![-28, 0, 41]], ![![-1, 1, 0], ![8, -16, 2], ![16, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![3, 1, 0]] ![![41, 0, 0], ![14, 1, 0]]
  ![![41, 0, 0], ![-20, 9, 1]] where
 M := ![![![1681, 0, 0], ![574, 41, 0]], ![![123, 41, 0], ![42, 18, 2]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-20, 9, 1]] ![![41, 0, 0], ![-17, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-697, 41, 0]], ![![-820, 369, 41], ![492, -164, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-17, 1, 0]]], ![![![-20, 9, 1]], ![![12, -4, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![8, 10, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![8, 10, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![8, 10, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![8, 10, 1], ![152, 18, 19], ![1368, 76, -1]]]
  hmulB := by decide  
  f := ![![![-7, -10, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -10, 43]], ![![0, 0, 1], ![0, -4, 19], ![32, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [26, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 42], [0, 1]]
 g := ![![[22, 13], [40, 21], [41], [27, 40], [1]], ![[25, 30], [25, 22], [41], [23, 3], [1]]]
 h' := ![![[30, 42], [35, 23], [33, 8], [29, 16], [17, 30], [0, 1]], ![[0, 1], [37, 20], [15, 35], [36, 27], [14, 13], [30, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [17, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [26, 13, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1202, 1228, 54]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38, 16, 54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![1, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![0, -18, 2], ![152, 0, -20]]]
  hmulB := by decide  
  f := ![![![685, -36, 0], ![1548, 0, 0]], ![![400, -21, 0], ![904, 0, 0]], ![![23, 8, -1], ![52, 22, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-1, 0, 43]], ![![-1, 1, 0], ![10, -18, 2], ![4, 0, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![8, 10, 1]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![344, 430, 43], ![0, -172, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-19, 1, 0]]], ![![![8, 10, 1]], ![![0, -4, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![19, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![19, 1, 0]] 
 ![![47, 0, 0], ![19, 1, 0], ![45, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![19, 1, 0], ![0, 20, 2], ![152, 0, 18]]]
  hmulB := by decide  
  f := ![![![20, 1, 0], ![-47, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![24, -9, -1], ![-57, 24, 0]]]
  g := ![![![1, 0, 0], ![-19, 47, 0], ![-45, 0, 47]], ![![0, 1, 0], ![-10, 20, 2], ![-14, 0, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-13, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-13, 1, 0]] 
 ![![47, 0, 0], ![34, 1, 0], ![16, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-13, 1, 0], ![0, -12, 2], ![152, 0, -14]]]
  hmulB := by decide  
  f := ![![![404, -31, 0], ![1457, 0, 0]], ![![300, -23, 0], ![1082, 0, 0]], ![![132, -4, -1], ![476, 24, 0]]]
  g := ![![![1, 0, 0], ![-34, 47, 0], ![-16, 0, 47]], ![![-1, 1, 0], ![8, -12, 2], ![8, 0, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-6, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-6, 1, 0]] 
 ![![47, 0, 0], ![41, 1, 0], ![32, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-6, 1, 0], ![0, -5, 2], ![152, 0, -7]]]
  hmulB := by decide  
  f := ![![![73, -12, 0], ![564, 0, 0]], ![![67, -11, 0], ![518, 0, 0]], ![![52, -6, -1], ![402, 24, 0]]]
  g := ![![![1, 0, 0], ![-41, 47, 0], ![-32, 0, 47]], ![![-1, 1, 0], ![3, -5, 2], ![8, 0, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![19, 1, 0]] ![![47, 0, 0], ![-13, 1, 0]]
  ![![47, 0, 0], ![-6, -20, 1]] where
 M := ![![![2209, 0, 0], ![-611, 47, 0]], ![![893, 47, 0], ![-247, 7, 2]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![-7, 21, -1], ![47, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![-5, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-6, -20, 1]] ![![47, 0, 0], ![-6, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-282, 47, 0]], ![![-282, -940, 47], ![188, 94, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-6, 1, 0]]], ![![![-6, -20, 1]], ![![4, 2, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![12, -2, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![12, -2, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![12, 51, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![12, -2, 1], ![152, 10, -5], ![-456, 76, 15]]]
  hmulB := by decide  
  f := ![![![-11, 2, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -51, 53]], ![![0, -1, 1], ![4, 5, -5], ![-12, -13, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [34, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 52], [0, 1]]
 g := ![![[47, 36], [47], [6, 16], [52], [45, 1]], ![[24, 17], [47], [37, 37], [52], [37, 52]]]
 h' := ![![[45, 52], [3, 47], [8, 43], [30, 4], [7, 30], [0, 1]], ![[0, 1], [51, 6], [35, 10], [51, 49], [32, 23], [45, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [6, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [34, 8, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3466, 76, 121]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, -115, 121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![5, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![5, 1, 0]] 
 ![![53, 0, 0], ![5, 1, 0], ![38, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![5, 1, 0], ![0, 6, 2], ![152, 0, 4]]]
  hmulB := by decide  
  f := ![![![151, 30, 0], ![-1590, 0, 0]], ![![5, 1, 0], ![-52, 0, 0]], ![![106, 18, -1], ![-1116, 27, 0]]]
  g := ![![![1, 0, 0], ![-5, 53, 0], ![-38, 0, 53]], ![![0, 1, 0], ![-2, 6, 2], ![0, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![12, -2, 1]] ![![53, 0, 0], ![5, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![265, 53, 0]], ![![636, -106, 53], ![212, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![5, 1, 0]]], ![![![12, -2, 1]], ![![4, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-27, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-27, 1, 0]] 
 ![![59, 0, 0], ![32, 1, 0], ![3, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-27, 1, 0], ![0, -26, 2], ![152, 0, -28]]]
  hmulB := by decide  
  f := ![![![1162, -43, 0], ![2537, 0, 0]], ![![622, -23, 0], ![1358, 0, 0]], ![![60, 11, -1], ![131, 30, 0]]]
  g := ![![![1, 0, 0], ![-32, 59, 0], ![-3, 0, 59]], ![![-1, 1, 0], ![14, -26, 2], ![4, 0, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-16, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-16, 1, 0]] 
 ![![59, 0, 0], ![43, 1, 0], ![57, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-16, 1, 0], ![0, -15, 2], ![152, 0, -17]]]
  hmulB := by decide  
  f := ![![![17, 659, -88], ![59, 2596, 0]], ![![17, 479, -64], ![60, 1888, 0]], ![![11, 637, -85], ![37, 2508, 0]]]
  g := ![![![1, 0, 0], ![-43, 59, 0], ![-57, 0, 59]], ![![-1, 1, 0], ![9, -15, 2], ![19, 0, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-27, 1, 0]] ![![59, 0, 0], ![-16, 1, 0]]
  ![![59, 0, 0], ![-20, -21, 1]] where
 M := ![![![3481, 0, 0], ![-944, 59, 0]], ![![-1593, 59, 0], ![432, -42, 2]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![4, 22, -1], ![59, 0, 0]]], ![![![-7, 22, -1], ![59, 0, 0]], ![![8, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-20, -21, 1]] ![![59, 0, 0], ![-16, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-944, 59, 0]], ![![-1180, -1239, 59], ![472, 295, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-16, 1, 0]]], ![![![-20, -21, 1]], ![![8, 5, -1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-23, -28, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-23, -28, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![38, 33, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-23, -28, 1], ![152, -51, -57], ![-4408, 76, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -33, 61]], ![![-1, -1, 1], ![38, 30, -57], ![-76, -2, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [55, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 60], [0, 1]]
 g := ![![[16, 48], [15], [26, 15], [10, 60], [35, 1]], ![[49, 13], [15], [2, 46], [36, 1], [9, 60]]]
 h' := ![![[35, 60], [26, 29], [34, 25], [60, 36], [27, 11], [0, 1]], ![[0, 1], [4, 32], [55, 36], [39, 25], [46, 50], [35, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [58, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [55, 26, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-678, 1848, -127]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68, 99, -127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-4, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-4, 1, 0]] 
 ![![61, 0, 0], ![57, 1, 0], ![55, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-4, 1, 0], ![0, -3, 2], ![152, 0, -5]]]
  hmulB := by decide  
  f := ![![![193, -48, 0], ![2928, 0, 0]], ![![181, -45, 0], ![2746, 0, 0]], ![![171, -41, -1], ![2594, 31, 0]]]
  g := ![![![1, 0, 0], ![-57, 61, 0], ![-55, 0, 61]], ![![-1, 1, 0], ![1, -3, 2], ![7, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-23, -28, 1]] ![![61, 0, 0], ![-4, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-244, 61, 0]], ![![-1403, -1708, 61], ![244, 61, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-4, 1, 0]]], ![![![-23, -28, 1]], ![![4, 1, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![14, -18, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![14, -18, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![14, 49, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![14, -18, 1], ![152, -4, -37], ![-2888, 76, 33]]]
  hmulB := by decide  
  f := ![![![-13, 18, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -49, 67]], ![![0, -1, 1], ![10, 27, -37], ![-50, -23, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [2, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 66], [0, 1]]
 g := ![![[56, 25], [18, 9], [33], [6], [15], [1]], ![[3, 42], [15, 58], [33], [6], [15], [1]]]
 h' := ![![[22, 66], [31, 5], [37, 3], [61, 10], [41, 41], [65, 22], [0, 1]], ![[0, 1], [7, 62], [36, 64], [13, 57], [5, 26], [13, 45], [22, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [51, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [2, 45, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![458, 598, -130]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, 104, -130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-30, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-30, 1, 0]] 
 ![![67, 0, 0], ![37, 1, 0], ![34, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-30, 1, 0], ![0, -29, 2], ![152, 0, -31]]]
  hmulB := by decide  
  f := ![![![1501, -50, 0], ![3350, 0, 0]], ![![871, -29, 0], ![1944, 0, 0]], ![![802, -12, -1], ![1790, 34, 0]]]
  g := ![![![1, 0, 0], ![-37, 67, 0], ![-34, 0, 67]], ![![-1, 1, 0], ![15, -29, 2], ![18, 0, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![14, -18, 1]] ![![67, 0, 0], ![-30, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2010, 67, 0]], ![![938, -1206, 67], ![-268, 536, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-30, 1, 0]]], ![![![14, -18, 1]], ![![-4, 8, -1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![28, -12, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![28, -12, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![28, 59, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![28, -12, 1], ![152, 16, -25], ![-1976, 76, 41]]]
  hmulB := by decide  
  f := ![![![-27, 12, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -59, 71]], ![![0, -1, 1], ![12, 21, -25], ![-44, -33, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [67, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 70], [0, 1]]
 g := ![![[22, 16], [30, 43], [26, 38], [64], [5], [1]], ![[10, 55], [51, 28], [33, 33], [64], [5], [1]]]
 h' := ![![[17, 70], [49, 67], [33, 55], [61, 31], [36, 8], [4, 17], [0, 1]], ![[0, 1], [52, 4], [45, 16], [20, 40], [30, 63], [9, 54], [17, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [38, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [67, 54, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60770, 35036, 1577]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![234, -817, 1577]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![25, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![25, 1, 0]] 
 ![![71, 0, 0], ![25, 1, 0], ![30, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![25, 1, 0], ![0, 26, 2], ![152, 0, 24]]]
  hmulB := by decide  
  f := ![![![801, 32, 0], ![-2272, 0, 0]], ![![275, 11, 0], ![-780, 0, 0]], ![![330, 0, -1], ![-936, 36, 0]]]
  g := ![![![1, 0, 0], ![-25, 71, 0], ![-30, 0, 71]], ![![0, 1, 0], ![-10, 26, 2], ![-8, 0, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![28, -12, 1]] ![![71, 0, 0], ![25, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1775, 71, 0]], ![![1988, -852, 71], ![852, -284, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![25, 1, 0]]], ![![![28, -12, 1]], ![![12, -4, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![33, -16, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![33, -16, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![33, 57, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![33, -16, 1], ![152, 17, -33], ![-2584, 76, 50]]]
  hmulB := by decide  
  f := ![![![-32, 16, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -57, 73]], ![![0, -1, 1], ![17, 26, -33], ![-58, -38, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [8, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 72], [0, 1]]
 g := ![![[62, 64], [46], [70], [39, 16], [6], [1]], ![[0, 9], [46], [70], [60, 57], [6], [1]]]
 h' := ![![[15, 72], [47, 65], [59, 51], [53, 56], [16, 69], [65, 15], [0, 1]], ![[0, 1], [0, 8], [21, 22], [17, 17], [29, 4], [71, 58], [15, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [64, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [8, 58, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![407, 192, 61]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -45, 61]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![33, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![33, 1, 0]] 
 ![![73, 0, 0], ![33, 1, 0], ![23, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![33, 1, 0], ![0, 34, 2], ![152, 0, 32]]]
  hmulB := by decide  
  f := ![![![364, 11, 0], ![-803, 0, 0]], ![![132, 4, 0], ![-291, 0, 0]], ![![74, -15, -1], ![-163, 37, 0]]]
  g := ![![![1, 0, 0], ![-33, 73, 0], ![-23, 0, 73]], ![![0, 1, 0], ![-16, 34, 2], ![-8, 0, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![33, -16, 1]] ![![73, 0, 0], ![33, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2409, 73, 0]], ![![2409, -1168, 73], ![1241, -511, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![33, 1, 0]]], ![![![33, -16, 1]], ![![17, -7, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-18, 27, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-18, 27, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![61, 27, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-18, 27, 1], ![152, 9, 53], ![3952, 76, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -27, 79]], ![![-1, 0, 1], ![-39, -18, 53], ![84, 16, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [48, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 78], [0, 1]]
 g := ![![[48, 45], [45, 51], [75, 72], [69, 1], [11], [1]], ![[16, 34], [14, 28], [8, 7], [56, 78], [11], [1]]]
 h' := ![![[66, 78], [52, 19], [34, 29], [6, 25], [38, 78], [31, 66], [0, 1]], ![[0, 1], [42, 60], [52, 50], [76, 54], [51, 1], [42, 13], [66, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [4, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [48, 13, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![808, 1948, 78]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, -2, 78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![26, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![26, 1, 0]] 
 ![![79, 0, 0], ![26, 1, 0], ![44, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![26, 1, 0], ![0, 27, 2], ![152, 0, 25]]]
  hmulB := by decide  
  f := ![![![1301, 50, 0], ![-3950, 0, 0]], ![![442, 17, 0], ![-1342, 0, 0]], ![![720, 14, -1], ![-2186, 40, 0]]]
  g := ![![![1, 0, 0], ![-26, 79, 0], ![-44, 0, 79]], ![![0, 1, 0], ![-10, 27, 2], ![-12, 0, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-18, 27, 1]] ![![79, 0, 0], ![26, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2054, 79, 0]], ![![-1422, 2133, 79], ![-316, 711, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![26, 1, 0]]], ![![![-18, 27, 1]], ![![-4, 9, 1]]]]
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


lemma PB224I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB224I1 : PrimesBelowBoundCertificateInterval O 31 79 224 where
  m := 11
  g := ![2, 3, 2, 3, 2, 3, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB224I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
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
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I47N0, I47N1, I47N2, I53N1, I59N0, I59N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N0, I47N1, I47N2], [I53N1], [I59N0, I59N1, I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
