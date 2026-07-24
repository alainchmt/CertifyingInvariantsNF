
import IdealArithmetic.Examples.NF3_1_817452_1.RI3_1_817452_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-16, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-16, 1, 0]] 
 ![![37, 0, 0], ![21, 1, 0], ![3, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-16, 1, 0], ![0, -16, 1], ![174, 0, -16]]]
  hmulB := by decide  
  f := ![![![209, -13, 0], ![481, 0, 0]], ![![129, -8, 0], ![297, 0, 0]], ![![23, -1, 0], ![53, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 37, 0], ![-3, 0, 37]], ![![-1, 1, 0], ![9, -16, 1], ![6, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, 1, 0]] 
 ![![37, 0, 0], ![25, 1, 0], ![4, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, 1, 0], ![0, -12, 1], ![174, 0, -12]]]
  hmulB := by decide  
  f := ![![![433, -36, 0], ![1332, 0, 0]], ![![301, -25, 0], ![926, 0, 0]], ![![52, -4, 0], ![160, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 37, 0], ![-4, 0, 37]], ![![-1, 1, 0], ![8, -12, 1], ![6, 0, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-9, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-9, 1, 0]] 
 ![![37, 0, 0], ![28, 1, 0], ![30, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-9, 1, 0], ![0, -9, 1], ![174, 0, -9]]]
  hmulB := by decide  
  f := ![![![316, -35, 0], ![1295, 0, 0]], ![![244, -27, 0], ![1000, 0, 0]], ![![264, -29, 0], ![1082, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 37, 0], ![-30, 0, 37]], ![![-1, 1, 0], ![6, -9, 1], ![12, 0, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-16, 1, 0]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![37, 0, 0], ![7, 9, 1]] where
 M := ![![![1369, 0, 0], ![-444, 37, 0]], ![![-592, 37, 0], ![192, -28, 1]]]
 hmul := by decide  
 g := ![![![![30, -9, -1], ![37, 0, 0]], ![![-12, 1, 0], ![0, 0, 0]]], ![![![-16, 1, 0], ![0, 0, 0]], ![![5, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![7, 9, 1]] ![![37, 0, 0], ![-9, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-333, 37, 0]], ![![259, 333, 37], ![111, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-9, 1, 0]]], ![![![7, 9, 1]], ![![3, -2, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-4, 18, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-4, 18, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![37, 18, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-4, 18, 1], ![174, -4, 18], ![3132, 174, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -18, 41]], ![![-1, 0, 1], ![-12, -8, 18], ![80, 6, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 40], [0, 1]]
 g := ![![[34, 21], [31], [10], [23, 32], [1]], ![[0, 20], [31], [10], [20, 9], [1]]]
 h' := ![![[14, 40], [4, 29], [5, 21], [36, 16], [39, 14], [0, 1]], ![[0, 1], [0, 12], [12, 20], [14, 25], [30, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [4, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 27, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![350, 147, -26]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, 15, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-18, 1, 0]] 
 ![![41, 0, 0], ![23, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-18, 1, 0], ![0, -18, 1], ![174, 0, -18]]]
  hmulB := by decide  
  f := ![![![433, -24, 0], ![984, 0, 0]], ![![235, -13, 0], ![534, 0, 0]], ![![44, -2, 0], ![100, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 41, 0], ![-4, 0, 41]], ![![-1, 1, 0], ![10, -18, 1], ![6, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-4, 18, 1]] ![![41, 0, 0], ![-18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-738, 41, 0]], ![![-164, 738, 41], ![246, -328, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-18, 1, 0]]], ![![![-4, 18, 1]], ![![6, -8, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![9, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![9, 1, 0]] 
 ![![43, 0, 0], ![9, 1, 0], ![5, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![9, 1, 0], ![0, 9, 1], ![174, 0, 9]]]
  hmulB := by decide  
  f := ![![![163, 18, 0], ![-774, 0, 0]], ![![27, 3, 0], ![-128, 0, 0]], ![![11, 1, 0], ![-52, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 43, 0], ![-5, 0, 43]], ![![0, 1, 0], ![-2, 9, 1], ![3, 0, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![11, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![11, 1, 0]] 
 ![![43, 0, 0], ![11, 1, 0], ![8, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![11, 1, 0], ![0, 11, 1], ![174, 0, 11]]]
  hmulB := by decide  
  f := ![![![23, 2, 0], ![-86, 0, 0]], ![![-11, -1, 0], ![44, 0, 0]], ![![-8, -1, 0], ![32, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 43, 0], ![-8, 0, 43]], ![![0, 1, 0], ![-3, 11, 1], ![2, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-20, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-20, 1, 0]] 
 ![![43, 0, 0], ![23, 1, 0], ![30, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-20, 1, 0], ![0, -20, 1], ![174, 0, -20]]]
  hmulB := by decide  
  f := ![![![721, -36, 0], ![1548, 0, 0]], ![![381, -19, 0], ![818, 0, 0]], ![![530, -26, 0], ![1138, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 43, 0], ![-30, 0, 43]], ![![-1, 1, 0], ![10, -20, 1], ![18, 0, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![9, 1, 0]] ![![43, 0, 0], ![11, 1, 0]]
  ![![43, 0, 0], ![13, 20, 1]] where
 M := ![![![1849, 0, 0], ![473, 43, 0]], ![![387, 43, 0], ![99, 20, 1]]]
 hmul := by decide  
 g := ![![![![30, -20, -1], ![43, 0, 0]], ![![-2, -19, -1], ![43, 0, 0]]], ![![![-4, -19, -1], ![43, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![13, 20, 1]] ![![43, 0, 0], ![-20, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-860, 43, 0]], ![![559, 860, 43], ![-86, -387, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-20, 1, 0]]], ![![![13, 20, 1]], ![![-2, -9, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![2, -7, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![2, -7, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![2, 40, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![2, -7, 1], ![174, 2, -7], ![-1218, 174, 2]]]
  hmulB := by decide  
  f := ![![![-1, 7, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -40, 47]], ![![0, -1, 1], ![4, 6, -7], ![-26, 2, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [28, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 46], [0, 1]]
 g := ![![[31, 42], [6, 14], [25, 17], [31, 14], [1]], ![[0, 5], [27, 33], [27, 30], [5, 33], [1]]]
 h' := ![![[25, 46], [20, 18], [5, 22], [25, 39], [19, 25], [0, 1]], ![[0, 1], [0, 29], [38, 25], [13, 8], [33, 22], [25, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [29, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [28, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2081, 1526, 64]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -22, 64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![7, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![7, 1, 0]] 
 ![![47, 0, 0], ![7, 1, 0], ![45, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![7, 1, 0], ![0, 7, 1], ![174, 0, 7]]]
  hmulB := by decide  
  f := ![![![148, 21, 0], ![-987, 0, 0]], ![![14, 2, 0], ![-93, 0, 0]], ![![142, 20, 0], ![-947, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 47, 0], ![-45, 0, 47]], ![![0, 1, 0], ![-2, 7, 1], ![-3, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![2, -7, 1]] ![![47, 0, 0], ![7, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![329, 47, 0]], ![![94, -329, 47], ![188, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![7, 1, 0]]], ![![![2, -7, 1]], ![![4, -1, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-9, 16, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-9, 16, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![44, 16, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-9, 16, 1], ![174, -9, 16], ![2784, 174, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -16, 53]], ![![-1, 0, 1], ![-10, -5, 16], ![60, 6, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [6, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 52], [0, 1]]
 g := ![![[52, 9], [37], [25, 49], [52], [6, 1]], ![[0, 44], [37], [1, 4], [52], [12, 52]]]
 h' := ![![[6, 52], [18, 50], [9, 14], [30, 7], [17, 30], [0, 1]], ![[0, 1], [0, 3], [40, 39], [19, 46], [38, 23], [6, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [27, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [6, 47, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![746, 93, 82]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -23, 82]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-16, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-16, 1, 0]] 
 ![![53, 0, 0], ![37, 1, 0], ![9, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-16, 1, 0], ![0, -16, 1], ![174, 0, -16]]]
  hmulB := by decide  
  f := ![![![257, -16, 0], ![848, 0, 0]], ![![177, -11, 0], ![584, 0, 0]], ![![69, -4, 0], ![228, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 53, 0], ![-9, 0, 53]], ![![-1, 1, 0], ![11, -16, 1], ![6, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-9, 16, 1]] ![![53, 0, 0], ![-16, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-848, 53, 0]], ![![-477, 848, 53], ![318, -265, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-16, 1, 0]]], ![![![-9, 16, 1]], ![![6, -5, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-18, 10, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-18, 10, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![41, 10, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-18, 10, 1], ![174, -18, 10], ![1740, 174, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -10, 59]], ![![-1, 0, 1], ![-4, -2, 10], ![42, 6, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [53, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 58], [0, 1]]
 g := ![![[29, 49], [33, 3], [22], [24, 48], [56, 1]], ![[0, 10], [24, 56], [22], [57, 11], [53, 58]]]
 h' := ![![[56, 58], [21, 7], [41, 48], [26, 9], [41, 15], [0, 1]], ![[0, 1], [0, 52], [15, 11], [58, 50], [55, 44], [56, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [16, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [53, 3, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-987, 1571, -14]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, 29, -14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-10, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-10, 1, 0]] 
 ![![59, 0, 0], ![49, 1, 0], ![18, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-10, 1, 0], ![0, -10, 1], ![174, 0, -10]]]
  hmulB := by decide  
  f := ![![![81, -8, 0], ![472, 0, 0]], ![![71, -7, 0], ![414, 0, 0]], ![![42, -4, 0], ![246, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 59, 0], ![-18, 0, 59]], ![![-1, 1, 0], ![8, -10, 1], ![6, 0, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-18, 10, 1]] ![![59, 0, 0], ![-10, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-590, 59, 0]], ![![-1062, 590, 59], ![354, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-10, 1, 0]]], ![![![-18, 10, 1]], ![![6, -2, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![16, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![16, 1, 0]] 
 ![![61, 0, 0], ![16, 1, 0], ![49, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![16, 1, 0], ![0, 16, 1], ![174, 0, 16]]]
  hmulB := by decide  
  f := ![![![417, 26, 0], ![-1586, 0, 0]], ![![112, 7, 0], ![-426, 0, 0]], ![![357, 22, 0], ![-1358, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 61, 0], ![-49, 0, 61]], ![![0, 1, 0], ![-5, 16, 1], ![-10, 0, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![27, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![0, 20, 1], ![174, 0, 20]]]
  hmulB := by decide  
  f := ![![![481, 24, 0], ![-1464, 0, 0]], ![![140, 7, 0], ![-426, 0, 0]], ![![207, 10, 0], ![-630, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-27, 0, 61]], ![![0, 1, 0], ![-7, 20, 1], ![-6, 0, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -2, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![11, -2, 0]] 
 ![![61, 0, 0], ![25, 1, 0], ![46, 0, 1]] where
  M :=![![![11, -2, 0], ![0, 11, -2], ![-348, 0, 11]]]
  hmulB := by decide  
  f := ![![![-121, -22, -4]], ![![-61, -11, -2]], ![![-154, -28, -5]]]
  g := ![![![1, -2, 0], ![-3, 11, -2], ![-14, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![16, 1, 0]] ![![61, 0, 0], ![20, 1, 0]]
  ![![121, 22, 4]] where
 M := ![![![3721, 0, 0], ![1220, 61, 0]], ![![976, 61, 0], ![320, 36, 1]]]
 hmul := by decide  
 g := ![![![![-671, 122, 0]], ![![-220, 29, 2]]], ![![![-176, 21, 2]], ![![-52, 4, 1]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![121, 22, 4]] ![![11, -2, 0]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![3, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![3, 1, 0]] 
 ![![67, 0, 0], ![3, 1, 0], ![58, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![3, 1, 0], ![0, 3, 1], ![174, 0, 3]]]
  hmulB := by decide  
  f := ![![![124, 41, 0], ![-2747, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![106, 35, 0], ![-2348, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 67, 0], ![-58, 0, 67]], ![![0, 1, 0], ![-1, 3, 1], ![0, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![20, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![20, 1, 0]] 
 ![![67, 0, 0], ![20, 1, 0], ![2, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![20, 1, 0], ![0, 20, 1], ![174, 0, 20]]]
  hmulB := by decide  
  f := ![![![581, 29, 0], ![-1943, 0, 0]], ![![180, 9, 0], ![-602, 0, 0]], ![![6, 0, 0], ![-20, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 67, 0], ![-2, 0, 67]], ![![0, 1, 0], ![-6, 20, 1], ![2, 0, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-23, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-23, 1, 0]] 
 ![![67, 0, 0], ![44, 1, 0], ![7, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-23, 1, 0], ![0, -23, 1], ![174, 0, -23]]]
  hmulB := by decide  
  f := ![![![1082, -47, 0], ![3149, 0, 0]], ![![714, -31, 0], ![2078, 0, 0]], ![![146, -6, 0], ![425, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 67, 0], ![-7, 0, 67]], ![![-1, 1, 0], ![15, -23, 1], ![5, 0, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![3, 1, 0]] ![![67, 0, 0], ![20, 1, 0]]
  ![![67, 0, 0], ![-7, 23, 1]] where
 M := ![![![4489, 0, 0], ![1340, 67, 0]], ![![201, 67, 0], ![60, 23, 1]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![20, 1, 0], ![0, 0, 0]]], ![![![10, -22, -1], ![67, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-7, 23, 1]] ![![67, 0, 0], ![-23, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1541, 67, 0]], ![![-469, 1541, 67], ![335, -536, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-23, 1, 0]]], ![![![-7, 23, 1]], ![![5, -8, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-34, -26, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-34, -26, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![37, 45, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-34, -26, 1], ![174, -34, -26], ![-4524, 174, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -45, 71]], ![![-1, -1, 1], ![16, 16, -26], ![-46, 24, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [25, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 70], [0, 1]]
 g := ![![[45, 54], [62, 25], [], [], [50], [1]], ![[0, 17], [53, 46], [], [], [50], [1]]]
 h' := ![![[11, 70], [12, 57], [0, 5], [54], [14], [46, 11], [0, 1]], ![[0, 1], [0, 14], [55, 66], [54], [14], [25, 60], [11, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [58, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [25, 60, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![373, 114, -59]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 39, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![26, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![26, 1, 0]] 
 ![![71, 0, 0], ![26, 1, 0], ![34, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![26, 1, 0], ![0, 26, 1], ![174, 0, 26]]]
  hmulB := by decide  
  f := ![![![651, 25, 0], ![-1775, 0, 0]], ![![234, 9, 0], ![-638, 0, 0]], ![![270, 10, 0], ![-736, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 71, 0], ![-34, 0, 71]], ![![0, 1, 0], ![-10, 26, 1], ![-10, 0, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-34, -26, 1]] ![![71, 0, 0], ![26, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1846, 71, 0]], ![![-2414, -1846, 71], ![-710, -710, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![26, 1, 0]]], ![![![-34, -26, 1]], ![![-10, -10, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [19, 13, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 66, 1], [38, 6, 72], [0, 1]]
 g := ![![[71, 17, 8], [60, 1], [63, 6], [38, 1, 16], [3, 1], []], ![[47, 5, 59, 8], [33, 4], [42, 32], [20, 63, 3, 8], [30, 36], [62, 1]], ![[23, 19, 1, 41], [66, 1], [9, 9], [51, 21, 11, 50], [56, 49], [64, 1]]]
 h' := ![![[38, 66, 1], [12, 28, 9], [35, 65, 1], [8, 35, 58], [16, 15, 69], [0, 0, 1], [0, 1]], ![[38, 6, 72], [39, 1, 9], [70, 13, 71], [49, 35, 18], [33, 67, 64], [47, 30, 6], [38, 66, 1]], ![[0, 1], [62, 44, 55], [32, 68, 1], [35, 3, 70], [39, 64, 13], [9, 43, 66], [38, 6, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 37], []]
 b := ![[], [57, 25, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [19, 13, 70, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1706521, 204108, 36427]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23377, 2796, 499]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [48, 68, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 58, 29], [29, 20, 50], [0, 1]]
 g := ![![[27, 46, 25], [73, 11, 73], [43, 11, 73], [21, 63, 5], [76, 1], []], ![[43, 29, 19, 61], [61, 57, 70, 60], [8, 53, 70, 60], [52, 73, 23, 12], [69, 5], [51, 51]], ![[38, 38, 46, 67], [63, 6, 10, 5], [25, 1, 10, 5], [9, 2, 52, 19], [45, 46], [30, 51]]]
 h' := ![![[47, 58, 29], [51, 59, 74], [69, 69, 28], [19, 10, 51], [65, 77, 20], [0, 0, 1], [0, 1]], ![[29, 20, 50], [69, 54, 31], [17, 16, 33], [71, 63, 46], [10, 5, 26], [77, 10, 20], [47, 58, 29]], ![[0, 1], [17, 45, 53], [71, 73, 18], [17, 6, 61], [35, 76, 33], [33, 69, 58], [29, 20, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19], []]
 b := ![[], [26, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [48, 68, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25596, -4503, 1501]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-324, -57, 19]
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



lemma PB256I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB256I1 : PrimesBelowBoundCertificateInterval O 31 79 256 where
  m := 11
  g := ![3, 2, 3, 2, 2, 2, 3, 3, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB256I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
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
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
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
      exact NI61N2
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
  β := ![I37N0, I37N1, I37N2, I41N1, I43N0, I43N1, I43N2, I47N1, I53N1, I59N1, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2, I71N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [I59N1], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
