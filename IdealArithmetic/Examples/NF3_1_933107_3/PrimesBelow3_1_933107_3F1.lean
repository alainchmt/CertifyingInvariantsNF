
import IdealArithmetic.Examples.NF3_1_933107_3.RI3_1_933107_3
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [31, 28, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 35, 17], [34, 1, 20], [0, 1]]
 g := ![![[12, 25, 11], [9, 34], [23, 4, 9], [32, 1], []], ![[14, 1, 10, 14], [13, 27], [28, 31], [36, 1], [4, 30]], ![[17, 33, 6, 22], [10, 27], [22, 4, 33, 32], [25, 4], [1, 30]]]
 h' := ![![[35, 35, 17], [6, 13, 23], [27, 21, 21], [7, 35, 34], [0, 0, 1], [0, 1]], ![[34, 1, 20], [32, 20, 22], [18, 0, 8], [1, 35], [28, 2, 1], [35, 35, 17]], ![[0, 1], [16, 4, 29], [20, 16, 8], [5, 4, 3], [15, 35, 35], [34, 1, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 18], []]
 b := ![[], [8, 30, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [31, 28, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-371369, 304140, -1645760]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10037, 8220, -44480]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![41, 9, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![41, 9, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 9, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![41, 9, 1], ![41, 1, 73], ![205, -280, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-41, -8, -1], ![41, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -9, 41]], ![![1, 0, 1], ![1, -16, 73], ![5, -11, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [31, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 40], [0, 1]]
 g := ![![[32, 4], [23], [8], [25, 23], [1]], ![[0, 37], [23], [8], [5, 18], [1]]]
 h' := ![![[33, 40], [16, 2], [14, 33], [4, 7], [10, 33], [0, 1]], ![[0, 1], [0, 39], [37, 8], [30, 34], [33, 8], [33, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [22, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [31, 8, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2050, 2198, -5063]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, 1165, -5063]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, 1, 0]] 
 ![![41, 0, 0], ![9, 1, 0], ![22, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, 1, 0], ![2, 8, 8], ![23, -31, 10]]]
  hmulB := by decide  
  f := ![![![1786, 7665, 7680], ![615, -39360, 0]], ![![384, 1676, 1680], ![165, -8610, 0]], ![![959, 4113, 4121], ![327, -21120, 0]]]
  g := ![![![1, 0, 0], ![-9, 41, 0], ![-22, 0, 41]], ![![0, 1, 0], ![-6, 8, 8], ![2, -31, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![41, 9, 1]] ![![41, 0, 0], ![9, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![369, 41, 0]], ![![1681, 369, 41], ![410, 82, 82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![9, 1, 0]]], ![![![41, 9, 1]], ![![10, 2, 2]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![19, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![19, 1, 0]] 
 ![![43, 0, 0], ![19, 1, 0], ![22, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![19, 1, 0], ![2, 18, 8], ![23, -31, 20]]]
  hmulB := by decide  
  f := ![![![295, 3666, 1632], ![258, -8772, 0]], ![![123, 1617, 720], ![130, -3870, 0]], ![![158, 1876, 835], ![116, -4488, 0]]]
  g := ![![![1, 0, 0], ![-19, 43, 0], ![-22, 0, 43]], ![![0, 1, 0], ![-12, 18, 8], ![4, -31, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-10, 1, 0]] 
 ![![43, 0, 0], ![33, 1, 0], ![8, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-10, 1, 0], ![2, -11, 8], ![23, -31, -9]]]
  hmulB := by decide  
  f := ![![![1281, -7580, 5520], ![-430, -29670, 0]], ![![979, -5811, 4232], ![-343, -22747, 0]], ![![246, -1411, 1027], ![-47, -5520, 0]]]
  g := ![![![1, 0, 0], ![-33, 43, 0], ![-8, 0, 43]], ![![-1, 1, 0], ![7, -11, 8], ![26, -31, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32, 0, -1]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-32, 0, -1]] 
 ![![43, 0, 0], ![34, 1, 0], ![32, 0, 1]] where
  M :=![![![-32, 0, -1], ![-23, -1, -1], ![2, 1, -1]]]
  hmulB := by decide  
  f := ![![![-2, 1, 1]], ![![-1, 0, 1]], ![![-1, 0, 0]]]
  g := ![![![0, 0, -1], ![1, -1, -1], ![0, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![19, 1, 0]] ![![43, 0, 0], ![-10, 1, 0]]
  ![![-2, 1, 1]] where
 M := ![![![1849, 0, 0], ![-430, 43, 0]], ![![817, 43, 0], ![-188, 8, 8]]]
 hmul := by decide  
 g := ![![![![-1376, 0, -43]], ![![297, -1, 9]]], ![![![-631, -1, -20]], ![![136, 0, 4]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-2, 1, 1]] ![![-32, 0, -1]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![6, -17, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![6, -17, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![6, 30, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![6, -17, 1], ![-11, -8, -135], ![-393, 526, -42]]]
  hmulB := by decide  
  f := ![![![-5, 17, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -30, 47]], ![![0, -1, 1], ![17, 86, -135], ![-3, 38, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [19, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 46], [0, 1]]
 g := ![![[21, 2], [34, 8], [45, 34], [34, 12], [1]], ![[22, 45], [38, 39], [15, 13], [40, 35], [1]]]
 h' := ![![[24, 46], [12, 40], [38, 14], [12, 9], [28, 24], [0, 1]], ![[0, 1], [32, 7], [45, 33], [40, 38], [40, 23], [24, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [29, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [19, 23, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-83097, -26372, -1170308]
  a := ![-65, 1, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![147633, 746444, -1170308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-6, 1, 0]] 
 ![![47, 0, 0], ![41, 1, 0], ![42, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-6, 1, 0], ![2, -7, 8], ![23, -31, -5]]]
  hmulB := by decide  
  f := ![![![1603, -5727, 6552], ![-282, -38493, 0]], ![![1393, -4992, 5712], ![-281, -33558, 0]], ![![1428, -5117, 5855], ![-287, -34398, 0]]]
  g := ![![![1, 0, 0], ![-41, 47, 0], ![-42, 0, 47]], ![![-1, 1, 0], ![-1, -7, 8], ![32, -31, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![6, -17, 1]] ![![47, 0, 0], ![-6, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-282, 47, 0]], ![![282, -799, 47], ![-47, 94, -141]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-6, 1, 0]]], ![![![6, -17, 1]], ![![-1, 2, -3]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [10, 36, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 9, 50], [0, 43, 3], [0, 1]]
 g := ![![[23, 17, 9], [52, 1], [39, 40, 44], [22, 6], [1]], ![[41, 4, 43, 23], [11, 28], [33, 40, 44, 39], [13, 52], [40, 44, 40, 26]], ![[0, 31, 4, 26], [6, 11], [29, 6, 25, 35], [30, 25], [22, 21, 39, 27]]]
 h' := ![![[35, 9, 50], [0, 21, 3], [34, 35, 1], [39, 27, 37], [43, 17, 35], [0, 1]], ![[0, 43, 3], [25, 15, 13], [33, 45, 44], [36, 5, 26], [22, 31, 23], [35, 9, 50]], ![[0, 1], [35, 17, 37], [28, 26, 8], [29, 21, 43], [45, 5, 48], [0, 43, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 52], []]
 b := ![[], [40, 46, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [10, 36, 18, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2045853, 2192186, -4747634]
  a := ![-4, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38601, 41362, -89578]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![32, 29, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![32, 29, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![32, 29, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![32, 29, 1], ![81, -28, 233], ![665, -900, 30]]]
  hmulB := by decide  
  f := ![![![-31, -29, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -29, 59]], ![![0, 0, 1], ![-125, -115, 233], ![-5, -30, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [7, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 58], [0, 1]]
 g := ![![[45, 17], [38, 16], [25], [29, 46], [39, 1]], ![[0, 42], [13, 43], [25], [53, 13], [19, 58]]]
 h' := ![![[39, 58], [29, 28], [29, 55], [33, 54], [22, 39], [0, 1]], ![[0, 1], [0, 31], [50, 4], [15, 5], [9, 20], [39, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [12, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [7, 20, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-882, 613, -4648]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2506, 2295, -4648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![3, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![3, 1, 0]] 
 ![![59, 0, 0], ![3, 1, 0], ![29, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![3, 1, 0], ![2, 2, 8], ![23, -31, 4]]]
  hmulB := by decide  
  f := ![![![-559, -560, -2240], ![0, 16520, 0]], ![![-28, -28, -112], ![1, 826, 0]], ![![-274, -275, -1101], ![-15, 8120, 0]]]
  g := ![![![1, 0, 0], ![-3, 59, 0], ![-29, 0, 59]], ![![0, 1, 0], ![-4, 2, 8], ![0, -31, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![32, 29, 1]] ![![59, 0, 0], ![3, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![177, 59, 0]], ![![1888, 1711, 59], ![177, 59, 236]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![3, 1, 0]]], ![![![32, 29, 1]], ![![3, 1, 4]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![19, -26, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![19, -26, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![19, 35, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![19, -26, 1], ![-29, 14, -207], ![-600, 805, -38]]]
  hmulB := by decide  
  f := ![![![-18, 26, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -35, 61]], ![![0, -1, 1], ![64, 119, -207], ![2, 35, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [44, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 60], [0, 1]]
 g := ![![[47, 36], [9], [58, 57], [33, 3], [6, 1]], ![[19, 25], [9], [34, 4], [51, 58], [12, 60]]]
 h' := ![![[6, 60], [9, 55], [10, 58], [12, 39], [41, 53], [0, 1]], ![[0, 1], [34, 6], [53, 3], [2, 22], [54, 8], [6, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [20, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [44, 55, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17400, -2275, -226192]
  a := ![22, -1, 87]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70168, 129745, -226192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![24, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![24, 1, 0]] 
 ![![61, 0, 0], ![24, 1, 0], ![38, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![24, 1, 0], ![2, 23, 8], ![23, -31, 25]]]
  hmulB := by decide  
  f := ![![![-1663, -23811, -8288], ![-1037, 63196, 0]], ![![-670, -9355, -3256], ![-365, 24827, 0]], ![![-1058, -14834, -5163], ![-590, 39368, 0]]]
  g := ![![![1, 0, 0], ![-24, 61, 0], ![-38, 0, 61]], ![![0, 1, 0], ![-14, 23, 8], ![-3, -31, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![19, -26, 1]] ![![61, 0, 0], ![24, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1464, 61, 0]], ![![1159, -1586, 61], ![427, -610, -183]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![24, 1, 0]]], ![![![19, -26, 1]], ![![7, -10, -3]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![37, -16, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![37, -16, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![37, 51, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![37, -16, 1], ![-9, 22, -127], ![-370, 495, -10]]]
  hmulB := by decide  
  f := ![![![-36, 16, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -51, 67]], ![![0, -1, 1], ![70, 97, -127], ![0, 15, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [20, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 66], [0, 1]]
 g := ![![[13, 40], [50, 60], [36], [14], [64], [1]], ![[65, 27], [61, 7], [36], [14], [64], [1]]]
 h' := ![![[8, 66], [5, 43], [21, 44], [2, 6], [58, 58], [47, 8], [0, 1]], ![[0, 1], [14, 24], [38, 23], [50, 61], [53, 9], [44, 59], [8, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [33, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [20, 59, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66, -5, 38]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -29, 38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-7, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-7, 1, 0]] 
 ![![67, 0, 0], ![60, 1, 0], ![10, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-7, 1, 0], ![2, -8, 8], ![23, -31, -6]]]
  hmulB := by decide  
  f := ![![![-1902, 7747, -7752], ![335, 64923, 0]], ![![-1698, 6931, -6936], ![336, 58089, 0]], ![![-282, 1156, -1157], ![68, 9690, 0]]]
  g := ![![![1, 0, 0], ![-60, 67, 0], ![-10, 0, 67]], ![![-1, 1, 0], ![6, -8, 8], ![29, -31, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![37, -16, 1]] ![![67, 0, 0], ![-7, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-469, 67, 0]], ![![2479, -1072, 67], ![-268, 134, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-7, 1, 0]]], ![![![37, -16, 1]], ![![-4, 2, -2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![9, -14, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![9, -14, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![9, 57, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![9, -14, 1], ![-5, -8, -111], ![-324, 433, -36]]]
  hmulB := by decide  
  f := ![![![-8, 14, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -57, 71]], ![![0, -1, 1], ![14, 89, -111], ![0, 35, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [27, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 70], [0, 1]]
 g := ![![[35, 50], [30, 1], [22, 6], [5], [58], [1]], ![[0, 21], [8, 70], [32, 65], [5], [58], [1]]]
 h' := ![![[49, 70], [42, 60], [45, 70], [19, 19], [15, 54], [44, 49], [0, 1]], ![[0, 1], [0, 11], [67, 1], [27, 52], [34, 17], [31, 22], [49, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [26, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [27, 22, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2470, 2012, -11808]
  a := ![5, -2, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1462, 9508, -11808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-31, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-31, 1, 0]] 
 ![![71, 0, 0], ![40, 1, 0], ![36, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-31, 1, 0], ![2, -32, 8], ![23, -31, -30]]]
  hmulB := by decide  
  f := ![![![-226, 5117, -1280], ![213, 11360, 0]], ![![-117, 2878, -720], ![143, 6390, 0]], ![![-98, 2594, -649], ![146, 5760, 0]]]
  g := ![![![1, 0, 0], ![-40, 71, 0], ![-36, 0, 71]], ![![-1, 1, 0], ![14, -32, 8], ![33, -31, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![9, -14, 1]] ![![71, 0, 0], ![-31, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2201, 71, 0]], ![![639, -994, 71], ![-284, 426, -142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-31, 1, 0]]], ![![![9, -14, 1]], ![![-4, 6, -2]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![34, -36, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![34, -36, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![34, 37, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![34, -36, 1], ![-49, 39, -287], ![-830, 1115, -33]]]
  hmulB := by decide  
  f := ![![![-33, 36, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -37, 73]], ![![0, -1, 1], ![133, 146, -287], ![4, 32, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [9, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 72], [0, 1]]
 g := ![![[42, 65], [41], [70], [72, 64], [23], [1]], ![[0, 8], [41], [70], [43, 9], [23], [1]]]
 h' := ![![[60, 72], [53, 49], [35, 25], [9, 56], [20, 8], [64, 60], [0, 1]], ![[0, 1], [0, 24], [2, 48], [11, 17], [62, 65], [14, 13], [60, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [1, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [9, 13, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-481, -225, -7020]
  a := ![-5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3263, 3555, -7020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-5, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-5, 1, 0]] 
 ![![73, 0, 0], ![68, 1, 0], ![33, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-5, 1, 0], ![2, -6, 8], ![23, -31, -4]]]
  hmulB := by decide  
  f := ![![![-458, 1391, -1856], ![73, 16936, 0]], ![![-426, 1295, -1728], ![74, 15768, 0]], ![![-203, 628, -839], ![92, 7656, 0]]]
  g := ![![![1, 0, 0], ![-68, 73, 0], ![-33, 0, 73]], ![![-1, 1, 0], ![2, -6, 8], ![31, -31, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![34, -36, 1]] ![![73, 0, 0], ![-5, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-365, 73, 0]], ![![2482, -2628, 73], ![-219, 219, -292]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-5, 1, 0]]], ![![![34, -36, 1]], ![![-3, 3, -4]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-18, 10, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-18, 10, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![61, 10, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-18, 10, 1], ![43, -59, 81], ![228, -311, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -10, 79]], ![![-1, 0, 1], ![-62, -11, 81], ![33, 1, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [52, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 78], [0, 1]]
 g := ![![[62, 38], [78, 52], [24, 50], [20, 4], [67], [1]], ![[0, 41], [68, 27], [63, 29], [1, 75], [67], [1]]]
 h' := ![![[15, 78], [52, 65], [16, 62], [66, 34], [10, 77], [27, 15], [0, 1]], ![[0, 1], [0, 14], [77, 17], [23, 45], [59, 2], [15, 64], [15, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [52, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [52, 64, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![828, -2672, -10948]
  a := ![-4, -2, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8464, 1352, -10948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-2, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-2, 1, 0]] 
 ![![79, 0, 0], ![77, 1, 0], ![39, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-2, 1, 0], ![2, -3, 8], ![23, -31, -1]]]
  hmulB := by decide  
  f := ![![![3041, -4562, 12168], ![-79, -120159, 0]], ![![2963, -4445, 11856], ![-78, -117078, 0]], ![![1501, -2252, 6007], ![-49, -59319, 0]]]
  g := ![![![1, 0, 0], ![-77, 79, 0], ![-39, 0, 79]], ![![-1, 1, 0], ![-1, -3, 8], ![31, -31, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-18, 10, 1]] ![![79, 0, 0], ![-2, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-158, 79, 0]], ![![-1422, 790, 79], ![79, -79, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-2, 1, 0]]], ![![![-18, 10, 1]], ![![1, -1, 1]]]]
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
  g := ![1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB274I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
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
  β := ![I41N1, I43N0, I43N1, I43N2, I47N1, I59N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
