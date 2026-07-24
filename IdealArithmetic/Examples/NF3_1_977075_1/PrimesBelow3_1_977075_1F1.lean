
import IdealArithmetic.Examples.NF3_1_977075_1.RI3_1_977075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2361, -759, 70]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![2361, -759, 70]] 
 ![![37, 0, 0], ![6, 1, 0], ![1, 0, 1]] where
  M :=![![![2361, -759, 70], ![-23240, 7471, -689], ![228748, -73537, 6782]]]
  hmulB := by decide  
  f := ![![![1329, -52, -19]], ![![386, -10, -5]], ![![673, 29, -4]]]
  g := ![![![185, -759, 70], ![-1821, 7471, -689], ![17924, -73537, 6782]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-6, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-6, 1, 0]] 
 ![![37, 0, 0], ![31, 1, 0], ![1, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-6, 1, 0], ![0, -6, 1], ![-332, 73, -5]]]
  hmulB := by decide  
  f := ![![![199, -33, 0], ![1221, 0, 0]], ![![169, -28, 0], ![1037, 0, 0]], ![![7, -1, 0], ![43, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 37, 0], ![-1, 0, 37]], ![![-1, 1, 0], ![5, -6, 1], ![-70, 73, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-1, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-1, 1, 0]] 
 ![![37, 0, 0], ![36, 1, 0], ![36, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-1, 1, 0], ![0, -1, 1], ![-332, 73, 0]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![111, 0, 0]], ![![2, -1, 0], ![38, 0, 0]], ![![2, -1, 0], ![38, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 37, 0], ![-36, 0, 37]], ![![-1, 1, 0], ![0, -1, 1], ![-80, 73, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![2361, -759, 70]] ![![37, 0, 0], ![-6, 1, 0]]
  ![![37, 0, 0], ![-36, 0, 1]] where
 M := ![![![87357, -28083, 2590], ![-37406, 12025, -1109]]]
 hmul := by decide  
 g := ![![![![1245, -759, 101], ![-1147, 0, 0]], ![![-506, 325, -44], ![519, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-36, 0, 1]] ![![37, 0, 0], ![-1, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-37, 37, 0]], ![![-1332, 0, 37], ![-296, 37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-1, 1, 0]]], ![![![-36, 0, 1]], ![![-8, 1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![7, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![7, 1, 0]] 
 ![![41, 0, 0], ![7, 1, 0], ![33, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![7, 1, 0], ![0, 7, 1], ![-332, 73, 8]]]
  hmulB := by decide  
  f := ![![![29, 4, 0], ![-164, 0, 0]], ![![-7, -1, 0], ![42, 0, 0]], ![![23, 3, 0], ![-130, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 41, 0], ![-33, 0, 41]], ![![0, 1, 0], ![-2, 7, 1], ![-27, 73, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![15, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![15, 1, 0]] 
 ![![41, 0, 0], ![15, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![15, 1, 0], ![0, 15, 1], ![-332, 73, 16]]]
  hmulB := by decide  
  f := ![![![136, 9, 0], ![-369, 0, 0]], ![![30, 2, 0], ![-81, 0, 0]], ![![66, 4, 0], ![-179, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-6, 15, 1], ![-43, 73, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 1, 0]] 
 ![![41, 0, 0], ![18, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 1, 0], ![0, 18, 1], ![-332, 73, 19]]]
  hmulB := by decide  
  f := ![![![181, 10, 0], ![-410, 0, 0]], ![![90, 5, 0], ![-204, 0, 0]], ![![8, 0, 0], ![-18, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 41, 0], ![-4, 0, 41]], ![![0, 1, 0], ![-8, 18, 1], ![-42, 73, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![7, 1, 0]] ![![41, 0, 0], ![15, 1, 0]]
  ![![41, 0, 0], ![-59, 22, 1]] where
 M := ![![![1681, 0, 0], ![615, 41, 0]], ![![287, 41, 0], ![105, 22, 1]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![15, 1, 0], ![0, 0, 0]]], ![![![7, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-59, 22, 1]] ![![41, 0, 0], ![18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![738, 41, 0]], ![![-2419, 902, 41], ![-1394, 410, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![18, 1, 0]]], ![![![-59, 22, 1]], ![![-34, 10, 1]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [23, 6, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 31, 27], [8, 11, 16], [0, 1]]
 g := ![![[18, 39, 23], [13], [15, 35], [11, 24, 1], []], ![[30, 33, 3, 2], [24, 21, 41, 29], [10, 14], [14, 35, 27, 42], [35, 41]], ![[2, 12, 20, 40], [0, 19, 37, 14], [16, 1], [37, 3, 1, 25], [3, 41]]]
 h' := ![![[16, 31, 27], [2, 25, 25], [24, 20], [5, 27, 11], [0, 0, 1], [0, 1]], ![[8, 11, 16], [7, 18, 4], [0, 18, 24], [31, 12, 33], [10, 11, 11], [16, 31, 27]], ![[0, 1], [34, 0, 14], [12, 5, 19], [37, 4, 42], [38, 32, 31], [8, 11, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 26], []]
 b := ![[], [10, 32, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [23, 6, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5289, 21414, -3096]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-123, 498, -72]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [9, 44, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 10, 13], [27, 36, 34], [0, 1]]
 g := ![![[12, 10, 34], [20, 42, 14], [34, 21, 6], [31, 13, 1], []], ![[16, 7, 5, 39], [40, 36, 42, 30], [5, 28, 38, 13], [5, 40, 37, 22], [13, 28]], ![[34, 1, 32, 1], [5, 13, 41, 4], [41, 22, 30, 25], [24, 31, 37, 16], [39, 28]]]
 h' := ![![[33, 10, 13], [8, 23, 9], [23, 16, 25], [3, 23, 10], [0, 0, 1], [0, 1]], ![[27, 36, 34], [21, 23, 12], [35, 8, 27], [1, 0, 1], [32, 24, 36], [33, 10, 13]], ![[0, 1], [36, 1, 26], [35, 23, 42], [33, 24, 36], [2, 23, 10], [27, 36, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 13], []]
 b := ![[], [36, 15, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [9, 44, 34, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3006590, -1411034, 164876]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![63970, -30022, 3508]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-45, -16, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-45, -16, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![8, 37, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-45, -16, 1], ![-332, 28, -15], ![4980, -1427, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -37, 53]], ![![-1, -1, 1], ![-4, 11, -15], ![92, -36, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [38, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 52], [0, 1]]
 g := ![![[26, 7], [15], [44, 37], [25], [19, 1]], ![[0, 46], [15], [5, 16], [25], [38, 52]]]
 h' := ![![[19, 52], [6, 22], [24, 42], [33, 39], [20, 5], [0, 1]], ![[0, 1], [0, 31], [27, 11], [32, 14], [9, 48], [19, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [29, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [38, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2290, -499, 167]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, -126, 167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![15, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![15, 1, 0]] 
 ![![53, 0, 0], ![15, 1, 0], ![40, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![15, 1, 0], ![0, 15, 1], ![-332, 73, 16]]]
  hmulB := by decide  
  f := ![![![361, 24, 0], ![-1272, 0, 0]], ![![105, 7, 0], ![-370, 0, 0]], ![![260, 17, 0], ![-916, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 53, 0], ![-40, 0, 53]], ![![0, 1, 0], ![-5, 15, 1], ![-39, 73, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-45, -16, 1]] ![![53, 0, 0], ![15, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![795, 53, 0]], ![![-2385, -848, 53], ![-1007, -212, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![15, 1, 0]]], ![![![-45, -16, 1]], ![![-19, -4, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-66, -21, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-66, -21, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![52, 38, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-66, -21, 1], ![-332, 7, -20], ![6640, -1792, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -38, 59]], ![![-2, -1, 1], ![12, 13, -20], ![124, -22, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [4, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 58], [0, 1]]
 g := ![![[11, 15], [35, 26], [27], [42, 48], [15, 1]], ![[0, 44], [12, 33], [27], [54, 11], [30, 58]]]
 h' := ![![[15, 58], [37, 29], [32, 47], [9, 26], [58, 44], [0, 1]], ![[0, 1], [0, 30], [29, 12], [45, 33], [10, 15], [15, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [6, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [4, 44, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-947, -2723, 523]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-477, -383, 523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![20, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![20, 1, 0]] 
 ![![59, 0, 0], ![20, 1, 0], ![13, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![20, 1, 0], ![0, 20, 1], ![-332, 73, 21]]]
  hmulB := by decide  
  f := ![![![21, 1, 0], ![-59, 0, 0]], ![![-20, -1, 0], ![60, 0, 0]], ![![-13, -1, 0], ![39, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 59, 0], ![-13, 0, 59]], ![![0, 1, 0], ![-7, 20, 1], ![-35, 73, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-66, -21, 1]] ![![59, 0, 0], ![20, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1180, 59, 0]], ![![-3894, -1239, 59], ![-1652, -413, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![20, 1, 0]]], ![![![-66, -21, 1]], ![![-28, -7, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2967, -954, 88]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![2967, -954, 88]] 
 ![![61, 0, 0], ![0, 61, 0], ![15, 46, 1]] where
  M :=![![![2967, -954, 88], ![-29216, 9391, -866], ![287512, -92434, 8525]]]
  hmulB := by decide  
  f := ![![![171, -22, -4]], ![![1328, -121, -26]], ![![1185, -106, -23]]]
  g := ![![![27, -82, 88], ![-266, 807, -866], ![2617, -7944, 8525]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [38, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 60], [0, 1]]
 g := ![![[28, 27], [12], [47, 49], [45, 34], [34, 1]], ![[31, 34], [12], [5, 12], [42, 27], [7, 60]]]
 h' := ![![[34, 60], [16, 37], [44, 45], [59, 54], [50, 20], [0, 1]], ![[0, 1], [54, 24], [49, 16], [4, 7], [59, 41], [34, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [23, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [38, 27, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-958, -140, 50]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -40, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-171, 22, 4]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-171, 22, 4]] 
 ![![61, 0, 0], ![14, 1, 0], ![48, 0, 1]] where
  M :=![![![-171, 22, 4], ![-1328, 121, 26], ![-8632, 570, 147]]]
  hmulB := by decide  
  f := ![![![-2967, 954, -88]], ![![-202, 65, -6]], ![![-7048, 2266, -209]]]
  g := ![![![-11, 22, 4], ![-70, 121, 26], ![-388, 570, 147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![2967, -954, 88]] ![![-171, 22, 4]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 4, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-53, 4, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![14, 4, 1]] where
  M :=![![![-53, 4, 1], ![-332, 20, 5], ![-1660, 33, 25]]]
  hmulB := by decide  
  f := ![![![5, -1, 0]], ![![0, 5, -1]], ![![6, -1, 0]]]
  g := ![![![-1, 0, 1], ![-6, 0, 5], ![-30, -1, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [12, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 66], [0, 1]]
 g := ![![[63, 40], [39, 10], [25], [37], [26], [1]], ![[40, 27], [50, 57], [25], [37], [26], [1]]]
 h' := ![![[48, 66], [1, 43], [57, 12], [42, 5], [33, 29], [55, 48], [0, 1]], ![[0, 1], [55, 24], [30, 55], [14, 62], [18, 38], [14, 19], [48, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [10, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [12, 19, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12916, 2914, 494]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-296, 14, 494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-5, 1, 0]] 
 ![![67, 0, 0], ![62, 1, 0], ![42, 0, 1]] where
  M :=![![![-5, 1, 0], ![0, -5, 1], ![-332, 73, -4]]]
  hmulB := by decide  
  f := ![![![53, -4, -1]], ![![54, -4, -1]], ![![58, -3, -1]]]
  g := ![![![-1, 1, 0], ![4, -5, 1], ![-70, 73, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-53, 4, 1]] ![![-5, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [54, 18, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 62, 8], [6, 8, 63], [0, 1]]
 g := ![![[62, 25, 48], [45, 1, 37], [38, 64, 2], [46, 49], [66, 1], []], ![[11, 33, 0, 25], [27, 59, 60, 20], [53, 35, 21, 12], [65, 50], [31, 64], [33, 64]], ![[5, 31, 27, 59], [33, 33, 62, 13], [5, 44, 34, 21], [37, 16], [52, 10], [49, 64]]]
 h' := ![![[60, 62, 8], [55, 37, 41], [7, 21, 45], [55, 62, 59], [57, 36, 7], [0, 0, 1], [0, 1]], ![[6, 8, 63], [62, 65, 56], [7, 66, 31], [64, 13, 45], [33, 47, 60], [43, 53, 8], [60, 62, 8]], ![[0, 1], [51, 40, 45], [46, 55, 66], [10, 67, 38], [37, 59, 4], [17, 18, 62], [6, 8, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 6], []]
 b := ![[], [16, 59, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [54, 18, 5, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-279172, 91306, -8378]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3932, 1286, -118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-59, 17, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-59, 17, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![14, 17, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-59, 17, 1], ![-332, 14, 18], ![-5976, 982, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -17, 73]], ![![-1, 0, 1], ![-8, -4, 18], ![-88, 6, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [30, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 72], [0, 1]]
 g := ![![[44, 49], [4], [1], [39, 4], [36], [1]], ![[42, 24], [4], [1], [15, 69], [36], [1]]]
 h' := ![![[67, 72], [45, 7], [47, 71], [71, 72], [39, 71], [43, 67], [0, 1]], ![[0, 1], [3, 66], [59, 2], [4, 1], [51, 2], [6, 6], [67, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [47, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [30, 6, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2626, -738, 313]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -83, 313]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-18, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-18, 1, 0]] 
 ![![73, 0, 0], ![55, 1, 0], ![41, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-18, 1, 0], ![0, -18, 1], ![-332, 73, -17]]]
  hmulB := by decide  
  f := ![![![1279, -71, 0], ![5183, 0, 0]], ![![973, -54, 0], ![3943, 0, 0]], ![![743, -41, 0], ![3011, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 73, 0], ![-41, 0, 73]], ![![-1, 1, 0], ![13, -18, 1], ![-50, 73, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-59, 17, 1]] ![![73, 0, 0], ![-18, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1314, 73, 0]], ![![-4307, 1241, 73], ![730, -292, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-18, 1, 0]]], ![![![-59, 17, 1]], ![![10, -4, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [18, 71, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 65, 13], [48, 13, 66], [0, 1]]
 g := ![![[48, 33, 76], [71, 35, 8], [52, 30, 18], [77, 44, 18], [53, 1], []], ![[63, 53, 74, 32], [12, 34, 47, 20], [46, 74, 44, 40], [67, 15, 40, 31], [59, 11], [61, 11]], ![[60, 50, 2, 15], [7, 19, 14, 29], [37, 18, 15, 14], [58, 22, 57, 27], [52, 38], [8, 11]]]
 h' := ![![[5, 65, 13], [65, 3, 32], [12, 66, 18], [36, 18, 27], [73, 11, 52], [0, 0, 1], [0, 1]], ![[48, 13, 66], [30, 18, 60], [67, 38, 65], [69, 6, 32], [27, 62, 29], [33, 71, 13], [5, 65, 13]], ![[0, 1], [46, 58, 66], [32, 54, 75], [49, 55, 20], [30, 6, 77], [27, 8, 65], [48, 13, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 7], []]
 b := ![[], [70, 66, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [18, 71, 26, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3955056, -1269846, 116446]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50064, -16074, 1474]
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



lemma PB280I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB280I1 : PrimesBelowBoundCertificateInterval O 31 79 280 where
  m := 11
  g := ![3, 3, 1, 1, 2, 2, 2, 2, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB280I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
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
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![5329, 73]
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
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I41N2, I53N1, I59N1, I61N1, I67N1, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N1, I41N2], [], [], [I53N1], [I59N1], [I61N1], [I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
