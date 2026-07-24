
import IdealArithmetic.Examples.NF3_1_933107_2.RI3_1_933107_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![9, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![9, 1, 0]] 
 ![![37, 0, 0], ![9, 1, 0], ![30, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![9, 1, 0], ![0, 9, 1], ![-218, 37, 10]]]
  hmulB := by decide  
  f := ![![![172, 19, 0], ![-703, 0, 0]], ![![36, 4, 0], ![-147, 0, 0]], ![![138, 15, 0], ![-564, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 37, 0], ![-30, 0, 37]], ![![0, 1, 0], ![-3, 9, 1], ![-23, 37, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-8, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-8, 1, 0]] 
 ![![37, 0, 0], ![29, 1, 0], ![10, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-8, 1, 0], ![0, -8, 1], ![-218, 37, -7]]]
  hmulB := by decide  
  f := ![![![145, -18, 0], ![666, 0, 0]], ![![121, -15, 0], ![556, 0, 0]], ![![50, -6, 0], ![230, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 37, 0], ![-10, 0, 37]], ![![-1, 1, 0], ![6, -8, 1], ![-33, 37, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-2, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-2, 1, 0]] 
 ![![37, 0, 0], ![35, 1, 0], ![33, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-2, 1, 0], ![0, -2, 1], ![-218, 37, -1]]]
  hmulB := by decide  
  f := ![![![43, -21, 0], ![777, 0, 0]], ![![41, -20, 0], ![741, 0, 0]], ![![39, -19, 0], ![705, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 37, 0], ![-33, 0, 37]], ![![-1, 1, 0], ![1, -2, 1], ![-40, 37, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![9, 1, 0]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0], ![-35, 1, 1]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![333, 37, 0], ![-72, 1, 1]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![27, 0, -1], ![37, 0, 0]]], ![![![9, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-35, 1, 1]] ![![37, 0, 0], ![-2, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-74, 37, 0]], ![![-1295, 37, 37], ![-148, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-2, 1, 0]]], ![![![-35, 1, 1]], ![![-4, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-6, 8, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-6, 8, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![35, 8, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-6, 8, 1], ![-218, 31, 9], ![-1962, 115, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -8, 41]], ![![-1, 0, 1], ![-13, -1, 9], ![-82, -5, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [37, 27, 1] where
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
 g := ![![[24, 10], [20], [39], [27, 32], [1]], ![[0, 31], [20], [39], [24, 9], [1]]]
 h' := ![![[14, 40], [19, 25], [12, 15], [26, 30], [4, 14], [0, 1]], ![[0, 1], [0, 16], [17, 26], [36, 11], [36, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [2, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [37, 27, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-617, -134, 14]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, -6, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-9, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-9, 1, 0]] 
 ![![41, 0, 0], ![32, 1, 0], ![1, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-9, 1, 0], ![0, -9, 1], ![-218, 37, -8]]]
  hmulB := by decide  
  f := ![![![325, -36, 0], ![1476, 0, 0]], ![![262, -29, 0], ![1190, 0, 0]], ![![11, -1, 0], ![50, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 41, 0], ![-1, 0, 41]], ![![-1, 1, 0], ![7, -9, 1], ![-34, 37, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-6, 8, 1]] ![![41, 0, 0], ![-9, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-369, 41, 0]], ![![-246, 328, 41], ![-164, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-9, 1, 0]]], ![![![-6, 8, 1]], ![![-4, -1, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [8, 41, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 19, 22], [4, 23, 21], [0, 1]]
 g := ![![[16, 9, 40], [22, 20, 23], [28, 21], [27, 5, 1], []], ![[5, 40, 33, 5], [6, 3], [38, 17], [24, 7, 18, 28], [31, 11]], ![[27, 18, 17, 38], [20, 41, 6, 10], [41, 41], [35, 8, 39, 13], [32, 11]]]
 h' := ![![[1, 19, 22], [39, 34, 13], [35, 32, 18], [42, 14, 8], [0, 0, 1], [0, 1]], ![[4, 23, 21], [1, 28, 15], [7, 7], [15, 18, 19], [11, 12, 23], [1, 19, 22]], ![[0, 1], [22, 24, 15], [14, 4, 25], [27, 11, 16], [18, 31, 19], [4, 23, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 22], []]
 b := ![[], [22, 14, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [8, 41, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1305824, -509980, 48891]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30368, -11860, 1137]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-42, -7, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-42, -7, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![5, 40, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-42, -7, 1], ![-218, -5, -6], ![1308, -440, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -40, 47]], ![![-1, -1, 1], ![-4, 5, -6], ![29, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [29, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 46], [0, 1]]
 g := ![![[12, 4], [4, 9], [36, 18], [24, 32], [1]], ![[30, 43], [21, 38], [23, 29], [27, 15], [1]]]
 h' := ![![[28, 46], [25, 45], [37, 3], [9, 21], [18, 28], [0, 1]], ![[0, 1], [16, 2], [27, 44], [33, 26], [3, 19], [28, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [31, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [29, 19, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3127, -364, 146]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, -132, 146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![6, 1, 0]] 
 ![![47, 0, 0], ![6, 1, 0], ![11, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![6, 1, 0], ![0, 6, 1], ![-218, 37, 7]]]
  hmulB := by decide  
  f := ![![![37, 6, 0], ![-282, 0, 0]], ![![-6, -1, 0], ![48, 0, 0]], ![![1, 0, 0], ![-6, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 47, 0], ![-11, 0, 47]], ![![0, 1, 0], ![-1, 6, 1], ![-11, 37, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-42, -7, 1]] ![![47, 0, 0], ![6, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![282, 47, 0]], ![![-1974, -329, 47], ![-470, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![6, 1, 0]]], ![![![-42, -7, 1]], ![![-10, -1, 0]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [39, 26, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 17, 22], [32, 35, 31], [0, 1]]
 g := ![![[16, 43, 9], [32, 47], [18, 5, 7], [4, 28], [1]], ![[10, 23, 13, 41], [21, 46], [29, 35, 46, 33], [44, 37], [41, 44, 31, 48]], ![[1, 7, 1, 32], [39, 37], [27, 21, 40, 5], [32, 25], [5, 31, 1, 5]]]
 h' := ![![[12, 17, 22], [34, 3, 3], [40, 36, 10], [40, 37, 31], [14, 27, 44], [0, 1]], ![[32, 35, 31], [16, 26, 12], [27, 34, 29], [32, 35, 44], [23, 4, 14], [12, 17, 22]], ![[0, 1], [6, 24, 38], [19, 36, 14], [31, 34, 31], [31, 22, 48], [32, 35, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 43], []]
 b := ![[], [28, 2, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [39, 26, 9, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1071395, 378102, -28514]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20215, 7134, -538]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-25, 3, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-25, 3, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![34, 3, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-25, 3, 1], ![-218, 12, 4], ![-872, -70, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -3, 59]], ![![-1, 0, 1], ![-6, 0, 4], ![-24, -2, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [26, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 58], [0, 1]]
 g := ![![[43, 25], [38, 7], [29], [38, 53], [3, 1]], ![[0, 34], [0, 52], [29], [20, 6], [6, 58]]]
 h' := ![![[3, 58], [15, 54], [2, 19], [15, 41], [40, 42], [0, 1]], ![[0, 1], [0, 5], [0, 40], [20, 18], [48, 17], [3, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [54, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [26, 56, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-628, -163, -15]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -2, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-4, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-4, 1, 0]] 
 ![![59, 0, 0], ![55, 1, 0], ![43, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-4, 1, 0], ![0, -4, 1], ![-218, 37, -3]]]
  hmulB := by decide  
  f := ![![![69, -17, 0], ![1003, 0, 0]], ![![65, -16, 0], ![945, 0, 0]], ![![53, -13, 0], ![771, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 59, 0], ![-43, 0, 59]], ![![-1, 1, 0], ![3, -4, 1], ![-36, 37, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-25, 3, 1]] ![![59, 0, 0], ![-4, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-236, 59, 0]], ![![-1475, 177, 59], ![-118, 0, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-4, 1, 0]]], ![![![-25, 3, 1]], ![![-2, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-44, -21, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-44, -21, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![17, 40, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-44, -21, 1], ![-218, -7, -20], ![4360, -958, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -40, 61]], ![![-1, -1, 1], ![2, 13, -20], ![79, 2, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [47, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 60], [0, 1]]
 g := ![![[49, 13], [19], [25, 46], [44, 25], [15, 1]], ![[0, 48], [19], [44, 15], [53, 36], [30, 60]]]
 h' := ![![[15, 60], [34, 14], [45, 18], [6, 31], [27, 56], [0, 1]], ![[0, 1], [0, 47], [10, 43], [44, 30], [13, 5], [15, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [7, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [47, 46, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8408, 2137, 485]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-273, -283, 485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![27, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![0, 20, 1], ![-218, 37, 21]]]
  hmulB := by decide  
  f := ![![![481, 24, 0], ![-1464, 0, 0]], ![![140, 7, 0], ![-426, 0, 0]], ![![207, 10, 0], ![-630, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-27, 0, 61]], ![![0, 1, 0], ![-7, 20, 1], ![-25, 37, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-44, -21, 1]] ![![61, 0, 0], ![20, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1220, 61, 0]], ![![-2684, -1281, 61], ![-1098, -427, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![20, 1, 0]]], ![![![-44, -21, 1]], ![![-18, -7, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![1, -18, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![1, -18, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![1, 49, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![1, -18, 1], ![-218, 38, -17], ![3706, -847, 21]]]
  hmulB := by decide  
  f := ![![![0, 18, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -49, 67]], ![![0, -1, 1], ![-3, 13, -17], ![55, -28, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [24, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 66], [0, 1]]
 g := ![![[28, 14], [16, 55], [56], [39], [4], [1]], ![[0, 53], [40, 12], [56], [39], [4], [1]]]
 h' := ![![[65, 66], [18, 9], [50, 16], [56, 49], [11, 21], [43, 65], [0, 1]], ![[0, 1], [0, 58], [18, 51], [25, 18], [36, 46], [47, 2], [65, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [51, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [24, 2, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1113, -403, 41]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, -36, 41]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![17, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![17, 1, 0]] 
 ![![67, 0, 0], ![17, 1, 0], ![46, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![17, 1, 0], ![0, 17, 1], ![-218, 37, 18]]]
  hmulB := by decide  
  f := ![![![35, 2, 0], ![-134, 0, 0]], ![![-17, -1, 0], ![68, 0, 0]], ![![22, 1, 0], ![-84, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 67, 0], ![-46, 0, 67]], ![![0, 1, 0], ![-5, 17, 1], ![-25, 37, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![1, -18, 1]] ![![67, 0, 0], ![17, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1139, 67, 0]], ![![67, -1206, 67], ![-201, -268, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![17, 1, 0]]], ![![![1, -18, 1]], ![![-3, -4, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-28, 22, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-28, 22, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![43, 22, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-28, 22, 1], ![-218, 9, 23], ![-5014, 633, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -22, 71]], ![![-1, 0, 1], ![-17, -7, 23], ![-90, -1, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [9, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 70], [0, 1]]
 g := ![![[56, 8], [5, 30], [18, 1], [16], [49], [1]], ![[0, 63], [8, 41], [11, 70], [16], [49], [1]]]
 h' := ![![[64, 70], [26, 24], [51, 39], [23, 70], [66, 67], [62, 64], [0, 1]], ![[0, 1], [0, 47], [62, 32], [30, 1], [23, 4], [40, 7], [64, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [65, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [9, 7, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1735, -569, 171]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-128, -61, 171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-23, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-23, 1, 0]] 
 ![![71, 0, 0], ![48, 1, 0], ![39, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-23, 1, 0], ![0, -23, 1], ![-218, 37, -22]]]
  hmulB := by decide  
  f := ![![![1059, -46, 0], ![3266, 0, 0]], ![![714, -31, 0], ![2202, 0, 0]], ![![583, -25, 0], ![1798, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 71, 0], ![-39, 0, 71]], ![![-1, 1, 0], ![15, -23, 1], ![-16, 37, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-28, 22, 1]] ![![71, 0, 0], ![-23, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1633, 71, 0]], ![![-1988, 1562, 71], ![426, -497, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-23, 1, 0]]], ![![![-28, 22, 1]], ![![6, -7, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-56, -31, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-56, -31, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![17, 42, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-56, -31, 1], ![-218, -19, -30], ![6540, -1328, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -42, 73]], ![![-1, -1, 1], ![4, 17, -30], ![101, 10, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [7, 58, 1] where
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
 g := ![![[50, 54], [32], [6], [65, 19], [6], [1]], ![[57, 19], [32], [6], [58, 54], [6], [1]]]
 h' := ![![[15, 72], [49, 28], [28, 18], [56, 15], [7, 26], [66, 15], [0, 1]], ![[0, 1], [31, 45], [6, 55], [62, 58], [32, 47], [72, 58], [15, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [69, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [7, 58, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7975, -2824, 336]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, -232, 336]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![30, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![30, 1, 0]] 
 ![![73, 0, 0], ![30, 1, 0], ![49, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![30, 1, 0], ![0, 30, 1], ![-218, 37, 31]]]
  hmulB := by decide  
  f := ![![![721, 24, 0], ![-1752, 0, 0]], ![![270, 9, 0], ![-656, 0, 0]], ![![493, 16, 0], ![-1198, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 73, 0], ![-49, 0, 73]], ![![0, 1, 0], ![-13, 30, 1], ![-39, 37, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-56, -31, 1]] ![![73, 0, 0], ![30, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2190, 73, 0]], ![![-4088, -2263, 73], ![-1898, -949, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![30, 1, 0]]], ![![![-56, -31, 1]], ![![-26, -13, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-8, -33, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-8, -33, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![71, 46, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-8, -33, 1], ![-218, 29, -32], ![6976, -1402, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -46, 79]], ![![-1, -1, 1], ![26, 19, -32], ![91, -16, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [47, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 78], [0, 1]]
 g := ![![[59, 65], [6, 26], [28, 50], [32, 9], [64], [1]], ![[13, 14], [35, 53], [23, 29], [39, 70], [64], [1]]]
 h' := ![![[71, 78], [34, 12], [27, 42], [76, 34], [70, 3], [32, 71], [0, 1]], ![[0, 1], [17, 67], [7, 37], [41, 45], [46, 76], [17, 8], [71, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [23, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [47, 8, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![538, -289, 71]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57, -45, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![32, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![32, 1, 0]] 
 ![![79, 0, 0], ![32, 1, 0], ![3, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![32, 1, 0], ![0, 32, 1], ![-218, 37, 33]]]
  hmulB := by decide  
  f := ![![![833, 26, 0], ![-2054, 0, 0]], ![![288, 9, 0], ![-710, 0, 0]], ![![13, 0, 0], ![-32, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 79, 0], ![-3, 0, 79]], ![![0, 1, 0], ![-13, 32, 1], ![-19, 37, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-8, -33, 1]] ![![79, 0, 0], ![32, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2528, 79, 0]], ![![-632, -2607, 79], ![-474, -1027, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![32, 1, 0]]], ![![![-8, -33, 1]], ![![-6, -13, 0]]]]
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
  g := ![3, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB274I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![79507]
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
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
  β := ![I37N0, I37N1, I37N2, I41N1, I47N1, I59N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [], [I47N1], [], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
