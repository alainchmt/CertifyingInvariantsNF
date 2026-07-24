
import IdealArithmetic.Examples.NF3_1_655215_2.RI3_1_655215_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 16, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 16, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![13, 16, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 16, 1], ![120, -6, 32], ![1860, -500, -22]]]
  hmulB := by decide  
  f := ![![![-12, -16, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -16, 37]], ![![0, 0, 1], ![-8, -14, 32], ![58, -4, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [35, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 36], [0, 1]]
 g := ![![[29, 4], [28], [1, 34], [34], [1]], ![[2, 33], [28], [12, 3], [34], [1]]]
 h' := ![![[21, 36], [23, 35], [2, 19], [35, 21], [2, 21], [0, 1]], ![[0, 1], [18, 2], [31, 18], [32, 16], [36, 16], [21, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [19, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [35, 16, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![935, 92, -355]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![150, 156, -355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![5, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![5, 1, 0]] 
 ![![37, 0, 0], ![5, 1, 0], ![22, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![5, 1, 0], ![0, 6, 2], ![120, -35, 5]]]
  hmulB := by decide  
  f := ![![![46, 9, 0], ![-333, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![26, 2, -1], ![-188, 19, 0]]]
  g := ![![![1, 0, 0], ![-5, 37, 0], ![-22, 0, 37]], ![![0, 1, 0], ![-2, 6, 2], ![5, -35, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![13, 16, 1]] ![![37, 0, 0], ![5, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![185, 37, 0]], ![![481, 592, 37], ![185, 74, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![5, 1, 0]]], ![![![13, 16, 1]], ![![5, 2, 1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![31, -6, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![31, -6, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![31, 35, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![31, -6, 1], ![120, -10, -12], ![-780, 270, -4]]]
  hmulB := by decide  
  f := ![![![-30, 6, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -35, 41]], ![![0, -1, 1], ![12, 10, -12], ![-16, 10, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [15, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 40], [0, 1]]
 g := ![![[36, 33], [8], [39], [31, 8], [1]], ![[10, 8], [8], [39], [16, 33], [1]]]
 h' := ![![[34, 40], [34, 19], [21, 34], [27, 11], [26, 34], [0, 1]], ![[0, 1], [24, 22], [29, 7], [32, 30], [34, 7], [34, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [23, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [15, 7, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9, 686, -538]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![407, 476, -538]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![0, 13, 2], ![120, -35, 12]]]
  hmulB := by decide  
  f := ![![![193, 16, 0], ![-656, 0, 0]], ![![60, 5, 0], ![-204, 0, 0]], ![![20, -5, -1], ![-68, 21, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-4, 0, 41]], ![![0, 1, 0], ![-4, 13, 2], ![12, -35, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![31, -6, 1]] ![![41, 0, 0], ![12, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![492, 41, 0]], ![![1271, -246, 41], ![492, -82, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![12, 1, 0]]], ![![![31, -6, 1]], ![![12, -2, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![28, -4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![28, -4, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![28, 39, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![28, -4, 1], ![120, -11, -8], ![-540, 200, -7]]]
  hmulB := by decide  
  f := ![![![-27, 4, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -39, 43]], ![![0, -1, 1], ![8, 7, -8], ![-8, 11, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [5, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[13, 16], [7, 16], [17], [21, 11], [1]], ![[5, 27], [42, 27], [17], [37, 32], [1]]]
 h' := ![![[21, 42], [8, 4], [18, 4], [24, 24], [38, 21], [0, 1]], ![[0, 1], [6, 39], [16, 39], [12, 19], [6, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [12, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [5, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2633, 60, 71]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, -63, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![8, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![8, 1, 0]] 
 ![![43, 0, 0], ![8, 1, 0], ![7, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![8, 1, 0], ![0, 9, 2], ![120, -35, 8]]]
  hmulB := by decide  
  f := ![![![153, 19, 0], ![-817, 0, 0]], ![![24, 3, 0], ![-128, 0, 0]], ![![13, -3, -1], ![-69, 22, 0]]]
  g := ![![![1, 0, 0], ![-8, 43, 0], ![-7, 0, 43]], ![![0, 1, 0], ![-2, 9, 2], ![8, -35, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![28, -4, 1]] ![![43, 0, 0], ![8, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![344, 43, 0]], ![![1204, -172, 43], ![344, -43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![8, 1, 0]]], ![![![28, -4, 1]], ![![8, -1, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [29, 14, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 34, 31], [41, 12, 16], [0, 1]]
 g := ![![[12, 25, 9], [24, 25, 21], [34, 7, 17], [0, 22, 1], []], ![[13, 36, 19, 26], [15, 42, 42, 38], [24, 40, 35, 15], [8, 15, 25, 46], [32, 21]], ![[2, 3, 6, 16], [28, 12, 24, 8], [7, 28, 28, 16], [2, 36, 33, 25], [0, 21]]]
 h' := ![![[28, 34, 31], [9, 21, 44], [1, 26, 16], [0, 20, 39], [0, 0, 1], [0, 1]], ![[41, 12, 16], [42, 6, 4], [23, 7, 11], [20, 14, 7], [44, 1, 12], [28, 34, 31]], ![[0, 1], [10, 20, 46], [45, 14, 20], [15, 13, 1], [36, 46, 34], [41, 12, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 5], []]
 b := ![[], [1, 8, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [29, 14, 25, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-509151, 359080, -184052]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10833, 7640, -3916]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [42, 41, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 22, 34], [15, 30, 19], [0, 1]]
 g := ![![[32, 50, 49], [51, 47], [25, 15, 10], [52, 16], [1]], ![[16, 35, 22, 32], [46, 38], [49, 31, 31, 33], [5, 52], [14, 22, 11, 31]], ![[29, 48, 37, 18], [34, 7], [0, 24, 2, 23], [6, 43], [16, 52, 19, 22]]]
 h' := ![![[34, 22, 34], [25, 43, 46], [10, 4, 10], [4, 4, 40], [11, 12, 49], [0, 1]], ![[15, 30, 19], [44, 20, 33], [42, 48, 12], [42, 34, 11], [26, 15, 23], [34, 22, 34]], ![[0, 1], [31, 43, 27], [44, 1, 31], [13, 15, 2], [0, 26, 34], [15, 30, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 7], []]
 b := ![[], [36, 35, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [42, 41, 4, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22578, 45156, -36782]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-426, 852, -694]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![37, 8, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![37, 8, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![37, 8, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![37, 8, 1], ![120, 10, 16], ![900, -220, 2]]]
  hmulB := by decide  
  f := ![![![-36, -8, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -8, 59]], ![![0, 0, 1], ![-8, -2, 16], ![14, -4, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [32, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 58], [0, 1]]
 g := ![![[16, 3], [34, 28], [15], [31, 35], [19, 1]], ![[14, 56], [35, 31], [15], [47, 24], [38, 58]]]
 h' := ![![[19, 58], [33, 11], [54, 38], [11, 29], [41, 34], [0, 1]], ![[0, 1], [6, 48], [9, 21], [31, 30], [38, 25], [19, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [33, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [32, 40, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74413, -1700, -13753]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9886, 1836, -13753]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-16, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-16, 1, 0]] 
 ![![59, 0, 0], ![43, 1, 0], ![57, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-16, 1, 0], ![0, -15, 2], ![120, -35, -16]]]
  hmulB := by decide  
  f := ![![![17, 659, -88], ![59, 2596, 0]], ![![17, 479, -64], ![60, 1888, 0]], ![![11, 637, -85], ![37, 2508, 0]]]
  g := ![![![1, 0, 0], ![-43, 59, 0], ![-57, 0, 59]], ![![-1, 1, 0], ![9, -15, 2], ![43, -35, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![37, 8, 1]] ![![59, 0, 0], ![-16, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-944, 59, 0]], ![![2183, 472, 59], ![-472, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-16, 1, 0]]], ![![![37, 8, 1]], ![![-8, -2, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [50, 60, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 0, 60], [0, 60, 1], [0, 1]]
 g := ![![[49, 59, 45], [57, 13], [27, 24, 9], [16, 17, 39], [1]], ![[25, 6, 33, 20], [55, 22], [40, 46, 31, 4], [42, 40, 14, 41], [28, 52, 10, 60]], ![[0, 27, 60, 36], [58, 5], [42, 33, 12, 56], [41, 33, 7, 1], [60, 12, 48, 1]]]
 h' := ![![[51, 0, 60], [20, 6, 17], [53, 35, 14], [54, 19, 3], [11, 1, 51], [0, 1]], ![[0, 60, 1], [34, 17, 38], [51, 14, 12], [17, 3, 39], [40, 51, 9], [51, 0, 60]], ![[0, 1], [33, 38, 6], [35, 12, 35], [24, 39, 19], [50, 9, 1], [0, 60, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 15], []]
 b := ![[], [53, 59, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [50, 60, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11041, 3172, 915]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-181, 52, 15]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![44, -23, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![44, -23, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![44, 44, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![44, -23, 1], ![120, -14, -46], ![-2820, 865, 9]]]
  hmulB := by decide  
  f := ![![![-43, 23, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -44, 67]], ![![0, -1, 1], ![32, 30, -46], ![-48, 7, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [59, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 66], [0, 1]]
 g := ![![[52, 25], [59, 24], [36], [65], [62], [1]], ![[0, 42], [60, 43], [36], [65], [62], [1]]]
 h' := ![![[14, 66], [3, 62], [60, 15], [24, 61], [24, 20], [8, 14], [0, 1]], ![[0, 1], [0, 5], [2, 52], [7, 6], [36, 47], [3, 53], [14, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [3, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [59, 53, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2159, 618, -592]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![421, 398, -592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-21, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-21, 1, 0]] 
 ![![67, 0, 0], ![46, 1, 0], ![58, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-21, 1, 0], ![0, -20, 2], ![120, -35, -21]]]
  hmulB := by decide  
  f := ![![![841, -40, 0], ![2680, 0, 0]], ![![610, -29, 0], ![1944, 0, 0]], ![![760, -26, -1], ![2422, 34, 0]]]
  g := ![![![1, 0, 0], ![-46, 67, 0], ![-58, 0, 67]], ![![-1, 1, 0], ![12, -20, 2], ![44, -35, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![44, -23, 1]] ![![67, 0, 0], ![-21, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1407, 67, 0]], ![![2948, -1541, 67], ![-804, 469, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-21, 1, 0]]], ![![![44, -23, 1]], ![![-12, 7, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![42, -29, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![42, -29, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![42, 42, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![42, -29, 1], ![120, -22, -58], ![-3540, 1075, 7]]]
  hmulB := by decide  
  f := ![![![-41, 29, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -42, 71]], ![![0, -1, 1], ![36, 34, -58], ![-54, 11, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [58, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 70], [0, 1]]
 g := ![![[5, 60], [68, 24], [59, 24], [5], [36], [1]], ![[0, 11], [66, 47], [57, 47], [5], [36], [1]]]
 h' := ![![[65, 70], [32, 29], [57, 33], [69, 38], [69, 54], [13, 65], [0, 1]], ![[0, 1], [0, 42], [1, 38], [54, 33], [29, 17], [49, 6], [65, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [8, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [58, 6, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9434, -1216, -1192]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![838, 688, -1192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-13, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-13, 1, 0]] 
 ![![71, 0, 0], ![58, 1, 0], ![64, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-13, 1, 0], ![0, -12, 2], ![120, -35, -13]]]
  hmulB := by decide  
  f := ![![![170, -13, 0], ![923, 0, 0]], ![![144, -11, 0], ![782, 0, 0]], ![![158, -6, -1], ![858, 36, 0]]]
  g := ![![![1, 0, 0], ![-58, 71, 0], ![-64, 0, 71]], ![![-1, 1, 0], ![8, -12, 2], ![42, -35, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![42, -29, 1]] ![![71, 0, 0], ![-13, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-923, 71, 0]], ![![2982, -2059, 71], ![-426, 355, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-13, 1, 0]]], ![![![42, -29, 1]], ![![-6, 5, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![6, 10, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![6, 10, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![6, 10, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![6, 10, 1], ![120, -19, 20], ![1140, -290, -29]]]
  hmulB := by decide  
  f := ![![![-5, -10, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -10, 73]], ![![0, 0, 1], ![0, -3, 20], ![18, 0, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [24, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 72], [0, 1]]
 g := ![![[28, 70], [2], [71], [47, 72], [6], [1]], ![[0, 3], [2], [71], [62, 1], [6], [1]]]
 h' := ![![[58, 72], [37, 56], [42, 41], [40, 12], [67, 46], [49, 58], [0, 1]], ![[0, 1], [0, 17], [11, 32], [6, 61], [34, 27], [55, 15], [58, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [61, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [24, 15, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![328, 60, 6]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 0, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-20, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-20, 1, 0]] 
 ![![73, 0, 0], ![53, 1, 0], ![29, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-20, 1, 0], ![0, -19, 2], ![120, -35, -20]]]
  hmulB := by decide  
  f := ![![![661, -33, 0], ![2409, 0, 0]], ![![481, -24, 0], ![1753, 0, 0]], ![![273, -4, -1], ![995, 37, 0]]]
  g := ![![![1, 0, 0], ![-53, 73, 0], ![-29, 0, 73]], ![![-1, 1, 0], ![13, -19, 2], ![35, -35, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![6, 10, 1]] ![![73, 0, 0], ![-20, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1460, 73, 0]], ![![438, 730, 73], ![0, -219, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-20, 1, 0]]], ![![![6, 10, 1]], ![![0, -3, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [55, 21, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 36, 16], [71, 42, 63], [0, 1]]
 g := ![![[77, 24, 46], [8], [1, 59, 5], [37, 37, 50], [23, 1], []], ![[20, 47, 78, 67], [77, 24, 67, 62], [69, 25, 34, 19], [25, 53, 24, 32], [58, 26], [9, 19]], ![[34, 12, 6, 74], [59, 36, 30, 17], [42, 62, 71, 12], [2, 65, 78, 41], [59, 32], [41, 19]]]
 h' := ![![[31, 36, 16], [34, 13, 21], [24, 18], [19, 33, 59], [78, 15, 34], [0, 0, 1], [0, 1]], ![[71, 42, 63], [32, 17, 63], [29, 16, 51], [17, 30, 4], [34, 28, 9], [71, 50, 42], [31, 36, 16]], ![[0, 1], [55, 49, 74], [38, 45, 28], [46, 16, 16], [40, 36, 36], [21, 29, 36], [71, 42, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 10], []]
 b := ![[], [35, 23, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [55, 21, 56, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![526693, 220410, -357396]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6667, 2790, -4524]
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



lemma PB230I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB230I1 : PrimesBelowBoundCertificateInterval O 31 79 230 where
  m := 11
  g := ![2, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB230I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
  β := ![I37N1, I41N1, I43N1, I59N1, I67N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [I43N1], [], [], [I59N1], [], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
