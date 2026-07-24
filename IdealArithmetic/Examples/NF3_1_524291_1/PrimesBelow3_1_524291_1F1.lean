
import IdealArithmetic.Examples.NF3_1_524291_1.RI3_1_524291_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [4, 16, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 26], [5, 10], [0, 1]]
 g := ![![[14, 34, 25], [5, 34], [1, 3, 25], [23, 1], []], ![[31, 12, 28], [25, 33], [15, 20, 28], [4, 26], []], ![[32, 28, 21], [27, 7], [12, 14, 21], [28, 10], []]]
 h' := ![![[18, 26], [33, 6, 32], [33, 0, 21], [19, 35, 32], [0, 0, 1], [0, 1]], ![[5, 10], [1, 27, 24], [29, 9, 25], [28, 4, 24], [28, 11, 10], [18, 26]], ![[0, 1], [12, 4, 18], [3, 28, 28], [32, 35, 18], [25, 26, 26], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34], []]
 b := ![[], [11, 10, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [4, 16, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1052317, 3737, -22422]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28441, 101, -606]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![4, -14, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![4, -14, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![4, 27, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![4, -14, 1], ![112, 18, -54], ![-1855, 35, -23]]]
  hmulB := by decide  
  f := ![![![-3, 14, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -27, 41]], ![![0, -1, 1], ![8, 36, -54], ![-43, 16, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [40, 32, 1] where
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
 g := ![![[9, 40], [40], [1], [9, 40], [1]], ![[0, 1], [40], [1], [0, 1], [1]]]
 h' := ![![[9, 40], [40, 32], [0, 32], [9, 40], [1, 9], [0, 1]], ![[0, 1], [0, 9], [1, 9], [0, 1], [0, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [3, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [40, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-572, 1592, 267]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40, -137, 267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![13, 1, 0]] 
 ![![41, 0, 0], ![13, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, 1, 0], ![2, 12, 4], ![140, 0, 15]]]
  hmulB := by decide  
  f := ![![![-996, -6829, -2280], ![-451, 23370, 0]], ![![-321, -2157, -720], ![-122, 7380, 0]], ![![-560, -3831, -1279], ![-249, 13110, 0]]]
  g := ![![![1, 0, 0], ![-13, 41, 0], ![-23, 0, 41]], ![![0, 1, 0], ![-6, 12, 4], ![-5, 0, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![4, -14, 1]] ![![41, 0, 0], ![13, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![533, 41, 0]], ![![164, -574, 41], ![164, -164, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![13, 1, 0]]], ![![![4, -14, 1]], ![![4, -4, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![9, -4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![9, -4, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![9, 39, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![9, -4, 1], ![132, 13, -14], ![-455, 35, 2]]]
  hmulB := by decide  
  f := ![![![-8, 4, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -39, 43]], ![![0, -1, 1], ![6, 13, -14], ![-11, -1, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [1, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 42], [0, 1]]
 g := ![![[6, 1], [37, 15], [10], [11, 36], [1]], ![[0, 42], [33, 28], [10], [10, 7], [1]]]
 h' := ![![[37, 42], [6, 1], [25, 12], [32, 28], [42, 37], [0, 1]], ![[0, 1], [0, 42], [39, 31], [36, 15], [35, 6], [37, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [24, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [1, 6, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![442738, 152335, 12280]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7726, -7595, 12280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![14, 1, 0]] 
 ![![43, 0, 0], ![14, 1, 0], ![41, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![14, 1, 0], ![2, 13, 4], ![140, 0, 16]]]
  hmulB := by decide  
  f := ![![![2329, 17652, 5440], ![1204, -58480, 0]], ![![758, 5737, 1768], ![388, -19006, 0]], ![![2221, 16831, 5187], ![1147, -55760, 0]]]
  g := ![![![1, 0, 0], ![-14, 43, 0], ![-41, 0, 43]], ![![0, 1, 0], ![-8, 13, 4], ![-12, 0, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![9, -4, 1]] ![![43, 0, 0], ![14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![602, 43, 0]], ![![387, -172, 43], ![258, -43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![14, 1, 0]]], ![![![9, -4, 1]], ![![6, -1, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![20, -18, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![20, -18, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![20, 29, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![20, -18, 1], ![104, 38, -70], ![-2415, 35, -15]]]
  hmulB := by decide  
  f := ![![![-19, 18, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -29, 47]], ![![0, -1, 1], ![32, 44, -70], ![-45, 10, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [3, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 46], [0, 1]]
 g := ![![[11, 16], [3, 34], [34, 1], [28, 8], [1]], ![[0, 31], [9, 13], [1, 46], [46, 39], [1]]]
 h' := ![![[14, 46], [38, 4], [39, 9], [10, 1], [44, 14], [0, 1]], ![[0, 1], [0, 43], [24, 38], [24, 46], [5, 33], [14, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [20, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [3, 33, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![850, 2901, -216]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![110, 195, -216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![23, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![23, 1, 0]] 
 ![![47, 0, 0], ![23, 1, 0], ![15, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![23, 1, 0], ![2, 22, 4], ![140, 0, 25]]]
  hmulB := by decide  
  f := ![![![2432, 37577, 6840], ![2021, -80370, 0]], ![![1189, 18371, 3344], ![988, -39292, 0]], ![![761, 11992, 2183], ![676, -25650, 0]]]
  g := ![![![1, 0, 0], ![-23, 47, 0], ![-15, 0, 47]], ![![0, 1, 0], ![-12, 22, 4], ![-5, 0, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![20, -18, 1]] ![![47, 0, 0], ![23, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![1081, 47, 0]], ![![940, -846, 47], ![564, -376, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![23, 1, 0]]], ![![![20, -18, 1]], ![![12, -8, -1]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [31, 42, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 28, 35], [36, 24, 18], [0, 1]]
 g := ![![[17, 0, 10], [51, 49], [33, 4, 42], [22, 37], [1]], ![[8, 2, 44, 35], [35, 52], [42, 51, 3, 51], [21, 16], [34, 15, 2, 51]], ![[27, 11, 44, 48], [17, 52], [23, 20, 50, 51], [13, 6], [1, 42, 33, 2]]]
 h' := ![![[3, 28, 35], [0, 15, 40], [37, 11, 7], [14, 3, 28], [22, 11, 39], [0, 1]], ![[36, 24, 18], [17, 36, 1], [28, 50, 23], [14, 6, 35], [33, 29, 49], [3, 28, 35]], ![[0, 1], [13, 2, 12], [40, 45, 23], [34, 44, 43], [38, 13, 18], [36, 24, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 8], []]
 b := ![[], [40, 10, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [31, 42, 14, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1052368, 3763, -22578]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19856, 71, -426]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-2, 21, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-2, 21, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![57, 21, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-2, 21, 1], ![182, -23, 86], ![3045, 35, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -21, 59]], ![![-1, 0, 1], ![-80, -31, 86], ![12, -14, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [46, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 58], [0, 1]]
 g := ![![[41, 9], [54, 36], [29], [46, 53], [2, 1]], ![[0, 50], [8, 23], [29], [34, 6], [4, 58]]]
 h' := ![![[2, 58], [53, 3], [28, 6], [8, 41], [26, 17], [0, 1]], ![[0, 1], [0, 56], [40, 53], [31, 18], [1, 42], [2, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [19, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [46, 57, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![183891, 64613, 6024]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2703, -1049, 6024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-27, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-27, 1, 0]] 
 ![![59, 0, 0], ![32, 1, 0], ![18, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-27, 1, 0], ![2, -28, 4], ![140, 0, -25]]]
  hmulB := by decide  
  f := ![![![1849, -34920, 4992], ![-1416, -73632, 0]], ![![1002, -18915, 2704], ![-766, -39884, 0]], ![![576, -10654, 1523], ![-406, -22464, 0]]]
  g := ![![![1, 0, 0], ![-32, 59, 0], ![-18, 0, 59]], ![![-1, 1, 0], ![14, -28, 4], ![10, 0, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-2, 21, 1]] ![![59, 0, 0], ![-27, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1593, 59, 0]], ![![-118, 1239, 59], ![236, -590, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-27, 1, 0]]], ![![![-2, 21, 1]], ![![4, -10, 1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![28, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![28, 1, 0]] 
 ![![61, 0, 0], ![28, 1, 0], ![25, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![28, 1, 0], ![2, 27, 4], ![140, 0, 30]]]
  hmulB := by decide  
  f := ![![![-1143, -20722, -3072], ![-854, 46848, 0]], ![![-536, -9498, -1408], ![-365, 21472, 0]], ![![-479, -8493, -1259], ![-327, 19200, 0]]]
  g := ![![![1, 0, 0], ![-28, 61, 0], ![-25, 0, 61]], ![![0, 1, 0], ![-14, 27, 4], ![-10, 0, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-18, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-18, 1, 0]] 
 ![![61, 0, 0], ![43, 1, 0], ![37, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-18, 1, 0], ![2, -19, 4], ![140, 0, -16]]]
  hmulB := by decide  
  f := ![![![4405, -47618, 10032], ![-2074, -152988, 0]], ![![3103, -33549, 7068], ![-1463, -107787, 0]], ![![2671, -28883, 6085], ![-1261, -92796, 0]]]
  g := ![![![1, 0, 0], ![-43, 61, 0], ![-37, 0, 61]], ![![-1, 1, 0], ![11, -19, 4], ![12, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-11, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-11, 1, 0]] 
 ![![61, 0, 0], ![50, 1, 0], ![59, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-11, 1, 0], ![2, -12, 4], ![140, 0, -9]]]
  hmulB := by decide  
  f := ![![![-186, 1187, -396], ![61, 6039, 0]], ![![-150, 971, -324], ![62, 4941, 0]], ![![-179, 1148, -383], ![64, 5841, 0]]]
  g := ![![![1, 0, 0], ![-50, 61, 0], ![-59, 0, 61]], ![![-1, 1, 0], ![6, -12, 4], ![11, 0, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![28, 1, 0]] ![![61, 0, 0], ![-18, 1, 0]]
  ![![61, 0, 0], ![27, -13, 1]] where
 M := ![![![3721, 0, 0], ![-1098, 61, 0]], ![![1708, 61, 0], ![-502, 9, 4]]]
 hmul := by decide  
 g := ![![![![34, 13, -1], ![61, 0, 0]], ![![-18, 1, 0], ![0, 0, 0]]], ![![![1, 14, -1], ![61, 0, 0]], ![![-10, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![27, -13, 1]] ![![61, 0, 0], ![-11, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-671, 61, 0]], ![![1647, -793, 61], ![-183, 183, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-11, 1, 0]]], ![![![27, -13, 1]], ![![-3, 3, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-30, -28, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-30, -28, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![37, 39, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-30, -28, 1], ![84, -2, -110], ![-3815, 35, -85]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -39, 67]], ![![-1, -1, 1], ![62, 64, -110], ![-10, 50, -85]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [27, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 66], [0, 1]]
 g := ![![[20, 37], [63, 55], [55], [56], [16], [1]], ![[6, 30], [44, 12], [55], [56], [16], [1]]]
 h' := ![![[63, 66], [41, 38], [57, 16], [66, 16], [29, 18], [40, 63], [0, 1]], ![[0, 1], [23, 29], [60, 51], [2, 51], [24, 49], [56, 4], [63, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [35, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [27, 4, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![414, 38, 13]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -7, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-24, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-24, 1, 0]] 
 ![![67, 0, 0], ![43, 1, 0], ![18, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-24, 1, 0], ![2, -25, 4], ![140, 0, -22]]]
  hmulB := by decide  
  f := ![![![3955, -59591, 9540], ![-2278, -159795, 0]], ![![2533, -38228, 6120], ![-1473, -102510, 0]], ![![1074, -16010, 2563], ![-580, -42930, 0]]]
  g := ![![![1, 0, 0], ![-43, 67, 0], ![-18, 0, 67]], ![![-1, 1, 0], ![15, -25, 4], ![8, 0, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-30, -28, 1]] ![![67, 0, 0], ![-24, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1608, 67, 0]], ![![-2010, -1876, 67], ![804, 670, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-24, 1, 0]]], ![![![-30, -28, 1]], ![![12, 10, -2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![3, -15, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![3, -15, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![3, 56, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![3, -15, 1], ![110, 18, -58], ![-1995, 35, -26]]]
  hmulB := by decide  
  f := ![![![-2, 15, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -56, 71]], ![![0, -1, 1], ![4, 46, -58], ![-27, 21, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [16, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 70], [0, 1]]
 g := ![![[52, 40], [58, 5], [16, 16], [8], [45], [1]], ![[0, 31], [16, 66], [52, 55], [8], [45], [1]]]
 h' := ![![[20, 70], [66, 18], [28, 17], [38, 67], [33, 47], [55, 20], [0, 1]], ![[0, 1], [0, 53], [13, 54], [29, 4], [50, 24], [29, 51], [20, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [55, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [16, 51, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5204, 3374, 646]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, -462, 646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-13, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-13, 1, 0]] 
 ![![71, 0, 0], ![58, 1, 0], ![26, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-13, 1, 0], ![2, -14, 4], ![140, 0, -11]]]
  hmulB := by decide  
  f := ![![![1029, -7556, 2160], ![-284, -38340, 0]], ![![844, -6171, 1764], ![-212, -31311, 0]], ![![377, -2767, 791], ![-103, -14040, 0]]]
  g := ![![![1, 0, 0], ![-58, 71, 0], ![-26, 0, 71]], ![![-1, 1, 0], ![10, -14, 4], ![6, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![3, -15, 1]] ![![71, 0, 0], ![-13, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-923, 71, 0]], ![![213, -1065, 71], ![71, 213, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-13, 1, 0]]], ![![![3, -15, 1]], ![![1, 3, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![5, -9, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![5, -9, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![5, 64, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![5, -9, 1], ![122, 14, -34], ![-1155, 35, -12]]]
  hmulB := by decide  
  f := ![![![-4, 9, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -64, 73]], ![![0, -1, 1], ![4, 30, -34], ![-15, 11, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [21, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 72], [0, 1]]
 g := ![![[14, 69], [61], [49], [7, 9], [4], [1]], ![[22, 4], [61], [49], [62, 64], [4], [1]]]
 h' := ![![[71, 72], [69, 54], [67, 34], [72, 7], [65, 3], [52, 71], [0, 1]], ![[0, 1], [34, 19], [72, 39], [58, 66], [59, 70], [56, 2], [71, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [42, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [21, 2, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2661, 875, 65]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, -45, 65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![34, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![34, 1, 0]] 
 ![![73, 0, 0], ![34, 1, 0], ![12, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![34, 1, 0], ![2, 33, 4], ![140, 0, 36]]]
  hmulB := by decide  
  f := ![![![4319, 97567, 11832], ![3431, -215934, 0]], ![![2006, 45419, 5508], ![1607, -100521, 0]], ![![696, 16038, 1945], ![594, -35496, 0]]]
  g := ![![![1, 0, 0], ![-34, 73, 0], ![-12, 0, 73]], ![![0, 1, 0], ![-16, 33, 4], ![-4, 0, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![5, -9, 1]] ![![73, 0, 0], ![34, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2482, 73, 0]], ![![365, -657, 73], ![292, -292, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![34, 1, 0]]], ![![![5, -9, 1]], ![![4, -4, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [34, 41, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 12, 37], [3, 66, 42], [0, 1]]
 g := ![![[31, 53, 19], [14, 18, 49], [30, 57, 67], [20, 52, 8], [55, 1], []], ![[12, 63, 67, 35], [57, 57, 17, 29], [12, 5, 8, 69], [15, 67, 10, 77], [15, 11], [27, 26]], ![[46, 13, 45, 40], [6, 44, 7, 32], [55, 17, 23, 51], [9, 29, 56, 31], [77, 65], [22, 26]]]
 h' := ![![[52, 12, 37], [77, 48, 16], [7, 5, 72], [31, 63, 64], [26, 2, 61], [0, 0, 1], [0, 1]], ![[3, 66, 42], [23, 64, 67], [10, 47, 39], [59, 51, 77], [56, 47, 71], [48, 47, 66], [52, 12, 37]], ![[0, 1], [10, 46, 75], [60, 27, 47], [8, 44, 17], [62, 30, 26], [51, 32, 12], [3, 66, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 10], []]
 b := ![[], [35, 29, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [34, 41, 24, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4975578, -51666, -258330]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62982, -654, -3270]
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



lemma PB205I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB205I1 : PrimesBelowBoundCertificateInterval O 31 79 205 where
  m := 11
  g := ![1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB205I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
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
      exact NI61N2
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
  β := ![I41N1, I43N1, I47N1, I59N1, I61N0, I61N1, I61N2, I67N1, I71N1, I73N1]
  Il := ![[], [I41N1], [I43N1], [I47N1], [], [I59N1], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
