
import IdealArithmetic.Examples.NF3_1_329427_1.RI3_1_329427_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [22, 2, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 13, 21], [23, 23, 16], [0, 1]]
 g := ![![[14, 6, 28], [27, 16], [8, 0, 27], [11, 1], []], ![[19, 8, 18, 26], [23, 30], [10, 33], [32, 11], [32, 34]], ![[21, 1, 19, 33], [12, 21], [28, 7, 9, 25], [3, 21], [0, 34]]]
 h' := ![![[25, 13, 21], [5, 31, 19], [9, 14, 33], [17, 30, 8], [0, 0, 1], [0, 1]], ![[23, 23, 16], [19, 26, 15], [9, 16, 17], [24, 19], [32, 23, 23], [25, 13, 21]], ![[0, 1], [2, 17, 3], [28, 7, 24], [18, 25, 29], [11, 14, 13], [23, 23, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 22], []]
 b := ![[], [3, 31, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [22, 2, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-176490, -20609, -2072]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4770, -557, -56]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [15, 11, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 8, 21], [0, 32, 20], [0, 1]]
 g := ![![[11, 22, 10], [1, 20], [29, 36], [31, 40, 1], []], ![[35, 20], [7, 20], [37, 21], [16, 3, 15, 20], [18, 31]], ![[0, 3, 1, 36], [16, 39], [10, 36], [22, 9, 10, 9], [19, 31]]]
 h' := ![![[40, 8, 21], [34, 40, 25], [7, 28, 26], [27, 2, 6], [0, 0, 1], [0, 1]], ![[0, 32, 20], [34, 32], [37, 36, 26], [10, 1, 29], [18, 18, 32], [40, 8, 21]], ![[0, 1], [2, 10, 16], [18, 18, 30], [39, 38, 6], [2, 23, 8], [0, 32, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 20], []]
 b := ![[], [15, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [15, 11, 1, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![346532, 70479, 1640]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8452, 1719, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![13, -20, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![13, -20, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![13, 23, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![13, -20, 1], ![112, 3, -41], ![-2352, -149, 44]]]
  hmulB := by decide  
  f := ![![![-12, 20, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -23, 43]], ![![0, -1, 1], ![15, 22, -41], ![-68, -27, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [39, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 42], [0, 1]]
 g := ![![[6, 23], [2, 4], [6], [41, 17], [1]], ![[42, 20], [12, 39], [6], [19, 26], [1]]]
 h' := ![![[24, 42], [8, 25], [2, 41], [35, 36], [4, 24], [0, 1]], ![[0, 1], [6, 18], [40, 2], [39, 7], [21, 19], [24, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [32, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [39, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2807, 51, 120]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, -63, 120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-2, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-2, 1, 0]] 
 ![![43, 0, 0], ![41, 1, 0], ![42, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-2, 1, 0], ![0, -1, 2], ![112, 10, -3]]]
  hmulB := by decide  
  f := ![![![3, 20, -42], ![43, 903, 0]], ![![1, 20, -40], ![1, 860, 0]], ![![2, 20, -41], ![22, 882, 0]]]
  g := ![![![1, 0, 0], ![-41, 43, 0], ![-42, 0, 43]], ![![-1, 1, 0], ![-1, -1, 2], ![-4, 10, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![13, -20, 1]] ![![43, 0, 0], ![-2, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-86, 43, 0]], ![![559, -860, 43], ![86, 43, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-2, 1, 0]]], ![![![13, -20, 1]], ![![2, 1, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-6, -1, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-6, -1, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![41, 46, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-6, -1, 1], ![112, 3, -3], ![-224, 41, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -46, 47]], ![![-1, -1, 1], ![5, 3, -3], ![-10, -5, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [16, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 46], [0, 1]]
 g := ![![[2, 3], [23, 18], [26, 6], [28, 37], [1]], ![[0, 44], [11, 29], [22, 41], [19, 10], [1]]]
 h' := ![![[15, 46], [8, 12], [7, 26], [22, 37], [31, 15], [0, 1]], ![[0, 1], [0, 35], [21, 21], [13, 10], [21, 32], [15, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [36, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [16, 32, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-511, 1411, 93]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92, -61, 93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, 1, 0]] 
 ![![47, 0, 0], ![3, 1, 0], ![41, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, 1, 0], ![0, 4, 2], ![112, 10, 2]]]
  hmulB := by decide  
  f := ![![![43, 14, 0], ![-658, 0, 0]], ![![-3, -1, 0], ![48, 0, 0]], ![![37, 10, -1], ![-566, 24, 0]]]
  g := ![![![1, 0, 0], ![-3, 47, 0], ![-41, 0, 47]], ![![0, 1, 0], ![-2, 4, 2], ![0, 10, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-6, -1, 1]] ![![47, 0, 0], ![3, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![141, 47, 0]], ![![-282, -47, 47], ![94, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![3, 1, 0]]], ![![![-6, -1, 1]], ![![2, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![8, -19, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![8, -19, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![8, 34, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![8, -19, 1], ![112, -1, -39], ![-2240, -139, 38]]]
  hmulB := by decide  
  f := ![![![-7, 19, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -34, 53]], ![![0, -1, 1], ![8, 25, -39], ![-48, -27, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [41, 27, 1] where
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
 g := ![![[11, 10], [47], [11, 13], [1], [26, 1]], ![[6, 43], [47], [31, 40], [1], [52, 52]]]
 h' := ![![[26, 52], [21, 13], [26, 43], [48, 38], [47, 52], [0, 1]], ![[0, 1], [41, 40], [31, 10], [29, 15], [21, 1], [26, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [28, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [41, 27, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![377, 529, 14]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 1, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-14, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-14, 1, 0]] 
 ![![53, 0, 0], ![39, 1, 0], ![15, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-14, 1, 0], ![0, -13, 2], ![112, 10, -15]]]
  hmulB := by decide  
  f := ![![![491, -35, 0], ![1855, 0, 0]], ![![365, -26, 0], ![1379, 0, 0]], ![![149, -4, -1], ![563, 27, 0]]]
  g := ![![![1, 0, 0], ![-39, 53, 0], ![-15, 0, 53]], ![![-1, 1, 0], ![9, -13, 2], ![-1, 10, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![8, -19, 1]] ![![53, 0, 0], ![-14, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-742, 53, 0]], ![![424, -1007, 53], ![0, 265, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-14, 1, 0]]], ![![![8, -19, 1]], ![![0, 5, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [9, 48, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 48, 4], [18, 10, 55], [0, 1]]
 g := ![![[51, 24, 17], [4], [17, 21], [0, 29, 17], [1]], ![[37, 15, 0, 27], [48, 30, 42, 20], [9, 12], [42, 19], [10, 8, 40, 5]], ![[30, 56, 45, 44], [16, 30, 2, 39], [21, 41], [37, 58, 29, 50], [17, 8, 30, 54]]]
 h' := ![![[13, 48, 4], [23, 30, 28], [24, 57], [0, 56, 27], [50, 11, 31], [0, 1]], ![[18, 10, 55], [33, 14, 46], [57, 22, 51], [16, 36, 22], [42, 7], [13, 48, 4]], ![[0, 1], [29, 15, 44], [47, 39, 8], [0, 26, 10], [15, 41, 28], [18, 10, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 57], []]
 b := ![[], [0, 4, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [9, 48, 28, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74443014, 15177632, 2699486]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1261746, 257248, 45754]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![5, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![5, 1, 0]] 
 ![![61, 0, 0], ![5, 1, 0], ![46, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![5, 1, 0], ![0, 6, 2], ![112, 10, 4]]]
  hmulB := by decide  
  f := ![![![196, 39, 0], ![-2379, 0, 0]], ![![10, 2, 0], ![-121, 0, 0]], ![![146, 26, -1], ![-1772, 31, 0]]]
  g := ![![![1, 0, 0], ![-5, 61, 0], ![-46, 0, 61]], ![![0, 1, 0], ![-2, 6, 2], ![-2, 10, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-4, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-4, 1, 0]] 
 ![![61, 0, 0], ![57, 1, 0], ![55, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-4, 1, 0], ![0, -3, 2], ![112, 10, -5]]]
  hmulB := by decide  
  f := ![![![193, -48, 0], ![2928, 0, 0]], ![![181, -45, 0], ![2746, 0, 0]], ![![171, -41, -1], ![2594, 31, 0]]]
  g := ![![![1, 0, 0], ![-57, 61, 0], ![-55, 0, 61]], ![![-1, 1, 0], ![1, -3, 2], ![-3, 10, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-1, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-1, 1, 0]] 
 ![![61, 0, 0], ![60, 1, 0], ![0, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-1, 1, 0], ![0, 0, 2], ![112, 10, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 31, 0]]]
  g := ![![![1, 0, 0], ![-60, 61, 0], ![0, 0, 61]], ![![-1, 1, 0], ![0, 0, 2], ![-8, 10, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![5, 1, 0]] ![![61, 0, 0], ![-4, 1, 0]]
  ![![61, 0, 0], ![-10, 1, 1]] where
 M := ![![![3721, 0, 0], ![-244, 61, 0]], ![![305, 61, 0], ![-20, 2, 2]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![6, 0, -1], ![61, 0, 0]]], ![![![5, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-10, 1, 1]] ![![61, 0, 0], ![-1, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-61, 61, 0]], ![![-610, 61, 61], ![122, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-1, 1, 0]]], ![![![-10, 1, 1]], ![![2, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-26, -30, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-26, -30, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![41, 37, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-26, -30, 1], ![112, -46, -61], ![-3472, -249, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -37, 67]], ![![-1, -1, 1], ![39, 33, -61], ![-61, -12, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [63, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 66], [0, 1]]
 g := ![![[65, 40], [13, 25], [10], [59], [64], [1]], ![[13, 27], [14, 42], [10], [59], [64], [1]]]
 h' := ![![[59, 66], [52, 43], [28, 5], [51, 12], [4, 27], [4, 59], [0, 1]], ![[0, 1], [43, 24], [55, 62], [22, 55], [56, 40], [1, 8], [59, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [20, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [63, 8, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![392, 107, 21]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -10, 21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-6, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-6, 1, 0]] 
 ![![67, 0, 0], ![61, 1, 0], ![52, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-6, 1, 0], ![0, -5, 2], ![112, 10, -7]]]
  hmulB := by decide  
  f := ![![![349, -58, 0], ![3886, 0, 0]], ![![319, -53, 0], ![3552, 0, 0]], ![![268, -42, -1], ![2984, 34, 0]]]
  g := ![![![1, 0, 0], ![-61, 67, 0], ![-52, 0, 67]], ![![-1, 1, 0], ![3, -5, 2], ![-2, 10, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-26, -30, 1]] ![![67, 0, 0], ![-6, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-402, 67, 0]], ![![-1742, -2010, 67], ![268, 134, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-6, 1, 0]]], ![![![-26, -30, 1]], ![![4, 2, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![225, 3, -11]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![225, 3, -11]] 
 ![![71, 0, 0], ![0, 71, 0], ![57, 32, 1]] where
  M :=![![![225, 3, -11], ![-1232, 118, 17], ![1568, -531, 101]]]
  hmulB := by decide  
  f := ![![![295, 78, 19]], ![![2128, 563, 137]], ![![1289, 341, 83]]]
  g := ![![![12, 5, -11], ![-31, -6, 17], ![-59, -53, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [69, 51, 1] where
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
 g := ![![[10, 19], [61, 1], [43, 29], [54], [45], [1]], ![[35, 52], [10, 70], [55, 42], [54], [45], [1]]]
 h' := ![![[20, 70], [51, 27], [15, 70], [69, 10], [23, 57], [2, 20], [0, 1]], ![[0, 1], [23, 44], [66, 1], [56, 61], [27, 14], [47, 51], [20, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [62, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [69, 51, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![629, 1737, 518]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-407, -209, 518]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![295, 78, 19]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![295, 78, 19]] 
 ![![71, 0, 0], ![8, 1, 0], ![35, 0, 1]] where
  M :=![![![295, 78, 19], ![2128, 563, 137], ![6608, 1749, 426]]]
  hmulB := by decide  
  f := ![![![225, 3, -11]], ![![8, 2, -1]], ![![133, -6, -4]]]
  g := ![![![-14, 78, 19], ![-101, 563, 137], ![-314, 1749, 426]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![225, 3, -11]] ![![295, 78, 19]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-23, 6, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-23, 6, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![50, 6, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-23, 6, 1], ![112, -7, 11], ![560, 111, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -6, 73]], ![![-1, 0, 1], ![-6, -1, 11], ![20, 3, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [11, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 72], [0, 1]]
 g := ![![[66, 72], [70], [67], [53, 65], [16], [1]], ![[62, 1], [70], [67], [21, 8], [16], [1]]]
 h' := ![![[4, 72], [69, 46], [67, 56], [1, 40], [18, 49], [62, 4], [0, 1]], ![[0, 1], [34, 27], [72, 17], [15, 33], [68, 24], [5, 69], [4, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [52, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [11, 69, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6873, 2276, -10]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![101, 32, -10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-11, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-11, 1, 0]] 
 ![![73, 0, 0], ![62, 1, 0], ![18, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-11, 1, 0], ![0, -10, 2], ![112, 10, -12]]]
  hmulB := by decide  
  f := ![![![287, -26, 0], ![1898, 0, 0]], ![![232, -21, 0], ![1534, 0, 0]], ![![78, -2, -1], ![516, 37, 0]]]
  g := ![![![1, 0, 0], ![-62, 73, 0], ![-18, 0, 73]], ![![-1, 1, 0], ![8, -10, 2], ![-4, 10, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-23, 6, 1]] ![![73, 0, 0], ![-11, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-803, 73, 0]], ![![-1679, 438, 73], ![365, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-11, 1, 0]]], ![![![-23, 6, 1]], ![![5, -1, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![30, 5, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![30, 5, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![30, 5, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![30, 5, 1], ![112, 45, 9], ![448, 101, 36]]]
  hmulB := by decide  
  f := ![![![-29, -5, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -5, 79]], ![![0, 0, 1], ![-2, 0, 9], ![-8, -1, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [76, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 78], [0, 1]]
 g := ![![[30, 26], [4, 46], [9, 11], [46, 72], [42], [1]], ![[0, 53], [36, 33], [51, 68], [48, 7], [42], [1]]]
 h' := ![![[11, 78], [12, 42], [27, 58], [59, 66], [56, 54], [3, 11], [0, 1]], ![[0, 1], [0, 37], [33, 21], [74, 13], [18, 25], [45, 68], [11, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [28, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [76, 68, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1017, 51, 105]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, -6, 105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-9, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-9, 1, 0]] 
 ![![79, 0, 0], ![70, 1, 0], ![43, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-9, 1, 0], ![0, -8, 2], ![112, 10, -10]]]
  hmulB := by decide  
  f := ![![![415, -46, 0], ![3634, 0, 0]], ![![370, -41, 0], ![3240, 0, 0]], ![![235, -22, -1], ![2058, 40, 0]]]
  g := ![![![1, 0, 0], ![-70, 79, 0], ![-43, 0, 79]], ![![-1, 1, 0], ![6, -8, 2], ![-2, 10, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![30, 5, 1]] ![![79, 0, 0], ![-9, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-711, 79, 0]], ![![2370, 395, 79], ![-158, 0, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-9, 1, 0]]], ![![![30, 5, 1]], ![![-2, 0, 0]]]]
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


lemma PB163I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB163I1 : PrimesBelowBoundCertificateInterval O 31 79 163 where
  m := 11
  g := ![1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB163I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
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
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
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
      exact NI79N1
  β := ![I43N1, I47N1, I53N1, I61N0, I61N1, I61N2, I67N1, I71N1, I73N1, I79N1]
  Il := ![[], [], [I43N1], [I47N1], [I53N1], [], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
