
import IdealArithmetic.Examples.NF3_1_213716_1.RI3_1_213716_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [24, 29, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 29, 21], [13, 7, 16], [0, 1]]
 g := ![![[20, 1, 36], [11, 36], [33, 36, 28], [14, 1], []], ![[19, 9, 28, 26], [17, 34], [32, 11, 14, 1], [19, 12], [29, 34]], ![[4, 21, 16, 1], [0, 26], [8, 22, 20, 27], [28, 27], [34, 34]]]
 h' := ![![[1, 29, 21], [35, 8, 31], [22, 1, 31], [34, 14, 19], [0, 0, 1], [0, 1]], ![[13, 7, 16], [32, 21, 15], [12, 3, 16], [15, 32, 20], [8, 29, 7], [1, 29, 21]], ![[0, 1], [25, 8, 28], [32, 33, 27], [22, 28, 35], [19, 8, 29], [13, 7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 32], []]
 b := ![[], [4, 7, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [24, 29, 23, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16058, -3589, 333]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-434, -97, 9]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![16, 9, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![16, 9, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![16, 9, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![16, 9, 1], ![-86, 8, 10], ![-860, -166, 18]]]
  hmulB := by decide  
  f := ![![![-15, -9, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -9, 41]], ![![0, 0, 1], ![-6, -2, 10], ![-28, -8, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [34, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 40], [0, 1]]
 g := ![![[35, 21], [10], [39], [26, 1], [1]], ![[14, 20], [10], [39], [25, 40], [1]]]
 h' := ![![[40, 40], [25, 29], [23, 16], [18, 30], [7, 40], [0, 1]], ![[0, 1], [37, 12], [7, 25], [29, 11], [8, 1], [40, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [24, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [34, 1, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![292, -748, -74]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, -2, -74]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-10, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-10, 1, 0]] 
 ![![41, 0, 0], ![31, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-10, 1, 0], ![0, -10, 1], ![-86, -8, -9]]]
  hmulB := by decide  
  f := ![![![391, -39, 0], ![1599, 0, 0]], ![![301, -30, 0], ![1231, 0, 0]], ![![233, -23, 0], ![953, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 41, 0], ![-23, 0, 41]], ![![-1, 1, 0], ![7, -10, 1], ![9, -8, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![16, 9, 1]] ![![41, 0, 0], ![-10, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-410, 41, 0]], ![![656, 369, 41], ![-246, -82, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-10, 1, 0]]], ![![![16, 9, 1]], ![![-6, -2, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![8, -1, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![8, -1, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![8, 42, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![8, -1, 1], ![-86, 0, 0], ![0, -86, 0]]]
  hmulB := by decide  
  f := ![![![-7, 1, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -42, 43]], ![![0, -1, 1], ![-2, 0, 0], ![0, -2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [5, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 42], [0, 1]]
 g := ![![[42, 1], [35, 16], [31], [32, 25], [1]], ![[4, 42], [29, 27], [31], [28, 18], [1]]]
 h' := ![![[5, 42], [40, 1], [32, 4], [12, 17], [38, 5], [0, 1]], ![[0, 1], [2, 42], [9, 39], [11, 26], [20, 38], [5, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [1, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [5, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-214, -758, -188]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30, 166, -188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![0, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![0, 1, 0]] 
 ![![43, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![0, 0, 1], ![-86, -8, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![0, 0, 1], ![-2, -8, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![8, -1, 1]] ![![43, 0, 0], ![0, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![0, 43, 0]], ![![344, -43, 43], ![-86, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![0, 1, 0]]], ![![![8, -1, 1]], ![![-2, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![8, 0, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![8, 0, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![8, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![8, 0, 1], ![-86, 0, 1], ![-86, -94, 1]]]
  hmulB := by decide  
  f := ![![![-7, 0, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, 0, 47]], ![![0, 0, 1], ![-2, 0, 1], ![-2, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [25, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 46], [0, 1]]
 g := ![![[5, 32], [46, 3], [34, 17], [6, 21], [1]], ![[0, 15], [0, 44], [24, 30], [13, 26], [1]]]
 h' := ![![[16, 46], [25, 19], [43, 12], [38, 8], [22, 16], [0, 1]], ![[0, 1], [0, 28], [0, 35], [25, 39], [43, 31], [16, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [23, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [25, 31, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-233, -141, -35]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -3, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-1, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-1, 1, 0]] 
 ![![47, 0, 0], ![46, 1, 0], ![46, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-1, 1, 0], ![0, -1, 1], ![-86, -8, 0]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![141, 0, 0]], ![![2, -1, 0], ![48, 0, 0]], ![![2, -1, 0], ![48, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 47, 0], ![-46, 0, 47]], ![![-1, 1, 0], ![0, -1, 1], ![6, -8, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![8, 0, 1]] ![![47, 0, 0], ![-1, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-47, 47, 0]], ![![376, 0, 47], ![-94, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-1, 1, 0]]], ![![![8, 0, 1]], ![![-2, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![10, 1, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![10, 1, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![10, 1, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![10, 1, 1], ![-86, 2, 2], ![-172, -102, 4]]]
  hmulB := by decide  
  f := ![![![-9, -1, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -1, 53]], ![![0, 0, 1], ![-2, 0, 2], ![-4, -2, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [38, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 52], [0, 1]]
 g := ![![[40, 7], [7], [14, 11], [37], [17, 1]], ![[0, 46], [7], [42, 42], [37], [34, 52]]]
 h' := ![![[17, 52], [3, 31], [51, 22], [19, 8], [43, 39], [0, 1]], ![[0, 1], [0, 22], [1, 31], [49, 45], [17, 14], [17, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [45, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [38, 36, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3279, 324, 430]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, -2, 430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-2, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-2, 1, 0]] 
 ![![53, 0, 0], ![51, 1, 0], ![49, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-2, 1, 0], ![0, -2, 1], ![-86, -8, -1]]]
  hmulB := by decide  
  f := ![![![59, -29, 0], ![1537, 0, 0]], ![![57, -28, 0], ![1485, 0, 0]], ![![55, -27, 0], ![1433, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 53, 0], ![-49, 0, 53]], ![![-1, 1, 0], ![1, -2, 1], ![7, -8, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![10, 1, 1]] ![![53, 0, 0], ![-2, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-106, 53, 0]], ![![530, 53, 53], ![-106, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-2, 1, 0]]], ![![![10, 1, 1]], ![![-2, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [58, 8, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 27, 33], [25, 31, 26], [0, 1]]
 g := ![![[49, 36, 36], [41, 47, 16], [31, 19], [7, 8, 48], [1]], ![[25, 54, 9, 43], [8, 5, 53, 33], [25, 16], [16, 26, 7, 10], [45, 35, 35, 6]], ![[43, 30, 41, 22], [43, 18, 5, 57], [47, 29], [9, 2, 24, 16], [29, 7, 2, 53]]]
 h' := ![![[49, 27, 33], [41, 42, 53], [21, 57, 4], [7, 12, 14], [1, 51, 15], [0, 1]], ![[25, 31, 26], [0, 38, 20], [44, 8, 58], [45, 10, 4], [48, 46, 24], [49, 27, 33]], ![[0, 1], [48, 38, 45], [37, 53, 56], [7, 37, 41], [19, 21, 20], [25, 31, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 47], []]
 b := ![[], [34, 41, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [58, 8, 44, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14455, -1475, -649]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![245, -25, -11]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![24, -30, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![24, -30, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![24, 31, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![24, -30, 1], ![-86, 16, -29], ![2494, 146, -13]]]
  hmulB := by decide  
  f := ![![![-23, 30, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -31, 61]], ![![0, -1, 1], ![10, 15, -29], ![46, 9, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [9, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 60], [0, 1]]
 g := ![![[13, 34], [41], [39, 56], [23, 12], [5, 1]], ![[0, 27], [41], [14, 5], [22, 49], [10, 60]]]
 h' := ![![[5, 60], [39, 41], [15, 23], [37, 19], [16, 16], [0, 1]], ![[0, 1], [0, 20], [8, 38], [10, 42], [35, 45], [5, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [55, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [9, 56, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3221, -656, 152]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -88, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![29, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![29, 1, 0]] 
 ![![61, 0, 0], ![29, 1, 0], ![13, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![29, 1, 0], ![0, 29, 1], ![-86, -8, 30]]]
  hmulB := by decide  
  f := ![![![523, 18, 0], ![-1098, 0, 0]], ![![261, 9, 0], ![-548, 0, 0]], ![![101, 3, 0], ![-212, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 61, 0], ![-13, 0, 61]], ![![0, 1, 0], ![-14, 29, 1], ![-4, -8, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![24, -30, 1]] ![![61, 0, 0], ![29, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1769, 61, 0]], ![![1464, -1830, 61], ![610, -854, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![29, 1, 0]]], ![![![24, -30, 1]], ![![10, -14, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [12, 2, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 50, 42], [66, 16, 25], [0, 1]]
 g := ![![[65, 54, 10], [18, 57, 17], [40, 14], [26, 14], [23, 1], []], ![[5, 55, 22, 7], [57, 29, 3, 11], [65, 15], [50, 17], [52, 55], [16, 22]], ![[15, 1, 27, 55], [47, 45, 35, 56], [26, 23], [32, 40], [61, 21], [33, 22]]]
 h' := ![![[24, 50, 42], [52, 52, 55], [54, 66, 33], [20, 38, 58], [59, 9, 58], [0, 0, 1], [0, 1]], ![[66, 16, 25], [42, 65, 49], [39, 37, 17], [22, 49, 45], [35, 6, 33], [49, 27, 16], [24, 50, 42]], ![[0, 1], [50, 17, 30], [18, 31, 17], [53, 47, 31], [54, 52, 43], [7, 40, 50], [66, 16, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 7], []]
 b := ![[], [58, 25, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [12, 2, 44, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23517, -6901, 1139]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![351, -103, 17]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-6, -34, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-6, -34, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![65, 37, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-6, -34, 1], ![-86, -14, -33], ![2838, 178, -47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -37, 71]], ![![-1, -1, 1], ![29, 17, -33], ![83, 27, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [22, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 70], [0, 1]]
 g := ![![[14, 10], [1, 5], [51, 38], [2], [8], [1]], ![[58, 61], [23, 66], [62, 33], [2], [8], [1]]]
 h' := ![![[47, 70], [49, 62], [14, 17], [35, 31], [24, 12], [49, 47], [0, 1]], ![[0, 1], [52, 9], [32, 54], [1, 40], [20, 59], [57, 24], [47, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [50, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [22, 24, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-727, -262, -9]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 1, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![33, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![33, 1, 0]] 
 ![![71, 0, 0], ![33, 1, 0], ![47, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![33, 1, 0], ![0, 33, 1], ![-86, -8, 34]]]
  hmulB := by decide  
  f := ![![![595, 18, 0], ![-1278, 0, 0]], ![![297, 9, 0], ![-638, 0, 0]], ![![379, 11, 0], ![-814, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 71, 0], ![-47, 0, 71]], ![![0, 1, 0], ![-16, 33, 1], ![-20, -8, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-6, -34, 1]] ![![71, 0, 0], ![33, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2343, 71, 0]], ![![-426, -2414, 71], ![-284, -1136, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![33, 1, 0]]], ![![![-6, -34, 1]], ![![-4, -16, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![2, 29, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![2, 29, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![2, 29, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![2, 29, 1], ![-86, -6, 30], ![-2580, -326, 24]]]
  hmulB := by decide  
  f := ![![![-1, -29, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -29, 73]], ![![0, 0, 1], ![-2, -12, 30], ![-36, -14, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [43, 69, 1] where
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
 g := ![![[5, 2], [61], [6], [43, 71], [16], [1]], ![[13, 71], [61], [6], [35, 2], [16], [1]]]
 h' := ![![[4, 72], [24, 41], [26, 34], [49, 15], [66, 12], [30, 4], [0, 1]], ![[0, 1], [42, 32], [16, 39], [36, 58], [41, 61], [46, 69], [4, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [58, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [43, 69, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69, -15, -71]
  a := ![-3, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, 28, -71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-30, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-30, 1, 0]] 
 ![![73, 0, 0], ![43, 1, 0], ![49, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-30, 1, 0], ![0, -30, 1], ![-86, -8, -29]]]
  hmulB := by decide  
  f := ![![![1981, -66, 0], ![4818, 0, 0]], ![![1171, -39, 0], ![2848, 0, 0]], ![![1333, -44, 0], ![3242, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 73, 0], ![-49, 0, 73]], ![![-1, 1, 0], ![17, -30, 1], ![23, -8, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![2, 29, 1]] ![![73, 0, 0], ![-30, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2190, 73, 0]], ![![146, 2117, 73], ![-146, -876, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-30, 1, 0]]], ![![![2, 29, 1]], ![![-2, -12, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![11, -16, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![11, -16, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![11, 63, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![11, -16, 1], ![-86, 3, -15], ![1290, 34, -12]]]
  hmulB := by decide  
  f := ![![![-10, 16, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -63, 79]], ![![0, -1, 1], ![1, 12, -15], ![18, 10, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [69, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 78], [0, 1]]
 g := ![![[5, 45], [61, 9], [71, 44], [48, 25], [51], [1]], ![[43, 34], [37, 70], [59, 35], [34, 54], [51], [1]]]
 h' := ![![[50, 78], [57, 60], [78, 76], [6, 53], [57, 74], [10, 50], [0, 1]], ![[0, 1], [55, 19], [7, 3], [49, 26], [44, 5], [61, 29], [50, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [70, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [69, 29, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![99, 93, 9]
  a := ![1, 3, 0]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -6, 9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![15, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![15, 1, 0]] 
 ![![79, 0, 0], ![15, 1, 0], ![12, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![15, 1, 0], ![0, 15, 1], ![-86, -8, 16]]]
  hmulB := by decide  
  f := ![![![631, 42, 0], ![-3318, 0, 0]], ![![105, 7, 0], ![-552, 0, 0]], ![![78, 5, 0], ![-410, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 79, 0], ![-12, 0, 79]], ![![0, 1, 0], ![-3, 15, 1], ![-2, -8, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![11, -16, 1]] ![![79, 0, 0], ![15, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1185, 79, 0]], ![![869, -1264, 79], ![79, -237, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![15, 1, 0]]], ![![![11, -16, 1]], ![![1, -3, 0]]]]
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


lemma PB131I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB131I1 : PrimesBelowBoundCertificateInterval O 31 79 131 where
  m := 11
  g := ![1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB131I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N1, I43N1, I47N1, I53N1, I61N1, I71N1, I73N1, I79N1]
  Il := ![[], [I41N1], [I43N1], [I47N1], [I53N1], [], [I61N1], [], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
