
import IdealArithmetic.Examples.NF3_1_297332_1.RI3_1_297332_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![9, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![9, 1, 0]] 
 ![![37, 0, 0], ![9, 1, 0], ![15, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![9, 1, 0], ![0, 9, 2], ![154, 35, 9]]]
  hmulB := by decide  
  f := ![![![172, 19, 0], ![-703, 0, 0]], ![![36, 4, 0], ![-147, 0, 0]], ![![60, 2, -1], ![-245, 19, 0]]]
  g := ![![![1, 0, 0], ![-9, 37, 0], ![-15, 0, 37]], ![![0, 1, 0], ![-3, 9, 2], ![-8, 35, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![0, 14, 2], ![154, 35, 14]]]
  hmulB := by decide  
  f := ![![![85, 6, 0], ![-222, 0, 0]], ![![14, 1, 0], ![-36, 0, 0]], ![![17, -6, -1], ![-44, 19, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-13, 0, 37]], ![![0, 1, 0], ![-6, 14, 2], ![-14, 35, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![9, 1, 0]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0], ![-11, -7, 1]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![333, 37, 0], ![126, 23, 2]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![9, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-11, -7, 1]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![-407, -259, 37], ![0, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![14, 1, 0]]], ![![![-11, -7, 1]], ![![0, -2, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-18, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-18, 1, 0]] 
 ![![41, 0, 0], ![23, 1, 0], ![2, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-18, 1, 0], ![0, -18, 2], ![154, 35, -18]]]
  hmulB := by decide  
  f := ![![![433, -24, 0], ![984, 0, 0]], ![![235, -13, 0], ![534, 0, 0]], ![![22, 8, -1], ![50, 21, 0]]]
  g := ![![![1, 0, 0], ![-23, 41, 0], ![-2, 0, 41]], ![![-1, 1, 0], ![10, -18, 2], ![-15, 35, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-5, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-5, 1, 0]] 
 ![![41, 0, 0], ![36, 1, 0], ![8, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-5, 1, 0], ![0, -5, 2], ![154, 35, -5]]]
  hmulB := by decide  
  f := ![![![176, -35, 0], ![1435, 0, 0]], ![![156, -31, 0], ![1272, 0, 0]], ![![38, -5, -1], ![310, 21, 0]]]
  g := ![![![1, 0, 0], ![-36, 41, 0], ![-8, 0, 41]], ![![-1, 1, 0], ![4, -5, 2], ![-26, 35, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-18, 1, 0]] ![![41, 0, 0], ![-18, 1, 0]]
  ![![41, 0, 0], ![-43, -18, 1]] where
 M := ![![![1681, 0, 0], ![-738, 41, 0]], ![![-738, 41, 0], ![324, -36, 2]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![25, 19, -1], ![41, 0, 0]]], ![![![25, 19, -1], ![41, 0, 0]], ![![10, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-43, -18, 1]] ![![41, 0, 0], ![-5, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-205, 41, 0]], ![![-1763, -738, 41], ![369, 82, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-5, 1, 0]]], ![![![-43, -18, 1]], ![![9, 2, -1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N0
    exact isPrimeI41N1
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [25, 5, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 31, 27], [25, 11, 16], [0, 1]]
 g := ![![[21, 42, 15], [26, 13, 23], [19, 4], [36, 16, 1], []], ![[4, 24, 8, 26], [38, 18, 17, 33], [41, 40], [7, 17, 35, 42], [8, 41]], ![[40, 21, 27, 24], [8, 35, 22, 24], [41, 35], [37, 34, 16, 25], [19, 41]]]
 h' := ![![[34, 31, 27], [38, 24, 12], [7, 23, 25], [3, 22, 41], [0, 0, 1], [0, 1]], ![[25, 11, 16], [28, 16, 6], [7, 42, 36], [0, 15, 13], [10, 11, 11], [34, 31, 27]], ![[0, 1], [30, 3, 25], [32, 21, 25], [38, 6, 32], [21, 32, 31], [25, 11, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 19], []]
 b := ![[], [6, 31, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [25, 5, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19995, -5633, -903]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-465, -131, -21]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [13, 34, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 12, 19], [33, 34, 28], [0, 1]]
 g := ![![[30, 26, 24], [24, 18, 7], [3, 44, 17], [45, 19, 1], []], ![[46, 22, 9, 26], [13, 1, 34, 40], [6, 44, 43, 33], [16, 18, 3, 15], [30, 32]], ![[42, 33, 39, 36], [2, 26, 43, 9], [20, 14, 9, 3], [15, 14, 45, 37], [21, 32]]]
 h' := ![![[33, 12, 19], [17, 1, 20], [8, 2, 30], [26, 9, 8], [0, 0, 1], [0, 1]], ![[33, 34, 28], [24, 10, 41], [35, 21, 24], [40, 32, 20], [41, 14, 34], [33, 12, 19]], ![[0, 1], [14, 36, 33], [20, 24, 40], [36, 6, 19], [17, 33, 12], [33, 34, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 8], []]
 b := ![[], [7, 26, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [13, 34, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19552, 91227, 35297]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-416, 1941, 751]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-9, 15, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-9, 15, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![44, 15, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-9, 15, 1], ![154, 26, 30], ![2310, 602, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -15, 53]], ![![-1, 0, 1], ![-22, -8, 30], ![22, 4, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [39, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 52], [0, 1]]
 g := ![![[31, 15], [37], [50, 6], [11], [10, 1]], ![[22, 38], [37], [4, 47], [11], [20, 52]]]
 h' := ![![[10, 52], [3, 42], [11, 14], [38, 18], [34, 8], [0, 1]], ![[0, 1], [52, 11], [45, 39], [6, 35], [8, 45], [10, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [32, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [39, 43, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1075, -78, 122]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81, -36, 122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![23, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![23, 1, 0]] 
 ![![53, 0, 0], ![23, 1, 0], ![27, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![23, 1, 0], ![0, 23, 2], ![154, 35, 23]]]
  hmulB := by decide  
  f := ![![![369, 16, 0], ![-848, 0, 0]], ![![161, 7, 0], ![-370, 0, 0]], ![![201, -3, -1], ![-462, 27, 0]]]
  g := ![![![1, 0, 0], ![-23, 53, 0], ![-27, 0, 53]], ![![0, 1, 0], ![-11, 23, 2], ![-24, 35, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-9, 15, 1]] ![![53, 0, 0], ![23, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1219, 53, 0]], ![![-477, 795, 53], ![-53, 371, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![23, 1, 0]]], ![![![-9, 15, 1]], ![![-1, 7, 1]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [53, 6, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 16, 40], [37, 42, 19], [0, 1]]
 g := ![![[38, 37, 29], [28, 21, 46], [7, 25], [44, 28, 15], [1]], ![[8, 27, 37, 11], [28, 6, 9, 40], [43, 49], [26, 1, 11, 43], [26, 41, 19, 44]], ![[58, 11, 28, 1], [13, 34, 12, 15], [55, 4], [56, 24, 31, 9], [22, 11, 19, 15]]]
 h' := ![![[51, 16, 40], [50, 17, 18], [0, 52, 39], [28, 58, 5], [6, 53, 29], [0, 1]], ![[37, 42, 19], [42, 40, 20], [58, 54, 1], [6, 31, 52], [57, 35, 34], [51, 16, 40]], ![[0, 1], [15, 2, 21], [33, 12, 19], [36, 29, 2], [45, 30, 55], [37, 42, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 1], []]
 b := ![[], [9, 7, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [53, 6, 30, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-204730, -97763, -19293]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3470, -1657, -327]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![5, -9, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![5, -9, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![5, 52, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![5, -9, 1], ![154, 40, -18], ![-1386, -238, 40]]]
  hmulB := by decide  
  f := ![![![-4, 9, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -52, 61]], ![![0, -1, 1], ![4, 16, -18], ![-26, -38, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [3, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 60], [0, 1]]
 g := ![![[16, 41], [56], [11, 1], [20, 45], [13, 1]], ![[0, 20], [56], [24, 60], [56, 16], [26, 60]]]
 h' := ![![[13, 60], [6, 23], [28, 19], [1, 60], [22, 44], [0, 1]], ![[0, 1], [0, 38], [31, 42], [49, 1], [45, 17], [13, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [30, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [3, 48, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![311, 99, -11]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 11, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![18, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![18, 1, 0]] 
 ![![61, 0, 0], ![18, 1, 0], ![21, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![18, 1, 0], ![0, 18, 2], ![154, 35, 18]]]
  hmulB := by decide  
  f := ![![![235, 13, 0], ![-793, 0, 0]], ![![54, 3, 0], ![-182, 0, 0]], ![![75, -5, -1], ![-253, 31, 0]]]
  g := ![![![1, 0, 0], ![-18, 61, 0], ![-21, 0, 61]], ![![0, 1, 0], ![-6, 18, 2], ![-14, 35, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![5, -9, 1]] ![![61, 0, 0], ![18, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1098, 61, 0]], ![![305, -549, 61], ![244, -122, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![18, 1, 0]]], ![![![5, -9, 1]], ![![4, -2, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [29, 16, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 50, 4], [20, 16, 63], [0, 1]]
 g := ![![[49, 62, 26], [45, 56, 54], [20, 4], [13, 65], [6, 1], []], ![[29, 49, 11, 40], [32, 1, 23, 21], [22, 47], [61, 39], [22, 55], [27, 16]], ![[45, 2, 55, 42], [56, 1, 41, 20], [46, 29], [47, 6], [50, 21], [35, 16]]]
 h' := ![![[53, 50, 4], [35, 61, 19], [44, 0, 56], [17, 1, 65], [27, 9, 20], [0, 0, 1], [0, 1]], ![[20, 16, 63], [21, 28, 12], [2, 64, 25], [38, 19, 39], [20, 23, 21], [16, 49, 16], [53, 50, 4]], ![[0, 1], [22, 45, 36], [42, 3, 53], [61, 47, 30], [34, 35, 26], [55, 18, 50], [20, 16, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 4], []]
 b := ![[], [25, 21, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [29, 16, 61, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2806295, 814854, 134402]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41885, 12162, 2006]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [38, 65, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 24, 23], [58, 46, 48], [0, 1]]
 g := ![![[24, 13, 43], [46, 49, 27], [41, 15, 10], [7, 29], [69, 1], []], ![[56, 6, 68, 66], [41, 12, 40, 22], [66, 16, 42, 53], [39, 45], [38, 57], [46, 32]], ![[15, 29], [55, 34, 25, 60], [3, 58, 63, 15], [44, 48], [22, 8], [21, 32]]]
 h' := ![![[11, 24, 23], [27, 63, 16], [4, 34, 13], [43, 2, 62], [5, 21, 10], [0, 0, 1], [0, 1]], ![[58, 46, 48], [35, 32, 55], [30, 4, 31], [11, 64, 58], [12, 5, 20], [6, 14, 46], [11, 24, 23]], ![[0, 1], [7, 47], [47, 33, 27], [69, 5, 22], [45, 45, 41], [10, 57, 24], [58, 46, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 29], []]
 b := ![[], [68, 0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [38, 65, 2, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45866, 3692, -1846]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![646, 52, -26]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [45, 37, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 37, 39], [12, 35, 34], [0, 1]]
 g := ![![[15, 8, 23], [39, 23], [13, 25], [62, 5, 1], [67, 1], []], ![[52, 67, 0, 29], [46, 72], [67, 6], [70, 67, 37, 17], [47, 57], [38, 61]], ![[43, 30, 10, 13], [7, 67], [44, 35], [18, 70, 70, 47], [43, 55], [43, 61]]]
 h' := ![![[55, 37, 39], [52, 0, 13], [36, 4, 13], [57, 9, 5], [51, 31, 72], [0, 0, 1], [0, 1]], ![[12, 35, 34], [65, 42, 17], [50, 44, 27], [46, 1, 15], [3, 60, 6], [1, 65, 35], [55, 37, 39]], ![[0, 1], [56, 31, 43], [15, 25, 33], [43, 63, 53], [24, 55, 68], [34, 8, 37], [12, 35, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 48], []]
 b := ![[], [7, 44, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [45, 37, 6, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163593, 61539, 12994]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2241, 843, 178]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-14, 34, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-14, 34, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![65, 34, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-14, 34, 1], ![154, 21, 68], ![5236, 1267, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -34, 79]], ![![-1, 0, 1], ![-54, -29, 68], ![49, 7, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [17, 8, 1] where
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
 g := ![![[33, 13], [8, 45], [64, 49], [61, 9], [64], [1]], ![[8, 66], [43, 34], [67, 30], [68, 70], [64], [1]]]
 h' := ![![[71, 78], [22, 48], [18, 19], [69, 72], [70, 76], [62, 71], [0, 1]], ![[0, 1], [33, 31], [24, 60], [46, 7], [15, 3], [47, 8], [71, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [17, 8, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6123, -1212, 364]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-377, -172, 364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![11, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![11, 1, 0]] 
 ![![79, 0, 0], ![11, 1, 0], ![58, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![11, 1, 0], ![0, 11, 2], ![154, 35, 11]]]
  hmulB := by decide  
  f := ![![![331, 30, 0], ![-2370, 0, 0]], ![![33, 3, 0], ![-236, 0, 0]], ![![238, 16, -1], ![-1704, 40, 0]]]
  g := ![![![1, 0, 0], ![-11, 79, 0], ![-58, 0, 79]], ![![0, 1, 0], ![-3, 11, 2], ![-11, 35, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-14, 34, 1]] ![![79, 0, 0], ![11, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![869, 79, 0]], ![![-1106, 2686, 79], ![0, 395, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![11, 1, 0]]], ![![![-14, 34, 1]], ![![0, 5, 1]]]]
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


lemma PB155I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB155I1 : PrimesBelowBoundCertificateInterval O 31 79 155 where
  m := 11
  g := ![3, 3, 1, 1, 2, 1, 2, 1, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB155I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
      exact NI37N1
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N0
      exact NI41N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I41N0, I41N1, I53N1, I61N1, I79N1]
  Il := ![[I37N0, I37N1, I37N1], [I41N0, I41N0, I41N1], [], [], [I53N1], [], [I61N1], [], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
