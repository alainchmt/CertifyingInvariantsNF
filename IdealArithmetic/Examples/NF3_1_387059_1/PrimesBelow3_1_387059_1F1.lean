
import IdealArithmetic.Examples.NF3_1_387059_1.RI3_1_387059_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![38, 3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![38, 3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![1, 3, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![38, 3, 1], ![14, 5, 14], ![15, -103, 15]]]
  hmulB := by decide  
  f := ![![![-37, -3, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -3, 37]], ![![1, 0, 1], ![0, -1, 14], ![0, -4, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [27, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 36], [0, 1]]
 g := ![![[24, 11], [7], [9, 21], [28], [1]], ![[0, 26], [7], [17, 16], [28], [1]]]
 h' := ![![[18, 36], [30, 23], [16, 28], [10, 13], [10, 18], [0, 1]], ![[0, 1], [0, 14], [2, 9], [22, 24], [1, 19], [18, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [34, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [27, 19, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-439, -96, -1142]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 90, -1142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-14, 1, 0]] 
 ![![37, 0, 0], ![23, 1, 0], ![22, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-14, 1, 0], ![2, -15, 4], ![8, -30, -12]]]
  hmulB := by decide  
  f := ![![![59, -435, 116], ![0, -1073, 0]], ![![37, -270, 72], ![1, -666, 0]], ![![40, -259, 69], ![13, -638, 0]]]
  g := ![![![1, 0, 0], ![-23, 37, 0], ![-22, 0, 37]], ![![-1, 1, 0], ![7, -15, 4], ![26, -30, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![38, 3, 1]] ![![37, 0, 0], ![-14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-518, 37, 0]], ![![1406, 111, 37], ![-518, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-14, 1, 0]]], ![![![38, 3, 1]], ![![-14, -1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![0, -4, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![0, -4, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 37, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![0, -4, 1], ![0, -26, -14], ![-41, 107, -37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -37, 41]], ![![0, -1, 1], ![0, 12, -14], ![-1, 36, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [7, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 40], [0, 1]]
 g := ![![[10, 23], [39], [23], [2, 21], [1]], ![[40, 18], [39], [23], [8, 20], [1]]]
 h' := ![![[12, 40], [9, 8], [35, 11], [27, 8], [34, 12], [0, 1]], ![[0, 1], [23, 33], [3, 30], [0, 33], [14, 29], [12, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [10, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [7, 29, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-656, 509, -1224]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, 1117, -1224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![37, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![2, 13, 4], ![8, -30, 16]]]
  hmulB := by decide  
  f := ![![![23, 233, 72], ![41, -738, 0]], ![![-2, 77, 24], ![42, -246, 0]], ![![17, 210, 65], ![48, -666, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-37, 0, 41]], ![![0, 1, 0], ![-8, 13, 4], ![-4, -30, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![0, -4, 1]] ![![41, 0, 0], ![14, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![574, 41, 0]], ![![0, -164, 41], ![0, -82, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![14, 1, 0]]], ![![![0, -4, 1]], ![![0, -2, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![20, 4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![20, 4, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![20, 4, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![20, 4, 1], ![16, -14, 18], ![23, -133, -1]]]
  hmulB := by decide  
  f := ![![![-19, -4, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -4, 43]], ![![0, 0, 1], ![-8, -2, 18], ![1, -3, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [10, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 42], [0, 1]]
 g := ![![[6, 13], [9, 41], [4], [28, 31], [1]], ![[0, 30], [0, 2], [4], [17, 12], [1]]]
 h' := ![![[26, 42], [39, 20], [14, 16], [21, 2], [33, 26], [0, 1]], ![[0, 1], [0, 23], [0, 27], [30, 41], [21, 17], [26, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [21, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [10, 17, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37128, -52782, -119126]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54544, 9854, -119126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-18, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-18, 1, 0]] 
 ![![43, 0, 0], ![25, 1, 0], ![1, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-18, 1, 0], ![2, -19, 4], ![8, -30, -16]]]
  hmulB := by decide  
  f := ![![![1253, -15294, 3224], ![-860, -34658, 0]], ![![739, -8881, 1872], ![-472, -20124, 0]], ![![35, -356, 75], ![-6, -806, 0]]]
  g := ![![![1, 0, 0], ![-25, 43, 0], ![-1, 0, 43]], ![![-1, 1, 0], ![11, -19, 4], ![18, -30, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![20, 4, 1]] ![![43, 0, 0], ![-18, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-774, 43, 0]], ![![860, 172, 43], ![-344, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-18, 1, 0]]], ![![![20, 4, 1]], ![![-8, -2, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![21, -5, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![21, -5, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![21, 42, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![21, -5, 1], ![-2, -4, -18], ![-49, 137, -18]]]
  hmulB := by decide  
  f := ![![![-20, 5, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -42, 47]], ![![0, -1, 1], ![8, 16, -18], ![7, 19, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [35, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 46], [0, 1]]
 g := ![![[27, 7], [46, 32], [8, 12], [37, 25], [1]], ![[39, 40], [27, 15], [42, 35], [6, 22], [1]]]
 h' := ![![[42, 46], [35, 17], [2, 28], [21, 24], [12, 42], [0, 1]], ![[0, 1], [44, 30], [3, 19], [42, 23], [37, 5], [42, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [45, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [35, 5, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1112, 549, -2394]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1046, 2151, -2394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![18, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![18, 1, 0]] 
 ![![47, 0, 0], ![18, 1, 0], ![18, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![18, 1, 0], ![2, 17, 4], ![8, -30, 20]]]
  hmulB := by decide  
  f := ![![![1931, 20205, 4760], ![1175, -55930, 0]], ![![730, 7725, 1820], ![471, -21385, 0]], ![![738, 7738, 1823], ![454, -21420, 0]]]
  g := ![![![1, 0, 0], ![-18, 47, 0], ![-18, 0, 47]], ![![0, 1, 0], ![-8, 17, 4], ![4, -30, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![21, -5, 1]] ![![47, 0, 0], ![18, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![846, 47, 0]], ![![987, -235, 47], ![376, -94, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![18, 1, 0]]], ![![![21, -5, 1]], ![![8, -2, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![11, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![11, 1, 0]] 
 ![![53, 0, 0], ![11, 1, 0], ![26, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![11, 1, 0], ![2, 10, 4], ![8, -30, 13]]]
  hmulB := by decide  
  f := ![![![-1151, -6084, -2436], ![-318, 32277, 0]], ![![-241, -1259, -504], ![-52, 6678, 0]], ![![-569, -2985, -1195], ![-135, 15834, 0]]]
  g := ![![![1, 0, 0], ![-11, 53, 0], ![-26, 0, 53]], ![![0, 1, 0], ![-4, 10, 4], ![0, -30, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-6, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-6, 1, 0]] 
 ![![53, 0, 0], ![47, 1, 0], ![43, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-6, 1, 0], ![2, -7, 4], ![8, -30, -4]]]
  hmulB := by decide  
  f := ![![![2505, -8924, 5104], ![-424, -67628, 0]], ![![2221, -7910, 4524], ![-370, -59943, 0]], ![![2031, -7240, 4141], ![-356, -54868, 0]]]
  g := ![![![1, 0, 0], ![-47, 53, 0], ![-43, 0, 53]], ![![-1, 1, 0], ![3, -7, 4], ![30, -30, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![11, 1, 0]] ![![53, 0, 0], ![-6, 1, 0]]
  ![![53, 0, 0], ![37, 1, 1]] where
 M := ![![![2809, 0, 0], ![-318, 53, 0]], ![![583, 53, 0], ![-64, 4, 4]]]
 hmul := by decide  
 g := ![![![![16, -1, -1], ![53, 0, 0]], ![![-6, 1, 0], ![0, 0, 0]]], ![![![-26, 0, -1], ![53, 0, 0]], ![![-4, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![37, 1, 1]] ![![53, 0, 0], ![-6, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-318, 53, 0]], ![![1961, 53, 53], ![-212, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-6, 1, 0]]], ![![![37, 1, 1]], ![![-4, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![38, 20, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![38, 20, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![38, 20, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![38, 20, 1], ![48, -12, 82], ![151, -613, 49]]]
  hmulB := by decide  
  f := ![![![-37, -20, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -20, 59]], ![![0, 0, 1], ![-52, -28, 82], ![-29, -27, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [14, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 58], [0, 1]]
 g := ![![[40, 12], [35, 46], [20], [16, 1], [30, 1]], ![[46, 47], [58, 13], [20], [46, 58], [1, 58]]]
 h' := ![![[30, 58], [41, 22], [41, 39], [12, 43], [52, 1], [0, 1]], ![[0, 1], [52, 37], [31, 20], [4, 16], [23, 58], [30, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [41, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [14, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-482, -86, -1202]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![766, 406, -1202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-23, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-23, 1, 0]] 
 ![![59, 0, 0], ![36, 1, 0], ![10, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-23, 1, 0], ![2, -24, 4], ![8, -30, -21]]]
  hmulB := by decide  
  f := ![![![342, -4917, 820], ![-177, -12095, 0]], ![![205, -2998, 500], ![-117, -7375, 0]], ![![72, -834, 139], ![6, -2050, 0]]]
  g := ![![![1, 0, 0], ![-36, 59, 0], ![-10, 0, 59]], ![![-1, 1, 0], ![14, -24, 4], ![22, -30, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![38, 20, 1]] ![![59, 0, 0], ![-23, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1357, 59, 0]], ![![2242, 1180, 59], ![-826, -472, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-23, 1, 0]]], ![![![38, 20, 1]], ![![-14, -8, 1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![6, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![6, 1, 0]] 
 ![![61, 0, 0], ![6, 1, 0], ![54, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![6, 1, 0], ![2, 5, 4], ![8, -30, 8]]]
  hmulB := by decide  
  f := ![![![2209, 5604, 4488], ![366, -68442, 0]], ![![214, 549, 440], ![62, -6710, 0]], ![![1956, 4961, 3973], ![319, -60588, 0]]]
  g := ![![![1, 0, 0], ![-6, 61, 0], ![-54, 0, 61]], ![![0, 1, 0], ![-4, 5, 4], ![-4, -30, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![265, -4, 9]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![265, -4, 9]] 
 ![![61, 0, 0], ![15, 1, 0], ![9, 0, 1]] where
  M :=![![![265, -4, 9], ![64, -1, 2], ![-113, 3, -4]]]
  hmulB := by decide  
  f := ![![![-2, 11, 1]], ![![0, 2, 1]], ![![1, -4, 0]]]
  g := ![![![4, -4, 9], ![1, -1, 2], ![-2, 3, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-22, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-22, 1, 0]] 
 ![![61, 0, 0], ![39, 1, 0], ![57, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-22, 1, 0], ![2, -23, 4], ![8, -30, -20]]]
  hmulB := by decide  
  f := ![![![3107, -43027, 7488], ![-1769, -114192, 0]], ![![1975, -27489, 4784], ![-1158, -72956, 0]], ![![2891, -40205, 6997], ![-1687, -106704, 0]]]
  g := ![![![1, 0, 0], ![-39, 61, 0], ![-57, 0, 61]], ![![-1, 1, 0], ![11, -23, 4], ![38, -30, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![6, 1, 0]] ![![265, -4, 9]]
  ![![61, 0, 0], ![23, 5, 1]] where
 M := ![![![16165, -244, 549]], ![![1654, -25, 56]]]
 hmul := by decide  
 g := ![![![![219, -14, 7], ![122, 0, 0]]], ![![![6, -5, 0], ![56, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![23, 5, 1]] ![![61, 0, 0], ![-22, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1342, 61, 0]], ![![1403, 305, 61], ![-488, -122, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-22, 1, 0]]], ![![![23, 5, 1]], ![![-8, -2, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 1, 0]] 
 ![![67, 0, 0], ![39, 1, 0], ![32, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 1, 0], ![2, -29, 4], ![8, -30, -26]]]
  hmulB := by decide  
  f := ![![![3421, -63765, 8800], ![-2345, -147400, 0]], ![![2001, -37100, 5120], ![-1339, -85760, 0]], ![![1636, -30455, 4203], ![-1115, -70400, 0]]]
  g := ![![![1, 0, 0], ![-39, 67, 0], ![-32, 0, 67]], ![![-1, 1, 0], ![15, -29, 4], ![30, -30, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-12, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-12, 1, 0]] 
 ![![67, 0, 0], ![55, 1, 0], ![62, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-12, 1, 0], ![2, -13, 4], ![8, -30, -10]]]
  hmulB := by decide  
  f := ![![![3943, -26855, 8268], ![-1072, -138489, 0]], ![![3237, -22035, 6784], ![-870, -113632, 0]], ![![3650, -24851, 7651], ![-985, -128154, 0]]]
  g := ![![![1, 0, 0], ![-55, 67, 0], ![-62, 0, 67]], ![![-1, 1, 0], ![7, -13, 4], ![34, -30, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-28, 1, 0]] ![![67, 0, 0], ![-28, 1, 0]]
  ![![67, 0, 0], ![29, -31, 1]] where
 M := ![![![4489, 0, 0], ![-1876, 67, 0]], ![![-1876, 67, 0], ![786, -57, 4]]]
 hmul := by decide  
 g := ![![![![38, 31, -1], ![67, 0, 0]], ![![-28, 1, 0], ![0, 0, 0]]], ![![![-28, 1, 0], ![0, 0, 0]], ![![10, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  
def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![29, -31, 1]] ![![67, 0, 0], ![-12, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-804, 67, 0]], ![![1943, -2077, 67], ![-402, 402, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-12, 1, 0]]], ![![![29, -31, 1]], ![![-6, 6, -2]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![41, -25, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![41, -25, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![41, 46, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![41, -25, 1], ![-42, 36, -98], ![-209, 737, -38]]]
  hmulB := by decide  
  f := ![![![-40, 25, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -46, 71]], ![![0, -1, 1], ![56, 64, -98], ![19, 35, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [55, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 70], [0, 1]]
 g := ![![[20, 12], [5, 10], [], [57], [18], [1]], ![[26, 59], [10, 61], [], [57], [18], [1]]]
 h' := ![![[36, 70], [9, 56], [0, 9], [68], [47, 25], [16, 36], [0, 1]], ![[0, 1], [37, 15], [40, 62], [68], [24, 46], [34, 35], [36, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [42, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [55, 35, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16018, -21537, -50392]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28874, 32345, -50392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![27, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![27, 1, 0]] 
 ![![71, 0, 0], ![27, 1, 0], ![38, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![27, 1, 0], ![2, 26, 4], ![8, -30, 29]]]
  hmulB := by decide  
  f := ![![![3810, 61067, 9400], ![2343, -166850, 0]], ![![1435, 23205, 3572], ![924, -63403, 0]], ![![2019, 32683, 5031], ![1307, -89300, 0]]]
  g := ![![![1, 0, 0], ![-27, 71, 0], ![-38, 0, 71]], ![![0, 1, 0], ![-12, 26, 4], ![-4, -30, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![41, -25, 1]] ![![71, 0, 0], ![27, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1917, 71, 0]], ![![2911, -1775, 71], ![1065, -639, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![27, 1, 0]]], ![![![41, -25, 1]], ![![15, -9, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![30, -19, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![30, -19, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![30, 54, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![30, -19, 1], ![-30, 19, -74], ![-161, 557, -37]]]
  hmulB := by decide  
  f := ![![![-29, 19, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -54, 73]], ![![0, -1, 1], ![30, 55, -74], ![13, 35, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [34, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 72], [0, 1]]
 g := ![![[65, 37], [71], [48], [54, 9], [35], [1]], ![[55, 36], [71], [48], [20, 64], [35], [1]]]
 h' := ![![[53, 72], [41, 57], [22, 12], [62, 62], [39, 3], [39, 53], [0, 1]], ![[0, 1], [69, 16], [1, 61], [63, 11], [52, 70], [1, 20], [53, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [32, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [34, 20, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43, -54, -1]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, 0, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![1, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![1, 1, 0]] 
 ![![73, 0, 0], ![1, 1, 0], ![37, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![1, 1, 0], ![2, 0, 4], ![8, -30, 3]]]
  hmulB := by decide  
  f := ![![![-73, 0, -148], ![0, 2701, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-37, 0, -75], ![0, 1369, 0]]]
  g := ![![![1, 0, 0], ![-1, 73, 0], ![-37, 0, 73]], ![![0, 1, 0], ![-2, 0, 4], ![-1, -30, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![30, -19, 1]] ![![73, 0, 0], ![1, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![73, 73, 0]], ![![2190, -1387, 73], ![0, 0, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![1, 1, 0]]], ![![![30, -19, 1]], ![![0, 0, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-13, 14, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-13, 14, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![66, 14, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-13, 14, 1], ![36, -57, 58], ![103, -433, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -14, 79]], ![![-1, 0, 1], ![-48, -11, 58], ![13, -3, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [18, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 78], [0, 1]]
 g := ![![[62, 22], [14, 5], [51, 4], [66, 64], [21], [1]], ![[0, 57], [43, 74], [11, 75], [58, 15], [21], [1]]]
 h' := ![![[69, 78], [64, 38], [30, 59], [76, 77], [25, 71], [61, 69], [0, 1]], ![[0, 1], [0, 41], [72, 20], [17, 2], [26, 8], [3, 10], [69, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [73, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [18, 10, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1119, -144, -2764]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2295, 488, -2764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![21, 1, 0]] 
 ![![79, 0, 0], ![21, 1, 0], ![14, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![21, 1, 0], ![2, 20, 4], ![8, -30, 23]]]
  hmulB := by decide  
  f := ![![![5643, 62690, 12544], ![2370, -247744, 0]], ![![1498, 16652, 3332], ![633, -65807, 0]], ![![987, 11109, 2223], ![469, -43904, 0]]]
  g := ![![![1, 0, 0], ![-21, 79, 0], ![-14, 0, 79]], ![![0, 1, 0], ![-6, 20, 4], ![4, -30, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-13, 14, 1]] ![![79, 0, 0], ![21, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1659, 79, 0]], ![![-1027, 1106, 79], ![-237, 237, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![21, 1, 0]]], ![![![-13, 14, 1]], ![![-3, 3, 1]]]]
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


lemma PB177I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB177I1 : PrimesBelowBoundCertificateInterval O 31 79 177 where
  m := 11
  g := ![2, 2, 2, 2, 3, 2, 3, 3, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB177I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N0, I67N1]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
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
  β := ![I37N1, I41N1, I43N1, I47N1, I53N0, I53N1, I59N1, I61N0, I61N1, I61N2, I67N0, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [I53N0, I53N1, I53N1], [I59N1], [I61N0, I61N1, I61N2], [I67N0, I67N0, I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
