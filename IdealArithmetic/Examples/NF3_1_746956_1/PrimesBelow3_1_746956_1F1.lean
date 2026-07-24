
import IdealArithmetic.Examples.NF3_1_746956_1.RI3_1_746956_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![9, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![9, 1, 0]] 
 ![![37, 0, 0], ![9, 1, 0], ![33, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![9, 1, 0], ![-1, 13, 11], ![106, -23, 5]]]
  hmulB := by decide  
  f := ![![![133, -1716, -1452], ![0, 4884, 0]], ![![32, -416, -352], ![1, 1184, 0]], ![![114, -1531, -1295], ![19, 4356, 0]]]
  g := ![![![1, 0, 0], ![-9, 37, 0], ![-33, 0, 37]], ![![0, 1, 0], ![-13, 13, 11], ![4, -23, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-18, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-18, 1, 0]] 
 ![![37, 0, 0], ![19, 1, 0], ![14, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-18, 1, 0], ![-1, -14, 11], ![106, -23, -22]]]
  hmulB := by decide  
  f := ![![![69, 952, -748], ![0, 2516, 0]], ![![35, 476, -374], ![1, 1258, 0]], ![![30, 360, -283], ![8, 952, 0]]]
  g := ![![![1, 0, 0], ![-19, 37, 0], ![-14, 0, 37]], ![![-1, 1, 0], ![3, -14, 11], ![23, -23, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![9, 1, 0]] ![![37, 0, 0], ![9, 1, 0]]
  ![![37, 0, 0], ![14, 2, 1]] where
 M := ![![![1369, 0, 0], ![333, 37, 0]], ![![333, 37, 0], ![80, 22, 11]]]
 hmul := by decide  
 g := ![![![![23, -2, -1], ![37, 0, 0]], ![![-5, -1, -1], ![37, 0, 0]]], ![![![-5, -1, -1], ![37, 0, 0]], ![![-2, 0, 0], ![11, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![14, 2, 1]] ![![37, 0, 0], ![-18, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-666, 37, 0]], ![![518, 74, 37], ![-148, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-18, 1, 0]]], ![![![14, 2, 1]], ![![-4, -1, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [16, 14, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 0, 3], [26, 40, 38], [0, 1]]
 g := ![![[18, 40, 40], [11, 36], [37, 20], [37, 25, 1], []], ![[25, 39, 38, 34], [13, 5], [40, 23], [24, 38, 36, 3], [20, 9]], ![[26, 38, 13, 34], [1, 8], [26, 8], [0, 27], [26, 9]]]
 h' := ![![[40, 0, 3], [21, 15, 9], [19, 25, 6], [23, 25, 26], [0, 0, 1], [0, 1]], ![[26, 40, 38], [5, 38, 36], [7, 39, 28], [27, 5, 8], [9, 27, 40], [40, 0, 3]], ![[0, 1], [4, 29, 37], [15, 18, 7], [12, 11, 7], [14, 14], [26, 40, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 27], []]
 b := ![[], [32, 24, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [16, 14, 16, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-421316, 138006, -695442]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10276, 3366, -16962]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [33, 7, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 33, 17], [31, 9, 26], [0, 1]]
 g := ![![[39, 30, 24], [38, 32, 31], [23, 38], [31, 34, 1], []], ![[16, 25, 29, 25], [35, 40, 40, 21], [14, 11], [20, 20, 37, 1], [26, 31]], ![[32, 42, 2, 34], [37, 22, 2, 19], [6, 15], [42, 24, 3, 20], [17, 31]]]
 h' := ![![[3, 33, 17], [36, 25, 29], [10, 25, 26], [9, 37, 9], [0, 0, 1], [0, 1]], ![[31, 9, 26], [0, 2, 41], [27, 13, 14], [4, 27, 22], [11, 25, 9], [3, 33, 17]], ![[0, 1], [27, 16, 16], [5, 5, 3], [26, 22, 12], [13, 18, 33], [31, 9, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 7], []]
 b := ![[], [41, 42, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [33, 7, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50290908, -12076722, 14132896]
  a := ![-3, 9, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1169556, -280854, 328672]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![18, -18, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![18, -18, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![18, 29, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![18, -18, 1], ![124, -77, -202], ![-1983, 432, 70]]]
  hmulB := by decide  
  f := ![![![-17, 18, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -29, 47]], ![![0, -1, 1], ![80, 123, -202], ![-69, -34, 70]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [26, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 46], [0, 1]]
 g := ![![[30, 4], [14, 14], [43, 9], [43, 32], [1]], ![[12, 43], [45, 33], [26, 38], [40, 15], [1]]]
 h' := ![![[19, 46], [12, 2], [10, 25], [10, 3], [21, 19], [0, 1]], ![[0, 1], [3, 45], [15, 22], [20, 44], [6, 28], [19, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [3, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [26, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![638991, -113954, -105571]
  a := ![1, -67, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54027, 62715, -105571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![14, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![14, 1, 0]] 
 ![![47, 0, 0], ![14, 1, 0], ![24, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![14, 1, 0], ![-1, 18, 11], ![106, -23, 10]]]
  hmulB := by decide  
  f := ![![![1546, -27304, -16687], ![-94, 71299, 0]], ![![451, -8118, -4961], ![1, 21197, 0]], ![![782, -13943, -8521], ![-23, 36408, 0]]]
  g := ![![![1, 0, 0], ![-14, 47, 0], ![-24, 0, 47]], ![![0, 1, 0], ![-11, 18, 11], ![4, -23, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![18, -18, 1]] ![![47, 0, 0], ![14, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![658, 47, 0]], ![![846, -846, 47], ![376, -329, -188]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![14, 1, 0]]], ![![![18, -18, 1]], ![![8, -7, -4]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![35, 27, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![35, 27, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![35, 27, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![35, 27, 1], ![79, 120, 293], ![2787, -603, -93]]]
  hmulB := by decide  
  f := ![![![-34, -27, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -27, 53]], ![![0, 0, 1], ![-192, -147, 293], ![114, 36, -93]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [20, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 52], [0, 1]]
 g := ![![[18, 43], [37], [20, 44], [25], [11, 1]], ![[14, 10], [37], [27, 9], [25], [22, 52]]]
 h' := ![![[11, 52], [48, 19], [24, 14], [41, 37], [45, 48], [0, 1]], ![[0, 1], [45, 34], [19, 39], [24, 16], [43, 5], [11, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [30, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [20, 42, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8905, 3632, -23476]
  a := ![3, -10, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15335, 12028, -23476]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![25, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![25, 1, 0]] 
 ![![53, 0, 0], ![25, 1, 0], ![40, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![25, 1, 0], ![-1, 29, 11], ![106, -23, 21]]]
  hmulB := by decide  
  f := ![![![-279, 7394, 2805], ![53, -13515, 0]], ![![-145, 3479, 1320], ![54, -6360, 0]], ![![-220, 5580, 2117], ![60, -10200, 0]]]
  g := ![![![1, 0, 0], ![-25, 53, 0], ![-40, 0, 53]], ![![0, 1, 0], ![-22, 29, 11], ![-3, -23, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![35, 27, 1]] ![![53, 0, 0], ![25, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1325, 53, 0]], ![![1855, 1431, 53], ![954, 795, 318]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![25, 1, 0]]], ![![![35, 27, 1]], ![![18, 15, 6]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![40, -20, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![40, -20, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![40, 39, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![40, -20, 1], ![126, -63, -224], ![-2195, 478, 100]]]
  hmulB := by decide  
  f := ![![![-39, 20, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -39, 59]], ![![0, -1, 1], ![154, 147, -224], ![-105, -58, 100]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [4, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 58], [0, 1]]
 g := ![![[19, 15], [39, 53], [53], [8, 41], [42, 1]], ![[0, 44], [23, 6], [53], [19, 18], [25, 58]]]
 h' := ![![[42, 58], [21, 29], [45, 17], [27, 17], [9, 49], [0, 1]], ![[0, 1], [0, 30], [51, 42], [33, 42], [2, 10], [42, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [41, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [4, 17, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2582, -347, -2794]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1938, 1841, -2794]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-12, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-12, 1, 0]] 
 ![![59, 0, 0], ![47, 1, 0], ![18, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-12, 1, 0], ![-1, -8, 11], ![106, -23, -16]]]
  hmulB := by decide  
  f := ![![![-473, -3889, 5346], ![59, -28674, 0]], ![![-374, -3097, 4257], ![60, -22833, 0]], ![![-138, -1187, 1631], ![49, -8748, 0]]]
  g := ![![![1, 0, 0], ![-47, 59, 0], ![-18, 0, 59]], ![![-1, 1, 0], ![3, -8, 11], ![25, -23, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![40, -20, 1]] ![![59, 0, 0], ![-12, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-708, 59, 0]], ![![2360, -1180, 59], ![-354, 177, -236]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-12, 1, 0]]], ![![![40, -20, 1]], ![![-6, 3, -4]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-14, 22, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-14, 22, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![47, 22, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-14, 22, 1], ![84, 51, 238], ![2257, -488, -122]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -22, 61]], ![![-1, 0, 1], ![-182, -85, 238], ![131, 36, -122]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [47, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 60], [0, 1]]
 g := ![![[43, 13], [57], [33, 15], [41, 45], [53, 1]], ![[0, 48], [57], [35, 46], [47, 16], [45, 60]]]
 h' := ![![[53, 60], [10, 47], [35, 22], [25, 36], [10, 17], [0, 1]], ![[0, 1], [0, 14], [42, 39], [42, 25], [57, 44], [53, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [47, 8, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49720, -8208, 1224]
  a := ![-1, 24, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-128, -576, 1224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![6, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![6, 1, 0]] 
 ![![61, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![6, 1, 0], ![-1, 10, 11], ![106, -23, 2]]]
  hmulB := by decide  
  f := ![![![-5, -1, 0], ![61, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-4, -9, -9], ![49, 50, 0]]]
  g := ![![![1, 0, 0], ![-6, 61, 0], ![0, 0, 61]], ![![0, 1, 0], ![-1, 10, 11], ![4, -23, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-14, 22, 1]] ![![61, 0, 0], ![6, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![366, 61, 0]], ![![-854, 1342, 61], ![0, 183, 244]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![6, 1, 0]]], ![![![-14, 22, 1]], ![![0, 3, 4]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![42, -1, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![42, -1, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![42, 66, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![42, -1, 1], ![107, 15, -15], ![-181, 41, 26]]]
  hmulB := by decide  
  f := ![![![-41, 1, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -66, 67]], ![![0, -1, 1], ![11, 15, -15], ![-19, -25, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [64, 4, 1] where
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
 g := ![![[21, 22], [56, 14], [16], [39], [16], [1]], ![[0, 45], [0, 53], [16], [39], [16], [1]]]
 h' := ![![[63, 66], [34, 42], [36, 9], [16, 63], [57, 46], [3, 63], [0, 1]], ![[0, 1], [0, 25], [0, 58], [32, 4], [7, 21], [19, 4], [63, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [19, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [64, 4, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5647, 1492, -3100]
  a := ![1, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1859, 3076, -3100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![15, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![15, 1, 0]] 
 ![![67, 0, 0], ![15, 1, 0], ![41, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![15, 1, 0], ![-1, 19, 11], ![106, -23, 11]]]
  hmulB := by decide  
  f := ![![![-122, 2051, 1188], ![67, -7236, 0]], ![![-39, 455, 264], ![68, -1608, 0]], ![![-76, 1255, 727], ![47, -4428, 0]]]
  g := ![![![1, 0, 0], ![-15, 67, 0], ![-41, 0, 67]], ![![0, 1, 0], ![-11, 19, 11], ![0, -23, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![42, -1, 1]] ![![67, 0, 0], ![15, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1005, 67, 0]], ![![2814, -67, 67], ![737, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![15, 1, 0]]], ![![![42, -1, 1]], ![![11, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![41, -6, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![41, -6, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![41, 65, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![41, -6, 1], ![112, -6, -70], ![-711, 156, 45]]]
  hmulB := by decide  
  f := ![![![-40, 6, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -65, 71]], ![![0, -1, 1], ![42, 64, -70], ![-36, -39, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [51, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 70], [0, 1]]
 g := ![![[41, 30], [32, 38], [59, 64], [30], [30], [1]], ![[4, 41], [23, 33], [70, 7], [30], [30], [1]]]
 h' := ![![[39, 70], [1, 39], [44, 40], [68, 63], [6, 32], [20, 39], [0, 1]], ![[0, 1], [31, 32], [42, 31], [40, 8], [47, 39], [50, 32], [39, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [51, 32, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5586, 180, -9757]
  a := ![-2, 9, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5713, 8935, -9757]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-1, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-1, 1, 0]] 
 ![![71, 0, 0], ![70, 1, 0], ![26, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-1, 1, 0], ![-1, 3, 11], ![106, -23, -5]]]
  hmulB := by decide  
  f := ![![![2450, -7349, -26950], ![-71, 173950, 0]], ![![2415, -7244, -26565], ![-70, 171465, 0]], ![![897, -2691, -9869], ![-39, 63700, 0]]]
  g := ![![![1, 0, 0], ![-70, 71, 0], ![-26, 0, 71]], ![![-1, 1, 0], ![-7, 3, 11], ![26, -23, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![41, -6, 1]] ![![71, 0, 0], ![-1, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-71, 71, 0]], ![![2911, -426, 71], ![71, 0, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-1, 1, 0]]], ![![![41, -6, 1]], ![![1, 0, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![23, 14, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![23, 14, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![23, 14, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![23, 14, 1], ![92, 56, 150], ![1409, -304, -53]]]
  hmulB := by decide  
  f := ![![![-22, -14, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -14, 73]], ![![0, 0, 1], ![-46, -28, 150], ![36, 6, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [19, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 72], [0, 1]]
 g := ![![[40, 50], [67], [41], [51, 32], [24], [1]], ![[0, 23], [67], [41], [40, 41], [24], [1]]]
 h' := ![![[43, 72], [18, 59], [59, 33], [53, 25], [51, 55], [54, 43], [0, 1]], ![[0, 1], [0, 14], [18, 40], [33, 48], [7, 18], [5, 30], [43, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [9, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [19, 30, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3419, -750, -575]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![228, 100, -575]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-4, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-4, 1, 0]] 
 ![![73, 0, 0], ![69, 1, 0], ![53, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-4, 1, 0], ![-1, 0, 11], ![106, -23, -8]]]
  hmulB := by decide  
  f := ![![![-1237, -1, 13662], ![73, -90666, 0]], ![![-1168, -1, 12903], ![74, -85629, 0]], ![![-897, -1, 9919], ![73, -65826, 0]]]
  g := ![![![1, 0, 0], ![-69, 73, 0], ![-53, 0, 73]], ![![-1, 1, 0], ![-8, 0, 11], ![29, -23, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![23, 14, 1]] ![![73, 0, 0], ![-4, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-292, 73, 0]], ![![1679, 1022, 73], ![0, 0, 146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-4, 1, 0]]], ![![![23, 14, 1]], ![![0, 0, 2]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![38, -9, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![38, -9, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![38, 70, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![38, -9, 1], ![115, -21, -103], ![-1029, 225, 54]]]
  hmulB := by decide  
  f := ![![![-37, 9, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -70, 79]], ![![0, -1, 1], ![51, 91, -103], ![-39, -45, 54]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [55, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 78], [0, 1]]
 g := ![![[74, 23], [41, 1], [74, 23], [38, 44], [22], [1]], ![[0, 56], [0, 78], [0, 56], [51, 35], [22], [1]]]
 h' := ![![[38, 78], [36, 24], [38, 78], [43, 55], [77, 53], [24, 38], [0, 1]], ![[0, 1], [0, 55], [0, 1], [0, 24], [37, 26], [46, 41], [38, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [55, 41, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43223, 10368, -10632]
  a := ![-2, 0, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4567, 9552, -10632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![24, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![24, 1, 0]] 
 ![![79, 0, 0], ![24, 1, 0], ![25, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![24, 1, 0], ![-1, 28, 11], ![106, -23, 20]]]
  hmulB := by decide  
  f := ![![![3577, -98782, -38808], ![-158, 278712, 0]], ![![1071, -29988, -11781], ![1, 84609, 0]], ![![1111, -31261, -12281], ![19, 88200, 0]]]
  g := ![![![1, 0, 0], ![-24, 79, 0], ![-25, 0, 79]], ![![0, 1, 0], ![-12, 28, 11], ![2, -23, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![38, -9, 1]] ![![79, 0, 0], ![24, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1896, 79, 0]], ![![3002, -711, 79], ![1027, -237, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![24, 1, 0]]], ![![![38, -9, 1]], ![![13, -3, -1]]]]
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


lemma PB245I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB245I1 : PrimesBelowBoundCertificateInterval O 31 79 245 where
  m := 11
  g := ![3, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB245I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
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
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
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
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I47N1, I53N1, I59N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N0, I37N1], [], [], [I47N1], [I53N1], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
