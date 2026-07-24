
import IdealArithmetic.Examples.NF3_1_190291_3.RI3_1_190291_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![0, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![0, 1, 0]] 
 ![![37, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![0, 1, 0], ![0, 0, 1], ![259, 74, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![0, 1, 0], ![0, 0, 1], ![7, 74, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![0, 1, 0]] ![![37, 0, 0], ![0, 1, 0]]
  ![![37, 0, 0], ![-37, 0, 1]] where
 M := ![![![1369, 0, 0], ![0, 37, 0]], ![![0, 37, 0], ![0, 0, 1]]]
 hmul := by decide  
 g := ![![![![-5, -6, 0], ![0, 6, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-37, 0, 1]] ![![37, 0, 0], ![0, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![0, 37, 0]], ![![-1369, 0, 37], ![259, 37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![0, 1, 0]]], ![![![-37, 0, 1]], ![![7, 1, 0]]]]
 hle2 := by decide  

def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N0
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [40, 33, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 11, 17], [39, 29, 24], [0, 1]]
 g := ![![[18, 39, 16], [28, 23], [31, 8], [18, 16, 1], []], ![[38, 4, 23, 29], [39, 16], [6, 21], [9, 17, 33, 29], [37, 2]], ![[18, 15, 27, 19], [36, 21], [38, 33], [34, 14, 20, 34], [30, 2]]]
 h' := ![![[18, 11, 17], [19, 22, 37], [27, 30, 8], [18, 37, 7], [0, 0, 1], [0, 1]], ![[39, 29, 24], [37, 8, 12], [11, 19, 4], [13, 17, 12], [33, 38, 29], [18, 11, 17]], ![[0, 1], [3, 11, 33], [34, 33, 29], [18, 28, 22], [34, 3, 11], [39, 29, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 5], []]
 b := ![[], [3, 29, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [40, 33, 25, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-111848, -45469, -4633]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2728, -1109, -113]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-39, 11, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-39, 11, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![4, 11, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-39, 11, 1], ![259, 35, 11], ![2849, 1073, 35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -11, 43]], ![![-1, 0, 1], ![5, -2, 11], ![63, 16, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [21, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 42], [0, 1]]
 g := ![![[30, 41], [36, 41], [9], [36, 10], [1]], ![[0, 2], [6, 2], [9], [14, 33], [1]]]
 h' := ![![[15, 42], [18, 16], [6, 27], [18, 40], [22, 15], [0, 1]], ![[0, 1], [0, 27], [24, 16], [16, 3], [32, 28], [15, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [12, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [21, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3114, 1391, 748]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-142, -159, 748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-11, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-11, 1, 0]] 
 ![![43, 0, 0], ![32, 1, 0], ![8, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-11, 1, 0], ![0, -11, 1], ![259, 74, -11]]]
  hmulB := by decide  
  f := ![![![67, -6, 0], ![258, 0, 0]], ![![56, -5, 0], ![216, 0, 0]], ![![14, -1, 0], ![54, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 43, 0], ![-8, 0, 43]], ![![-1, 1, 0], ![8, -11, 1], ![-47, 74, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-39, 11, 1]] ![![43, 0, 0], ![-11, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-473, 43, 0]], ![![-1677, 473, 43], ![688, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-11, 1, 0]]], ![![![-39, 11, 1]], ![![16, -2, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [3, 46, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 43, 30], [31, 3, 17], [0, 1]]
 g := ![![[14, 33, 6], [44, 37, 42], [22, 33, 2], [28, 36, 1], []], ![[34, 28, 39, 5], [42, 12, 20, 40], [2, 5, 1, 38], [44, 44, 18, 35], [12, 7]], ![[11, 3, 36, 16], [46, 29, 44, 8], [16, 27, 20, 3], [30, 33, 27, 37], [25, 7]]]
 h' := ![![[5, 43, 30], [9, 12, 10], [28, 23, 18], [10, 14, 7], [0, 0, 1], [0, 1]], ![[31, 3, 17], [6, 26, 14], [39, 13, 39], [3, 24, 18], [36, 45, 3], [5, 43, 30]], ![[0, 1], [29, 9, 23], [4, 11, 37], [19, 9, 22], [40, 2, 43], [31, 3, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 3], []]
 b := ![[], [45, 22, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [3, 46, 11, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135595, -31772, -29422]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2885, -676, -626]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-31, 19, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-31, 19, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![22, 19, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-31, 19, 1], ![259, 43, 19], ![4921, 1665, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -19, 53]], ![![-1, 0, 1], ![-3, -6, 19], ![75, 16, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [52, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 52], [0, 1]]
 g := ![![[39, 52], [9], [26, 40], [13], [39, 1]], ![[0, 1], [9], [49, 13], [13], [25, 52]]]
 h' := ![![[39, 52], [49, 30], [26, 3], [50, 26], [39, 38], [0, 1]], ![[0, 1], [0, 23], [37, 50], [4, 27], [37, 15], [39, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [10, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [52, 14, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1487, 1903, 619]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-285, -186, 619]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-19, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-19, 1, 0]] 
 ![![53, 0, 0], ![34, 1, 0], ![10, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-19, 1, 0], ![0, -19, 1], ![259, 74, -19]]]
  hmulB := by decide  
  f := ![![![419, -22, 0], ![1166, 0, 0]], ![![286, -15, 0], ![796, 0, 0]], ![![102, -5, 0], ![284, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 53, 0], ![-10, 0, 53]], ![![-1, 1, 0], ![12, -19, 1], ![-39, 74, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-31, 19, 1]] ![![53, 0, 0], ![-19, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1007, 53, 0]], ![![-1643, 1007, 53], ![848, -318, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-19, 1, 0]]], ![![![-31, 19, 1]], ![![16, -6, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-26, 15, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-26, 15, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![33, 15, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-26, 15, 1], ![259, 48, 15], ![3885, 1369, 48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -15, 59]], ![![-1, 0, 1], ![-4, -3, 15], ![39, 11, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [37, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 58], [0, 1]]
 g := ![![[31, 46], [26, 28], [3], [49, 41], [33, 1]], ![[15, 13], [6, 31], [3], [45, 18], [7, 58]]]
 h' := ![![[33, 58], [41, 20], [27, 38], [16, 11], [18, 49], [0, 1]], ![[0, 1], [52, 39], [42, 21], [25, 48], [42, 10], [33, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [48, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [37, 26, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![555, 381, 49]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -6, 49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-15, 1, 0]] 
 ![![59, 0, 0], ![44, 1, 0], ![11, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-15, 1, 0], ![0, -15, 1], ![259, 74, -15]]]
  hmulB := by decide  
  f := ![![![91, -6, 0], ![354, 0, 0]], ![![76, -5, 0], ![296, 0, 0]], ![![19, -1, 0], ![74, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 59, 0], ![-11, 0, 59]], ![![-1, 1, 0], ![11, -15, 1], ![-48, 74, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-26, 15, 1]] ![![59, 0, 0], ![-15, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-885, 59, 0]], ![![-1534, 885, 59], ![649, -177, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-15, 1, 0]]], ![![![-26, 15, 1]], ![![11, -3, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 13, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 13, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![34, 13, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 13, 1], ![259, 47, 13], ![3367, 1221, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -13, 61]], ![![-1, 0, 1], ![-3, -2, 13], ![29, 10, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [7, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 60], [0, 1]]
 g := ![![[38, 12], [1], [44, 3], [50, 60], [39, 1]], ![[18, 49], [1], [39, 58], [11, 1], [17, 60]]]
 h' := ![![[39, 60], [2, 45], [58, 60], [16, 53], [32, 50], [0, 1]], ![[0, 1], [49, 16], [19, 1], [9, 8], [30, 11], [39, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [35, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [7, 22, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9872, 3527, 459]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94, -40, 459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-13, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-13, 1, 0]] 
 ![![61, 0, 0], ![48, 1, 0], ![14, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-13, 1, 0], ![0, -13, 1], ![259, 74, -13]]]
  hmulB := by decide  
  f := ![![![690, -53, 0], ![3233, 0, 0]], ![![534, -41, 0], ![2502, 0, 0]], ![![172, -13, 0], ![806, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 61, 0], ![-14, 0, 61]], ![![-1, 1, 0], ![10, -13, 1], ![-51, 74, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-27, 13, 1]] ![![61, 0, 0], ![-13, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-793, 61, 0]], ![![-1647, 793, 61], ![610, -122, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-13, 1, 0]]], ![![![-27, 13, 1]], ![![10, -2, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [55, 3, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 26, 30], [36, 40, 37], [0, 1]]
 g := ![![[57, 32, 54], [51, 59, 54], [15, 62], [43, 56], [50, 1], []], ![[19, 59, 11, 66], [32, 7, 39, 32], [3, 55], [27, 9], [48, 59], [62, 29]], ![[21, 21, 59, 21], [10, 9, 49, 9], [27, 29], [46, 24], [49, 6], [55, 29]]]
 h' := ![![[14, 26, 30], [9, 36, 56], [33, 17, 11], [56, 31, 14], [64, 63, 18], [0, 0, 1], [0, 1]], ![[36, 40, 37], [22, 57, 37], [25, 48, 12], [49, 0, 16], [44, 37, 64], [2, 19, 40], [14, 26, 30]], ![[0, 1], [23, 41, 41], [51, 2, 44], [14, 36, 37], [20, 34, 52], [13, 48, 26], [36, 40, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 35], []]
 b := ![[], [51, 59, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [55, 3, 17, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![90718, 3283, -3953]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1354, 49, -59]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [50, 41, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 5, 37], [59, 65, 34], [0, 1]]
 g := ![![[62, 60, 27], [61, 20, 57], [23, 42, 38], [36, 30], [12, 1], []], ![[55, 13, 9, 29], [56, 10, 22, 15], [10, 10, 47, 50], [30, 50], [41, 36], [42, 20]], ![[13, 16, 14, 52], [2, 56, 57, 41], [46, 47, 58, 53], [43, 15], [57, 25], [45, 20]]]
 h' := ![![[24, 5, 37], [3, 32, 58], [57, 35, 25], [5, 46, 31], [39, 26, 32], [0, 0, 1], [0, 1]], ![[59, 65, 34], [64, 50, 55], [1, 37, 9], [15, 39, 25], [33, 13, 60], [38, 3, 65], [24, 5, 37]], ![[0, 1], [17, 60, 29], [24, 70, 37], [55, 57, 15], [69, 32, 50], [24, 68, 5], [59, 65, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 8], []]
 b := ![[], [17, 36, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [50, 41, 59, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![828073, 452625, 64965]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11663, 6375, 915]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-50, -30, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-50, -30, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![23, 43, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-50, -30, 1], ![259, 24, -30], ![-7770, -1961, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -43, 73]], ![![-1, -1, 1], ![13, 18, -30], ![-114, -41, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [6, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 72], [0, 1]]
 g := ![![[8, 61], [36], [35], [24, 25], [41], [1]], ![[0, 12], [36], [35], [65, 48], [41], [1]]]
 h' := ![![[25, 72], [26, 34], [13, 6], [2, 20], [9, 68], [67, 25], [0, 1]], ![[0, 1], [0, 39], [17, 67], [64, 53], [30, 5], [35, 48], [25, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [53, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [6, 48, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10254, -2444, 500]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-298, -328, 500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![30, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![30, 1, 0]] 
 ![![73, 0, 0], ![30, 1, 0], ![49, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![30, 1, 0], ![0, 30, 1], ![259, 74, 30]]]
  hmulB := by decide  
  f := ![![![721, 24, 0], ![-1752, 0, 0]], ![![270, 9, 0], ![-656, 0, 0]], ![![493, 16, 0], ![-1198, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 73, 0], ![-49, 0, 73]], ![![0, 1, 0], ![-13, 30, 1], ![-47, 74, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-50, -30, 1]] ![![73, 0, 0], ![30, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2190, 73, 0]], ![![-3650, -2190, 73], ![-1241, -876, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![30, 1, 0]]], ![![![-50, -30, 1]], ![![-17, -12, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [26, 27, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 50, 43], [12, 28, 36], [0, 1]]
 g := ![![[51, 20, 10], [8, 36, 9], [43, 3, 50], [51, 71, 23], [29, 1], []], ![[14, 50, 46, 68], [1, 78, 41, 30], [21, 57, 61, 47], [35, 59, 49, 78], [11, 73], [14, 32]], ![[41, 32, 51, 20], [30, 78, 63, 42], [32, 4, 34, 21], [26, 5, 57, 67], [37, 51], [21, 32]]]
 h' := ![![[17, 50, 43], [29, 19, 22], [67, 77, 76], [17, 48, 45], [36, 60, 24], [0, 0, 1], [0, 1]], ![[12, 28, 36], [45, 38, 11], [21, 10, 67], [65, 39, 6], [46, 66, 13], [4, 16, 28], [17, 50, 43]], ![[0, 1], [24, 22, 46], [64, 71, 15], [41, 71, 28], [35, 32, 42], [72, 63, 50], [12, 28, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 29], []]
 b := ![[], [38, 63, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [26, 27, 50, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25754, 30652, 13430]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-326, 388, 170]
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



lemma PB124I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB124I1 : PrimesBelowBoundCertificateInterval O 31 79 124 where
  m := 11
  g := ![3, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB124I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
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
      exact NI37N0
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
  β := ![I37N0, I43N1, I53N1, I59N1, I61N1, I73N1]
  Il := ![[I37N0, I37N0, I37N0], [], [I43N1], [], [I53N1], [I59N1], [I61N1], [], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
