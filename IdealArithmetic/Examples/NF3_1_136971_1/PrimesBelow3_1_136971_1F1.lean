
import IdealArithmetic.Examples.NF3_1_136971_1.RI3_1_136971_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [25, 14, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 23, 23], [15, 13, 14], [0, 1]]
 g := ![![[9, 8, 34], [26, 34], [15, 32, 28], [12, 1], []], ![[19, 10, 21, 2], [2, 28], [23, 17, 20, 8], [21, 21], [6, 11]], ![[18, 17, 5, 8], [35, 4], [4, 27, 10, 8], [17, 11], [15, 11]]]
 h' := ![![[34, 23, 23], [4, 31, 21], [32, 5, 21], [33, 29, 19], [0, 0, 1], [0, 1]], ![[15, 13, 14], [21, 7, 24], [16, 1, 18], [5, 30, 26], [7, 21, 13], [34, 23, 23]], ![[0, 1], [20, 36, 29], [28, 31, 35], [23, 15, 29], [35, 16, 23], [15, 13, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 18], []]
 b := ![[], [9, 16, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [25, 14, 25, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-259, 1998, -370]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, 54, -10]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [31, 20, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 6, 1], [7, 34, 40], [0, 1]]
 g := ![![[20, 15, 25], [26, 39], [9, 31], [25, 2, 1], []], ![[11, 11, 18, 37], [0, 10], [17, 25], [1, 19, 10, 8], [14, 1]], ![[13, 5, 1, 36], [18, 25], [7, 20], [22, 15, 21, 5], [16, 1]]]
 h' := ![![[36, 6, 1], [16, 17, 5], [24, 21, 30], [4, 12, 20], [0, 0, 1], [0, 1]], ![[7, 34, 40], [18, 10, 23], [31, 25, 16], [5, 32, 36], [1, 39, 34], [36, 6, 1]], ![[0, 1], [32, 14, 13], [4, 36, 36], [4, 38, 26], [4, 2, 6], [7, 34, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 4], []]
 b := ![[], [3, 5, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [31, 20, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![127920, 3362, -5043]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3120, 82, -123]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![20, 10, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![20, 10, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![20, 10, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![20, 10, 1], ![71, 14, 10], ![710, 11, 14]]]
  hmulB := by decide  
  f := ![![![-19, -10, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -10, 43]], ![![0, 0, 1], ![-3, -2, 10], ![10, -3, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [37, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 42], [0, 1]]
 g := ![![[10, 36], [0, 41], [6], [0, 31], [1]], ![[20, 7], [9, 2], [6], [11, 12], [1]]]
 h' := ![![[17, 42], [0, 37], [36, 16], [0, 7], [6, 17], [0, 1]], ![[0, 1], [27, 6], [7, 27], [33, 36], [37, 26], [17, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [37, 26, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2327, -19, 97]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, -23, 97]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-10, 1, 0]] 
 ![![43, 0, 0], ![33, 1, 0], ![29, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-10, 1, 0], ![0, -10, 1], ![71, -6, -10]]]
  hmulB := by decide  
  f := ![![![171, -17, 0], ![731, 0, 0]], ![![141, -14, 0], ![603, 0, 0]], ![![133, -13, 0], ![569, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 43, 0], ![-29, 0, 43]], ![![-1, 1, 0], ![7, -10, 1], ![13, -6, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![20, 10, 1]] ![![43, 0, 0], ![-10, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-430, 43, 0]], ![![860, 430, 43], ![-129, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-10, 1, 0]]], ![![![20, 10, 1]], ![![-3, -2, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [19, 10, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 38, 19], [31, 8, 28], [0, 1]]
 g := ![![[7, 20, 42], [11, 44, 24], [43, 9, 25], [7, 39, 1], []], ![[44, 28, 39, 46], [30, 39, 34, 40], [21, 31], [46, 19, 43, 41], [13, 32]], ![[2, 25], [42, 12, 24, 25], [18, 24, 32, 42], [2, 39, 33, 12], [4, 32]]]
 h' := ![![[8, 38, 19], [26, 36, 18], [29, 27, 27], [8, 35, 5], [0, 0, 1], [0, 1]], ![[31, 8, 28], [28, 15, 29], [4, 7, 24], [31, 22], [5, 11, 8], [8, 38, 19]], ![[0, 1], [11, 43], [39, 13, 43], [19, 37, 42], [39, 36, 38], [31, 8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 23], []]
 b := ![[], [32, 34, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [19, 10, 8, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-152186, 30785, 329]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3238, 655, 7]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![22, -4, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![22, -4, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![22, 49, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![22, -4, 1], ![71, 16, -4], ![-284, 95, 16]]]
  hmulB := by decide  
  f := ![![![-21, 4, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -49, 53]], ![![0, -1, 1], ![3, 4, -4], ![-12, -13, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [11, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 52], [0, 1]]
 g := ![![[46, 29], [29], [48, 4], [6], [24, 1]], ![[0, 24], [29], [38, 49], [6], [48, 52]]]
 h' := ![![[24, 52], [3, 33], [2, 33], [41, 2], [1, 35], [0, 1]], ![[0, 1], [0, 20], [52, 20], [36, 51], [46, 18], [24, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [12, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [11, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153, 30, -34]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 32, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![4, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![4, 1, 0]] 
 ![![53, 0, 0], ![4, 1, 0], ![37, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![4, 1, 0], ![0, 4, 1], ![71, -6, 4]]]
  hmulB := by decide  
  f := ![![![137, 34, 0], ![-1802, 0, 0]], ![![4, 1, 0], ![-52, 0, 0]], ![![97, 24, 0], ![-1276, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 53, 0], ![-37, 0, 53]], ![![0, 1, 0], ![-1, 4, 1], ![-1, -6, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![22, -4, 1]] ![![53, 0, 0], ![4, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![212, 53, 0]], ![![1166, -212, 53], ![159, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![4, 1, 0]]], ![![![22, -4, 1]], ![![3, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [46, 22, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 31, 38], [55, 27, 21], [0, 1]]
 g := ![![[45, 36, 9], [22, 57, 51], [40, 22], [49, 21, 22], [1]], ![[44, 23, 52, 18], [50, 39, 16, 32], [54, 48], [54, 40, 8, 8], [32, 30, 49, 2]], ![[55, 3, 4, 21], [10, 7, 29, 57], [50, 36], [4, 11, 30, 36], [15, 45, 44, 57]]]
 h' := ![![[54, 31, 38], [50, 10, 56], [15, 38, 13], [47, 13, 50], [13, 37, 50], [0, 1]], ![[55, 27, 21], [56, 8, 4], [15, 48, 25], [32, 28, 15], [55, 5, 42], [54, 31, 38]], ![[0, 1], [20, 41, 58], [36, 32, 21], [25, 18, 53], [13, 17, 26], [55, 27, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 6], []]
 b := ![[], [34, 57, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [46, 22, 9, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![500202, 35872, 1888]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8478, 608, 32]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![26, -9, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![26, -9, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![26, 52, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![26, -9, 1], ![71, 20, -9], ![-639, 125, 20]]]
  hmulB := by decide  
  f := ![![![-25, 9, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -52, 61]], ![![0, -1, 1], ![5, 8, -9], ![-19, -15, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [28, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 60], [0, 1]]
 g := ![![[35, 57], [4], [45, 5], [30, 22], [57, 1]], ![[51, 4], [4], [25, 56], [3, 39], [53, 60]]]
 h' := ![![[57, 60], [24, 22], [21, 59], [14, 35], [51, 49], [0, 1]], ![[0, 1], [58, 39], [29, 2], [57, 26], [38, 12], [57, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [28, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [28, 4, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-401, 113, 1]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, 1, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![9, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![9, 1, 0]] 
 ![![61, 0, 0], ![9, 1, 0], ![41, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![9, 1, 0], ![0, 9, 1], ![71, -6, 9]]]
  hmulB := by decide  
  f := ![![![253, 28, 0], ![-1708, 0, 0]], ![![27, 3, 0], ![-182, 0, 0]], ![![173, 19, 0], ![-1168, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 61, 0], ![-41, 0, 61]], ![![0, 1, 0], ![-2, 9, 1], ![-4, -6, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![26, -9, 1]] ![![61, 0, 0], ![9, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![549, 61, 0]], ![![1586, -549, 61], ![305, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![9, 1, 0]]], ![![![26, -9, 1]], ![![5, -1, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![25, -32, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![25, -32, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![25, 35, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![25, -32, 1], ![71, 19, -32], ![-2272, 263, 19]]]
  hmulB := by decide  
  f := ![![![-24, 32, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -35, 67]], ![![0, -1, 1], ![13, 17, -32], ![-41, -6, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [38, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 66], [0, 1]]
 g := ![![[29, 6], [51, 56], [59], [9], [29], [1]], ![[50, 61], [46, 11], [59], [9], [29], [1]]]
 h' := ![![[37, 66], [5, 41], [58, 49], [42, 40], [7, 3], [29, 37], [0, 1]], ![[0, 1], [48, 26], [62, 18], [48, 27], [51, 64], [58, 30], [37, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [46, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [38, 30, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![322, 290, 37]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -15, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![32, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![32, 1, 0]] 
 ![![67, 0, 0], ![32, 1, 0], ![48, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![32, 1, 0], ![0, 32, 1], ![71, -6, 32]]]
  hmulB := by decide  
  f := ![![![641, 20, 0], ![-1340, 0, 0]], ![![288, 9, 0], ![-602, 0, 0]], ![![464, 14, 0], ![-970, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 67, 0], ![-48, 0, 67]], ![![0, 1, 0], ![-16, 32, 1], ![-19, -6, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![25, -32, 1]] ![![67, 0, 0], ![32, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2144, 67, 0]], ![![1675, -2144, 67], ![871, -1005, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![32, 1, 0]]], ![![![25, -32, 1]], ![![13, -15, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![6, 0, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![6, 0, 1]] where
  M :=![![![6, 0, 1], ![71, 0, 0], ![0, 71, 0]]]
  hmulB := by decide  
  f := ![![![0, 1, 0]], ![![0, 0, 1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [61, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 70], [0, 1]]
 g := ![![[69, 58], [32, 50], [25, 27], [58], [45], [1]], ![[45, 13], [26, 21], [53, 44], [58], [45], [1]]]
 h' := ![![[51, 70], [36, 22], [37, 60], [52, 58], [53, 49], [10, 51], [0, 1]], ![[0, 1], [22, 49], [44, 11], [28, 13], [67, 22], [55, 20], [51, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [29, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [61, 20, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2735, 284, 124]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49, 4, 124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![71, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![71, -6, 0]]]
  hmulB := by decide  
  f := ![![![6, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, -6, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![6, 0, 1]] ![![0, 1, 0]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [2, 12, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 11, 61], [71, 61, 12], [0, 1]]
 g := ![![[22, 51, 69], [68, 57], [41, 12], [68, 45, 23], [27, 1], []], ![[53, 8, 54, 72], [71, 19], [25, 55], [2, 67, 26, 18], [45, 71], [47, 71]], ![[4, 66, 66, 36], [70, 8], [66, 36], [36, 35, 6, 1], [18, 48], [23, 71]]]
 h' := ![![[29, 11, 61], [42, 33, 19], [18, 45, 38], [10, 39, 31], [19, 39, 60], [0, 0, 1], [0, 1]], ![[71, 61, 12], [8, 20, 33], [71, 28, 26], [62, 0, 36], [53, 72, 53], [17, 5, 61], [29, 11, 61]], ![[0, 1], [54, 20, 21], [11, 0, 9], [17, 34, 6], [49, 35, 33], [31, 68, 11], [71, 61, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 22], []]
 b := ![[], [71, 65, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [2, 12, 46, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4307, 4599, 1095]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![59, 63, 15]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-23, -34, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-23, -34, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![56, 45, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-23, -34, 1], ![71, -29, -34], ![-2414, 275, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -45, 79]], ![![-1, -1, 1], ![25, 19, -34], ![-10, 20, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [41, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 78], [0, 1]]
 g := ![![[48, 62], [43, 36], [16, 55], [29, 36], [49], [1]], ![[8, 17], [58, 43], [6, 24], [44, 43], [49], [1]]]
 h' := ![![[7, 78], [54, 33], [55, 6], [75, 56], [67, 6], [38, 7], [0, 1]], ![[0, 1], [48, 46], [18, 73], [72, 23], [30, 73], [8, 72], [7, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [2, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [41, 72, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![682, -273, -64]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54, 33, -64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![34, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![34, 1, 0]] 
 ![![79, 0, 0], ![34, 1, 0], ![29, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![34, 1, 0], ![0, 34, 1], ![71, -6, 34]]]
  hmulB := by decide  
  f := ![![![171, 5, 0], ![-395, 0, 0]], ![![34, 1, 0], ![-78, 0, 0]], ![![49, 1, 0], ![-113, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 79, 0], ![-29, 0, 79]], ![![0, 1, 0], ![-15, 34, 1], ![-9, -6, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-23, -34, 1]] ![![79, 0, 0], ![34, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2686, 79, 0]], ![![-1817, -2686, 79], ![-711, -1185, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![34, 1, 0]]], ![![![-23, -34, 1]], ![![-9, -15, 0]]]]
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


lemma PB105I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB105I1 : PrimesBelowBoundCertificateInterval O 31 79 105 where
  m := 11
  g := ![1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB105I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I43N1, I53N1, I61N1, I67N1, I71N1, I79N1]
  Il := ![[], [], [I43N1], [], [I53N1], [], [I61N1], [I67N1], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
