
import IdealArithmetic.Examples.NF3_1_491724_2.RI3_1_491724_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-109, 11, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-109, 11, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![2, 11, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-109, 11, 1], ![762, 47, 11], ![8382, 2478, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -11, 37]], ![![-3, 0, 1], ![20, -2, 11], ![224, 53, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [21, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 36], [0, 1]]
 g := ![![[35, 30], [28], [11, 10], [25], [1]], ![[0, 7], [28], [24, 27], [25], [1]]]
 h' := ![![[5, 36], [11, 20], [28, 19], [27, 26], [16, 5], [0, 1]], ![[0, 1], [0, 17], [12, 18], [9, 11], [4, 32], [5, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [25, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [21, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1545, 1042, 125]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35, -9, 125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-11, 1, 0]] 
 ![![37, 0, 0], ![26, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-11, 1, 0], ![0, -11, 1], ![762, 156, -11]]]
  hmulB := by decide  
  f := ![![![342, -31, 0], ![1147, 0, 0]], ![![254, -23, 0], ![852, 0, 0]], ![![268, -24, 0], ![899, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 37, 0], ![-27, 0, 37]], ![![-1, 1, 0], ![7, -11, 1], ![-81, 156, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-109, 11, 1]] ![![37, 0, 0], ![-11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-407, 37, 0]], ![![-4033, 407, 37], ![1961, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-11, 1, 0]]], ![![![-109, 11, 1]], ![![53, -2, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-111, 2, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-111, 2, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![12, 2, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-111, 2, 1], ![762, 45, 2], ![1524, 1074, 45]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -2, 41]], ![![-3, 0, 1], ![18, 1, 2], ![24, 24, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [28, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 40], [0, 1]]
 g := ![![[5, 16], [20], [25], [16, 2], [1]], ![[20, 25], [20], [25], [23, 39], [1]]]
 h' := ![![[24, 40], [9, 4], [6, 15], [3, 5], [13, 24], [0, 1]], ![[0, 1], [23, 37], [38, 26], [0, 36], [15, 17], [24, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [5, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [28, 17, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9132, 4956, 1453]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-648, 50, 1453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-2, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-2, 1, 0]] 
 ![![41, 0, 0], ![39, 1, 0], ![37, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-2, 1, 0], ![0, -2, 1], ![762, 156, -2]]]
  hmulB := by decide  
  f := ![![![47, -23, 0], ![943, 0, 0]], ![![45, -22, 0], ![903, 0, 0]], ![![43, -21, 0], ![863, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 41, 0], ![-37, 0, 41]], ![![-1, 1, 0], ![1, -2, 1], ![-128, 156, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-111, 2, 1]] ![![41, 0, 0], ![-2, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-82, 41, 0]], ![![-4551, 82, 41], ![984, 41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-2, 1, 0]]], ![![![-111, 2, 1]], ![![24, 1, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [23, 0, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 31, 9], [5, 11, 34], [0, 1]]
 g := ![![[24, 39, 14], [11, 0, 23], [15, 10], [15, 12, 1], []], ![[33, 3, 13, 24], [24, 36], [2, 31], [7, 4, 4, 14], [25, 38]], ![[33, 11, 23, 2], [16, 17, 41, 8], [21, 4], [29, 32, 17, 37], [0, 38]]]
 h' := ![![[7, 31, 9], [5, 0, 33], [0, 21, 18], [42, 25, 28], [0, 0, 1], [0, 1]], ![[5, 11, 34], [19, 14, 19], [10, 41], [23, 22, 17], [33, 33, 11], [7, 31, 9]], ![[0, 1], [13, 29, 34], [39, 24, 25], [7, 39, 41], [25, 10, 31], [5, 11, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 26], []]
 b := ![[], [27, 20, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [23, 0, 31, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-113047, -230996, -56115]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2629, -5372, -1305]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [8, 43, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 27, 24], [38, 19, 23], [0, 1]]
 g := ![![[45, 41, 1], [40, 40, 21], [42, 4, 37], [6, 7, 1], []], ![[11, 27, 28, 8], [9, 38, 11, 6], [45, 35, 30, 14], [22, 28, 34, 16], [17, 12]], ![[5, 3, 8, 11], [44, 33, 24, 46], [29, 44, 39, 45], [41, 0, 8, 35], [18, 12]]]
 h' := ![![[16, 27, 24], [9, 30, 46], [40, 43, 31], [46, 15, 15], [0, 0, 1], [0, 1]], ![[38, 19, 23], [40, 21, 43], [30, 5, 23], [18, 20, 34], [26, 37, 19], [16, 27, 24]], ![[0, 1], [37, 43, 5], [3, 46, 40], [0, 12, 45], [31, 10, 27], [38, 19, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 15], []]
 b := ![[], [41, 42, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [8, 43, 40, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12663586, -5513946, -577865]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-269438, -117318, -12295]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [3, 5, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 48, 45], [13, 4, 8], [0, 1]]
 g := ![![[20, 42, 52], [50, 43], [21, 47, 9], [50, 36], [1]], ![[4, 47, 37, 34], [2, 15], [24, 41, 32, 22], [6, 15], [17, 9, 49, 18]], ![[45, 30, 45, 2], [3, 52], [52, 2, 39, 14], [8, 24], [31, 40, 24, 35]]]
 h' := ![![[46, 48, 45], [3, 22, 30], [43, 25, 34], [18, 43, 3], [50, 48, 6], [0, 1]], ![[13, 4, 8], [51, 35, 50], [51, 4, 42], [34, 38, 39], [30, 1, 11], [46, 48, 45]], ![[0, 1], [19, 49, 26], [9, 24, 30], [20, 25, 11], [37, 4, 36], [13, 4, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 10], []]
 b := ![[], [18, 9, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [3, 5, 47, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-866391, -262721, -19716]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16347, -4957, -372]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [33, 25, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 34, 30], [23, 24, 29], [0, 1]]
 g := ![![[43, 19, 45], [7, 56, 35], [33, 46], [36, 38, 46], [1]], ![[47, 30, 24, 44], [8, 47, 47, 55], [53, 57], [58, 28, 29, 47], [43, 54, 28, 37]], ![[9, 36, 51, 3], [4, 48, 37, 45], [28, 9], [50, 16, 28, 20], [28, 49, 45, 22]]]
 h' := ![![[56, 34, 30], [5, 54, 35], [37, 6, 25], [51, 56, 20], [26, 34, 20], [0, 1]], ![[23, 24, 29], [12, 4, 41], [47, 8, 13], [47, 48, 36], [29, 8, 25], [56, 34, 30]], ![[0, 1], [53, 1, 42], [47, 45, 21], [33, 14, 3], [33, 17, 14], [23, 24, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 2], []]
 b := ![[], [23, 9, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [33, 25, 39, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13799156, 3803140, 258538]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![233884, 64460, 4382]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [8, 39, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 47, 40], [8, 13, 21], [0, 1]]
 g := ![![[48, 29, 12], [7, 60], [9, 17, 49], [42, 24, 39], [1]], ![[4, 16, 38, 50], [53, 39], [10, 60, 52, 29], [29, 37, 14, 28], [35, 35, 34, 11]], ![[20, 37, 40, 32], [1, 14], [21, 6, 10, 38], [43, 9, 59, 2], [28, 33, 46, 50]]]
 h' := ![![[43, 47, 40], [4, 43, 45], [50, 47, 11], [30, 3, 54], [53, 22, 51], [0, 1]], ![[8, 13, 21], [28, 8, 48], [5, 13, 10], [43, 19, 29], [49, 58, 18], [43, 47, 40]], ![[0, 1], [52, 10, 29], [50, 1, 40], [16, 39, 39], [44, 42, 53], [8, 13, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 26], []]
 b := ![[], [57, 52, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [8, 39, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![477752, -36234, -20557]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7832, -594, -337]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [56, 22, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 49, 44], [38, 17, 23], [0, 1]]
 g := ![![[35, 60, 26], [30, 52, 16], [0, 62], [48, 21], [21, 1], []], ![[52, 26, 16, 12], [40, 3, 28, 46], [50, 1], [35, 14], [18, 21], [11, 60]], ![[27, 56, 34, 29], [63, 48, 30, 59], [13, 24], [16, 6], [66, 56], [32, 60]]]
 h' := ![![[50, 49, 44], [62, 26, 19], [39, 2, 63], [21, 54, 14], [30, 18, 17], [0, 0, 1], [0, 1]], ![[38, 17, 23], [40, 7, 60], [40, 65, 20], [19, 48, 1], [61, 34, 9], [8, 25, 17], [50, 49, 44]], ![[0, 1], [66, 34, 55], [33, 0, 51], [15, 32, 52], [24, 15, 41], [54, 42, 49], [38, 17, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 11], []]
 b := ![[], [39, 17, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [56, 22, 46, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6212642, 2367646, 233562]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![92726, 35338, 3486]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-200311, -54873, -3798]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-200311, -54873, -3798]] 
 ![![71, 0, 0], ![0, 71, 0], ![31, 20, 1]] where
  M :=![![![-200311, -54873, -3798], ![-2894076, -792799, -54873], ![-41813226, -11454264, -792799]]]
  hmulB := by decide  
  f := ![![![-5999, -495, 63]], ![![48006, 3829, -495]], ![![5591, 451, -58]]]
  g := ![![![-1163, 297, -3798], ![-16803, 4291, -54873], ![-242767, 61996, -792799]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [13, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 70], [0, 1]]
 g := ![![[47, 37], [27, 24], [70, 30], [25], [3], [1]], ![[18, 34], [60, 47], [58, 41], [25], [3], [1]]]
 h' := ![![[28, 70], [4, 45], [13, 38], [32, 39], [59, 66], [58, 28], [0, 1]], ![[0, 1], [57, 26], [12, 33], [59, 32], [61, 5], [61, 43], [28, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [40, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [13, 43, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30377, -3662, 818]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-785, -282, 818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5999, -495, 63]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-5999, -495, 63]] 
 ![![71, 0, 0], ![51, 1, 0], ![26, 0, 1]] where
  M :=![![![-5999, -495, 63], ![48006, 3829, -495], ![-377190, -29214, 3829]]]
  hmulB := by decide  
  f := ![![![-200311, -54873, -3798]], ![![-184647, -50582, -3501]], ![![-662272, -181422, -12557]]]
  g := ![![![248, -495, 63], ![-1893, 3829, -495], ![14270, -29214, 3829]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-200311, -54873, -3798]] ![![-5999, -495, 63]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [37, 45, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 68, 41], [27, 4, 32], [0, 1]]
 g := ![![[9, 60, 64], [45, 50], [32, 9], [38, 32, 25], [59, 1], []], ![[60, 15, 63, 71], [34, 32], [45, 3], [56, 37, 19, 37], [55, 16], [0, 2]], ![[46, 20, 16, 24], [37, 2], [5, 65], [4, 3, 1, 48], [17, 25], [9, 2]]]
 h' := ![![[32, 68, 41], [49, 5, 8], [53, 49, 59], [54, 2, 3], [7, 9, 5], [0, 0, 1], [0, 1]], ![[27, 4, 32], [6, 35, 18], [60, 15, 55], [51, 49, 21], [13, 29, 24], [2, 44, 4], [32, 68, 41]], ![[0, 1], [67, 33, 47], [66, 9, 32], [55, 22, 49], [40, 35, 44], [31, 29, 68], [27, 4, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 60], []]
 b := ![[], [25, 29, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [37, 45, 14, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![147679, 189800, 31755]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2023, 2600, 435]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [50, 67, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 52, 14], [19, 26, 65], [0, 1]]
 g := ![![[35, 70, 18], [78, 67, 5], [33, 36, 67], [67, 17, 8], [7, 1], []], ![[69, 31, 54, 7], [45, 48, 62, 30], [71, 47, 27, 74], [74, 77, 33, 27], [33, 44], [63, 38]], ![[1, 8, 17, 62], [57, 39, 37, 21], [52, 69, 22, 4], [18, 62, 19, 22], [44, 18], [12, 38]]]
 h' := ![![[67, 52, 14], [50, 37, 27], [9, 15, 59], [47, 4, 15], [45, 34, 61], [0, 0, 1], [0, 1]], ![[19, 26, 65], [51, 66, 35], [67, 35, 6], [18, 36, 51], [25, 31, 8], [75, 57, 26], [67, 52, 14]], ![[0, 1], [67, 55, 17], [18, 29, 14], [14, 39, 13], [16, 14, 10], [77, 22, 52], [19, 26, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 70], []]
 b := ![[], [57, 37, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [50, 67, 72, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1598486, -426442, -28282]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20234, -5398, -358]
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



lemma PB199I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB199I1 : PrimesBelowBoundCertificateInterval O 31 79 199 where
  m := 11
  g := ![2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB199I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![79507]
    · exact ![103823]
    · exact ![148877]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I71N1]
  Il := ![[I37N1], [I41N1], [], [], [], [], [], [], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
