
import IdealArithmetic.Examples.NF3_1_662796_1.RI3_1_662796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![9, 18, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![9, 18, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![9, 18, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![9, 18, 1], ![48, 22, 178], ![1483, -401, -49]]]
  hmulB := by decide  
  f := ![![![-8, -18, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -18, 37]], ![![0, 0, 1], ![-42, -86, 178], ![52, 13, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [14, 32, 1] where
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
 g := ![![[34, 21], [12], [10, 3], [25], [1]], ![[28, 16], [12], [25, 34], [25], [1]]]
 h' := ![![[5, 36], [7, 24], [8, 7], [31, 22], [23, 5], [0, 1]], ![[0, 1], [16, 13], [6, 30], [30, 15], [11, 32], [5, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [7, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [14, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![994, -195, -720]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![202, 345, -720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![7, 1, 0]] 
 ![![37, 0, 0], ![7, 1, 0], ![12, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![7, 1, 0], ![-2, 9, 10], ![84, -23, 5]]]
  hmulB := by decide  
  f := ![![![282, -1297, -1440], ![37, 5328, 0]], ![![47, -244, -270], ![38, 999, 0]], ![![89, -421, -467], ![25, 1728, 0]]]
  g := ![![![1, 0, 0], ![-7, 37, 0], ![-12, 0, 37]], ![![0, 1, 0], ![-5, 9, 10], ![5, -23, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![9, 18, 1]] ![![37, 0, 0], ![7, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![259, 37, 0]], ![![333, 666, 37], ![111, 148, 185]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![7, 1, 0]]], ![![![9, 18, 1]], ![![3, 4, 5]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [25, 29, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 20, 14], [0, 20, 27], [0, 1]]
 g := ![![[19, 27, 36], [8, 5], [23, 8], [14, 17, 1], []], ![[11, 16, 15, 27], [36, 37], [11, 32], [12, 14, 14, 24], [38, 32]], ![[0, 23, 2, 38], [29, 25], [3, 8], [25, 3, 18, 17], [25, 32]]]
 h' := ![![[17, 20, 14], [4, 18, 35], [32, 27, 13], [19, 30, 7], [0, 0, 1], [0, 1]], ![[0, 20, 27], [12, 25, 9], [16, 29, 23], [2, 0, 27], [36, 8, 20], [17, 20, 14]], ![[0, 1], [23, 39, 38], [25, 26, 5], [31, 11, 7], [31, 33, 20], [0, 20, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 9], []]
 b := ![[], [9, 22, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [25, 29, 24, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4661987, -1567020, 1111264]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![113707, -38220, 27104]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [19, 28, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 13, 32], [24, 29, 11], [0, 1]]
 g := ![![[21, 21, 16], [17, 41, 17], [26, 25], [30, 12, 1], []], ![[29, 23, 21, 12], [7, 0, 20, 37], [2, 23], [35, 17, 32, 37], [5, 35]], ![[5, 33, 17, 17], [8, 30, 32, 17], [38, 40], [13, 14, 5, 10], [26, 35]]]
 h' := ![![[31, 13, 32], [21, 16, 39], [14, 19, 24], [32, 7, 5], [0, 0, 1], [0, 1]], ![[24, 29, 11], [20, 32, 9], [16, 13, 14], [21, 10, 25], [6, 1, 29], [31, 13, 32]], ![[0, 1], [34, 38, 38], [30, 11, 5], [8, 26, 13], [39, 42, 13], [24, 29, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 30], []]
 b := ![[], [12, 3, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [19, 28, 31, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1049264715, -283602673, -111142358]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24401505, -6595411, -2584706]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-5, 20, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-5, 20, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![42, 20, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-5, 20, 1], ![44, 12, 198], ![1651, -447, -67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -20, 47]], ![![-1, 0, 1], ![-176, -84, 198], ![95, 19, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [26, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 46], [0, 1]]
 g := ![![[4, 37], [37, 16], [16, 34], [37, 6], [1]], ![[10, 10], [18, 31], [5, 13], [24, 41], [1]]]
 h' := ![![[37, 46], [25, 15], [7, 4], [25, 9], [21, 37], [0, 1]], ![[0, 1], [16, 32], [14, 43], [29, 38], [27, 10], [37, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [26, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [26, 10, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3269, 1890, -4582]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4025, 1990, -4582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-10, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-10, 1, 0]] 
 ![![47, 0, 0], ![37, 1, 0], ![20, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-10, 1, 0], ![-2, -8, 10], ![84, -23, -12]]]
  hmulB := by decide  
  f := ![![![-1089, -4483, 5600], ![141, -26320, 0]], ![![-849, -3523, 4400], ![142, -20680, 0]], ![![-460, -1908, 2383], ![76, -11200, 0]]]
  g := ![![![1, 0, 0], ![-37, 47, 0], ![-20, 0, 47]], ![![-1, 1, 0], ![2, -8, 10], ![25, -23, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-5, 20, 1]] ![![47, 0, 0], ![-10, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-470, 47, 0]], ![![-235, 940, 47], ![94, -188, 188]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-10, 1, 0]]], ![![![-5, 20, 1]], ![![2, -4, 4]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![37, -1, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![37, -1, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![37, 52, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![37, -1, 1], ![86, 12, -12], ![-113, 36, 17]]]
  hmulB := by decide  
  f := ![![![-36, 1, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -52, 53]], ![![0, -1, 1], ![10, 12, -12], ![-14, -16, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [47, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 52], [0, 1]]
 g := ![![[48, 44], [9], [43, 36], [25], [23, 1]], ![[0, 9], [9], [23, 17], [25], [46, 52]]]
 h' := ![![[23, 52], [50, 37], [46, 50], [8, 47], [32, 5], [0, 1]], ![[0, 1], [0, 16], [30, 3], [29, 6], [41, 48], [23, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [1, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [47, 30, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1025, -191, -710]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![515, 693, -710]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![12, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![12, 1, 0]] 
 ![![53, 0, 0], ![12, 1, 0], ![36, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![12, 1, 0], ![-2, 14, 10], ![84, -23, 10]]]
  hmulB := by decide  
  f := ![![![1391, -9985, -7130], ![159, 37789, 0]], ![![310, -2255, -1610], ![54, 8533, 0]], ![![948, -6782, -4843], ![94, 25668, 0]]]
  g := ![![![1, 0, 0], ![-12, 53, 0], ![-36, 0, 53]], ![![0, 1, 0], ![-10, 14, 10], ![0, -23, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![37, -1, 1]] ![![53, 0, 0], ![12, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![636, 53, 0]], ![![1961, -53, 53], ![530, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![12, 1, 0]]], ![![![37, -1, 1]], ![![10, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-8, -16, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-8, -16, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![51, 43, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-8, -16, 1], ![116, -63, -162], ![-1373, 381, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -43, 59]], ![![-1, -1, 1], ![142, 117, -162], ![-25, 5, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [4, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 58], [0, 1]]
 g := ![![[17, 15], [21, 22], [49], [32, 29], [50, 1]], ![[0, 44], [0, 37], [49], [7, 30], [41, 58]]]
 h' := ![![[50, 58], [34, 30], [22, 9], [49, 7], [36, 18], [0, 1]], ![[0, 1], [0, 29], [0, 50], [45, 52], [51, 41], [50, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [28, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [4, 9, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19238, -4299, 3156]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2402, -2373, 3156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-15, 1, 0]] 
 ![![59, 0, 0], ![44, 1, 0], ![57, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-15, 1, 0], ![-2, -13, 10], ![84, -23, -17]]]
  hmulB := by decide  
  f := ![![![4786, 32186, -24750], ![-649, 146025, 0]], ![![3571, 23993, -18450], ![-471, 108855, 0]], ![![4623, 31095, -23911], ![-630, 141075, 0]]]
  g := ![![![1, 0, 0], ![-44, 59, 0], ![-57, 0, 59]], ![![-1, 1, 0], ![0, -13, 10], ![35, -23, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-8, -16, 1]] ![![59, 0, 0], ![-15, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-885, 59, 0]], ![![-472, -944, 59], ![236, 177, -177]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-15, 1, 0]]], ![![![-8, -16, 1]], ![![4, 3, -3]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![29, -25, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![29, -25, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![29, 36, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![29, -25, 1], ![134, -44, -252], ![-2129, 588, 57]]]
  hmulB := by decide  
  f := ![![![-28, 25, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -36, 61]], ![![0, -1, 1], ![122, 148, -252], ![-62, -24, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [1, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 60], [0, 1]]
 g := ![![[49, 1], [48], [50, 4], [30, 14], [12, 1]], ![[0, 60], [48], [37, 57], [15, 47], [24, 60]]]
 h' := ![![[12, 60], [12, 60], [11, 32], [31, 2], [49, 21], [0, 1]], ![[0, 1], [0, 1], [29, 29], [55, 59], [57, 40], [12, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [21, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [1, 49, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2003, 797, -1064]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![473, 641, -1064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![8, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![8, 1, 0]] 
 ![![61, 0, 0], ![8, 1, 0], ![4, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![8, 1, 0], ![-2, 10, 10], ![84, -23, 6]]]
  hmulB := by decide  
  f := ![![![-551, 2760, 2760], ![0, -16836, 0]], ![![-72, 360, 360], ![1, -2196, 0]], ![![-36, 181, 181], ![-1, -1104, 0]]]
  g := ![![![1, 0, 0], ![-8, 61, 0], ![-4, 0, 61]], ![![0, 1, 0], ![-2, 10, 10], ![4, -23, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![29, -25, 1]] ![![61, 0, 0], ![8, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![488, 61, 0]], ![![1769, -1525, 61], ![366, -244, -244]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![8, 1, 0]]], ![![![29, -25, 1]], ![![6, -4, -4]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [23, 57, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 52, 42], [66, 14, 25], [0, 1]]
 g := ![![[46, 35, 37], [46, 26, 49], [57, 10], [43, 15], [13, 1], []], ![[24, 44, 49, 58], [63, 54, 63, 48], [57, 33], [50, 19], [40, 62], [31, 22]], ![[5, 9, 30, 64], [27, 36, 36, 9], [45, 4], [41, 33], [56, 24], [48, 22]]]
 h' := ![![[14, 52, 42], [14, 10, 38], [9, 58, 60], [39, 17, 55], [36, 40, 45], [0, 0, 1], [0, 1]], ![[66, 14, 25], [5, 26, 14], [18, 25, 60], [49, 35, 10], [44, 21, 32], [19, 54, 14], [14, 52, 42]], ![[0, 1], [32, 31, 15], [34, 51, 14], [59, 15, 2], [8, 6, 57], [36, 13, 52], [66, 14, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 7], []]
 b := ![[], [58, 9, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [23, 57, 54, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135005, -119193, 416070]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2015, -1779, 6210]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![1, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![1, 1, 0]] 
 ![![71, 0, 0], ![1, 1, 0], ![35, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![1, 1, 0], ![-2, 3, 10], ![84, -23, -1]]]
  hmulB := by decide  
  f := ![![![-114, 170, 570], ![71, -4047, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-56, 84, 281], ![21, -1995, 0]]]
  g := ![![![1, 0, 0], ![-1, 71, 0], ![-35, 0, 71]], ![![0, 1, 0], ![-5, 3, 10], ![2, -23, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![23, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![23, 1, 0]] 
 ![![71, 0, 0], ![23, 1, 0], ![63, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![23, 1, 0], ![-2, 25, 10], ![84, -23, 21]]]
  hmulB := by decide  
  f := ![![![1881, -24654, -9860], ![284, 70006, 0]], ![![592, -7977, -3190], ![143, 22649, 0]], ![![1671, -21876, -8749], ![246, 62118, 0]]]
  g := ![![![1, 0, 0], ![-23, 71, 0], ![-63, 0, 71]], ![![0, 1, 0], ![-17, 25, 10], ![-10, -23, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-24, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-24, 1, 0]] 
 ![![71, 0, 0], ![47, 1, 0], ![18, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-24, 1, 0], ![-2, -22, 10], ![84, -23, -26]]]
  hmulB := by decide  
  f := ![![![4249, 49378, -22440], ![-710, 159324, 0]], ![![2827, 32676, -14850], ![-425, 105435, 0]], ![![1086, 12518, -5689], ![-154, 40392, 0]]]
  g := ![![![1, 0, 0], ![-47, 71, 0], ![-18, 0, 71]], ![![-1, 1, 0], ![12, -22, 10], ![23, -23, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![1, 1, 0]] ![![71, 0, 0], ![23, 1, 0]]
  ![![71, 0, 0], ![-5, 31, 1]] where
 M := ![![![5041, 0, 0], ![1633, 71, 0]], ![![71, 71, 0], ![21, 26, 10]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![23, 1, 0], ![0, 0, 0]]], ![![![6, -30, -1], ![71, 0, 0]], ![![1, -4, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-5, 31, 1]] ![![71, 0, 0], ![-24, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1704, 71, 0]], ![![-355, 2201, 71], ![142, -710, 284]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-24, 1, 0]]], ![![![-5, 31, 1]], ![![2, -10, 4]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![1, -5, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![1, -5, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![1, 68, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![1, -5, 1], ![94, -32, -52], ![-449, 128, -11]]]
  hmulB := by decide  
  f := ![![![0, -1, 1], ![-21, 1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -68, 73]], ![![0, -1, 1], ![2, 48, -52], ![-6, 12, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [32, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 72], [0, 1]]
 g := ![![[53, 16], [19], [1], [21, 38], [70], [1]], ![[0, 57], [19], [1], [32, 35], [70], [1]]]
 h' := ![![[56, 72], [68, 4], [47, 26], [58, 1], [25, 44], [41, 56], [0, 1]], ![[0, 1], [0, 69], [43, 47], [41, 72], [7, 29], [38, 17], [56, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [67, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [32, 17, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3457, -860, -485]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54, 440, -485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-21, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-21, 1, 0]] 
 ![![73, 0, 0], ![52, 1, 0], ![11, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-21, 1, 0], ![-2, -19, 10], ![84, -23, -23]]]
  hmulB := by decide  
  f := ![![![3925, 38882, -20460], ![-584, 149358, 0]], ![![2810, 27688, -14570], ![-364, 106361, 0]], ![![611, 5858, -3083], ![-20, 22506, 0]]]
  g := ![![![1, 0, 0], ![-52, 73, 0], ![-11, 0, 73]], ![![-1, 1, 0], ![12, -19, 10], ![21, -23, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![1, -5, 1]] ![![73, 0, 0], ![-21, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1533, 73, 0]], ![![73, -365, 73], ![73, 73, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-21, 1, 0]]], ![![![1, -5, 1]], ![![1, 1, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![4, 21, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![4, 21, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![4, 21, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![4, 21, 1], ![42, 23, 208], ![1735, -470, -60]]]
  hmulB := by decide  
  f := ![![![-3, -21, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -21, 79]], ![![0, 0, 1], ![-10, -55, 208], ![25, 10, -60]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [43, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 78], [0, 1]]
 g := ![![[22, 36], [20, 16], [56, 42], [14, 36], [4], [1]], ![[15, 43], [52, 63], [61, 37], [7, 43], [4], [1]]]
 h' := ![![[2, 78], [9, 6], [41, 75], [30, 68], [18, 73], [36, 2], [0, 1]], ![[0, 1], [21, 73], [33, 4], [8, 11], [6, 6], [40, 77], [2, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [63, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [43, 77, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16451, 4818, -1644]
  a := ![-2, -6, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125, 498, -1644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![29, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![29, 1, 0]] 
 ![![79, 0, 0], ![29, 1, 0], ![60, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![29, 1, 0], ![-2, 31, 10], ![84, -23, 27]]]
  hmulB := by decide  
  f := ![![![2587, -42786, -13800], ![474, 109020, 0]], ![![954, -15688, -5060], ![159, 39974, 0]], ![![1956, -32496, -10481], ![384, 82800, 0]]]
  g := ![![![1, 0, 0], ![-29, 79, 0], ![-60, 0, 79]], ![![0, 1, 0], ![-19, 31, 10], ![-11, -23, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![4, 21, 1]] ![![79, 0, 0], ![29, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2291, 79, 0]], ![![316, 1659, 79], ![158, 632, 237]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![29, 1, 0]]], ![![![4, 21, 1]], ![![2, 8, 3]]]]
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


lemma PB231I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB231I1 : PrimesBelowBoundCertificateInterval O 31 79 231 where
  m := 11
  g := ![2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB231I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I47N1, I53N1, I59N1, I61N1, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[I37N1], [], [], [I47N1], [I53N1], [I59N1], [I61N1], [], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
