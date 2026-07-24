
import IdealArithmetic.Examples.NF3_1_478467_2.RI3_1_478467_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-117, 10, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-117, 10, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![31, 10, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-117, 10, 1], ![939, 63, 10], ![9390, 2739, 63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -10, 37]], ![![-4, 0, 1], ![17, -1, 10], ![201, 57, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [16, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36], [0, 1]]
 g := ![![[11, 7], [9], [31, 9], [7], [1]], ![[0, 30], [9], [1, 28], [7], [1]]]
 h' := ![![[9, 36], [7, 28], [22, 3], [33, 34], [21, 9], [0, 1]], ![[0, 1], [0, 9], [12, 34], [6, 3], [28, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [31, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [16, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1894, 1271, 153]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -7, 153]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-10, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-10, 1, 0]] 
 ![![37, 0, 0], ![27, 1, 0], ![11, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-10, 1, 0], ![0, -10, 1], ![939, 180, -10]]]
  hmulB := by decide  
  f := ![![![301, -30, 0], ![1110, 0, 0]], ![![231, -23, 0], ![852, 0, 0]], ![![103, -10, 0], ![380, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 37, 0], ![-11, 0, 37]], ![![-1, 1, 0], ![7, -10, 1], ![-103, 180, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-117, 10, 1]] ![![37, 0, 0], ![-10, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-370, 37, 0]], ![![-4329, 370, 37], ![2109, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-10, 1, 0]]], ![![![-117, 10, 1]], ![![57, -1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-241, -62, -4]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-241, -62, -4]] 
 ![![41, 0, 0], ![0, 41, 0], ![9, 36, 1]] where
  M :=![![![-241, -62, -4], ![-3756, -961, -62], ![-58218, -14916, -961]]]
  hmulB := by decide  
  f := ![![![31, -2, 0]], ![![0, 31, -2]], ![![-39, 18, -1]]]
  g := ![![![-5, 2, -4], ![-78, 31, -62], ![-1209, 480, -961]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [34, 32, 1] where
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
 g := ![![[13, 23], [23], [21], [35, 40], [1]], ![[15, 18], [23], [21], [26, 1], [1]]]
 h' := ![![[9, 40], [7, 33], [25, 8], [40, 29], [7, 9], [0, 1]], ![[0, 1], [17, 8], [15, 33], [14, 12], [6, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [14, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [34, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11265, 6231, 1714]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-651, -1353, 1714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -2, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![31, -2, 0]] 
 ![![41, 0, 0], ![5, 1, 0], ![16, 0, 1]] where
  M :=![![![31, -2, 0], ![0, 31, -2], ![-1878, -360, 31]]]
  hmulB := by decide  
  f := ![![![-241, -62, -4]], ![![-121, -31, -2]], ![![-1514, -388, -25]]]
  g := ![![![1, -2, 0], ![-3, 31, -2], ![-14, -360, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-241, -62, -4]] ![![31, -2, 0]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-136, 1, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-136, 1, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![36, 1, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-136, 1, 1], ![939, 44, 1], ![939, 1119, 44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -1, 43]], ![![-4, 0, 1], ![21, 1, 1], ![-15, 25, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [38, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 42], [0, 1]]
 g := ![![[40, 17], [29, 36], [31], [1, 10], [1]], ![[0, 26], [5, 7], [31], [23, 33], [1]]]
 h' := ![![[28, 42], [16, 24], [8, 6], [5, 17], [5, 28], [0, 1]], ![[0, 1], [0, 19], [4, 37], [8, 26], [15, 15], [28, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [21, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [38, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1296, 466, 294]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-216, 4, 294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-1, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-1, 1, 0]] 
 ![![43, 0, 0], ![42, 1, 0], ![42, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-1, 1, 0], ![0, -1, 1], ![939, 180, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![129, 0, 0]], ![![2, -1, 0], ![44, 0, 0]], ![![2, -1, 0], ![44, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 43, 0], ![-42, 0, 43]], ![![-1, 1, 0], ![0, -1, 1], ![-153, 180, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-136, 1, 1]] ![![43, 0, 0], ![-1, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-43, 43, 0]], ![![-5848, 43, 43], ![1075, 43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-1, 1, 0]]], ![![![-136, 1, 1]], ![![25, 1, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-127, 10, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-127, 10, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![14, 10, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-127, 10, 1], ![939, 53, 10], ![9390, 2739, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -10, 47]], ![![-3, 0, 1], ![17, -1, 10], ![184, 47, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [46, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 46], [0, 1]]
 g := ![![[11, 34], [19, 3], [28, 3], [37, 27], [1]], ![[9, 13], [5, 44], [14, 44], [5, 20], [1]]]
 h' := ![![[11, 46], [19, 9], [28, 35], [37, 12], [1, 11], [0, 1]], ![[0, 1], [24, 38], [37, 12], [28, 35], [28, 36], [11, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [14, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [46, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5551, 7409, 1507]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-567, -163, 1507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-10, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-10, 1, 0]] 
 ![![47, 0, 0], ![37, 1, 0], ![41, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-10, 1, 0], ![0, -10, 1], ![939, 180, -10]]]
  hmulB := by decide  
  f := ![![![371, -37, 0], ![1739, 0, 0]], ![![301, -30, 0], ![1411, 0, 0]], ![![333, -33, 0], ![1561, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 47, 0], ![-41, 0, 47]], ![![-1, 1, 0], ![7, -10, 1], ![-113, 180, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-127, 10, 1]] ![![47, 0, 0], ![-10, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-470, 47, 0]], ![![-5969, 470, 47], ![2209, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-10, 1, 0]]], ![![![-127, 10, 1]], ![![47, -1, 0]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [48, 41, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 39, 51], [36, 13, 2], [0, 1]]
 g := ![![[48, 22, 37], [21, 11], [4, 19, 38], [5, 15], [1]], ![[25, 12, 41, 14], [18, 44], [27, 22, 17, 5], [22, 10], [29, 11, 9, 45]], ![[41, 26, 2, 26], [41, 11], [15, 19, 4, 39], [43, 46], [27, 39, 32, 8]]]
 h' := ![![[28, 39, 51], [28, 27, 39], [20, 46, 45], [50, 43, 12], [5, 12, 11], [0, 1]], ![[36, 13, 2], [33, 37, 29], [46, 2, 16], [20, 19, 17], [49, 17, 13], [28, 39, 51]], ![[0, 1], [39, 42, 38], [29, 5, 45], [14, 44, 24], [45, 24, 29], [36, 13, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 13], []]
 b := ![[], [34, 4, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [48, 41, 42, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1310796, -383720, -28196]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24732, -7240, -532]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-135, -24, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-135, -24, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![42, 35, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-135, -24, 1], ![939, 45, -24], ![-22536, -3381, 45]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -35, 59]], ![![-3, -1, 1], ![33, 15, -24], ![-414, -84, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [34, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 58], [0, 1]]
 g := ![![[38, 7], [40, 16], [15], [34, 4], [6, 1]], ![[21, 52], [18, 43], [15], [58, 55], [12, 58]]]
 h' := ![![[6, 58], [56, 40], [7, 55], [24, 30], [32, 2], [0, 1]], ![[0, 1], [1, 19], [42, 4], [27, 29], [44, 57], [6, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [20, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [34, 53, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35770, 8824, 596]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![182, -204, 596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![24, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![24, 1, 0]] 
 ![![59, 0, 0], ![24, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![24, 1, 0], ![0, 24, 1], ![939, 180, 24]]]
  hmulB := by decide  
  f := ![![![433, 18, 0], ![-1062, 0, 0]], ![![168, 7, 0], ![-412, 0, 0]], ![![106, 4, 0], ![-260, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 59, 0], ![-14, 0, 59]], ![![0, 1, 0], ![-10, 24, 1], ![-63, 180, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-135, -24, 1]] ![![59, 0, 0], ![24, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1416, 59, 0]], ![![-7965, -1416, 59], ![-2301, -531, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![24, 1, 0]]], ![![![-135, -24, 1]], ![![-39, -9, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-99, 9, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-99, 9, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![23, 9, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-99, 9, 1], ![939, 81, 9], ![8451, 2559, 81]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -9, 61]], ![![-2, 0, 1], ![12, 0, 9], ![108, 30, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [17, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 60], [0, 1]]
 g := ![![[54, 20], [14], [13, 41], [29, 3], [58, 1]], ![[55, 41], [14], [12, 20], [20, 58], [55, 60]]]
 h' := ![![[58, 60], [47, 9], [23, 21], [56, 23], [51, 53], [0, 1]], ![[0, 1], [20, 52], [21, 40], [48, 38], [14, 8], [58, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [29, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [17, 3, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5619, -138, 188]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-163, -30, 188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-9, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-9, 1, 0]] 
 ![![61, 0, 0], ![52, 1, 0], ![41, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-9, 1, 0], ![0, -9, 1], ![939, 180, -9]]]
  hmulB := by decide  
  f := ![![![361, -40, 0], ![2440, 0, 0]], ![![298, -33, 0], ![2014, 0, 0]], ![![245, -27, 0], ![1656, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 61, 0], ![-41, 0, 61]], ![![-1, 1, 0], ![7, -9, 1], ![-132, 180, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-99, 9, 1]] ![![61, 0, 0], ![-9, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-549, 61, 0]], ![![-6039, 549, 61], ![1830, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-9, 1, 0]]], ![![![-99, 9, 1]], ![![30, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [41, 37, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 15, 41], [28, 51, 26], [0, 1]]
 g := ![![[6, 22, 60], [0, 55, 9], [52, 23], [14, 55], [50, 1], []], ![[18, 5, 53, 44], [42, 44, 35, 3], [12, 10], [61, 40], [62, 55], [56, 6]], ![[22, 50, 3, 16], [29, 34, 55, 4], [33, 40], [25, 59], [20, 24], [4, 6]]]
 h' := ![![[22, 15, 41], [0, 11, 23], [51, 10, 64], [21, 35, 36], [27, 52, 51], [0, 0, 1], [0, 1]], ![[28, 51, 26], [39, 20, 16], [12, 32, 56], [13, 65, 55], [13, 39, 43], [64, 17, 51], [22, 15, 41]], ![[0, 1], [29, 36, 28], [12, 25, 14], [5, 34, 43], [5, 43, 40], [17, 50, 15], [28, 51, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 14], []]
 b := ![[], [42, 23, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [41, 37, 17, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9146840, 3175063, 283879]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136520, 47389, 4237]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![3, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![3, 1, 0]] 
 ![![71, 0, 0], ![3, 1, 0], ![62, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![3, 1, 0], ![0, 3, 1], ![939, 180, 3]]]
  hmulB := by decide  
  f := ![![![67, 22, 0], ![-1562, 0, 0]], ![![-3, -1, 0], ![72, 0, 0]], ![![58, 19, 0], ![-1352, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 71, 0], ![-62, 0, 71]], ![![0, 1, 0], ![-1, 3, 1], ![3, 180, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![27, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![27, 1, 0]] 
 ![![71, 0, 0], ![27, 1, 0], ![52, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![27, 1, 0], ![0, 27, 1], ![939, 180, 27]]]
  hmulB := by decide  
  f := ![![![703, 26, 0], ![-1846, 0, 0]], ![![243, 9, 0], ![-638, 0, 0]], ![![524, 19, 0], ![-1376, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 71, 0], ![-52, 0, 71]], ![![0, 1, 0], ![-11, 27, 1], ![-75, 180, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-30, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-30, 1, 0]] 
 ![![71, 0, 0], ![41, 1, 0], ![23, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-30, 1, 0], ![0, -30, 1], ![939, 180, -30]]]
  hmulB := by decide  
  f := ![![![1711, -57, 0], ![4047, 0, 0]], ![![1021, -34, 0], ![2415, 0, 0]], ![![583, -19, 0], ![1379, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 71, 0], ![-23, 0, 71]], ![![-1, 1, 0], ![17, -30, 1], ![-81, 180, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![3, 1, 0]] ![![71, 0, 0], ![27, 1, 0]]
  ![![71, 0, 0], ![-132, -41, 1]] where
 M := ![![![5041, 0, 0], ![1917, 71, 0]], ![![213, 71, 0], ![81, 30, 1]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![27, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-132, -41, 1]] ![![71, 0, 0], ![-30, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2130, 71, 0]], ![![-9372, -2911, 71], ![4899, 1278, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-30, 1, 0]]], ![![![-132, -41, 1]], ![![69, 18, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [51, 12, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 22, 54], [43, 50, 19], [0, 1]]
 g := ![![[41, 63, 72], [25, 64], [69, 71], [49, 58, 16], [69, 1], []], ![[24, 12, 15, 2], [23, 49], [71, 48], [26, 64, 52, 12], [3, 18], [56, 69]], ![[6, 15, 10, 67], [1, 6], [64, 1], [14, 31, 56, 9], [2, 46], [18, 69]]]
 h' := ![![[26, 22, 54], [71, 43, 27], [55, 60, 65], [56, 37, 61], [58, 70, 4], [0, 0, 1], [0, 1]], ![[43, 50, 19], [72, 72, 22], [2, 0, 66], [22, 2, 11], [20, 10, 38], [10, 19, 50], [26, 22, 54]], ![[0, 1], [47, 31, 24], [5, 13, 15], [38, 34, 1], [3, 66, 31], [55, 54, 22], [43, 50, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 29], []]
 b := ![[], [27, 72, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [51, 12, 4, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14543133, -835120, 262800]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-199221, -11440, 3600]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [67, 32, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 24, 18], [10, 54, 61], [0, 1]]
 g := ![![[39, 29, 8], [48, 7, 19], [29, 4, 20], [78, 75, 19], [4, 1], []], ![[33, 45, 42, 67], [58, 56, 56, 49], [45, 69, 21, 72], [35, 11, 17, 49], [0, 72], [27, 8]], ![[38, 12, 47, 61], [23, 4, 21, 39], [78, 16, 12, 6], [46, 9, 15, 48], [62, 23], [63, 8]]]
 h' := ![![[73, 24, 18], [23, 46, 18], [32, 54, 63], [67, 76, 39], [48, 42, 63], [0, 0, 1], [0, 1]], ![[10, 54, 61], [65, 29, 62], [31, 22, 29], [63, 61, 77], [40, 50, 50], [44, 50, 54], [73, 24, 18]], ![[0, 1], [12, 4, 78], [69, 3, 66], [4, 21, 42], [44, 66, 45], [66, 29, 24], [10, 54, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 10], []]
 b := ![[], [14, 31, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [67, 32, 75, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![174985, 306994, 53246]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2215, 3886, 674]
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



lemma PB196I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB196I1 : PrimesBelowBoundCertificateInterval O 31 79 196 where
  m := 11
  g := ![2, 2, 2, 2, 1, 2, 2, 1, 3, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB196I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N1, I47N1, I59N1, I61N1, I71N0, I71N1, I71N2]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [], [I59N1], [I61N1], [], [I71N0, I71N1, I71N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
