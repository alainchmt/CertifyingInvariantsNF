
import IdealArithmetic.Examples.NF3_1_466627_2.RI3_1_466627_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, 3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, 3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![32, 3, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, 3, 1], ![133, 9, 3], ![399, 175, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -3, 37]], ![![-1, 0, 1], ![1, 0, 3], ![3, 4, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [35, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 36], [0, 1]]
 g := ![![[29, 4], [28], [1, 34], [34], [1]], ![[2, 33], [28], [12, 3], [34], [1]]]
 h' := ![![[21, 36], [23, 35], [2, 19], [35, 21], [2, 21], [0, 1]], ![[0, 1], [18, 2], [31, 18], [32, 16], [36, 16], [21, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [19, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [35, 16, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![301, 145, -1]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 4, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-3, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-3, 1, 0]] 
 ![![37, 0, 0], ![34, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-3, 1, 0], ![0, -3, 1], ![133, 14, -3]]]
  hmulB := by decide  
  f := ![![![82, -27, 0], ![999, 0, 0]], ![![76, -25, 0], ![926, 0, 0]], ![![64, -21, 0], ![780, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 37, 0], ![-28, 0, 37]], ![![-1, 1, 0], ![2, -3, 1], ![-7, 14, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-5, 3, 1]] ![![37, 0, 0], ![-3, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-111, 37, 0]], ![![-185, 111, 37], ![148, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-3, 1, 0]]], ![![![-5, 3, 1]], ![![4, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, -8, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, -8, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![9, 33, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, -8, 1], ![133, 23, -8], ![-1064, 21, 23]]]
  hmulB := by decide  
  f := ![![![-8, 8, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -33, 41]], ![![0, -1, 1], ![5, 7, -8], ![-31, -18, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [7, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 40], [0, 1]]
 g := ![![[18, 36], [31], [37], [15, 9], [1]], ![[33, 5], [31], [37], [29, 32], [1]]]
 h' := ![![[38, 40], [31, 6], [24, 20], [18, 23], [34, 38], [0, 1]], ![[0, 1], [13, 35], [5, 21], [31, 18], [2, 3], [38, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [39, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [7, 3, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1591, 1027, 133]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68, -82, 133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![8, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![8, 1, 0]] 
 ![![41, 0, 0], ![8, 1, 0], ![18, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![8, 1, 0], ![0, 8, 1], ![133, 14, 8]]]
  hmulB := by decide  
  f := ![![![193, 24, 0], ![-984, 0, 0]], ![![24, 3, 0], ![-122, 0, 0]], ![![82, 10, 0], ![-418, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 41, 0], ![-18, 0, 41]], ![![0, 1, 0], ![-2, 8, 1], ![-3, 14, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![9, -8, 1]] ![![41, 0, 0], ![8, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![328, 41, 0]], ![![369, -328, 41], ![205, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![8, 1, 0]]], ![![![9, -8, 1]], ![![5, -1, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [37, 27, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 7, 18], [26, 35, 25], [0, 1]]
 g := ![![[2, 8, 17], [32, 38, 21], [12, 11], [41, 38, 1], []], ![[30, 30, 14, 12], [12, 31, 7, 7], [31, 4], [36, 20, 29, 34], [8, 23]], ![[17, 12, 18, 31], [10, 42, 11, 9], [41, 13], [10, 39, 38, 21], [1, 23]]]
 h' := ![![[12, 7, 18], [20, 10, 24], [1, 26, 35], [31, 24, 22], [0, 0, 1], [0, 1]], ![[26, 35, 25], [18, 37, 31], [24, 21, 16], [28, 41, 41], [20, 4, 35], [12, 7, 18]], ![[0, 1], [7, 39, 31], [37, 39, 35], [7, 21, 23], [37, 39, 7], [26, 35, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 20], []]
 b := ![[], [2, 38, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [37, 27, 5, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-205583, -11481, -14319]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4781, -267, -333]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![4, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![4, 1, 0]] 
 ![![47, 0, 0], ![4, 1, 0], ![31, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![4, 1, 0], ![0, 4, 1], ![133, 14, 4]]]
  hmulB := by decide  
  f := ![![![41, 10, 0], ![-470, 0, 0]], ![![-4, -1, 0], ![48, 0, 0]], ![![25, 6, 0], ![-286, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 47, 0], ![-31, 0, 47]], ![![0, 1, 0], ![-1, 4, 1], ![-1, 14, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![5, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![5, 1, 0]] 
 ![![47, 0, 0], ![5, 1, 0], ![22, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![5, 1, 0], ![0, 5, 1], ![133, 14, 5]]]
  hmulB := by decide  
  f := ![![![86, 17, 0], ![-799, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![36, 7, 0], ![-334, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 47, 0], ![-22, 0, 47]], ![![0, 1, 0], ![-1, 5, 1], ![-1, 14, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-9, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-9, 1, 0]] 
 ![![47, 0, 0], ![38, 1, 0], ![13, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-9, 1, 0], ![0, -9, 1], ![133, 14, -9]]]
  hmulB := by decide  
  f := ![![![244, -27, 0], ![1269, 0, 0]], ![![190, -21, 0], ![988, 0, 0]], ![![74, -8, 0], ![385, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 47, 0], ![-13, 0, 47]], ![![-1, 1, 0], ![7, -9, 1], ![-6, 14, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![4, 1, 0]] ![![47, 0, 0], ![5, 1, 0]]
  ![![47, 0, 0], ![-27, 9, 1]] where
 M := ![![![2209, 0, 0], ![235, 47, 0]], ![![188, 47, 0], ![20, 9, 1]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![5, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-27, 9, 1]] ![![47, 0, 0], ![-9, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-423, 47, 0]], ![![-1269, 423, 47], ![376, -94, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-9, 1, 0]]], ![![![-27, 9, 1]], ![![8, -2, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![6, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![6, 1, 0]] 
 ![![53, 0, 0], ![6, 1, 0], ![17, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![6, 1, 0], ![0, 6, 1], ![133, 14, 6]]]
  hmulB := by decide  
  f := ![![![43, 7, 0], ![-371, 0, 0]], ![![-6, -1, 0], ![54, 0, 0]], ![![7, 1, 0], ![-59, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 53, 0], ![-17, 0, 53]], ![![0, 1, 0], ![-1, 6, 1], ![-1, 14, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![23, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![23, 1, 0]] 
 ![![53, 0, 0], ![23, 1, 0], ![1, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![23, 1, 0], ![0, 23, 1], ![133, 14, 23]]]
  hmulB := by decide  
  f := ![![![369, 16, 0], ![-848, 0, 0]], ![![161, 7, 0], ![-370, 0, 0]], ![![-13, -1, 0], ![30, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 53, 0], ![-1, 0, 53]], ![![0, 1, 0], ![-10, 23, 1], ![-4, 14, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![24, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![24, 1, 0]] 
 ![![53, 0, 0], ![24, 1, 0], ![7, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![24, 1, 0], ![0, 24, 1], ![133, 14, 24]]]
  hmulB := by decide  
  f := ![![![385, 16, 0], ![-848, 0, 0]], ![![168, 7, 0], ![-370, 0, 0]], ![![11, 0, 0], ![-24, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 53, 0], ![-7, 0, 53]], ![![0, 1, 0], ![-11, 24, 1], ![-7, 14, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![6, 1, 0]] ![![53, 0, 0], ![23, 1, 0]]
  ![![53, 0, 0], ![-21, -24, 1]] where
 M := ![![![2809, 0, 0], ![1219, 53, 0]], ![![318, 53, 0], ![138, 29, 1]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![23, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-21, -24, 1]] ![![53, 0, 0], ![24, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1272, 53, 0]], ![![-1113, -1272, 53], ![-371, -583, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![24, 1, 0]]], ![![![-21, -24, 1]], ![![-7, -11, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![3, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![3, 1, 0]] 
 ![![59, 0, 0], ![3, 1, 0], ![50, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![3, 1, 0], ![0, 3, 1], ![133, 14, 3]]]
  hmulB := by decide  
  f := ![![![55, 18, 0], ![-1062, 0, 0]], ![![-3, -1, 0], ![60, 0, 0]], ![![46, 15, 0], ![-888, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 59, 0], ![-50, 0, 59]], ![![0, 1, 0], ![-1, 3, 1], ![-1, 14, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![19, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![19, 1, 0]] 
 ![![59, 0, 0], ![19, 1, 0], ![52, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![19, 1, 0], ![0, 19, 1], ![133, 14, 19]]]
  hmulB := by decide  
  f := ![![![381, 20, 0], ![-1180, 0, 0]], ![![95, 5, 0], ![-294, 0, 0]], ![![330, 17, 0], ![-1022, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 59, 0], ![-52, 0, 59]], ![![0, 1, 0], ![-7, 19, 1], ![-19, 14, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-22, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-22, 1, 0]] 
 ![![59, 0, 0], ![37, 1, 0], ![47, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-22, 1, 0], ![0, -22, 1], ![133, 14, -22]]]
  hmulB := by decide  
  f := ![![![1255, -57, 0], ![3363, 0, 0]], ![![793, -36, 0], ![2125, 0, 0]], ![![999, -45, 0], ![2677, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 59, 0], ![-47, 0, 59]], ![![-1, 1, 0], ![13, -22, 1], ![11, 14, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![3, 1, 0]] ![![59, 0, 0], ![19, 1, 0]]
  ![![59, 0, 0], ![-2, 22, 1]] where
 M := ![![![3481, 0, 0], ![1121, 59, 0]], ![![177, 59, 0], ![57, 22, 1]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![19, 1, 0], ![0, 0, 0]]], ![![![5, -21, -1], ![59, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-2, 22, 1]] ![![59, 0, 0], ![-22, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1298, 59, 0]], ![![-118, 1298, 59], ![177, -472, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-22, 1, 0]]], ![![![-2, 22, 1]], ![![3, -8, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-34, 23, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-34, 23, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![27, 23, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-34, 23, 1], ![133, -20, 23], ![3059, 455, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -23, 61]], ![![-1, 0, 1], ![-8, -9, 23], ![59, 15, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [50, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 60], [0, 1]]
 g := ![![[46, 13], [56], [59, 49], [20, 46], [18, 1]], ![[36, 48], [56], [26, 12], [55, 15], [36, 60]]]
 h' := ![![[18, 60], [2, 14], [39, 42], [37, 54], [15, 30], [0, 1]], ![[0, 1], [10, 47], [2, 19], [33, 7], [6, 31], [18, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [9, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [50, 43, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-704, 1158, -8]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, 22, -8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-23, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-23, 1, 0]] 
 ![![61, 0, 0], ![38, 1, 0], ![20, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-23, 1, 0], ![0, -23, 1], ![133, 14, -23]]]
  hmulB := by decide  
  f := ![![![323, -14, 0], ![854, 0, 0]], ![![208, -9, 0], ![550, 0, 0]], ![![124, -5, 0], ![328, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 61, 0], ![-20, 0, 61]], ![![-1, 1, 0], ![14, -23, 1], ![1, 14, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-34, 23, 1]] ![![61, 0, 0], ![-23, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1403, 61, 0]], ![![-2074, 1403, 61], ![915, -549, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-23, 1, 0]]], ![![![-34, 23, 1]], ![![15, -9, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![8, 25, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![8, 25, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![8, 25, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![8, 25, 1], ![133, 22, 25], ![3325, 483, 22]]]
  hmulB := by decide  
  f := ![![![-7, -25, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -25, 67]], ![![0, 0, 1], ![-1, -9, 25], ![47, -1, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [6, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 66], [0, 1]]
 g := ![![[8, 56], [57, 64], [65], [4], [26], [1]], ![[0, 11], [0, 3], [65], [4], [26], [1]]]
 h' := ![![[19, 66], [60, 18], [49, 8], [38, 20], [14, 65], [61, 19], [0, 1]], ![[0, 1], [0, 49], [0, 59], [16, 47], [43, 2], [20, 48], [19, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [43, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [6, 48, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![272, 113, -33]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 14, -33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-25, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-25, 1, 0]] 
 ![![67, 0, 0], ![42, 1, 0], ![45, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-25, 1, 0], ![0, -25, 1], ![133, 14, -25]]]
  hmulB := by decide  
  f := ![![![1626, -65, 0], ![4355, 0, 0]], ![![1026, -41, 0], ![2748, 0, 0]], ![![1110, -44, 0], ![2973, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 67, 0], ![-45, 0, 67]], ![![-1, 1, 0], ![15, -25, 1], ![10, 14, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![8, 25, 1]] ![![67, 0, 0], ![-25, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1675, 67, 0]], ![![536, 1675, 67], ![-67, -603, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-25, 1, 0]]], ![![![8, 25, 1]], ![![-1, -9, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![6, 34, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![6, 34, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![6, 34, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![6, 34, 1], ![133, 20, 34], ![4522, 609, 20]]]
  hmulB := by decide  
  f := ![![![-5, -34, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -34, 71]], ![![0, 0, 1], ![-1, -16, 34], ![62, -1, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [32, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 70], [0, 1]]
 g := ![![[11, 20], [19, 50], [61, 18], [32], [9], [1]], ![[0, 51], [27, 21], [44, 53], [32], [9], [1]]]
 h' := ![![[3, 70], [31, 37], [36, 11], [7, 36], [26, 48], [39, 3], [0, 1]], ![[0, 1], [0, 34], [69, 60], [44, 35], [28, 23], [48, 68], [3, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [31, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [32, 68, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5155, 1995, 445]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35, -185, 445]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-34, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-34, 1, 0]] 
 ![![71, 0, 0], ![37, 1, 0], ![51, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-34, 1, 0], ![0, -34, 1], ![133, 14, -34]]]
  hmulB := by decide  
  f := ![![![1259, -37, 0], ![2627, 0, 0]], ![![681, -20, 0], ![1421, 0, 0]], ![![867, -25, 0], ![1809, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 71, 0], ![-51, 0, 71]], ![![-1, 1, 0], ![17, -34, 1], ![19, 14, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![6, 34, 1]] ![![71, 0, 0], ![-34, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2414, 71, 0]], ![![426, 2414, 71], ![-71, -1136, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-34, 1, 0]]], ![![![6, 34, 1]], ![![-1, -16, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-13, 1, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-13, 1, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![60, 1, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-13, 1, 1], ![133, 1, 1], ![133, 147, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -1, 73]], ![![-1, 0, 1], ![1, 0, 1], ![1, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [44, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 72], [0, 1]]
 g := ![![[14, 57], [69], [38], [71, 46], [2], [1]], ![[15, 16], [69], [38], [59, 27], [2], [1]]]
 h' := ![![[41, 72], [53, 38], [13, 19], [15, 29], [23, 51], [29, 41], [0, 1]], ![[0, 1], [5, 35], [62, 54], [36, 44], [70, 22], [31, 32], [41, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [22, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [44, 32, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-785, 139, -7]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, 2, -7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-1, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-1, 1, 0]] 
 ![![73, 0, 0], ![72, 1, 0], ![72, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-1, 1, 0], ![0, -1, 1], ![133, 14, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![219, 0, 0]], ![![2, -1, 0], ![74, 0, 0]], ![![2, -1, 0], ![74, 1, 0]]]
  g := ![![![1, 0, 0], ![-72, 73, 0], ![-72, 0, 73]], ![![-1, 1, 0], ![0, -1, 1], ![-11, 14, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-13, 1, 1]] ![![73, 0, 0], ![-1, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-73, 73, 0]], ![![-949, 73, 73], ![146, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-1, 1, 0]]], ![![![-13, 1, 1]], ![![2, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [24, 51, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 38, 65], [18, 40, 14], [0, 1]]
 g := ![![[5, 36, 67], [35, 35, 36], [61, 65, 62], [76, 55, 16], [56, 1], []], ![[49, 32, 11, 65], [65, 8, 30, 22], [2, 18, 62, 64], [46, 37, 16, 42], [24, 20], [37, 38]], ![[54, 40, 39, 29], [8, 76, 67, 29], [20, 12, 5, 77], [75, 43, 65, 53], [77, 22], [9, 38]]]
 h' := ![![[38, 38, 65], [29, 8, 64], [37, 39, 6], [72, 19, 33], [78, 43, 4], [0, 0, 1], [0, 1]], ![[18, 40, 14], [51, 75, 78], [36, 41, 10], [24, 25, 27], [65, 15, 32], [3, 10, 40], [38, 38, 65]], ![[0, 1], [54, 75, 16], [44, 78, 63], [28, 35, 19], [20, 21, 43], [29, 69, 38], [18, 40, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 64], []]
 b := ![[], [20, 1, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [24, 51, 23, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![176249, 46531, 4661]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2231, 589, 59]
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



lemma PB194I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB194I1 : PrimesBelowBoundCertificateInterval O 31 79 194 where
  m := 11
  g := ![2, 2, 1, 3, 3, 3, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB194I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
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
  β := ![I37N1, I41N1, I47N0, I47N1, I47N2, I53N0, I53N1, I53N2, I59N0, I59N1, I59N2, I61N1, I67N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [], [I47N0, I47N1, I47N2], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
