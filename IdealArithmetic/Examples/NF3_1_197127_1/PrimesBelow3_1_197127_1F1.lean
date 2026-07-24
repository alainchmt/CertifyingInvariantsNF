
import IdealArithmetic.Examples.NF3_1_197127_1.RI3_1_197127_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![0, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![0, 1, 0]] 
 ![![37, 0, 0], ![0, 1, 0], ![12, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![0, 1, 0], ![-1, -1, 3], ![86, 7, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 3], ![0, -37, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![-12, -12, 0]]]
  g := ![![![1, 0, 0], ![0, 37, 0], ![-12, 0, 37]], ![![0, 1, 0], ![-1, -1, 3], ![2, 7, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 1, 0]] 
 ![![37, 0, 0], ![13, 1, 0], ![34, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 1, 0], ![-1, 12, 3], ![86, 7, 14]]]
  hmulB := by decide  
  f := ![![![-439, 5280, 1320], ![0, -16280, 0]], ![![-154, 1848, 462], ![1, -5698, 0]], ![![-402, 4852, 1213], ![-4, -14960, 0]]]
  g := ![![![1, 0, 0], ![-13, 37, 0], ![-34, 0, 37]], ![![0, 1, 0], ![-7, 12, 3], ![-13, 7, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-13, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-13, 1, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![13, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-13, 1, 0], ![-1, -14, 3], ![86, 7, -12]]]
  hmulB := by decide  
  f := ![![![-424, -5950, 1275], ![0, -15725, 0]], ![![-274, -3850, 825], ![1, -10175, 0]], ![![-143, -2091, 448], ![17, -5525, 0]]]
  g := ![![![1, 0, 0], ![-24, 37, 0], ![-13, 0, 37]], ![![-1, 1, 0], ![8, -14, 3], ![2, 7, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![0, 1, 0]] ![![37, 0, 0], ![13, 1, 0]]
  ![![37, 0, 0], ![12, 4, 1]] where
 M := ![![![1369, 0, 0], ![481, 37, 0]], ![![0, 37, 0], ![-1, 12, 3]]]
 hmul := by decide  
 g := ![![![![25, -4, -1], ![37, 0, 0]], ![![1, -3, -1], ![37, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![12, 4, 1]] ![![37, 0, 0], ![-13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-481, 37, 0]], ![![444, 148, 37], ![-74, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-13, 1, 0]]], ![![![12, 4, 1]], ![![-2, -1, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [32, 12, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 14, 10], [0, 26, 31], [0, 1]]
 g := ![![[9, 11, 25], [13, 39], [1, 40], [30, 40, 1], []], ![[0, 12, 26, 40], [20, 16], [2, 21], [39, 12, 14, 36], [16, 18]], ![[0, 13, 36, 2], [7, 20], [7, 9], [34, 14, 0, 8], [36, 18]]]
 h' := ![![[40, 14, 10], [33, 20, 5], [11, 20, 30], [24, 0, 32], [0, 0, 1], [0, 1]], ![[0, 26, 31], [0, 31, 2], [36, 16, 37], [31, 30, 12], [22, 24, 26], [40, 14, 10]], ![[0, 1], [13, 31, 34], [14, 5, 15], [19, 11, 38], [37, 17, 14], [0, 26, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 25], []]
 b := ![[], [0, 6, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [32, 12, 1, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81836, -11439, -3813]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1996, -279, -93]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -5, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![15, -5, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![15, 38, 1]] where
  M :=![![![15, -5, 1], ![91, 27, -14], ![-375, -4, 18]]]
  hmulB := by decide  
  f := ![![![-10, -2, -1]], ![![-84, -15, -7]], ![![-83, -15, -7]]]
  g := ![![![0, -1, 1], ![7, 13, -14], ![-15, -16, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [29, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 42], [0, 1]]
 g := ![![[42, 31], [1, 25], [31], [3, 24], [1]], ![[38, 12], [38, 18], [31], [11, 19], [1]]]
 h' := ![![[29, 42], [14, 17], [5, 5], [42, 17], [14, 29], [0, 1]], ![[0, 1], [34, 26], [21, 38], [19, 26], [38, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [31, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [29, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3389, 1359, 571]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-278, -473, 571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 2, 1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![10, 2, 1]] 
 ![![43, 0, 0], ![14, 1, 0], ![25, 0, 1]] where
  M :=![![![10, 2, 1], ![84, 15, 7], ![227, 45, 20]]]
  hmulB := by decide  
  f := ![![![-15, 5, -1]], ![![-7, 1, 0]], ![![0, 3, -1]]]
  g := ![![![-1, 2, 1], ![-7, 15, 7], ![-21, 45, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![15, -5, 1]] ![![10, 2, 1]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![4, -19, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![4, -19, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![4, 28, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![4, -19, 1], ![105, 30, -56], ![-1579, -102, -7]]]
  hmulB := by decide  
  f := ![![![-3, 19, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -28, 47]], ![![0, -1, 1], ![7, 34, -56], ![-33, 2, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [32, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 46], [0, 1]]
 g := ![![[19, 25], [46, 16], [18, 36], [23, 9], [1]], ![[0, 22], [0, 31], [32, 11], [3, 38], [1]]]
 h' := ![![[3, 46], [32, 5], [35, 4], [16, 6], [15, 3], [0, 1]], ![[0, 1], [0, 42], [0, 43], [34, 41], [24, 44], [3, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [45, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [32, 44, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![223920, 137371, 32574]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1992, -16483, 32574]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![9, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![9, 1, 0]] 
 ![![47, 0, 0], ![9, 1, 0], ![7, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![9, 1, 0], ![-1, 8, 3], ![86, 7, 10]]]
  hmulB := by decide  
  f := ![![![-272, 2184, 819], ![0, -12831, 0]], ![![-52, 416, 156], ![1, -2444, 0]], ![![-43, 325, 122], ![13, -1911, 0]]]
  g := ![![![1, 0, 0], ![-9, 47, 0], ![-7, 0, 47]], ![![0, 1, 0], ![-2, 8, 3], ![-1, 7, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![4, -19, 1]] ![![47, 0, 0], ![9, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![423, 47, 0]], ![![188, -893, 47], ![141, -141, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![9, 1, 0]]], ![![![4, -19, 1]], ![![3, -3, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![7, 6, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![7, 6, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![7, 6, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![7, 6, 1], ![80, 8, 19], ![571, 73, 21]]]
  hmulB := by decide  
  f := ![![![-6, -6, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -6, 53]], ![![0, 0, 1], ![-1, -2, 19], ![8, -1, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [13, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 52], [0, 1]]
 g := ![![[18, 49], [7], [23, 44], [36], [31, 1]], ![[0, 4], [7], [9, 9], [36], [9, 52]]]
 h' := ![![[31, 52], [5, 46], [19, 22], [26, 16], [21, 47], [0, 1]], ![[0, 1], [0, 7], [12, 31], [45, 37], [47, 6], [31, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [37, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [13, 22, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1912, 1632, 272]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72, 0, 272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-19, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-19, 1, 0]] 
 ![![53, 0, 0], ![34, 1, 0], ![32, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-19, 1, 0], ![-1, -20, 3], ![86, 7, -18]]]
  hmulB := by decide  
  f := ![![![-545, -10920, 1638], ![0, -28938, 0]], ![![-349, -7000, 1050], ![1, -18550, 0]], ![![-314, -6594, 989], ![42, -17472, 0]]]
  g := ![![![1, 0, 0], ![-34, 53, 0], ![-32, 0, 53]], ![![-1, 1, 0], ![11, -20, 3], ![8, 7, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![7, 6, 1]] ![![53, 0, 0], ![-19, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1007, 53, 0]], ![![371, 318, 53], ![-53, -106, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-19, 1, 0]]], ![![![7, 6, 1]], ![![-1, -2, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![13, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![13, 1, 0]] 
 ![![59, 0, 0], ![13, 1, 0], ![46, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![13, 1, 0], ![-1, 12, 3], ![86, 7, 14]]]
  hmulB := by decide  
  f := ![![![1938, -23401, -5850], ![59, 115050, 0]], ![![416, -5149, -1287], ![60, 25311, 0]], ![![1509, -18245, -4561], ![55, 89700, 0]]]
  g := ![![![1, 0, 0], ![-13, 59, 0], ![-46, 0, 59]], ![![0, 1, 0], ![-5, 12, 3], ![-11, 7, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-10, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-10, 1, 0]] 
 ![![59, 0, 0], ![49, 1, 0], ![22, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-10, 1, 0], ![-1, -11, 3], ![86, 7, -9]]]
  hmulB := by decide  
  f := ![![![-2755, -30316, 8268], ![0, -162604, 0]], ![![-2287, -25168, 6864], ![1, -134992, 0]], ![![-1030, -11304, 3083], ![-16, -60632, 0]]]
  g := ![![![1, 0, 0], ![-49, 59, 0], ![-22, 0, 59]], ![![-1, 1, 0], ![8, -11, 3], ![-1, 7, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-3, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-3, 1, 0]] 
 ![![59, 0, 0], ![56, 1, 0], ![35, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-3, 1, 0], ![-1, -4, 3], ![86, 7, -2]]]
  hmulB := by decide  
  f := ![![![-1052, -4212, 3159], ![0, -62127, 0]], ![![-998, -3996, 2997], ![1, -58941, 0]], ![![-623, -2499, 1874], ![21, -36855, 0]]]
  g := ![![![1, 0, 0], ![-56, 59, 0], ![-35, 0, 59]], ![![-1, 1, 0], ![2, -4, 3], ![-4, 7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![13, 1, 0]] ![![59, 0, 0], ![-10, 1, 0]]
  ![![59, 0, 0], ![-24, -19, 1]] where
 M := ![![![3481, 0, 0], ![-590, 59, 0]], ![![767, 59, 0], ![-131, 2, 3]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![14, 20, -1], ![59, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-24, -19, 1]] ![![59, 0, 0], ![-3, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-177, 59, 0]], ![![-1416, -1121, 59], ![177, 59, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-3, 1, 0]]], ![![![-24, -19, 1]], ![![3, 1, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [47, 9, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 55, 19], [12, 5, 42], [0, 1]]
 g := ![![[31, 38, 4], [28, 20], [28, 47, 4], [41, 51, 56], [1]], ![[21, 10, 1, 56], [37, 3], [37, 44, 6, 22], [3, 4, 31, 5], [32, 46, 54, 27]], ![[60, 9, 54, 16], [40, 1], [29, 11, 7, 34], [37, 54, 45, 1], [27, 32, 22, 34]]]
 h' := ![![[7, 55, 19], [31, 21, 2], [26, 55, 9], [25, 53, 59], [14, 52, 19], [0, 1]], ![[12, 5, 42], [16, 12, 43], [48, 47, 53], [9, 32, 21], [59, 23, 46], [7, 55, 19]], ![[0, 1], [33, 28, 16], [49, 20, 60], [57, 37, 42], [32, 47, 57], [12, 5, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 49], []]
 b := ![[], [19, 14, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [47, 9, 42, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61488, 0, -1098]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1008, 0, -18]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![8, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![8, 1, 0]] 
 ![![67, 0, 0], ![8, 1, 0], ![48, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![8, 1, 0], ![-1, 7, 3], ![86, 7, 9]]]
  hmulB := by decide  
  f := ![![![-1091, 7644, 3276], ![0, -73164, 0]], ![![-130, 910, 390], ![1, -8710, 0]], ![![-784, 5476, 2347], ![20, -52416, 0]]]
  g := ![![![1, 0, 0], ![-8, 67, 0], ![-48, 0, 67]], ![![0, 1, 0], ![-3, 7, 3], ![-6, 7, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![20, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![20, 1, 0]] 
 ![![67, 0, 0], ![20, 1, 0], ![7, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![20, 1, 0], ![-1, 19, 3], ![86, 7, 21]]]
  hmulB := by decide  
  f := ![![![2945, -56317, -8892], ![67, 198588, 0]], ![![864, -16797, -2652], ![68, 59228, 0]], ![![305, -5884, -929], ![16, 20748, 0]]]
  g := ![![![1, 0, 0], ![-20, 67, 0], ![-7, 0, 67]], ![![0, 1, 0], ![-6, 19, 3], ![-3, 7, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 1, 0]] 
 ![![67, 0, 0], ![39, 1, 0], ![64, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 1, 0], ![-1, -29, 3], ![86, 7, -27]]]
  hmulB := by decide  
  f := ![![![-2694, -78155, 8085], ![0, -180565, 0]], ![![-1567, -45472, 4704], ![1, -105056, 0]], ![![-2560, -74656, 7723], ![32, -172480, 0]]]
  g := ![![![1, 0, 0], ![-39, 67, 0], ![-64, 0, 67]], ![![-1, 1, 0], ![14, -29, 3], ![23, 7, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![8, 1, 0]] ![![67, 0, 0], ![20, 1, 0]]
  ![![67, 0, 0], ![-14, 9, 1]] where
 M := ![![![4489, 0, 0], ![1340, 67, 0]], ![![536, 67, 0], ![159, 27, 3]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![20, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-14, 9, 1]] ![![67, 0, 0], ![-28, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1876, 67, 0]], ![![-938, 603, 67], ![469, -268, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-28, 1, 0]]], ![![![-14, 9, 1]], ![![7, -4, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [40, 65, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 38, 31], [22, 32, 40], [0, 1]]
 g := ![![[8, 37, 64], [34, 65, 57], [29, 44, 19], [40, 50], [57, 1], []], ![[56, 63, 47, 33], [47, 55, 50, 70], [46, 53, 35, 53], [59, 49], [50, 30], [49, 38]], ![[42, 69, 4, 60], [27, 1, 54, 32], [34, 31, 36, 8], [18, 40], [20, 24], [40, 38]]]
 h' := ![![[35, 38, 31], [60, 26, 63], [47, 13, 25], [26, 11, 27], [63, 18, 60], [0, 0, 1], [0, 1]], ![[22, 32, 40], [34, 24, 53], [19, 63, 67], [20, 15, 69], [45, 33, 64], [46, 14, 32], [35, 38, 31]], ![[0, 1], [46, 21, 26], [52, 66, 50], [27, 45, 46], [26, 20, 18], [20, 57, 38], [22, 32, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 32], []]
 b := ![[], [33, 9, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [40, 65, 14, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2726400, 569420, 196244]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38400, 8020, 2764]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [52, 4, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 56, 66], [47, 16, 7], [0, 1]]
 g := ![![[2, 23, 6], [46, 54], [0, 8], [27, 59, 67], [16, 1], []], ![[55, 38, 49, 52], [22, 3], [29, 8], [49, 46, 5, 13], [15, 37], [0, 49]], ![[23, 46, 25, 20], [71, 65], [], [21, 3, 68, 58], [37, 70], [59, 49]]]
 h' := ![![[42, 56, 66], [26, 0, 58], [70, 61, 28], [56, 1, 9], [44, 30, 33], [0, 0, 1], [0, 1]], ![[47, 16, 7], [65, 72, 52], [48, 55, 21], [60, 42, 64], [21, 47, 26], [12, 39, 16], [42, 56, 66]], ![[0, 1], [63, 1, 36], [55, 30, 24], [37, 30], [44, 69, 14], [17, 34, 56], [47, 16, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 45], []]
 b := ![[], [6, 2, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [52, 4, 57, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-184398, -13724, 13724]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2526, -188, 188]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![18, -16, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![18, -16, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![18, 63, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![18, -16, 1], ![102, 41, -47], ![-1321, -81, 10]]]
  hmulB := by decide  
  f := ![![![-17, 16, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -63, 79]], ![![0, -1, 1], ![12, 38, -47], ![-19, -9, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [24, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 78], [0, 1]]
 g := ![![[70, 18], [14, 72], [51, 36], [53, 26], [46], [1]], ![[8, 61], [3, 7], [6, 43], [60, 53], [46], [1]]]
 h' := ![![[58, 78], [59, 52], [40, 25], [71, 73], [25, 42], [55, 58], [0, 1]], ![[0, 1], [73, 27], [68, 54], [39, 6], [12, 37], [22, 21], [58, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [2, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [24, 21, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![933, 1014, 381]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75, -291, 381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-32, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-32, 1, 0]] 
 ![![79, 0, 0], ![47, 1, 0], ![69, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-32, 1, 0], ![-1, -33, 3], ![86, 7, -31]]]
  hmulB := by decide  
  f := ![![![-739, -24420, 2220], ![0, -58460, 0]], ![![-439, -14520, 1320], ![1, -34760, 0]], ![![-641, -21329, 1939], ![11, -51060, 0]]]
  g := ![![![1, 0, 0], ![-47, 79, 0], ![-69, 0, 79]], ![![-1, 1, 0], ![17, -33, 3], ![24, 7, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![18, -16, 1]] ![![79, 0, 0], ![-32, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2528, 79, 0]], ![![1422, -1264, 79], ![-474, 553, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-32, 1, 0]]], ![![![18, -16, 1]], ![![-6, 7, -1]]]]
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


lemma PB126I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB126I1 : PrimesBelowBoundCertificateInterval O 31 79 126 where
  m := 11
  g := ![3, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB126I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
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
      exact NI37N2
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
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
  β := ![I37N0, I37N1, I37N2, I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I67N0, I67N1, I67N2, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [], [I67N0, I67N1, I67N2], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
