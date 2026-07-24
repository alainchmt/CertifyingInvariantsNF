
import IdealArithmetic.Examples.NF3_1_592379_1.RI3_1_592379_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![5, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![5, 1, 0]] 
 ![![37, 0, 0], ![5, 1, 0], ![12, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![5, 1, 0], ![0, 5, 1], ![86, -49, 6]]]
  hmulB := by decide  
  f := ![![![66, 13, 0], ![-481, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![16, 3, 0], ![-116, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 37, 0], ![-12, 0, 37]], ![![0, 1, 0], ![-1, 5, 1], ![7, -49, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, 1, 0]] 
 ![![37, 0, 0], ![32, 1, 0], ![12, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, 1, 0], ![0, -5, 1], ![86, -49, -4]]]
  hmulB := by decide  
  f := ![![![96, -19, 0], ![703, 0, 0]], ![![76, -15, 0], ![556, 0, 0]], ![![36, -7, 0], ![264, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 37, 0], ![-12, 0, 37]], ![![-1, 1, 0], ![4, -5, 1], ![46, -49, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![1, -1, 0]] 
 ![![37, 0, 0], ![36, 1, 0], ![36, 0, 1]] where
  M :=![![![1, -1, 0], ![0, 1, -1], ![-86, 49, 0]]]
  hmulB := by decide  
  f := ![![![-49, 0, -1]], ![![-50, 0, -1]], ![![-50, -1, -1]]]
  g := ![![![1, -1, 0], ![0, 1, -1], ![-50, 49, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![5, 1, 0]] ![![37, 0, 0], ![-5, 1, 0]]
  ![![-49, 0, -1]] where
 M := ![![![1369, 0, 0], ![-185, 37, 0]], ![![185, 37, 0], ![-25, 0, 1]]]
 hmul := by decide  
 g := ![![![![37, -37, 0]], ![![-5, 6, -1]]], ![![![5, -4, -1]], ![![-3, 2, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-49, 0, -1]] ![![1, -1, 0]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![34, 16, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![34, 16, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![34, 16, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![34, 16, 1], ![86, -15, 17], ![1462, -747, 2]]]
  hmulB := by decide  
  f := ![![![-33, -16, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -16, 41]], ![![0, 0, 1], ![-12, -7, 17], ![34, -19, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [31, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 40], [0, 1]]
 g := ![![[32, 4], [23], [8], [25, 23], [1]], ![[0, 37], [23], [8], [5, 18], [1]]]
 h' := ![![[33, 40], [16, 2], [14, 33], [4, 7], [10, 33], [0, 1]], ![[0, 1], [0, 39], [37, 8], [30, 34], [33, 8], [33, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [22, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [31, 8, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![289, -69, -53]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, 19, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-17, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-17, 1, 0]] 
 ![![41, 0, 0], ![24, 1, 0], ![39, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-17, 1, 0], ![0, -17, 1], ![86, -49, -16]]]
  hmulB := by decide  
  f := ![![![596, -35, 0], ![1435, 0, 0]], ![![358, -21, 0], ![862, 0, 0]], ![![586, -34, 0], ![1411, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 41, 0], ![-39, 0, 41]], ![![-1, 1, 0], ![9, -17, 1], ![46, -49, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![34, 16, 1]] ![![41, 0, 0], ![-17, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-697, 41, 0]], ![![1394, 656, 41], ![-492, -287, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-17, 1, 0]]], ![![![34, 16, 1]], ![![-12, -7, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![0, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![0, 1, 0]] 
 ![![43, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![0, 0, 1], ![86, -49, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 1, 0], ![0, 0, 1], ![2, -49, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![49, -1, 1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![49, -1, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![6, 42, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![49, -1, 1], ![86, 0, 0], ![0, 86, 0]]]
  hmulB := by decide  
  f := ![![![-48, 1, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -42, 43]], ![![1, -1, 1], ![2, 0, 0], ![0, 2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [4, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 42], [0, 1]]
 g := ![![[20, 11], [10, 40], [13], [39, 36], [1]], ![[0, 32], [35, 3], [13], [40, 7], [1]]]
 h' := ![![[6, 42], [3, 21], [32, 30], [16, 20], [39, 6], [0, 1]], ![[0, 1], [0, 22], [40, 13], [7, 23], [32, 37], [6, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [39, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [4, 37, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-290, 851, -335]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 347, -335]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![0, 1, 0]] ![![43, 0, 0], ![49, -1, 1]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![2107, -43, 43]], ![![0, 43, 0], ![86, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![49, -1, 1]]], ![![![0, 1, 0]], ![![2, 0, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [9, 22, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36, 38], [38, 10, 9], [0, 1]]
 g := ![![[46, 2, 24], [24, 38, 32], [20, 30, 34], [25, 0, 1], []], ![[28, 36, 33, 41], [32, 0, 12, 29], [33, 18, 38, 41], [36, 33, 17, 40], [10, 34]], ![[45, 23, 23, 9], [36, 41, 29, 27], [0, 18, 0, 7], [1, 34, 33, 8], [39, 34]]]
 h' := ![![[9, 36, 38], [19, 40, 20], [8, 1, 19], [10, 14, 38], [0, 0, 1], [0, 1]], ![[38, 10, 9], [11, 26, 28], [34, 4, 40], [29, 17, 19], [38, 28, 10], [9, 36, 38]], ![[0, 1], [40, 28, 46], [39, 42, 35], [11, 16, 37], [12, 19, 36], [38, 10, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 17], []]
 b := ![[], [22, 20, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [9, 22, 0, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-258641, -2867, -5217]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5503, -61, -111]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![25, -23, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![25, -23, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![25, 30, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![25, -23, 1], ![86, -24, -22], ![-1892, 1164, -46]]]
  hmulB := by decide  
  f := ![![![-24, 23, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -30, 53]], ![![0, -1, 1], ![12, 12, -22], ![-14, 48, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [21, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 52], [0, 1]]
 g := ![![[42, 13], [7], [42, 37], [7], [19, 1]], ![[24, 40], [7], [3, 16], [7], [38, 52]]]
 h' := ![![[19, 52], [2, 15], [19, 22], [1, 14], [25, 22], [0, 1]], ![[0, 1], [22, 38], [13, 31], [2, 39], [19, 31], [19, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [6, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [21, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![314, 663, -545]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![263, 321, -545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![22, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![22, 1, 0]] 
 ![![53, 0, 0], ![22, 1, 0], ![46, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![22, 1, 0], ![0, 22, 1], ![86, -49, 23]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-901, 0, 0]], ![![154, 7, 0], ![-370, 0, 0]], ![![318, 14, 0], ![-764, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 53, 0], ![-46, 0, 53]], ![![0, 1, 0], ![-10, 22, 1], ![2, -49, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![25, -23, 1]] ![![53, 0, 0], ![22, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1166, 53, 0]], ![![1325, -1219, 53], ![636, -530, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![22, 1, 0]]], ![![![25, -23, 1]], ![![12, -10, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![3, 8, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![3, 8, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![3, 8, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![3, 8, 1], ![86, -46, 9], ![774, -355, -37]]]
  hmulB := by decide  
  f := ![![![-2, -8, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -8, 59]], ![![0, 0, 1], ![1, -2, 9], ![15, -1, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [47, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 58], [0, 1]]
 g := ![![[45, 49], [15, 4], [5], [48, 35], [9, 1]], ![[14, 10], [51, 55], [5], [9, 24], [18, 58]]]
 h' := ![![[9, 58], [3, 52], [20, 57], [45, 8], [49, 34], [0, 1]], ![[0, 1], [58, 7], [2, 2], [58, 51], [1, 25], [9, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [33, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [47, 50, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![305, -111, -95]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 11, -95]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-9, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-9, 1, 0]] 
 ![![59, 0, 0], ![50, 1, 0], ![37, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-9, 1, 0], ![0, -9, 1], ![86, -49, -8]]]
  hmulB := by decide  
  f := ![![![451, -50, 0], ![2950, 0, 0]], ![![388, -43, 0], ![2538, 0, 0]], ![![281, -31, 0], ![1838, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 59, 0], ![-37, 0, 59]], ![![-1, 1, 0], ![7, -9, 1], ![48, -49, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![3, 8, 1]] ![![59, 0, 0], ![-9, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-531, 59, 0]], ![![177, 472, 59], ![59, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-9, 1, 0]]], ![![![3, 8, 1]], ![![1, -2, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![19, 26, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![19, 26, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![19, 26, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![19, 26, 1], ![86, -30, 27], ![2322, -1237, -3]]]
  hmulB := by decide  
  f := ![![![-18, -26, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -26, 61]], ![![0, 0, 1], ![-7, -12, 27], ![39, -19, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [53, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 60], [0, 1]]
 g := ![![[3, 36], [57], [11, 16], [18, 5], [24, 1]], ![[13, 25], [57], [29, 45], [16, 56], [48, 60]]]
 h' := ![![[24, 60], [26, 55], [27, 22], [22, 4], [9, 35], [0, 1]], ![[0, 1], [4, 6], [6, 39], [57, 57], [56, 26], [24, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [49, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [53, 37, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3445, -1084, 390]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65, -184, 390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 1, 0]] 
 ![![61, 0, 0], ![34, 1, 0], ![3, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 1, 0], ![0, -27, 1], ![86, -49, -26]]]
  hmulB := by decide  
  f := ![![![1567, -58, 0], ![3538, 0, 0]], ![![892, -33, 0], ![2014, 0, 0]], ![![93, -3, 0], ![210, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 61, 0], ![-3, 0, 61]], ![![-1, 1, 0], ![15, -27, 1], ![30, -49, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![19, 26, 1]] ![![61, 0, 0], ![-27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1647, 61, 0]], ![![1159, 1586, 61], ![-427, -732, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-27, 1, 0]]], ![![![19, 26, 1]], ![![-7, -12, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![11, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![11, 1, 0]] 
 ![![67, 0, 0], ![11, 1, 0], ![13, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![11, 1, 0], ![0, 11, 1], ![86, -49, 12]]]
  hmulB := by decide  
  f := ![![![474, 43, 0], ![-2881, 0, 0]], ![![66, 6, 0], ![-401, 0, 0]], ![![90, 8, 0], ![-547, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 67, 0], ![-13, 0, 67]], ![![0, 1, 0], ![-2, 11, 1], ![7, -49, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![12, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![12, 1, 0]] 
 ![![67, 0, 0], ![12, 1, 0], ![57, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![12, 1, 0], ![0, 12, 1], ![86, -49, 13]]]
  hmulB := by decide  
  f := ![![![265, 22, 0], ![-1474, 0, 0]], ![![36, 3, 0], ![-200, 0, 0]], ![![243, 20, 0], ![-1352, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 67, 0], ![-57, 0, 67]], ![![0, 1, 0], ![-3, 12, 1], ![-1, -49, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 3, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-5, 3, 0]] 
 ![![67, 0, 0], ![43, 1, 0], ![27, 0, 1]] where
  M :=![![![-5, 3, 0], ![0, -5, 3], ![258, -147, -2]]]
  hmulB := by decide  
  f := ![![![451, 6, 9]], ![![301, 4, 6]], ![![201, 3, 4]]]
  g := ![![![-2, 3, 0], ![2, -5, 3], ![99, -147, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![11, 1, 0]] ![![67, 0, 0], ![12, 1, 0]]
  ![![451, 6, 9]] where
 M := ![![![4489, 0, 0], ![804, 67, 0]], ![![737, 67, 0], ![132, 23, 1]]]
 hmul := by decide  
 g := ![![![![-335, 201, 0]], ![![-60, 31, 3]]], ![![![-55, 28, 3]], ![![-6, 2, 1]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![451, 6, 9]] ![![-5, 3, 0]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [25, 47, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 15, 12], [14, 55, 59], [0, 1]]
 g := ![![[62, 26, 20], [43, 70, 24], [51, 5, 18], [63, 29], [26, 1], []], ![[28, 20, 40, 24], [25, 61, 6, 57], [17, 11, 29, 18], [27, 18], [33, 43], [57, 2]], ![[23, 12, 3, 26], [31, 49, 50, 39], [32, 60, 7, 7], [19, 57], [27, 12], [10, 2]]]
 h' := ![![[12, 15, 12], [61, 1, 37], [3, 54, 33], [37, 34, 36], [60, 31, 61], [0, 0, 1], [0, 1]], ![[14, 55, 59], [33, 47, 59], [55, 23, 49], [53, 0, 45], [36, 15, 35], [68, 45, 55], [12, 15, 12]], ![[0, 1], [65, 23, 46], [42, 65, 60], [60, 37, 61], [40, 25, 46], [17, 26, 15], [14, 55, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 24], []]
 b := ![[], [42, 34, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [25, 47, 45, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54244, 36991, -3053]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-764, 521, -43]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [3, 6, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 7, 72], [27, 65, 1], [0, 1]]
 g := ![![[49, 61, 48], [66, 3], [47, 8], [18, 41, 23], [26, 1], []], ![[14, 21, 48, 35], [19, 35], [49, 50], [12, 69, 16, 41], [22, 64], [12, 1]], ![[69, 11, 65, 67], [63, 2], [10, 18], [4, 21, 66, 25], [38, 49], [10, 1]]]
 h' := ![![[72, 7, 72], [22, 44, 62], [1, 42, 52], [19, 13, 64], [68, 60, 13], [0, 0, 1], [0, 1]], ![[27, 65, 1], [71, 46, 44], [37, 46, 53], [29, 16, 59], [64, 66, 55], [38, 57, 65], [72, 7, 72]], ![[0, 1], [18, 56, 40], [34, 58, 41], [65, 44, 23], [44, 20, 5], [42, 16, 7], [27, 65, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 42], []]
 b := ![[], [42, 26, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [3, 6, 47, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24163, -1533, 10220]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-331, -21, 140]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![6, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![6, 1, 0]] 
 ![![79, 0, 0], ![6, 1, 0], ![43, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![6, 1, 0], ![0, 6, 1], ![86, -49, 7]]]
  hmulB := by decide  
  f := ![![![337, 56, 0], ![-4424, 0, 0]], ![![18, 3, 0], ![-236, 0, 0]], ![![181, 30, 0], ![-2376, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 79, 0], ![-43, 0, 79]], ![![0, 1, 0], ![-1, 6, 1], ![1, -49, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-4, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-4, 1, 0]] 
 ![![79, 0, 0], ![75, 1, 0], ![63, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-4, 1, 0], ![0, -4, 1], ![86, -49, -3]]]
  hmulB := by decide  
  f := ![![![89, -22, 0], ![1738, 0, 0]], ![![85, -21, 0], ![1660, 0, 0]], ![![73, -18, 0], ![1426, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 79, 0], ![-63, 0, 79]], ![![-1, 1, 0], ![3, -4, 1], ![50, -49, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![79, 0, 0], ![76, 1, 0], ![70, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 1], ![86, -49, -2]]]
  hmulB := by decide  
  f := ![![![-55, -2, -1]], ![![-54, -2, -1]], ![![-52, -1, -1]]]
  g := ![![![-1, 1, 0], ![2, -3, 1], ![50, -49, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![6, 1, 0]] ![![79, 0, 0], ![-4, 1, 0]]
  ![![55, 2, 1]] where
 M := ![![![6241, 0, 0], ![-316, 79, 0]], ![![474, 79, 0], ![-24, 2, 1]]]
 hmul := by decide  
 g := ![![![![237, -79, 0]], ![![-12, 7, -1]]], ![![![18, -3, -1]], ![![-2, 1, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![55, 2, 1]] ![![-3, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB218I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB218I1 : PrimesBelowBoundCertificateInterval O 31 79 218 where
  m := 11
  g := ![3, 2, 2, 1, 2, 2, 2, 3, 1, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB218I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![1681, 41]
    · exact ![43, 1849]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![389017]
    · exact ![79, 79, 79]
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
      exact NI41N1
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
      exact NI79N2
  β := ![I37N0, I37N1, I37N2, I41N1, I43N0, I53N1, I59N1, I61N1, I67N0, I67N1, I67N2, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N0], [], [I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N2], [], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
