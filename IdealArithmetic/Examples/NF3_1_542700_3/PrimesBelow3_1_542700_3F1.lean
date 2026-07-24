
import IdealArithmetic.Examples.NF3_1_542700_3.RI3_1_542700_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![5, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![5, 1, 0]] 
 ![![37, 0, 0], ![5, 1, 0], ![32, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![5, 1, 0], ![0, 5, 5], ![10, -30, 5]]]
  hmulB := by decide  
  f := ![![![66, 13, 0], ![-481, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![56, 9, -2], ![-408, 15, 0]]]
  g := ![![![1, 0, 0], ![-5, 37, 0], ![-32, 0, 37]], ![![0, 1, 0], ![-5, 5, 5], ![0, -30, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![7, 1, 0]] 
 ![![37, 0, 0], ![7, 1, 0], ![5, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![7, 1, 0], ![0, 7, 5], ![10, -30, 7]]]
  hmulB := by decide  
  f := ![![![85, 12, 0], ![-444, 0, 0]], ![![7, 1, 0], ![-36, 0, 0]], ![![-1, -3, -2], ![6, 15, 0]]]
  g := ![![![1, 0, 0], ![-7, 37, 0], ![-5, 0, 37]], ![![0, 1, 0], ![-2, 7, 5], ![5, -30, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, 1, 0]] 
 ![![37, 0, 0], ![25, 1, 0], ![23, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, 1, 0], ![0, -12, 5], ![10, -30, -12]]]
  hmulB := by decide  
  f := ![![![433, -36, 0], ![1332, 0, 0]], ![![301, -25, 0], ![926, 0, 0]], ![![275, -18, -2], ![846, 15, 0]]]
  g := ![![![1, 0, 0], ![-25, 37, 0], ![-23, 0, 37]], ![![-1, 1, 0], ![5, -12, 5], ![28, -30, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![5, 1, 0]] ![![37, 0, 0], ![7, 1, 0]]
  ![![37, 0, 0], ![7, -5, 1]] where
 M := ![![![1369, 0, 0], ![259, 37, 0]], ![![185, 37, 0], ![35, 12, 5]]]
 hmul := by decide  
 g := ![![![![30, 5, -1], ![37, 0, 0]], ![![0, 6, -1], ![37, 0, 0]]], ![![![-2, 6, -1], ![37, 0, 0]], ![![0, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![7, -5, 1]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-444, 37, 0]], ![![259, -185, 37], ![-74, 37, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-12, 1, 0]]], ![![![7, -5, 1]], ![![-2, 1, -1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![29, -7, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![29, -7, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![29, 34, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![29, -7, 1], ![10, -1, -35], ![-70, 212, -1]]]
  hmulB := by decide  
  f := ![![![-28, 7, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -34, 41]], ![![0, -1, 1], ![25, 29, -35], ![-1, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [33, 17, 1] where
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
 g := ![![[3, 5], [2], [8], [22, 2], [1]], ![[0, 36], [2], [8], [29, 39], [1]]]
 h' := ![![[24, 40], [25, 28], [3, 24], [12, 34], [8, 24], [0, 1]], ![[0, 1], [0, 13], [5, 17], [8, 7], [10, 17], [24, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [20, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [33, 17, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53, -75, -42]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, 33, -42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-6, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-6, 1, 0]] 
 ![![41, 0, 0], ![35, 1, 0], ![1, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-6, 1, 0], ![0, -6, 5], ![10, -30, -6]]]
  hmulB := by decide  
  f := ![![![55, -9, 0], ![369, 0, 0]], ![![49, -8, 0], ![329, 0, 0]], ![![11, 3, -4], ![75, 33, 0]]]
  g := ![![![1, 0, 0], ![-35, 41, 0], ![-1, 0, 41]], ![![-1, 1, 0], ![5, -6, 5], ![26, -30, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![29, -7, 1]] ![![41, 0, 0], ![-6, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-246, 41, 0]], ![![1189, -287, 41], ![-164, 41, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-6, 1, 0]]], ![![![29, -7, 1]], ![![-4, 1, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![5, 9, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![5, 9, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![5, 9, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![5, 9, 1], ![10, -25, 45], ![90, -268, -25]]]
  hmulB := by decide  
  f := ![![![-4, -9, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -9, 43]], ![![0, 0, 1], ![-5, -10, 45], ![5, -1, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [14, 17, 1] where
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
 g := ![![[35, 40], [18, 17], [41], [35, 31], [1]], ![[0, 3], [30, 26], [41], [24, 12], [1]]]
 h' := ![![[26, 42], [6, 13], [16, 19], [26, 27], [29, 26], [0, 1]], ![[0, 1], [0, 30], [37, 24], [40, 16], [17, 17], [26, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [11, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [14, 17, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122, 348, -205]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21, 51, -205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-2, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-2, 1, 0]] 
 ![![43, 0, 0], ![41, 1, 0], ![25, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-2, 1, 0], ![0, -2, 5], ![10, -30, -2]]]
  hmulB := by decide  
  f := ![![![49, -24, 0], ![1032, 0, 0]], ![![47, -23, 0], ![990, 0, 0]], ![![31, -14, -3], ![654, 26, 0]]]
  g := ![![![1, 0, 0], ![-41, 43, 0], ![-25, 0, 43]], ![![-1, 1, 0], ![-1, -2, 5], ![30, -30, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![5, 9, 1]] ![![43, 0, 0], ![-2, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-86, 43, 0]], ![![215, 387, 43], ![0, -43, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-2, 1, 0]]], ![![![5, 9, 1]], ![![0, -1, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-21, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-21, 1, 0]] 
 ![![47, 0, 0], ![26, 1, 0], ![34, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-21, 1, 0], ![0, -21, 5], ![10, -30, -21]]]
  hmulB := by decide  
  f := ![![![316, -15, 0], ![705, 0, 0]], ![![190, -9, 0], ![424, 0, 0]], ![![242, -3, -2], ![540, 19, 0]]]
  g := ![![![1, 0, 0], ![-26, 47, 0], ![-34, 0, 47]], ![![-1, 1, 0], ![8, -21, 5], ![32, -30, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-14, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-14, 1, 0]] 
 ![![47, 0, 0], ![33, 1, 0], ![36, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-14, 1, 0], ![0, -14, 5], ![10, -30, -14]]]
  hmulB := by decide  
  f := ![![![603, -43, 0], ![2021, 0, 0]], ![![421, -30, 0], ![1411, 0, 0]], ![![444, -26, -2], ![1488, 19, 0]]]
  g := ![![![1, 0, 0], ![-33, 47, 0], ![-36, 0, 47]], ![![-1, 1, 0], ![6, -14, 5], ![32, -30, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-12, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-12, 1, 0]] 
 ![![47, 0, 0], ![35, 1, 0], ![37, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-12, 1, 0], ![0, -12, 5], ![10, -30, -12]]]
  hmulB := by decide  
  f := ![![![73, -6, 0], ![282, 0, 0]], ![![61, -5, 0], ![236, 0, 0]], ![![59, 0, -2], ![228, 19, 0]]]
  g := ![![![1, 0, 0], ![-35, 47, 0], ![-37, 0, 47]], ![![-1, 1, 0], ![5, -12, 5], ![32, -30, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-21, 1, 0]] ![![47, 0, 0], ![-14, 1, 0]]
  ![![47, 0, 0], ![40, -7, 1]] where
 M := ![![![2209, 0, 0], ![-658, 47, 0]], ![![-987, 47, 0], ![294, -35, 5]]]
 hmul := by decide  
 g := ![![![![7, 7, -1], ![47, 0, 0]], ![![-14, 1, 0], ![0, 0, 0]]], ![![![-21, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![40, -7, 1]] ![![47, 0, 0], ![-12, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-564, 47, 0]], ![![1880, -329, 47], ![-470, 94, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-12, 1, 0]]], ![![![40, -7, 1]], ![![-10, 2, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![16, 20, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![16, 20, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![16, 20, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![16, 20, 1], ![10, -14, 100], ![200, -598, -14]]]
  hmulB := by decide  
  f := ![![![-15, -20, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -20, 53]], ![![0, 0, 1], ![-30, -38, 100], ![8, -6, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [1, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 52], [0, 1]]
 g := ![![[23, 1], [17], [26, 42], [4], [30, 1]], ![[0, 52], [17], [14, 11], [4], [7, 52]]]
 h' := ![![[30, 52], [23, 1], [27, 21], [48, 28], [23, 51], [0, 1]], ![[0, 1], [0, 52], [21, 32], [40, 25], [16, 2], [30, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [47, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [1, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2605, -43, 80]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, -31, 80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![6, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![6, 1, 0]] 
 ![![53, 0, 0], ![6, 1, 0], ![14, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![6, 1, 0], ![0, 6, 5], ![10, -30, 6]]]
  hmulB := by decide  
  f := ![![![43, 7, 0], ![-371, 0, 0]], ![![-6, -1, 0], ![54, 0, 0]], ![![10, -2, -3], ![-86, 32, 0]]]
  g := ![![![1, 0, 0], ![-6, 53, 0], ![-14, 0, 53]], ![![0, 1, 0], ![-2, 6, 5], ![2, -30, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![16, 20, 1]] ![![53, 0, 0], ![6, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![318, 53, 0]], ![![848, 1060, 53], ![106, 106, 106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![6, 1, 0]]], ![![![16, 20, 1]], ![![2, 2, 2]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [7, 30, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 33, 46], [56, 25, 13], [0, 1]]
 g := ![![[24, 31, 53], [27, 9, 57], [46, 28], [52, 33, 36], [1]], ![[11, 45, 16, 7], [57, 2, 8, 4], [53, 20], [34, 45, 0, 9], [41, 31, 9, 45]], ![[33, 55, 6, 32], [16, 30, 30, 18], [49, 25], [48, 10, 31, 34], [57, 45, 15, 14]]]
 h' := ![![[9, 33, 46], [47, 31, 42], [14, 47, 36], [49, 28, 21], [52, 29, 6], [0, 1]], ![[56, 25, 13], [49, 31, 57], [31, 18, 53], [15, 15, 43], [29, 23, 9], [9, 33, 46]], ![[0, 1], [49, 56, 19], [5, 53, 29], [42, 16, 54], [46, 7, 44], [56, 25, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 44], []]
 b := ![[], [35, 33, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [7, 30, 53, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11859, 38527, -37937]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-201, 653, -643]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![44, 25, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![44, 25, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![44, 25, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![44, 25, 1], ![10, 14, 125], ![250, -748, 14]]]
  hmulB := by decide  
  f := ![![![-43, -25, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -25, 61]], ![![0, 0, 1], ![-90, -51, 125], ![-6, -18, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [11, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 60], [0, 1]]
 g := ![![[54, 27], [58], [29, 46], [30, 1], [16, 1]], ![[59, 34], [58], [33, 15], [46, 60], [32, 60]]]
 h' := ![![[16, 60], [46, 37], [47, 34], [36, 30], [7, 1], [0, 1]], ![[0, 1], [28, 24], [42, 27], [28, 31], [23, 60], [16, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [30, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [11, 45, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31, -103, -70]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, 27, -70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-3, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-3, 1, 0]] 
 ![![61, 0, 0], ![58, 1, 0], ![47, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-3, 1, 0], ![0, -3, 5], ![10, -30, -3]]]
  hmulB := by decide  
  f := ![![![130, -43, 0], ![2623, 0, 0]], ![![124, -41, 0], ![2502, 0, 0]], ![![104, -32, -4], ![2099, 49, 0]]]
  g := ![![![1, 0, 0], ![-58, 61, 0], ![-47, 0, 61]], ![![-1, 1, 0], ![-1, -3, 5], ![31, -30, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![44, 25, 1]] ![![61, 0, 0], ![-3, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-183, 61, 0]], ![![2684, 1525, 61], ![-122, -61, 122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-3, 1, 0]]], ![![![44, 25, 1]], ![![-2, -1, 2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![1, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![1, 1, 0]] 
 ![![67, 0, 0], ![1, 1, 0], ![40, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![1, 1, 0], ![0, 1, 5], ![10, -30, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![67, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -2], ![40, 27, 0]]]
  g := ![![![1, 0, 0], ![-1, 67, 0], ![-40, 0, 67]], ![![0, 1, 0], ![-3, 1, 5], ![0, -30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![33, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![33, 1, 0]] 
 ![![67, 0, 0], ![33, 1, 0], ![10, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![33, 1, 0], ![0, 33, 5], ![10, -30, 33]]]
  hmulB := by decide  
  f := ![![![496, 15, 0], ![-1005, 0, 0]], ![![198, 6, 0], ![-401, 0, 0]], ![![10, -13, -2], ![-20, 27, 0]]]
  g := ![![![1, 0, 0], ![-33, 67, 0], ![-10, 0, 67]], ![![0, 1, 0], ![-17, 33, 5], ![10, -30, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![1, 1, 0]] ![![67, 0, 0], ![33, 1, 0]]
  ![![67, 0, 0], ![20, -20, 1]] where
 M := ![![![4489, 0, 0], ![2211, 67, 0]], ![![67, 67, 0], ![33, 34, 5]]]
 hmul := by decide  
 g := ![![![![47, 20, -1], ![67, 0, 0]], ![![13, 21, -1], ![67, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![-1, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![20, -20, 1]] ![![67, 0, 0], ![33, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2211, 67, 0]], ![![1340, -1340, 67], ![670, -670, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![33, 1, 0]]], ![![![20, -20, 1]], ![![10, -10, -1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [47, 48, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 6, 53], [29, 64, 18], [0, 1]]
 g := ![![[26, 65, 2], [50, 48, 6], [3, 0, 32], [41, 36], [14, 1], []], ![[26, 45, 22, 63], [62, 14, 61, 59], [67, 18, 61, 28], [25, 58], [53, 49], [60, 40]], ![[26, 65, 68, 48], [41, 17, 56, 48], [41, 26, 50, 38], [53, 43], [2, 36], [24, 40]]]
 h' := ![![[56, 6, 53], [64, 31, 59], [1, 14, 19], [67, 19, 48], [52, 62, 6], [0, 0, 1], [0, 1]], ![[29, 64, 18], [67, 39, 23], [44, 15, 41], [40, 63, 32], [24, 55, 49], [32, 30, 64], [56, 6, 53]], ![[0, 1], [5, 1, 60], [66, 42, 11], [48, 60, 62], [57, 25, 16], [68, 41, 6], [29, 64, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 3], []]
 b := ![[], [41, 64, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [47, 48, 57, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![348823, -1031985, -54315]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4913, -14535, -765]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-29, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-29, 1, 0]] 
 ![![73, 0, 0], ![44, 1, 0], ![7, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-29, 1, 0], ![0, -29, 5], ![10, -30, -29]]]
  hmulB := by decide  
  f := ![![![2089, -72, 0], ![5256, 0, 0]], ![![1248, -43, 0], ![3140, 0, 0]], ![![217, 10, -3], ![546, 44, 0]]]
  g := ![![![1, 0, 0], ![-44, 73, 0], ![-7, 0, 73]], ![![-1, 1, 0], ![17, -29, 5], ![21, -30, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-24, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-24, 1, 0]] 
 ![![73, 0, 0], ![49, 1, 0], ![60, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-24, 1, 0], ![0, -24, 5], ![10, -30, -24]]]
  hmulB := by decide  
  f := ![![![1729, -72, 0], ![5256, 0, 0]], ![![1177, -49, 0], ![3578, 0, 0]], ![![1452, -46, -3], ![4414, 44, 0]]]
  g := ![![![1, 0, 0], ![-49, 73, 0], ![-60, 0, 73]], ![![-1, 1, 0], ![12, -24, 5], ![40, -30, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-20, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-20, 1, 0]] 
 ![![73, 0, 0], ![53, 1, 0], ![66, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-20, 1, 0], ![0, -20, 5], ![10, -30, -20]]]
  hmulB := by decide  
  f := ![![![341, -17, 0], ![1241, 0, 0]], ![![241, -12, 0], ![877, 0, 0]], ![![322, -4, -3], ![1172, 44, 0]]]
  g := ![![![1, 0, 0], ![-53, 73, 0], ![-66, 0, 73]], ![![-1, 1, 0], ![10, -20, 5], ![40, -30, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-29, 1, 0]] ![![73, 0, 0], ![-24, 1, 0]]
  ![![73, 0, 0], ![37, 4, 1]] where
 M := ![![![5329, 0, 0], ![-1752, 73, 0]], ![![-2117, 73, 0], ![696, -53, 5]]]
 hmul := by decide  
 g := ![![![![36, -4, -1], ![73, 0, 0]], ![![-24, 1, 0], ![0, 0, 0]]], ![![![-29, 1, 0], ![0, 0, 0]], ![![7, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![37, 4, 1]] ![![73, 0, 0], ![-20, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1460, 73, 0]], ![![2701, 292, 73], ![-730, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-20, 1, 0]]], ![![![37, 4, 1]], ![![-10, -1, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![24, 33, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![24, 33, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![24, 33, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![24, 33, 1], ![10, -6, 165], ![330, -988, -6]]]
  hmulB := by decide  
  f := ![![![-23, -33, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -33, 79]], ![![0, 0, 1], ![-50, -69, 165], ![6, -10, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [74, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 78], [0, 1]]
 g := ![![[22, 32], [40, 73], [37, 55], [10, 4], [13], [1]], ![[66, 47], [12, 6], [4, 24], [55, 75], [13], [1]]]
 h' := ![![[31, 78], [42, 43], [27, 51], [50, 56], [11, 2], [5, 31], [0, 1]], ![[0, 1], [32, 36], [28, 28], [48, 23], [73, 77], [18, 48], [31, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [56, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [74, 48, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33, 320, -31]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 17, -31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-7, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-7, 1, 0]] 
 ![![79, 0, 0], ![72, 1, 0], ![6, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-7, 1, 0], ![0, -7, 5], ![10, -30, -7]]]
  hmulB := by decide  
  f := ![![![267, -38, 0], ![3002, 0, 0]], ![![246, -35, 0], ![2766, 0, 0]], ![![24, -2, -1], ![270, 16, 0]]]
  g := ![![![1, 0, 0], ![-72, 79, 0], ![-6, 0, 79]], ![![-1, 1, 0], ![6, -7, 5], ![28, -30, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![24, 33, 1]] ![![79, 0, 0], ![-7, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-553, 79, 0]], ![![1896, 2607, 79], ![-158, -237, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-7, 1, 0]]], ![![![24, 33, 1]], ![![-2, -3, 2]]]]
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


lemma PB209I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB209I1 : PrimesBelowBoundCertificateInterval O 31 79 209 where
  m := 11
  g := ![3, 2, 2, 3, 2, 1, 2, 3, 1, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB209I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![73, 73, 73]
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
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
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
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I43N1, I47N0, I47N1, I47N2, I53N1, I61N1, I67N0, I67N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [I53N1], [], [I61N1], [I67N0, I67N1, I67N1], [], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
