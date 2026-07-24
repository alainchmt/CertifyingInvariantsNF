
import IdealArithmetic.Examples.NF3_1_547575_2.RI3_1_547575_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [18, 13, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 21, 35], [36, 15, 2], [0, 1]]
 g := ![![[9, 15, 28], [27, 1], [33, 29, 26], [22, 1], []], ![[36, 31, 36, 13], [36, 26], [29, 18, 8, 15], [18, 3], [4, 4]], ![[15, 22, 28, 20], [11, 10], [7, 16, 12, 32], [16, 34], [0, 4]]]
 h' := ![![[23, 21, 35], [36, 28, 19], [35, 21, 1], [11, 29, 27], [0, 0, 1], [0, 1]], ![[36, 15, 2], [2, 10, 7], [13, 25, 10], [30, 33, 14], [13, 28, 15], [23, 21, 35]], ![[0, 1], [27, 36, 11], [15, 28, 26], [9, 12, 33], [1, 9, 21], [36, 15, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 11], []]
 b := ![[], [9, 29, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [18, 13, 15, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34410, -68672, -48877]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![930, -1856, -1321]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![10, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![10, 1, 0]] 
 ![![41, 0, 0], ![10, 1, 0], ![27, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![10, 1, 0], ![0, 11, 2], ![24, -41, 10]]]
  hmulB := by decide  
  f := ![![![291, 29, 0], ![-1189, 0, 0]], ![![70, 7, 0], ![-286, 0, 0]], ![![197, 14, -1], ![-805, 21, 0]]]
  g := ![![![1, 0, 0], ![-10, 41, 0], ![-27, 0, 41]], ![![0, 1, 0], ![-4, 11, 2], ![4, -41, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17043023, -122386, -416916]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-17043023, -122386, -416916]] 
 ![![41, 0, 0], ![34, 1, 0], ![20, 0, 1]] where
  M :=![![![-17043023, -122386, -416916], ![-10005984, -71853, -244772], ![2065728, 14834, 50533]]]
  hmulB := by decide  
  f := ![![![-199, 206, -644]], ![![-542, 815, -524]], ![![212, -294, 325]]]
  g := ![![![-110819, -122386, -416916], ![-65062, -71853, -244772], ![13432, 14834, 50533]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-4, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-4, 1, 0]] 
 ![![41, 0, 0], ![37, 1, 0], ![35, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-4, 1, 0], ![0, -3, 2], ![24, -41, -4]]]
  hmulB := by decide  
  f := ![![![133, -33, 0], ![1353, 0, 0]], ![![121, -30, 0], ![1231, 0, 0]], ![![111, -26, -1], ![1129, 21, 0]]]
  g := ![![![1, 0, 0], ![-37, 41, 0], ![-35, 0, 41]], ![![-1, 1, 0], ![1, -3, 2], ![41, -41, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![10, 1, 0]] ![![-17043023, -122386, -416916]]
  ![![41, 0, 0], ![47, 2, 1]] where
 M := ![![![-698763943, -5017826, -17093556]], ![![-180436214, -1295713, -4413932]]]
 hmul := by decide  
 g := ![![![![-7369342, 289260, -211093], ![-8438743, 0, 0]]], ![![![-1902933, 74693, -54509], ![-2179063, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![47, 2, 1]] ![![41, 0, 0], ![-4, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-164, 41, 0]], ![![1927, 82, 41], ![-164, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-4, 1, 0]]], ![![![47, 2, 1]], ![![-4, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, -16, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, -16, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![10, 27, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, -16, 1], ![24, -47, -32], ![-396, 668, -31]]]
  hmulB := by decide  
  f := ![![![-9, 16, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -27, 43]], ![![0, -1, 1], ![8, 19, -32], ![-2, 35, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [42, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 42], [0, 1]]
 g := ![![[42, 17], [29, 15], [25], [40, 1], [1]], ![[25, 26], [14, 28], [25], [39, 42], [1]]]
 h' := ![![[42, 42], [29, 24], [34, 31], [40, 5], [1, 42], [0, 1]], ![[0, 1], [5, 19], [3, 12], [35, 38], [2, 1], [42, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [17, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [42, 1, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42, -136, -658]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![154, 410, -658]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-11, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-11, 1, 0]] 
 ![![43, 0, 0], ![32, 1, 0], ![31, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-11, 1, 0], ![0, -10, 2], ![24, -41, -11]]]
  hmulB := by decide  
  f := ![![![111, -10, 0], ![430, 0, 0]], ![![78, -7, 0], ![302, 0, 0]], ![![79, -2, -1], ![306, 22, 0]]]
  g := ![![![1, 0, 0], ![-32, 43, 0], ![-31, 0, 43]], ![![-1, 1, 0], ![6, -10, 2], ![39, -41, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![10, -16, 1]] ![![43, 0, 0], ![-11, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-473, 43, 0]], ![![430, -688, 43], ![-86, 129, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-11, 1, 0]]], ![![![10, -16, 1]], ![![-2, 3, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![5, -7, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![5, -7, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![5, 40, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![5, -7, 1], ![24, -43, -14], ![-180, 299, -36]]]
  hmulB := by decide  
  f := ![![![-4, 7, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -40, 47]], ![![0, -1, 1], ![2, 11, -14], ![0, 37, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [14, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 46], [0, 1]]
 g := ![![[26, 37], [14, 28], [28, 37], [29, 3], [1]], ![[0, 10], [21, 19], [2, 10], [18, 44], [1]]]
 h' := ![![[12, 46], [39, 32], [31, 13], [17, 32], [33, 12], [0, 1]], ![[0, 1], [0, 15], [46, 34], [25, 15], [36, 35], [12, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [45, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [14, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1858, 12, 52]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, -44, 52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![14, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![14, 1, 0]] 
 ![![47, 0, 0], ![14, 1, 0], ![36, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![14, 1, 0], ![0, 15, 2], ![24, -41, 14]]]
  hmulB := by decide  
  f := ![![![351, 25, 0], ![-1175, 0, 0]], ![![98, 7, 0], ![-328, 0, 0]], ![![276, 12, -1], ![-924, 24, 0]]]
  g := ![![![1, 0, 0], ![-14, 47, 0], ![-36, 0, 47]], ![![0, 1, 0], ![-6, 15, 2], ![2, -41, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![5, -7, 1]] ![![47, 0, 0], ![14, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![658, 47, 0]], ![![235, -329, 47], ![94, -141, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![14, 1, 0]]], ![![![5, -7, 1]], ![![2, -3, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![39, -16, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![39, -16, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![39, 37, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![39, -16, 1], ![24, -18, -32], ![-396, 668, -2]]]
  hmulB := by decide  
  f := ![![![-38, 16, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -37, 53]], ![![0, -1, 1], ![24, 22, -32], ![-6, 14, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [23, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 52], [0, 1]]
 g := ![![[43, 9], [47], [19, 37], [24], [18, 1]], ![[46, 44], [47], [49, 16], [24], [36, 52]]]
 h' := ![![[18, 52], [42, 3], [40, 10], [25, 39], [10, 36], [0, 1]], ![[0, 1], [43, 50], [8, 43], [38, 14], [22, 17], [18, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [38, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [23, 35, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![239, -590, -1202]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![889, 828, -1202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-21, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-21, 1, 0]] 
 ![![53, 0, 0], ![32, 1, 0], ![2, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-21, 1, 0], ![0, -20, 2], ![24, -41, -21]]]
  hmulB := by decide  
  f := ![![![22, 799, -80], ![53, 2120, 0]], ![![22, 479, -48], ![54, 1272, 0]], ![![4, 30, -3], ![10, 80, 0]]]
  g := ![![![1, 0, 0], ![-32, 53, 0], ![-2, 0, 53]], ![![-1, 1, 0], ![12, -20, 2], ![26, -41, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![39, -16, 1]] ![![53, 0, 0], ![-21, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1113, 53, 0]], ![![2067, -848, 53], ![-795, 318, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-21, 1, 0]]], ![![![39, -16, 1]], ![![-15, 6, -1]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [15, 19, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 35, 17], [10, 23, 42], [0, 1]]
 g := ![![[8, 23, 57], [55, 23, 12], [31, 27], [38, 31, 5], [1]], ![[20, 43, 22, 22], [50, 20, 10, 16], [51, 7], [5, 33, 4, 4], [34, 17, 29, 16]], ![[54, 18, 34, 40], [29, 9, 20, 47], [15, 19], [27, 49, 33, 18], [54, 20, 48, 43]]]
 h' := ![![[57, 35, 17], [1, 3, 36], [53, 56, 22], [20, 41, 33], [44, 40, 8], [0, 1]], ![[10, 23, 42], [9, 48, 53], [2, 47, 42], [0, 11, 40], [13, 50, 38], [57, 35, 17]], ![[0, 1], [9, 8, 29], [3, 15, 54], [46, 7, 45], [13, 28, 13], [10, 23, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 14], []]
 b := ![[], [28, 33, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [15, 19, 51, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![40887, -82364, -61891]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![693, -1396, -1049]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [50, 29, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 49, 10], [6, 11, 51], [0, 1]]
 g := ![![[28, 38, 52], [54, 25], [38, 25, 34], [4, 24, 20], [1]], ![[39, 55, 27, 17], [12, 36], [44, 35, 38, 7], [31, 49, 1, 30], [21, 54, 32, 24]], ![[41, 22, 45, 35], [31, 60], [12, 34, 35, 21], [35, 39, 22, 51], [15, 26, 34, 37]]]
 h' := ![![[3, 49, 10], [4, 36, 33], [52, 11, 56], [44, 25, 20], [11, 32, 9], [0, 1]], ![[6, 11, 51], [15, 38, 52], [35, 26, 55], [14, 44, 43], [14, 27, 53], [3, 49, 10]], ![[0, 1], [39, 48, 37], [53, 24, 11], [27, 53, 59], [15, 2, 60], [6, 11, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 40], []]
 b := ![[], [35, 11, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [50, 29, 52, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17611188, 32711616, 13093650]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-288708, 536256, 214650]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [30, 15, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 8, 56], [56, 58, 11], [0, 1]]
 g := ![![[56, 21, 15], [9, 16, 21], [28, 22], [44, 59], [51, 1], []], ![[29, 5, 49, 24], [30, 6, 15, 47], [39, 35], [51, 33], [22, 14], [32, 54]], ![[3, 15, 39, 28], [52, 33, 1, 66], [44, 37], [42, 21], [21, 64], [10, 54]]]
 h' := ![![[62, 8, 56], [65, 23, 45], [13, 33, 50], [7, 46, 42], [11, 9, 40], [0, 0, 1], [0, 1]], ![[56, 58, 11], [18, 38, 12], [65, 5, 58], [37, 62, 54], [19, 39, 10], [3, 31, 58], [62, 8, 56]], ![[0, 1], [65, 6, 10], [13, 29, 26], [23, 26, 38], [55, 19, 17], [22, 36, 8], [56, 58, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 7], []]
 b := ![[], [57, 3, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [30, 15, 16, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3618, 6298, 402]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, 94, 6]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [15, 46, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 42, 57], [41, 28, 14], [0, 1]]
 g := ![![[63, 17, 57], [0, 27, 58], [6, 1, 64], [61, 38], [19, 1], []], ![[3, 61, 43, 48], [58, 59, 21, 64], [50, 20, 5, 8], [8, 20], [43, 3], [63, 54]], ![[11, 55, 5, 52], [24, 45, 10, 42], [52, 29, 18, 21], [1, 9], [25, 60], [35, 54]]]
 h' := ![![[49, 42, 57], [0, 27, 46], [52, 3, 22], [9, 35, 8], [70, 34, 31], [0, 0, 1], [0, 1]], ![[41, 28, 14], [68, 22, 58], [68, 14, 6], [24, 48, 18], [12, 18, 37], [36, 53, 28], [49, 42, 57]], ![[0, 1], [39, 22, 38], [47, 54, 43], [42, 59, 45], [25, 19, 3], [20, 18, 42], [41, 28, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 37], []]
 b := ![[], [12, 6, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [15, 46, 52, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100749, 202989, 150875]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1419, 2859, 2125]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [26, 13, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 55, 3], [16, 17, 70], [0, 1]]
 g := ![![[66, 14, 1], [49, 16], [69, 12], [40, 41, 27], [52, 1], []], ![[10, 0, 52, 55], [0, 61], [24, 54], [41, 14, 42, 69], [39, 70], [68, 9]], ![[21, 62, 14, 36], [34, 24], [11, 50], [61, 25, 30, 19], [24, 32], [1, 9]]]
 h' := ![![[36, 55, 3], [67, 19, 72], [63, 34, 69], [55, 4, 31], [35, 28, 63], [0, 0, 1], [0, 1]], ![[16, 17, 70], [55, 28, 40], [36, 65, 34], [21, 65, 28], [69, 57, 60], [39, 68, 17], [36, 55, 3]], ![[0, 1], [68, 26, 34], [52, 47, 43], [22, 4, 14], [8, 61, 23], [11, 5, 55], [16, 17, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 45], []]
 b := ![[], [72, 6, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [26, 13, 21, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![707808, -1272536, -324850]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9696, -17432, -4450]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![1, 12, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![1, 12, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![1, 12, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![1, 12, 1], ![24, -28, 24], ![276, -480, -40]]]
  hmulB := by decide  
  f := ![![![0, 4, -1], ![-17, 4, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -12, 79]], ![![0, 0, 1], ![0, -4, 24], ![4, 0, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [31, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 78], [0, 1]]
 g := ![![[26, 51], [43, 10], [36, 25], [20, 55], [19], [1]], ![[0, 28], [41, 69], [31, 54], [9, 24], [19], [1]]]
 h' := ![![[63, 78], [10, 50], [69, 57], [12, 5], [56, 56], [48, 63], [0, 1]], ![[0, 1], [0, 29], [26, 22], [11, 74], [29, 23], [67, 16], [63, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [31, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [31, 16, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![396, 12, 1]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 0, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-24, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-24, 1, 0]] 
 ![![79, 0, 0], ![55, 1, 0], ![40, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-24, 1, 0], ![0, -23, 2], ![24, -41, -24]]]
  hmulB := by decide  
  f := ![![![1585, -66, 0], ![5214, 0, 0]], ![![1081, -45, 0], ![3556, 0, 0]], ![![808, -22, -1], ![2658, 40, 0]]]
  g := ![![![1, 0, 0], ![-55, 79, 0], ![-40, 0, 79]], ![![-1, 1, 0], ![15, -23, 2], ![41, -41, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![1, 12, 1]] ![![79, 0, 0], ![-24, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1896, 79, 0]], ![![79, 948, 79], ![0, -316, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-24, 1, 0]]], ![![![1, 12, 1]], ![![0, -4, 0]]]]
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


lemma PB210I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB210I1 : PrimesBelowBoundCertificateInterval O 31 79 210 where
  m := 11
  g := ![1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB210I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
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
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
  β := ![I41N0, I41N1, I41N2, I43N1, I47N1, I53N1, I79N1]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [I53N1], [], [], [], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
