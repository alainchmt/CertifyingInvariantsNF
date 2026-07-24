
import IdealArithmetic.Examples.NF3_1_116424_1.RI3_1_116424_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![22, -13, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![22, -13, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![22, 24, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![22, -13, 1], ![80, -17, -67], ![-740, 185, 37]]]
  hmulB := by decide  
  f := ![![![-21, 13, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -24, 37]], ![![0, -1, 1], ![42, 43, -67], ![-42, -19, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [32, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 36], [0, 1]]
 g := ![![[29, 3], [12], [33, 30], [9], [1]], ![[20, 34], [12], [17, 7], [9], [1]]]
 h' := ![![[34, 36], [16, 22], [17, 30], [33, 17], [5, 34], [0, 1]], ![[0, 1], [24, 15], [1, 7], [19, 20], [14, 3], [34, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [5, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [32, 3, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![694, 7, -325]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![212, 211, -325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-7, 1, 0]] 
 ![![37, 0, 0], ![30, 1, 0], ![0, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-7, 1, 0], ![-2, -5, 5], ![54, -13, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![1, 2, -2], ![1, 15, 0]]]
  g := ![![![1, 0, 0], ![-30, 37, 0], ![0, 0, 37]], ![![-1, 1, 0], ![4, -5, 5], ![12, -13, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![22, -13, 1]] ![![37, 0, 0], ![-7, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-259, 37, 0]], ![![814, -481, 37], ![-74, 74, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-7, 1, 0]]], ![![![22, -13, 1]], ![![-2, 2, -2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-19, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-19, 1, 0]] 
 ![![41, 0, 0], ![22, 1, 0], ![17, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-19, 1, 0], ![-2, -17, 5], ![54, -13, -21]]]
  hmulB := by decide  
  f := ![![![-1005, -9526, 2800], ![246, -22960, 0]], ![![-523, -5104, 1500], ![165, -12300, 0]], ![![-413, -3950, 1161], ![110, -9520, 0]]]
  g := ![![![1, 0, 0], ![-22, 41, 0], ![-17, 0, 41]], ![![-1, 1, 0], ![7, -17, 5], ![17, -13, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-16, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-16, 1, 0]] 
 ![![41, 0, 0], ![25, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-16, 1, 0], ![-2, -14, 5], ![54, -13, -18]]]
  hmulB := by decide  
  f := ![![![-381, -2900, 1035], ![82, -8487, 0]], ![![-219, -1766, 630], ![83, -5166, 0]], ![![-36, -283, 101], ![11, -828, 0]]]
  g := ![![![1, 0, 0], ![-25, 41, 0], ![-4, 0, 41]], ![![-1, 1, 0], ![8, -14, 5], ![11, -13, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-6, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-6, 1, 0]] 
 ![![41, 0, 0], ![35, 1, 0], ![3, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-6, 1, 0], ![-2, -4, 5], ![54, -13, -8]]]
  hmulB := by decide  
  f := ![![![1077, 2178, -2720], ![-82, 22304, 0]], ![![917, 1858, -2320], ![-81, 19024, 0]], ![![81, 159, -199], ![9, 1632, 0]]]
  g := ![![![1, 0, 0], ![-35, 41, 0], ![-3, 0, 41]], ![![-1, 1, 0], ![3, -4, 5], ![13, -13, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-19, 1, 0]] ![![41, 0, 0], ![-16, 1, 0]]
  ![![41, 0, 0], ![3, 18, 1]] where
 M := ![![![1681, 0, 0], ![-656, 41, 0]], ![![-779, 41, 0], ![302, -33, 5]]]
 hmul := by decide  
 g := ![![![![38, -18, -1], ![41, 0, 0]], ![![-16, 1, 0], ![0, 0, 0]]], ![![![-19, 1, 0], ![0, 0, 0]], ![![7, -3, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![3, 18, 1]] ![![41, 0, 0], ![-6, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-246, 41, 0]], ![![123, 738, 41], ![0, -82, 82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-6, 1, 0]]], ![![![3, 18, 1]], ![![0, -2, 2]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![28, -18, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![28, -18, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![28, 25, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![28, -18, 1], ![90, -21, -92], ![-1010, 250, 53]]]
  hmulB := by decide  
  f := ![![![-27, 18, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -25, 43]], ![![0, -1, 1], ![62, 53, -92], ![-58, -25, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [8, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 42], [0, 1]]
 g := ![![[40, 21], [34, 13], [15], [24, 17], [1]], ![[28, 22], [2, 30], [15], [2, 26], [1]]]
 h' := ![![[24, 42], [29, 35], [22, 23], [23, 31], [35, 24], [0, 1]], ![[0, 1], [9, 8], [15, 20], [36, 12], [9, 19], [24, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [7, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [8, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2950, 1706, -1552]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![942, 942, -1552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![6, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![6, 1, 0]] 
 ![![43, 0, 0], ![6, 1, 0], ![33, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![6, 1, 0], ![-2, 8, 5], ![54, -13, 4]]]
  hmulB := by decide  
  f := ![![![2575, -10371, -6480], ![129, 55728, 0]], ![![354, -1441, -900], ![44, 7740, 0]], ![![1977, -7959, -4973], ![93, 42768, 0]]]
  g := ![![![1, 0, 0], ![-6, 43, 0], ![-33, 0, 43]], ![![0, 1, 0], ![-5, 8, 5], ![0, -13, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![28, -18, 1]] ![![43, 0, 0], ![6, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![258, 43, 0]], ![![1204, -774, 43], ![258, -129, -86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![6, 1, 0]]], ![![![28, -18, 1]], ![![6, -3, -2]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [30, 16, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 36, 29], [15, 10, 18], [0, 1]]
 g := ![![[29, 34, 24], [3, 1, 14], [17, 27, 1], [18, 38, 1], []], ![[37, 35, 35, 15], [39, 21, 14, 20], [45, 43, 43, 39], [2, 46, 2, 33], [18, 42]], ![[27, 41, 30, 14], [13, 1, 12, 32], [38, 34, 33, 2], [43, 23, 30, 16], [29, 42]]]
 h' := ![![[23, 36, 29], [4, 18, 20], [7, 11, 25], [24, 29, 46], [0, 0, 1], [0, 1]], ![[15, 10, 18], [10, 35, 17], [32, 41, 5], [44, 43, 32], [36, 14, 10], [23, 36, 29]], ![[0, 1], [17, 41, 10], [27, 42, 17], [23, 22, 16], [13, 33, 36], [15, 10, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 20], []]
 b := ![[], [32, 24, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [30, 16, 9, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![92314486, 479180322, -1416934004]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1964138, 10195326, -30147532]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [27, 28, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 35, 4], [5, 17, 49], [0, 1]]
 g := ![![[40, 1, 13], [31, 38], [48, 46, 6], [9, 13], [1]], ![[15, 45, 14, 16], [13, 25], [29, 26, 35, 6], [17, 16], [5, 35, 31, 11]], ![[29, 34, 47, 10], [52, 49], [17, 14, 6, 52], [42, 15], [31, 14, 27, 42]]]
 h' := ![![[33, 35, 4], [4, 50, 38], [29, 39, 41], [9, 8, 35], [26, 25, 38], [0, 1]], ![[5, 17, 49], [35, 26, 51], [42, 7, 5], [5, 45, 44], [27, 52, 4], [33, 35, 4]], ![[0, 1], [27, 30, 17], [0, 7, 7], [31, 0, 27], [30, 29, 11], [5, 17, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 31], []]
 b := ![[], [52, 32, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [27, 28, 15, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1432007, 511026, -254082]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27019, 9642, -4794]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![28, -20, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![28, -20, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![28, 39, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![28, -20, 1], ![94, -25, -102], ![-1118, 276, 57]]]
  hmulB := by decide  
  f := ![![![-27, 20, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -39, 59]], ![![0, -1, 1], ![50, 67, -102], ![-46, -33, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [39, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 58], [0, 1]]
 g := ![![[14, 21], [44, 51], [46], [52, 22], [44, 1]], ![[53, 38], [46, 8], [46], [17, 37], [29, 58]]]
 h' := ![![[44, 58], [54, 32], [47, 13], [37, 39], [54, 9], [0, 1]], ![[0, 1], [46, 27], [29, 46], [42, 20], [37, 50], [44, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [28, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [39, 15, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![725, -29, -385]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![195, 254, -385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-16, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-16, 1, 0]] 
 ![![59, 0, 0], ![43, 1, 0], ![2, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-16, 1, 0], ![-2, -14, 5], ![54, -13, -18]]]
  hmulB := by decide  
  f := ![![![-781, -5700, 2035], ![118, -24013, 0]], ![![-559, -4146, 1480], ![119, -17464, 0]], ![![-14, -194, 69], ![50, -814, 0]]]
  g := ![![![1, 0, 0], ![-43, 59, 0], ![-2, 0, 59]], ![![-1, 1, 0], ![10, -14, 5], ![11, -13, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![28, -20, 1]] ![![59, 0, 0], ![-16, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-944, 59, 0]], ![![1652, -1180, 59], ![-354, 295, -118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-16, 1, 0]]], ![![![28, -20, 1]], ![![-6, 5, -2]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [27, 43, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 58, 8], [51, 2, 53], [0, 1]]
 g := ![![[50, 51, 34], [36, 60], [34, 33, 60], [60, 47, 19], [1]], ![[8, 15, 13, 43], [22, 41], [16, 55, 41, 50], [40, 27, 8, 43], [27, 54, 29, 24]], ![[54, 4, 56, 24], [23, 58], [58, 23, 32, 6], [22, 29, 56, 43], [49, 5, 23, 37]]]
 h' := ![![[53, 58, 8], [13, 49, 41], [58, 23, 11], [27, 52, 50], [34, 18, 43], [0, 1]], ![[51, 2, 53], [52, 23, 47], [6, 51, 23], [28, 29, 28], [40, 38, 47], [53, 58, 8]], ![[0, 1], [5, 50, 34], [57, 48, 27], [10, 41, 44], [56, 5, 32], [51, 2, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 2], []]
 b := ![[], [44, 57, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [27, 43, 18, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![234789, 302255, -287371]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3849, 4955, -4711]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 1, 0]] 
 ![![67, 0, 0], ![39, 1, 0], ![55, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 1, 0], ![-2, -26, 5], ![54, -13, -30]]]
  hmulB := by decide  
  f := ![![![6399, 90109, -17325], ![-1273, 232155, 0]], ![![3725, 52427, -10080], ![-736, 135072, 0]], ![![5255, 73970, -14222], ![-1040, 190575, 0]]]
  g := ![![![1, 0, 0], ![-39, 67, 0], ![-55, 0, 67]], ![![-1, 1, 0], ![11, -26, 5], ![33, -13, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-21, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-21, 1, 0]] 
 ![![67, 0, 0], ![46, 1, 0], ![27, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-21, 1, 0], ![-2, -19, 5], ![54, -13, -23]]]
  hmulB := by decide  
  f := ![![![4483, 44584, -11730], ![-670, 157182, 0]], ![![3074, 30597, -8050], ![-468, 107870, 0]], ![![1800, 17967, -4727], ![-291, 63342, 0]]]
  g := ![![![1, 0, 0], ![-46, 67, 0], ![-27, 0, 67]], ![![-1, 1, 0], ![11, -19, 5], ![19, -13, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-18, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-18, 1, 0]] 
 ![![67, 0, 0], ![49, 1, 0], ![9, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-18, 1, 0], ![-2, -16, 5], ![54, -13, -20]]]
  hmulB := by decide  
  f := ![![![-2699, -22470, 7020], ![402, -94068, 0]], ![![-1961, -16421, 5130], ![336, -68742, 0]], ![![-351, -3019, 943], ![97, -12636, 0]]]
  g := ![![![1, 0, 0], ![-49, 67, 0], ![-9, 0, 67]], ![![-1, 1, 0], ![11, -16, 5], ![13, -13, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-28, 1, 0]] ![![67, 0, 0], ![-21, 1, 0]]
  ![![67, 0, 0], ![10, 4, 1]] where
 M := ![![![4489, 0, 0], ![-1407, 67, 0]], ![![-1876, 67, 0], ![586, -47, 5]]]
 hmul := by decide  
 g := ![![![![57, -4, -1], ![67, 0, 0]], ![![-21, 1, 0], ![0, 0, 0]]], ![![![-28, 1, 0], ![0, 0, 0]], ![![8, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![10, 4, 1]] ![![67, 0, 0], ![-18, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1206, 67, 0]], ![![670, 268, 67], ![-134, -67, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-18, 1, 0]]], ![![![10, 4, 1]], ![![-2, -1, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![9, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![9, 1, 0]] 
 ![![71, 0, 0], ![9, 1, 0], ![65, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![9, 1, 0], ![-2, 11, 5], ![54, -13, 7]]]
  hmulB := by decide  
  f := ![![![-799, 4400, 2000], ![0, -28400, 0]], ![![-100, 550, 250], ![1, -3550, 0]], ![![-733, 4028, 1831], ![12, -26000, 0]]]
  g := ![![![1, 0, 0], ![-9, 71, 0], ![-65, 0, 71]], ![![0, 1, 0], ![-6, 11, 5], ![-4, -13, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![25, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![25, 1, 0]] 
 ![![71, 0, 0], ![25, 1, 0], ![35, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![25, 1, 0], ![-2, 27, 5], ![54, -13, 23]]]
  hmulB := by decide  
  f := ![![![6239, -88952, -16470], ![994, 233874, 0]], ![![2193, -31298, -5795], ![356, 82289, 0]], ![![3065, -43850, -8119], ![520, 115290, 0]]]
  g := ![![![1, 0, 0], ![-25, 71, 0], ![-35, 0, 71]], ![![0, 1, 0], ![-12, 27, 5], ![-6, -13, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-34, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-34, 1, 0]] 
 ![![71, 0, 0], ![37, 1, 0], ![66, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-34, 1, 0], ![-2, -32, 5], ![54, -13, -36]]]
  hmulB := by decide  
  f := ![![![-857, -15363, 2400], ![213, -34080, 0]], ![![-431, -8002, 1250], ![143, -17750, 0]], ![![-800, -14281, 2231], ![191, -31680, 0]]]
  g := ![![![1, 0, 0], ![-37, 71, 0], ![-66, 0, 71]], ![![-1, 1, 0], ![12, -32, 5], ![41, -13, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![9, 1, 0]] ![![71, 0, 0], ![25, 1, 0]]
  ![![71, 0, 0], ![2, -7, 1]] where
 M := ![![![5041, 0, 0], ![1775, 71, 0]], ![![639, 71, 0], ![223, 36, 5]]]
 hmul := by decide  
 g := ![![![![69, 7, -1], ![71, 0, 0]], ![![23, 8, -1], ![71, 0, 0]]], ![![![7, 8, -1], ![71, 0, 0]], ![![3, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![2, -7, 1]] ![![71, 0, 0], ![-34, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2414, 71, 0]], ![![142, -497, 71], ![0, 213, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-34, 1, 0]]], ![![![2, -7, 1]], ![![0, 3, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![26, -18, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![26, -18, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![26, 55, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![26, -18, 1], ![90, -23, -92], ![-1010, 250, 51]]]
  hmulB := by decide  
  f := ![![![-25, 18, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -55, 73]], ![![0, -1, 1], ![34, 69, -92], ![-32, -35, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [44, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 72], [0, 1]]
 g := ![![[58, 50], [16], [4], [63, 32], [9], [1]], ![[62, 23], [16], [4], [13, 41], [9], [1]]]
 h' := ![![[3, 72], [45, 59], [47, 4], [2, 71], [7, 55], [29, 3], [0, 1]], ![[0, 1], [3, 14], [59, 69], [69, 2], [26, 18], [38, 70], [3, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [52, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [44, 70, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1307, 742, -1339]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![459, 1019, -1339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![19, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![19, 1, 0]] 
 ![![73, 0, 0], ![19, 1, 0], ![22, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![19, 1, 0], ![-2, 21, 5], ![54, -13, 17]]]
  hmulB := by decide  
  f := ![![![3687, -39906, -9500], ![438, 138700, 0]], ![![950, -10376, -2470], ![147, 36062, 0]], ![![1101, -12027, -2863], ![171, 41800, 0]]]
  g := ![![![1, 0, 0], ![-19, 73, 0], ![-22, 0, 73]], ![![0, 1, 0], ![-7, 21, 5], ![-1, -13, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![26, -18, 1]] ![![73, 0, 0], ![19, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1387, 73, 0]], ![![1898, -1314, 73], ![584, -365, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![19, 1, 0]]], ![![![26, -18, 1]], ![![8, -5, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![10, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![10, 1, 0]] 
 ![![79, 0, 0], ![10, 1, 0], ![23, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![10, 1, 0], ![-2, 12, 5], ![54, -13, 8]]]
  hmulB := by decide  
  f := ![![![-767, 4608, 1920], ![0, -30336, 0]], ![![-96, 576, 240], ![1, -3792, 0]], ![![-229, 1341, 559], ![45, -8832, 0]]]
  g := ![![![1, 0, 0], ![-10, 79, 0], ![-23, 0, 79]], ![![0, 1, 0], ![-3, 12, 5], ![0, -13, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![34, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![34, 1, 0]] 
 ![![79, 0, 0], ![34, 1, 0], ![55, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![34, 1, 0], ![-2, 36, 5], ![54, -13, 32]]]
  hmulB := by decide  
  f := ![![![-651, 12349, 1715], ![-79, -27097, 0]], ![![-294, 5292, 735], ![1, -11613, 0]], ![![-467, 8597, 1194], ![-23, -18865, 0]]]
  g := ![![![1, 0, 0], ![-34, 79, 0], ![-55, 0, 79]], ![![0, 1, 0], ![-19, 36, 5], ![-16, -13, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![35, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![35, 1, 0]] 
 ![![79, 0, 0], ![35, 1, 0], ![25, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![35, 1, 0], ![-2, 37, 5], ![54, -13, 33]]]
  hmulB := by decide  
  f := ![![![6966, -139877, -18900], ![1343, 298620, 0]], ![![3068, -61946, -8370], ![633, 132246, 0]], ![![2200, -44265, -5981], ![435, 94500, 0]]]
  g := ![![![1, 0, 0], ![-35, 79, 0], ![-25, 0, 79]], ![![0, 1, 0], ![-18, 37, 5], ![-4, -13, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![10, 1, 0]] ![![79, 0, 0], ![34, 1, 0]]
  ![![79, 0, 0], ![36, 25, 1]] where
 M := ![![![6241, 0, 0], ![2686, 79, 0]], ![![790, 79, 0], ![338, 46, 5]]]
 hmul := by decide  
 g := ![![![![43, -25, -1], ![79, 0, 0]], ![![-2, -24, -1], ![79, 0, 0]]], ![![![-26, -24, -1], ![79, 0, 0]], ![![2, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![36, 25, 1]] ![![79, 0, 0], ![35, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2765, 79, 0]], ![![2844, 1975, 79], ![1264, 948, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![35, 1, 0]]], ![![![36, 25, 1]], ![![16, 12, 2]]]]
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


lemma PB97I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB97I1 : PrimesBelowBoundCertificateInterval O 31 79 97 where
  m := 11
  g := ![2, 3, 2, 1, 1, 2, 1, 3, 3, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB97I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
      exact NI79N2
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I59N1, I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [], [], [I59N1], [], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
