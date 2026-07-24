
import IdealArithmetic.Examples.NF3_1_767839_1.RI3_1_767839_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![4, 11, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![4, 11, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![4, 11, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![4, 11, 1], ![155, -27, 11], ![1705, -186, -27]]]
  hmulB := by decide  
  f := ![![![-3, -11, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -11, 37]], ![![0, 0, 1], ![3, -4, 11], ![49, 3, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [13, 28, 1] where
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
 g := ![![[5, 1], [16], [26, 11], [7], [1]], ![[14, 36], [16], [14, 26], [7], [1]]]
 h' := ![![[9, 36], [2, 36], [32, 33], [4, 14], [24, 9], [0, 1]], ![[0, 1], [30, 1], [33, 4], [19, 23], [31, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [22, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [13, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![323, 65, -58]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 19, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-11, 1, 0]] 
 ![![37, 0, 0], ![26, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-11, 1, 0], ![0, -11, 1], ![155, -31, -11]]]
  hmulB := by decide  
  f := ![![![342, -31, 0], ![1147, 0, 0]], ![![254, -23, 0], ![852, 0, 0]], ![![268, -24, 0], ![899, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 37, 0], ![-27, 0, 37]], ![![-1, 1, 0], ![7, -11, 1], ![34, -31, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![4, 11, 1]] ![![37, 0, 0], ![-11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-407, 37, 0]], ![![148, 407, 37], ![111, -148, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-11, 1, 0]]], ![![![4, 11, 1]], ![![3, -4, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![0, 12, 1], ![155, -31, 12]]]
  hmulB := by decide  
  f := ![![![193, 16, 0], ![-656, 0, 0]], ![![36, 3, 0], ![-122, 0, 0]], ![![76, 6, 0], ![-258, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-20, 0, 41]], ![![0, 1, 0], ![-4, 12, 1], ![7, -31, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-11, 1, 0]] 
 ![![41, 0, 0], ![30, 1, 0], ![2, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-11, 1, 0], ![0, -11, 1], ![155, -31, -11]]]
  hmulB := by decide  
  f := ![![![232, -21, 0], ![861, 0, 0]], ![![166, -15, 0], ![616, 0, 0]], ![![14, -1, 0], ![52, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 41, 0], ![-2, 0, 41]], ![![-1, 1, 0], ![8, -11, 1], ![27, -31, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-1, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-1, 1, 0]] 
 ![![41, 0, 0], ![40, 1, 0], ![40, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-1, 1, 0], ![0, -1, 1], ![155, -31, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![123, 0, 0]], ![![2, -1, 0], ![42, 0, 0]], ![![2, -1, 0], ![42, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 41, 0], ![-40, 0, 41]], ![![-1, 1, 0], ![0, -1, 1], ![35, -31, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![12, 1, 0]] ![![41, 0, 0], ![-11, 1, 0]]
  ![![41, 0, 0], ![32, 1, 1]] where
 M := ![![![1681, 0, 0], ![-451, 41, 0]], ![![492, 41, 0], ![-132, 1, 1]]]
 hmul := by decide  
 g := ![![![![9, -1, -1], ![41, 0, 0]], ![![-11, 1, 0], ![0, 0, 0]]], ![![![-20, 0, -1], ![41, 0, 0]], ![![-4, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![32, 1, 1]] ![![41, 0, 0], ![-1, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-41, 41, 0]], ![![1312, 41, 41], ![123, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-1, 1, 0]]], ![![![32, 1, 1]], ![![3, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![11, 18, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![11, 18, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![11, 18, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![11, 18, 1], ![155, -20, 18], ![2790, -403, -20]]]
  hmulB := by decide  
  f := ![![![-10, -18, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -18, 43]], ![![0, 0, 1], ![-1, -8, 18], ![70, -1, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 42], [0, 1]]
 g := ![![[23, 11], [33, 40], [13], [4, 36], [1]], ![[0, 32], [8, 3], [13], [3, 7], [1]]]
 h' := ![![[37, 42], [40, 21], [32, 13], [27, 20], [39, 37], [0, 1]], ![[0, 1], [0, 22], [40, 30], [36, 23], [32, 6], [37, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [4, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1861, 1759, -263]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24, 151, -263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-18, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-18, 1, 0]] 
 ![![43, 0, 0], ![25, 1, 0], ![20, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-18, 1, 0], ![0, -18, 1], ![155, -31, -18]]]
  hmulB := by decide  
  f := ![![![361, -20, 0], ![860, 0, 0]], ![![199, -11, 0], ![474, 0, 0]], ![![188, -10, 0], ![448, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 43, 0], ![-20, 0, 43]], ![![-1, 1, 0], ![10, -18, 1], ![30, -31, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![11, 18, 1]] ![![43, 0, 0], ![-18, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-774, 43, 0]], ![![473, 774, 43], ![-43, -344, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-18, 1, 0]]], ![![![11, 18, 1]], ![![-1, -8, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2331369, 189883, 53442]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![2331369, 189883, 53442]] 
 ![![47, 0, 0], ![15, 1, 0], ![10, 0, 1]] where
  M :=![![![2331369, 189883, 53442], ![8283510, 674667, 189883], ![29431865, 2397137, 674667]]]
  hmulB := by decide  
  f := ![![![-4082, 1593, -125]], ![![-1715, 504, -6]], ![![4385, -1124, -31]]]
  g := ![![![-22368, 189883, 53442], ![-79475, 674667, 189883], ![-282380, 2397137, 674667]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![16, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![16, 1, 0]] 
 ![![47, 0, 0], ![16, 1, 0], ![26, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![16, 1, 0], ![0, 16, 1], ![155, -31, 16]]]
  hmulB := by decide  
  f := ![![![17, 1, 0], ![-47, 0, 0]], ![![-16, -1, 0], ![48, 0, 0]], ![![6, 0, 0], ![-16, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 47, 0], ![-26, 0, 47]], ![![0, 1, 0], ![-6, 16, 1], ![5, -31, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![2331369, 189883, 53442]] ![![47, 0, 0], ![16, 1, 0]]
  ![![47, 0, 0], ![5, -16, 1]] where
 M := ![![![109574343, 8924501, 2511774], ![45585414, 3712795, 1044955]]]
 hmul := by decide  
 g := ![![![![2313959, 245595, 49960], ![163654, 0, 0]], ![![962657, 102181, 20784], ![68107, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![5, -16, 1]] ![![47, 0, 0], ![16, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![752, 47, 0]], ![![235, -752, 47], ![235, -282, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![16, 1, 0]]], ![![![5, -16, 1]], ![![5, -6, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [36, 32, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 11], [29, 46, 42], [0, 1]]
 g := ![![[0, 50, 37], [3, 47], [50, 9, 42], [8, 46], [1]], ![[36, 4, 10, 28], [31, 52], [49, 9, 9, 13], [8, 42], [14, 39, 20, 6]], ![[15, 1, 51, 44], [18, 10], [52, 28, 3, 13], [20, 16], [30, 9, 41, 47]]]
 h' := ![![[0, 6, 11], [2, 7, 14], [2, 38, 10], [1, 21, 28], [17, 21, 29], [0, 1]], ![[29, 46, 42], [10, 21, 32], [38, 1, 30], [17, 31, 35], [26, 3, 28], [0, 6, 11]], ![[0, 1], [51, 25, 7], [40, 14, 13], [37, 1, 43], [42, 29, 49], [29, 46, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 47], []]
 b := ![[], [23, 23, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [36, 32, 24, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-152057, -15211, -4611]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2869, -287, -87]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [57, 7, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 55, 52], [23, 3, 7], [0, 1]]
 g := ![![[24, 42, 12], [43, 51, 9], [2, 15], [50, 26, 26], [1]], ![[39, 52, 26, 42], [40, 32, 20, 56], [11, 28], [51, 50, 29, 47], [14, 50, 16, 11]], ![[8, 26, 8, 57], [35, 33, 36, 51], [6, 22], [13, 36, 35, 19], [28, 39, 14, 48]]]
 h' := ![![[48, 55, 52], [27, 5, 37], [33, 39, 56], [41, 1, 29], [2, 52, 12], [0, 1]], ![[23, 3, 7], [8, 15, 17], [38, 7, 13], [4, 33, 21], [54, 25, 26], [48, 55, 52]], ![[0, 1], [19, 39, 5], [47, 13, 49], [25, 25, 9], [10, 41, 21], [23, 3, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 6], []]
 b := ![[], [13, 33, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [57, 7, 47, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-824643, 363145, -35695]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13977, 6155, -605]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![34, -8, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![34, -8, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![34, 53, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![34, -8, 1], ![155, 3, -8], ![-1240, 403, 3]]]
  hmulB := by decide  
  f := ![![![-33, 8, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -53, 61]], ![![0, -1, 1], ![7, 7, -8], ![-22, 4, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [59, 4, 1] where
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
 g := ![![[59, 20], [19], [56, 52], [2, 19], [57, 1]], ![[40, 41], [19], [31, 9], [48, 42], [53, 60]]]
 h' := ![![[57, 60], [16, 52], [51, 18], [4, 33], [53, 18], [0, 1]], ![[0, 1], [52, 9], [40, 43], [55, 28], [42, 43], [57, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [10, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [59, 4, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![369, 89, -34]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 31, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![8, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![8, 1, 0]] 
 ![![61, 0, 0], ![8, 1, 0], ![58, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![8, 1, 0], ![0, 8, 1], ![155, -31, 8]]]
  hmulB := by decide  
  f := ![![![153, 19, 0], ![-1159, 0, 0]], ![![8, 1, 0], ![-60, 0, 0]], ![![146, 18, 0], ![-1106, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 61, 0], ![-58, 0, 61]], ![![0, 1, 0], ![-2, 8, 1], ![-1, -31, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![34, -8, 1]] ![![61, 0, 0], ![8, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![488, 61, 0]], ![![2074, -488, 61], ![427, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![8, 1, 0]]], ![![![34, -8, 1]], ![![7, -1, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-12, 15, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-12, 15, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![55, 15, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-12, 15, 1], ![155, -43, 15], ![2325, -310, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -15, 67]], ![![-1, 0, 1], ![-10, -4, 15], ![70, 5, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [1, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 66], [0, 1]]
 g := ![![[34, 1], [34, 1], [23], [6], [17], [1]], ![[0, 66], [0, 66], [23], [6], [17], [1]]]
 h' := ![![[33, 66], [33, 66], [33, 66], [49, 36], [51, 26], [66, 33], [0, 1]], ![[0, 1], [0, 1], [0, 1], [31, 31], [38, 41], [16, 34], [33, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [18, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [1, 34, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5926, -339, 366]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-212, -87, 366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-15, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-15, 1, 0]] 
 ![![67, 0, 0], ![52, 1, 0], ![43, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-15, 1, 0], ![0, -15, 1], ![155, -31, -15]]]
  hmulB := by decide  
  f := ![![![196, -13, 0], ![871, 0, 0]], ![![166, -11, 0], ![738, 0, 0]], ![![124, -8, 0], ![551, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 67, 0], ![-43, 0, 67]], ![![-1, 1, 0], ![11, -15, 1], ![36, -31, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-12, 15, 1]] ![![67, 0, 0], ![-15, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1005, 67, 0]], ![![-804, 1005, 67], ![335, -268, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-15, 1, 0]]], ![![![-12, 15, 1]], ![![5, -4, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![39, 24, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![39, 24, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![39, 24, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![39, 24, 1], ![155, 8, 24], ![3720, -589, 8]]]
  hmulB := by decide  
  f := ![![![-38, -24, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -24, 71]], ![![0, 0, 1], ![-11, -8, 24], ![48, -11, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [68, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 70], [0, 1]]
 g := ![![[46, 37], [24, 8], [43, 48], [5], [16], [1]], ![[40, 34], [63, 63], [64, 23], [5], [16], [1]]]
 h' := ![![[67, 70], [1, 26], [58, 47], [69, 30], [57, 54], [3, 67], [0, 1]], ![[0, 1], [39, 45], [12, 24], [20, 41], [54, 17], [19, 4], [67, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [10, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [68, 4, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-865, 347, -24]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, 13, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-24, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-24, 1, 0]] 
 ![![71, 0, 0], ![47, 1, 0], ![63, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-24, 1, 0], ![0, -24, 1], ![155, -31, -24]]]
  hmulB := by decide  
  f := ![![![121, -5, 0], ![355, 0, 0]], ![![97, -4, 0], ![285, 0, 0]], ![![129, -5, 0], ![379, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 71, 0], ![-63, 0, 71]], ![![-1, 1, 0], ![15, -24, 1], ![44, -31, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![39, 24, 1]] ![![71, 0, 0], ![-24, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1704, 71, 0]], ![![2769, 1704, 71], ![-781, -568, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-24, 1, 0]]], ![![![39, 24, 1]], ![![-11, -8, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [52, 25, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 15, 44], [66, 57, 29], [0, 1]]
 g := ![![[57, 16, 8], [62, 24], [16, 19], [20, 40, 3], [22, 1], []], ![[61, 51, 28, 22], [61, 8], [51, 24], [58, 11, 53, 28], [27, 37], [39, 38]], ![[19, 28, 22, 34], [13, 3], [5, 70], [11, 23, 68, 15], [1, 6], [54, 38]]]
 h' := ![![[29, 15, 44], [70, 17, 64], [3, 19, 30], [55, 40, 26], [24, 55, 21], [0, 0, 1], [0, 1]], ![[66, 57, 29], [4, 4, 16], [57, 51, 64], [64, 3, 30], [52, 48, 40], [54, 36, 57], [29, 15, 44]], ![[0, 1], [35, 52, 66], [28, 3, 52], [19, 30, 17], [27, 43, 12], [15, 37, 15], [66, 57, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 2], []]
 b := ![[], [60, 61, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [52, 25, 51, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![166367, -39128, 3139]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2279, -536, 43]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![7, -23, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![7, -23, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![7, 56, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![7, -23, 1], ![155, -24, -23], ![-3565, 868, -24]]]
  hmulB := by decide  
  f := ![![![-6, 23, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -56, 79]], ![![0, -1, 1], ![4, 16, -23], ![-43, 28, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [70, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 78], [0, 1]]
 g := ![![[63, 50], [20, 32], [72, 19], [10, 36], [38], [1]], ![[52, 29], [73, 47], [22, 60], [40, 43], [38], [1]]]
 h' := ![![[14, 78], [22, 34], [16, 36], [11, 63], [28, 73], [9, 14], [0, 1]], ![[0, 1], [24, 45], [46, 43], [24, 16], [23, 6], [47, 65], [14, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [13, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [70, 65, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5996, 1170, 114]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86, -66, 114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![23, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![23, 1, 0]] 
 ![![79, 0, 0], ![23, 1, 0], ![24, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![23, 1, 0], ![0, 23, 1], ![155, -31, 23]]]
  hmulB := by decide  
  f := ![![![760, 33, 0], ![-2607, 0, 0]], ![![230, 10, 0], ![-789, 0, 0]], ![![214, 9, 0], ![-734, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 79, 0], ![-24, 0, 79]], ![![0, 1, 0], ![-7, 23, 1], ![4, -31, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![7, -23, 1]] ![![79, 0, 0], ![23, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1817, 79, 0]], ![![553, -1817, 79], ![316, -553, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![23, 1, 0]]], ![![![7, -23, 1]], ![![4, -7, 0]]]]
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


lemma PB248I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB248I1 : PrimesBelowBoundCertificateInterval O 31 79 248 where
  m := 11
  g := ![2, 3, 2, 3, 1, 1, 2, 2, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB248I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N1]
    · exact ![I53N0]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
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
      exact NI47N1
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
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
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I47N0, I47N1, I61N1, I67N1, I71N1, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N0, I47N1, I47N1], [], [], [I61N1], [I67N1], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
