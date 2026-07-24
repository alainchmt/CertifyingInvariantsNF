
import IdealArithmetic.Examples.NF3_1_64823_1.RI3_1_64823_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![6, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![6, 1, 0]] 
 ![![37, 0, 0], ![6, 1, 0], ![1, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![6, 1, 0], ![0, 6, 1], ![49, 1, 6]]]
  hmulB := by decide  
  f := ![![![127, 21, 0], ![-777, 0, 0]], ![![18, 3, 0], ![-110, 0, 0]], ![![-5, -1, 0], ![31, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 37, 0], ![-1, 0, 37]], ![![0, 1, 0], ![-1, 6, 1], ![1, 1, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![11, 1, 0]] 
 ![![37, 0, 0], ![11, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![11, 1, 0], ![0, 11, 1], ![49, 1, 11]]]
  hmulB := by decide  
  f := ![![![166, 15, 0], ![-555, 0, 0]], ![![44, 4, 0], ![-147, 0, 0]], ![![114, 10, 0], ![-381, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 37, 0], ![-27, 0, 37]], ![![0, 1, 0], ![-4, 11, 1], ![-7, 1, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -4, -1]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-13, -4, -1]] 
 ![![37, 0, 0], ![20, 1, 0], ![7, 0, 1]] where
  M :=![![![-13, -4, -1], ![-49, -14, -4], ![-196, -53, -14]]]
  hmulB := by decide  
  f := ![![![16, 3, -2]], ![![6, 2, -1]], ![![7, -2, 0]]]
  g := ![![![2, -4, -1], ![7, -14, -4], ![26, -53, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![6, 1, 0]] ![![37, 0, 0], ![11, 1, 0]]
  ![![16, 3, -2]] where
 M := ![![![1369, 0, 0], ![407, 37, 0]], ![![222, 37, 0], ![66, 17, 1]]]
 hmul := by decide  
 g := ![![![![-481, -148, -37]], ![![-192, -58, -15]]], ![![![-127, -38, -10]], ![![-51, -15, -4]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![16, 3, -2]] ![![-13, -4, -1]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 1, 0]] 
 ![![41, 0, 0], ![18, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 1, 0], ![0, 18, 1], ![49, 1, 18]]]
  hmulB := by decide  
  f := ![![![181, 10, 0], ![-410, 0, 0]], ![![90, 5, 0], ![-204, 0, 0]], ![![8, 0, 0], ![-18, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 41, 0], ![-4, 0, 41]], ![![0, 1, 0], ![-8, 18, 1], ![-1, 1, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-11, 1, 0]] 
 ![![41, 0, 0], ![30, 1, 0], ![2, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-11, 1, 0], ![0, -11, 1], ![49, 1, -11]]]
  hmulB := by decide  
  f := ![![![232, -21, 0], ![861, 0, 0]], ![![166, -15, 0], ![616, 0, 0]], ![![14, -1, 0], ![52, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 41, 0], ![-2, 0, 41]], ![![-1, 1, 0], ![8, -11, 1], ![1, 1, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 1, 0]] 
 ![![41, 0, 0], ![34, 1, 0], ![33, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 1, 0], ![0, -7, 1], ![49, 1, -7]]]
  hmulB := by decide  
  f := ![![![57, -8, 0], ![328, 0, 0]], ![![50, -7, 0], ![288, 0, 0]], ![![51, -7, 0], ![294, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 41, 0], ![-33, 0, 41]], ![![-1, 1, 0], ![5, -7, 1], ![6, 1, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![18, 1, 0]] ![![41, 0, 0], ![-11, 1, 0]]
  ![![41, 0, 0], ![7, 7, 1]] where
 M := ![![![1681, 0, 0], ![-451, 41, 0]], ![![738, 41, 0], ![-198, 7, 1]]]
 hmul := by decide  
 g := ![![![![34, -7, -1], ![41, 0, 0]], ![![-11, 1, 0], ![0, 0, 0]]], ![![![11, -6, -1], ![41, 0, 0]], ![![-5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![7, 7, 1]] ![![41, 0, 0], ![-7, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-287, 41, 0]], ![![287, 287, 41], ![0, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-7, 1, 0]]], ![![![7, 7, 1]], ![![0, -1, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![17, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![17, 1, 0]] 
 ![![43, 0, 0], ![17, 1, 0], ![12, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![17, 1, 0], ![0, 17, 1], ![49, 1, 17]]]
  hmulB := by decide  
  f := ![![![239, 14, 0], ![-602, 0, 0]], ![![85, 5, 0], ![-214, 0, 0]], ![![58, 3, 0], ![-146, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 43, 0], ![-12, 0, 43]], ![![0, 1, 0], ![-7, 17, 1], ![-4, 1, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-15, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-15, 1, 0]] 
 ![![43, 0, 0], ![28, 1, 0], ![33, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-15, 1, 0], ![0, -15, 1], ![49, 1, -15]]]
  hmulB := by decide  
  f := ![![![466, -31, 0], ![1333, 0, 0]], ![![316, -21, 0], ![904, 0, 0]], ![![366, -24, 0], ![1047, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 43, 0], ![-33, 0, 43]], ![![-1, 1, 0], ![9, -15, 1], ![12, 1, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![43, 0, 0], ![41, 1, 0], ![39, 0, 1]] where
  M :=![![![-2, 1, 0], ![0, -2, 1], ![49, 1, -2]]]
  hmulB := by decide  
  f := ![![![3, 2, 1]], ![![4, 2, 1]], ![![5, 3, 1]]]
  g := ![![![-1, 1, 0], ![1, -2, 1], ![2, 1, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![17, 1, 0]] ![![43, 0, 0], ![-15, 1, 0]]
  ![![3, 2, 1]] where
 M := ![![![1849, 0, 0], ![-645, 43, 0]], ![![731, 43, 0], ![-255, 2, 1]]]
 hmul := by decide  
 g := ![![![![-86, 43, 0]], ![![30, -17, 1]]], ![![![-34, 15, 1]], ![![13, -6, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![3, 2, 1]] ![![-2, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [4, 41, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 19, 7], [39, 27, 40], [0, 1]]
 g := ![![[22, 35, 37], [9, 8, 18], [35, 32, 27], [10, 45, 1], []], ![[5, 24, 17, 3], [34, 37, 11, 32], [26, 32, 30, 32], [33, 8, 38, 27], [27, 2]], ![[40, 25, 27, 10], [39, 31], [20, 23, 36, 23], [20, 39, 41, 11], [41, 2]]]
 h' := ![![[6, 19, 7], [11, 23, 32], [1, 37, 26], [7, 21, 11], [0, 0, 1], [0, 1]], ![[39, 27, 40], [7, 18, 38], [43, 13, 21], [46, 42, 21], [22, 6, 27], [6, 19, 7]], ![[0, 1], [11, 6, 24], [19, 44], [8, 31, 15], [41, 41, 19], [39, 27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 24], []]
 b := ![[], [5, 44, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [4, 41, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2397, -188, -188]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51, -4, -4]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [13, 30, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 2, 18], [16, 50, 35], [0, 1]]
 g := ![![[1, 15, 40], [15, 15], [13, 33, 10], [6, 9], [1]], ![[47, 47, 21, 51], [44, 43], [16, 24, 7, 48], [33, 43], [33, 48, 42, 2]], ![[7, 33, 42, 45], [17, 11], [18, 7, 18, 39], [46, 44], [40, 0, 46, 51]]]
 h' := ![![[40, 2, 18], [11, 52, 26], [43, 42, 11], [38, 6, 40], [40, 23, 3], [0, 1]], ![[16, 50, 35], [21, 35, 10], [40, 12, 34], [41, 20, 41], [24, 36, 34], [40, 2, 18]], ![[0, 1], [50, 19, 17], [35, 52, 8], [27, 27, 25], [25, 47, 16], [16, 50, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 21], []]
 b := ![[], [18, 18, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [13, 30, 50, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34185, 24645, -2173]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![645, 465, -41]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-3, 23, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-3, 23, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![56, 23, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-3, 23, 1], ![49, -2, 23], ![1127, 72, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -23, 59]], ![![-1, 0, 1], ![-21, -9, 23], ![21, 2, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [38, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 58], [0, 1]]
 g := ![![[46, 46], [10, 15], [29], [52, 27], [22, 1]], ![[55, 13], [45, 44], [29], [56, 32], [44, 58]]]
 h' := ![![[22, 58], [33, 39], [34, 30], [30, 41], [49, 33], [0, 1]], ![[0, 1], [6, 20], [45, 29], [47, 18], [8, 26], [22, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [58, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [38, 37, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1668, -44, 93]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, -37, 93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-23, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-23, 1, 0]] 
 ![![59, 0, 0], ![36, 1, 0], ![2, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-23, 1, 0], ![0, -23, 1], ![49, 1, -23]]]
  hmulB := by decide  
  f := ![![![645, -28, 0], ![1652, 0, 0]], ![![392, -17, 0], ![1004, 0, 0]], ![![32, -1, 0], ![82, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 59, 0], ![-2, 0, 59]], ![![-1, 1, 0], ![14, -23, 1], ![1, 1, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-3, 23, 1]] ![![59, 0, 0], ![-23, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1357, 59, 0]], ![![-177, 1357, 59], ![118, -531, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-23, 1, 0]]], ![![![-3, 23, 1]], ![![2, -9, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![22, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![22, 1, 0]] 
 ![![61, 0, 0], ![22, 1, 0], ![4, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![22, 1, 0], ![0, 22, 1], ![49, 1, 22]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-1037, 0, 0]], ![![110, 5, 0], ![-304, 0, 0]], ![![8, 0, 0], ![-22, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 61, 0], ![-4, 0, 61]], ![![0, 1, 0], ![-8, 22, 1], ![-1, 1, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-13, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-13, 1, 0]] 
 ![![61, 0, 0], ![48, 1, 0], ![14, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-13, 1, 0], ![0, -13, 1], ![49, 1, -13]]]
  hmulB := by decide  
  f := ![![![690, -53, 0], ![3233, 0, 0]], ![![534, -41, 0], ![2502, 0, 0]], ![![172, -13, 0], ![806, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 61, 0], ![-14, 0, 61]], ![![-1, 1, 0], ![10, -13, 1], ![3, 1, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-9, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-9, 1, 0]] 
 ![![61, 0, 0], ![52, 1, 0], ![41, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-9, 1, 0], ![0, -9, 1], ![49, 1, -9]]]
  hmulB := by decide  
  f := ![![![361, -40, 0], ![2440, 0, 0]], ![![298, -33, 0], ![2014, 0, 0]], ![![245, -27, 0], ![1656, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 61, 0], ![-41, 0, 61]], ![![-1, 1, 0], ![7, -9, 1], ![6, 1, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![22, 1, 0]] ![![61, 0, 0], ![-13, 1, 0]]
  ![![61, 0, 0], ![19, 9, 1]] where
 M := ![![![3721, 0, 0], ![-793, 61, 0]], ![![1342, 61, 0], ![-286, 9, 1]]]
 hmul := by decide  
 g := ![![![![42, -9, -1], ![61, 0, 0]], ![![-13, 1, 0], ![0, 0, 0]]], ![![![3, -8, -1], ![61, 0, 0]], ![![-5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![19, 9, 1]] ![![61, 0, 0], ![-9, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-549, 61, 0]], ![![1159, 549, 61], ![-122, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-9, 1, 0]]], ![![![19, 9, 1]], ![![-2, -1, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [53, 38, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 20, 50], [45, 46, 17], [0, 1]]
 g := ![![[54, 26, 9], [39, 11, 59], [35, 65], [36, 37], [64, 1], []], ![[65, 43, 50, 50], [56, 61, 51, 27], [24, 19], [29, 6], [41, 39], [61, 21]], ![[24, 34, 25, 1], [62, 57, 48, 60], [55, 10], [62, 10], [48, 65], [27, 21]]]
 h' := ![![[19, 20, 50], [10, 47, 64], [54, 1, 27], [57, 56, 20], [25, 61, 38], [0, 0, 1], [0, 1]], ![[45, 46, 17], [5, 42, 1], [48, 62, 19], [28, 27, 35], [52, 21, 41], [9, 9, 46], [19, 20, 50]], ![[0, 1], [8, 45, 2], [57, 4, 21], [52, 51, 12], [16, 52, 55], [58, 58, 20], [45, 46, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 48], []]
 b := ![[], [3, 42, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [53, 38, 3, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65124, -402, 1206]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-972, -6, 18]
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


def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-33, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-33, 1, 0]] 
 ![![71, 0, 0], ![38, 1, 0], ![47, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-33, 1, 0], ![0, -33, 1], ![49, 1, -33]]]
  hmulB := by decide  
  f := ![![![1387, -42, 0], ![2982, 0, 0]], ![![760, -23, 0], ![1634, 0, 0]], ![![907, -27, 0], ![1950, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 71, 0], ![-47, 0, 71]], ![![-1, 1, 0], ![17, -33, 1], ![22, 1, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-5, 1, 0]] 
 ![![71, 0, 0], ![66, 1, 0], ![46, 0, 1]] where
  M :=![![![-5, 1, 0], ![0, -5, 1], ![49, 1, -5]]]
  hmulB := by decide  
  f := ![![![-24, -5, -1]], ![![-23, -5, -1]], ![![-19, -4, -1]]]
  g := ![![![-1, 1, 0], ![4, -5, 1], ![3, 1, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-33, 1, 0]] ![![71, 0, 0], ![-33, 1, 0]]
  ![![24, 5, 1]] where
 M := ![![![5041, 0, 0], ![-2343, 71, 0]], ![![-2343, 71, 0], ![1089, -66, 1]]]
 hmul := by decide  
 g := ![![![![355, -71, 0]], ![![-165, 38, -1]]], ![![![-165, 38, -1]], ![![76, -20, 1]]]]
 hle2 := by decide  
def MulI71N1 : IdealMulLeCertificate' Table 
  ![![24, 5, 1]] ![![-5, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)


lemma PB73I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 72 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 72 (by omega)

def PB73I1 : PrimesBelowBoundCertificateInterval O 31 72 73 where
  m := 9
  g := ![3, 3, 3, 1, 1, 2, 3, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71]
  hP := PB73I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N0, I71N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
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
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
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
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N0
      exact NI71N1
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I41N2, I43N0, I43N1, I43N2, I59N1, I61N0, I61N1, I61N2, I71N0, I71N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N1, I41N2], [I43N0, I43N1, I43N2], [], [], [I59N1], [I61N0, I61N1, I61N2], [], [I71N0, I71N0, I71N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
