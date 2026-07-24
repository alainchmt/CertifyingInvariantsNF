
import IdealArithmetic.Examples.NF3_1_132328_2.RI3_1_132328_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![1, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![1, 1, 0]] 
 ![![37, 0, 0], ![1, 1, 0], ![36, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![1, 1, 0], ![0, 2, 2], ![55, -19, 0]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![37, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -2, -1], ![36, 19, 0]]]
  g := ![![![1, 0, 0], ![-1, 37, 0], ![-36, 0, 37]], ![![0, 1, 0], ![-2, 2, 2], ![2, -19, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![767802928, 62485239, 35367527]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![767802928, 62485239, 35367527]] 
 ![![37, 0, 0], ![10, 1, 0], ![19, 0, 1]] where
  M :=![![![767802928, 62485239, 35367527], ![1945213985, 158305154, 89602951], ![1491474160, 121378958, 68702203]]]
  hmulB := by decide  
  f := ![![![-50796, 15349, 6131]], ![![-4615, 42, 2321]], ![![-12382, 6131, -1622]]]
  g := ![![![-14298175, 62485239, 35367527], ![-36224152, 158305154, 89602951], ![-27774521, 121378958, 68702203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-11, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-11, 1, 0]] 
 ![![37, 0, 0], ![26, 1, 0], ![19, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-11, 1, 0], ![0, -10, 2], ![55, -19, -12]]]
  hmulB := by decide  
  f := ![![![342, -31, 0], ![1147, 0, 0]], ![![254, -23, 0], ![852, 0, 0]], ![![178, -11, -1], ![597, 19, 0]]]
  g := ![![![1, 0, 0], ![-26, 37, 0], ![-19, 0, 37]], ![![-1, 1, 0], ![6, -10, 2], ![21, -19, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![1, 1, 0]] ![![767802928, 62485239, 35367527]]
  ![![37, 0, 0], ![5, 6, 1]] where
 M := ![![![28408708336, 2311953843, 1308598499]], ![![2713016913, 220790393, 124970478]]]
 hmul := by decide  
 g := ![![![![752955638, 44668491, 32398069], ![109869946, 0, 0]]], ![![![71906869, 4265813, 3093998], ![10492552, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![5, 6, 1]] ![![37, 0, 0], ![-11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-407, 37, 0]], ![![185, 222, 37], ![0, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-11, 1, 0]]], ![![![5, 6, 1]], ![![0, -2, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![13, 1, 0]] 
 ![![41, 0, 0], ![13, 1, 0], ![32, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, 1, 0], ![0, 14, 2], ![55, -19, 12]]]
  hmulB := by decide  
  f := ![![![222, 17, 0], ![-697, 0, 0]], ![![52, 4, 0], ![-163, 0, 0]], ![![172, 6, -1], ![-540, 21, 0]]]
  g := ![![![1, 0, 0], ![-13, 41, 0], ![-32, 0, 41]], ![![0, 1, 0], ![-6, 14, 2], ![-2, -19, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 1, 0]] 
 ![![41, 0, 0], ![34, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 1, 0], ![0, -6, 2], ![55, -19, -8]]]
  hmulB := by decide  
  f := ![![![57, -8, 0], ![328, 0, 0]], ![![50, -7, 0], ![288, 0, 0]], ![![36, -2, -1], ![208, 21, 0]]]
  g := ![![![1, 0, 0], ![-34, 41, 0], ![-20, 0, 41]], ![![-1, 1, 0], ![4, -6, 2], ![21, -19, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-282, -23, -13]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-282, -23, -13]] 
 ![![41, 0, 0], ![35, 1, 0], ![26, 0, 1]] where
  M :=![![![-282, -23, -13], ![-715, -58, -33], ![-550, -44, -25]]]
  hmulB := by decide  
  f := ![![![2, 3, -5]], ![![-5, 5, -4]], ![![12, -4, -1]]]
  g := ![![![21, -23, -13], ![53, -58, -33], ![40, -44, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![13, 1, 0]] ![![41, 0, 0], ![-7, 1, 0]]
  ![![-2, -3, 5]] where
 M := ![![![1681, 0, 0], ![-287, 41, 0]], ![![533, 41, 0], ![-91, 7, 2]]]
 hmul := by decide  
 g := ![![![![11562, 943, 533]], ![![-1259, -103, -58]]], ![![![4381, 357, 202]], ![![-477, -39, -22]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-2, -3, 5]] ![![-282, -23, -13]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![24, -10, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![24, -10, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![24, 33, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![24, -10, 1], ![55, -5, -21], ![-605, 227, 16]]]
  hmulB := by decide  
  f := ![![![-23, 10, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -33, 43]], ![![0, -1, 1], ![13, 16, -21], ![-23, -7, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [18, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 42], [0, 1]]
 g := ![![[15, 24], [7, 23], [9], [37, 15], [1]], ![[28, 19], [32, 20], [9], [29, 28], [1]]]
 h' := ![![[31, 42], [3, 29], [21, 18], [22, 40], [25, 31], [0, 1]], ![[0, 1], [42, 14], [20, 25], [15, 3], [40, 12], [31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [7, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [18, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![183, 85, -202]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![117, 157, -202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![21, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![21, 1, 0]] 
 ![![43, 0, 0], ![21, 1, 0], ![27, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![21, 1, 0], ![0, 22, 2], ![55, -19, 20]]]
  hmulB := by decide  
  f := ![![![820, 39, 0], ![-1677, 0, 0]], ![![378, 18, 0], ![-773, 0, 0]], ![![510, 13, -1], ![-1043, 22, 0]]]
  g := ![![![1, 0, 0], ![-21, 43, 0], ![-27, 0, 43]], ![![0, 1, 0], ![-12, 22, 2], ![-2, -19, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![24, -10, 1]] ![![43, 0, 0], ![21, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![903, 43, 0]], ![![1032, -430, 43], ![559, -215, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![21, 1, 0]]], ![![![24, -10, 1]], ![![13, -5, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [31, 33, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 38, 43], [25, 8, 4], [0, 1]]
 g := ![![[36, 4, 14], [27, 36, 21], [37, 10, 25], [20, 37, 1], []], ![[7, 13, 9, 26], [23, 45, 1, 40], [13, 29, 26, 19], [37, 7, 17, 26], [6, 16]], ![[43, 43, 18, 32], [46, 31, 45, 37], [31, 28, 20, 12], [7, 28, 38, 42], [45, 16]]]
 h' := ![![[12, 38, 43], [9, 46, 22], [28, 7, 31], [38, 26, 5], [0, 0, 1], [0, 1]], ![[25, 8, 4], [13, 11, 39], [32, 21, 32], [46, 10, 30], [5, 30, 8], [12, 38, 43]], ![[0, 1], [11, 37, 33], [21, 19, 31], [34, 11, 12], [29, 17, 38], [25, 8, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 2], []]
 b := ![[], [36, 45, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [31, 33, 10, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142457, -68338, 16826]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3031, -1454, 358]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [21, 36, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 29, 27], [32, 23, 26], [0, 1]]
 g := ![![[19, 41, 17], [29, 38], [24, 19, 40], [41, 16], [1]], ![[33, 34], [24, 42], [38, 1, 30, 18], [8, 17], [9, 0, 9, 20]], ![[6, 46, 7, 18], [23, 44], [31, 40, 47, 18], [38, 42], [41, 44, 30, 33]]]
 h' := ![![[25, 29, 27], [14, 41, 21], [26, 25, 41], [4, 18, 27], [32, 17, 4], [0, 1]], ![[32, 23, 26], [33, 11], [22, 5, 28], [1, 22, 47], [13, 44, 21], [25, 29, 27]], ![[0, 1], [43, 1, 32], [7, 23, 37], [51, 13, 32], [1, 45, 28], [32, 23, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 48], []]
 b := ![[], [19, 13, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [21, 36, 49, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-58883, -3922, -3710]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1111, -74, -70]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![18, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![18, 1, 0]] 
 ![![59, 0, 0], ![18, 1, 0], ![6, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![18, 1, 0], ![0, 19, 2], ![55, -19, 17]]]
  hmulB := by decide  
  f := ![![![271, 15, 0], ![-885, 0, 0]], ![![90, 5, 0], ![-294, 0, 0]], ![![30, -8, -1], ![-98, 30, 0]]]
  g := ![![![1, 0, 0], ![-18, 59, 0], ![-6, 0, 59]], ![![0, 1, 0], ![-6, 19, 2], ![5, -19, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![20, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![20, 1, 0]] 
 ![![59, 0, 0], ![20, 1, 0], ![26, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![20, 1, 0], ![0, 21, 2], ![55, -19, 19]]]
  hmulB := by decide  
  f := ![![![21, 1, 0], ![-59, 0, 0]], ![![-20, -1, 0], ![60, 0, 0]], ![![-26, -12, -1], ![78, 30, 0]]]
  g := ![![![1, 0, 0], ![-20, 59, 0], ![-26, 0, 59]], ![![0, 1, 0], ![-8, 21, 2], ![-1, -19, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![425299953, 34611706, 19590714]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![425299953, 34611706, 19590714]] 
 ![![59, 0, 0], ![21, 1, 0], ![5, 0, 1]] where
  M :=![![![425299953, 34611706, 19590714], ![1077489270, 87688093, 49632698], ![826154560, 67234004, 38055395]]]
  hmulB := by decide  
  f := ![![![48943, -15014, -5614]], ![![12187, -2961, -2412]], ![![-4615, 42, 2321]]]
  g := ![![![-6771177, 34611706, 19590714], ![-17154647, 87688093, 49632698], ![-13153161, 67234004, 38055395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![18, 1, 0]] ![![59, 0, 0], ![20, 1, 0]]
  ![![48943, -15014, -5614]] where
 M := ![![![3481, 0, 0], ![1180, 59, 0]], ![![1062, 59, 0], ![360, 39, 2]]]
 hmul := by decide  
 g := ![![![![25092697227, 2042090654, 1155852126]], ![![9583488330, 779922213, 441446978]]], ![![![8732888424, 710698801, 402265550]], ![![3335294470, 271432505, 153634628]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![48943, -15014, -5614]] ![![425299953, 34611706, 19590714]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [26, 18, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 2, 40], [43, 58, 21], [0, 1]]
 g := ![![[39, 59, 48], [34, 58], [3, 38, 12], [10, 6, 25], [1]], ![[44, 3, 43, 26], [14, 25], [33, 47, 8, 53], [18, 49, 54, 55], [41, 52, 17, 11]], ![[57, 7, 60, 30], [21, 48], [40, 10, 20, 32], [46, 53, 38, 23], [46, 19, 2, 50]]]
 h' := ![![[23, 2, 40], [15, 21, 32], [44, 7, 34], [45, 35, 45], [35, 43, 5], [0, 1]], ![[43, 58, 21], [38, 12, 12], [6, 5, 56], [43, 24, 45], [60, 47, 58], [23, 2, 40]], ![[0, 1], [50, 28, 17], [48, 49, 32], [32, 2, 32], [48, 32, 59], [43, 58, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 48], []]
 b := ![[], [1, 40, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [26, 18, 56, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-243329, 151646, -68503]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3989, 2486, -1123]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [4, 28, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 5, 18], [15, 61, 49], [0, 1]]
 g := ![![[43, 40, 26], [26, 15, 60], [45, 17], [55, 19], [44, 1], []], ![[48, 17, 35, 41], [60, 42, 55, 7], [18, 36], [39, 25], [19, 36], [31, 56]], ![[6, 52, 12, 65], [51, 57, 38, 16], [35, 59], [62, 29], [8, 25], [0, 56]]]
 h' := ![![[29, 5, 18], [30, 45, 19], [30, 9, 44], [3, 33, 33], [25, 37, 32], [0, 0, 1], [0, 1]], ![[15, 61, 49], [17, 62, 26], [14, 66, 32], [32, 30, 61], [56, 48, 5], [47, 2, 61], [29, 5, 18]], ![[0, 1], [22, 27, 22], [15, 59, 58], [17, 4, 40], [8, 49, 30], [24, 65, 5], [15, 61, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 21], []]
 b := ![[], [23, 23, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [4, 28, 23, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23316, 20234, -13802]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-348, 302, -206]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [24, 26, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 8, 65], [53, 62, 6], [0, 1]]
 g := ![![[67, 28, 32], [1, 58, 50], [24, 15, 9], [49, 32], [7, 1], []], ![[21, 31, 37, 23], [26, 39], [6, 44, 30, 52], [15, 18], [64, 10], [14, 36]], ![[56, 47, 40, 6], [65, 23, 69, 16], [67, 35, 51, 48], [32, 27], [64, 64], [2, 36]]]
 h' := ![![[25, 8, 65], [47, 66, 48], [63, 19, 11], [68, 8, 68], [45, 7, 23], [0, 0, 1], [0, 1]], ![[53, 62, 6], [20, 47, 24], [25, 61], [40, 63, 50], [51, 40, 35], [5, 24, 62], [25, 8, 65]], ![[0, 1], [37, 29, 70], [59, 62, 60], [19, 0, 24], [19, 24, 13], [63, 47, 8], [53, 62, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 50], []]
 b := ![[], [16, 28, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [24, 26, 64, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2783555, -2961410, 3119243]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39205, -41710, 43933]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![20, 11, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![20, 11, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![20, 11, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![20, 11, 1], ![55, 12, 21], ![550, -172, -9]]]
  hmulB := by decide  
  f := ![![![-19, -11, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -11, 73]], ![![0, 0, 1], ![-5, -3, 21], ![10, -1, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [4, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 72], [0, 1]]
 g := ![![[18, 55], [61], [41], [27, 49], [1], [1]], ![[0, 18], [61], [41], [3, 24], [1], [1]]]
 h' := ![![[1, 72], [36, 37], [39, 39], [38, 48], [12, 66], [69, 1], [0, 1]], ![[0, 1], [0, 36], [5, 34], [13, 25], [5, 7], [70, 72], [1, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [34, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [4, 72, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![98, 105, 56]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -7, 56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-21, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-21, 1, 0]] 
 ![![73, 0, 0], ![52, 1, 0], ![9, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-21, 1, 0], ![0, -20, 2], ![55, -19, -22]]]
  hmulB := by decide  
  f := ![![![274, -13, 0], ![949, 0, 0]], ![![190, -9, 0], ![658, 0, 0]], ![![66, 7, -1], ![229, 37, 0]]]
  g := ![![![1, 0, 0], ![-52, 73, 0], ![-9, 0, 73]], ![![-1, 1, 0], ![14, -20, 2], ![17, -19, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![20, 11, 1]] ![![73, 0, 0], ![-21, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1533, 73, 0]], ![![1460, 803, 73], ![-365, -219, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-21, 1, 0]]], ![![![20, 11, 1]], ![![-5, -3, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [50, 16, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 25, 48], [7, 53, 31], [0, 1]]
 g := ![![[7, 33, 1], [27, 38, 40], [5, 13, 18], [29, 77, 4], [52, 1], []], ![[24, 19, 3, 70], [30, 50, 78, 58], [10, 39, 43, 12], [49, 24, 0, 24], [11, 44], [74, 13]], ![[58, 9, 23, 18], [44, 64, 64, 62], [39, 6, 75, 40], [68, 12, 58, 16], [8, 72], [12, 13]]]
 h' := ![![[45, 25, 48], [72, 49, 78], [66, 54, 44], [51, 1, 52], [7, 66, 2], [0, 0, 1], [0, 1]], ![[7, 53, 31], [2, 19, 8], [54, 62, 26], [54, 11, 39], [22, 33, 35], [63, 21, 53], [45, 25, 48]], ![[0, 1], [18, 11, 72], [58, 42, 9], [4, 67, 67], [78, 59, 42], [2, 58, 25], [7, 53, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 40], []]
 b := ![[], [8, 7, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [50, 16, 27, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![158395, -81923, 32311]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2005, -1037, 409]
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



lemma PB103I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB103I1 : PrimesBelowBoundCertificateInterval O 31 79 103 where
  m := 11
  g := ![3, 3, 2, 1, 1, 3, 1, 1, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB103I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![357911]
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
      exact NI59N2
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I41N2, I43N1, I59N0, I59N1, I59N2, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N1, I41N2], [I43N1], [], [], [I59N0, I59N1, I59N2], [], [], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
