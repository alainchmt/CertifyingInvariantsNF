
import IdealArithmetic.Examples.NF3_1_439052_1.RI3_1_439052_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [29, 32, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 19, 11], [16, 17, 26], [0, 1]]
 g := ![![[26, 13, 28], [3, 26], [28, 5, 7], [2, 1], []], ![[14, 4, 22, 7], [15, 27], [15, 9, 1, 12], [26, 30], [31, 10]], ![[2, 7, 36, 3], [4, 28], [26, 5, 19, 10], [20, 28], [16, 10]]]
 h' := ![![[23, 19, 11], [28, 6, 18], [2, 29, 10], [16, 18, 9], [0, 0, 1], [0, 1]], ![[16, 17, 26], [18, 22, 2], [3, 23, 8], [23, 0, 18], [0, 36, 17], [23, 19, 11]], ![[0, 1], [6, 9, 17], [14, 22, 19], [23, 19, 10], [14, 1, 19], [16, 17, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 22], []]
 b := ![[], [2, 24, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [29, 32, 35, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59385, 54686, -13098]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1605, 1478, -354]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-47, 11, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-47, 11, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![35, 11, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-47, 11, 1], ![-261, 7, 23], ![-3101, 485, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -11, 41]], ![![-2, 0, 1], ![-26, -6, 23], ![-91, 7, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [22, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 40], [0, 1]]
 g := ![![[37, 9], [37], [33], [34, 36], [1]], ![[9, 32], [37], [33], [4, 5], [1]]]
 h' := ![![[6, 40], [4, 3], [30, 23], [31, 19], [19, 6], [0, 1]], ![[0, 1], [22, 38], [4, 18], [22, 22], [14, 35], [6, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [33, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [22, 35, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2815, -3883, 1533]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1240, -506, 1533]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 1, 0]] 
 ![![41, 0, 0], ![18, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 1, 0], ![1, 18, 2], ![-272, 54, 19]]]
  hmulB := by decide  
  f := ![![![211, 6041, 672], ![287, -13776, 0]], ![![93, 2643, 294], ![124, -6027, 0]], ![![121, 3389, 377], ![155, -7728, 0]]]
  g := ![![![1, 0, 0], ![-18, 41, 0], ![-23, 0, 41]], ![![0, 1, 0], ![-9, 18, 2], ![-41, 54, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-47, 11, 1]] ![![41, 0, 0], ![18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![738, 41, 0]], ![![-1927, 451, 41], ![-1107, 205, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![18, 1, 0]]], ![![![-47, 11, 1]], ![![-27, 5, 1]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [29, 38, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 15, 3], [0, 27, 40], [0, 1]]
 g := ![![[36, 22, 14], [0, 7, 6], [33, 10], [20, 31, 1], []], ![[12, 3, 31, 8], [20, 22, 21, 22], [6, 24], [15, 31, 14, 37], [25, 9]], ![[0, 38, 34, 14], [34, 6, 2, 40], [3, 1], [12, 15, 22, 13], [31, 9]]]
 h' := ![![[31, 15, 3], [0, 12, 33], [0, 22, 36], [22, 18, 15], [0, 0, 1], [0, 1]], ![[0, 27, 40], [33, 23, 24], [19, 18, 6], [35, 11, 29], [21, 20, 27], [31, 15, 3]], ![[0, 1], [3, 8, 29], [15, 3, 1], [39, 14, 42], [4, 23, 15], [0, 27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 22], []]
 b := ![[], [38, 10, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [29, 38, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6944712377, 3509332770, -821587240]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-161504939, 81612390, -19106680]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-39, -3, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-39, -3, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![8, 44, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-39, -3, 1], ![-275, 15, -5], ![707, -271, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -44, 47]], ![![-1, -1, 1], ![-5, 5, -5], ![13, -17, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [17, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 46], [0, 1]]
 g := ![![[6, 36], [36, 28], [16, 2], [42, 17], [1]], ![[0, 11], [0, 19], [0, 45], [0, 30], [1]]]
 h' := ![![[39, 46], [46, 41], [10, 13], [38, 40], [30, 39], [0, 1]], ![[0, 1], [0, 6], [0, 34], [0, 7], [0, 8], [39, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [17, 8, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1, -3261, 1322]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-225, -1307, 1322]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![5, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![5, 1, 0]] 
 ![![47, 0, 0], ![5, 1, 0], ![35, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![5, 1, 0], ![1, 5, 2], ![-272, 54, 6]]]
  hmulB := by decide  
  f := ![![![-687, -3512, -1406], ![-141, 33041, 0]], ![![-74, -370, -148], ![1, 3478, 0]], ![![-515, -2616, -1047], ![-73, 24605, 0]]]
  g := ![![![1, 0, 0], ![-5, 47, 0], ![-35, 0, 47]], ![![0, 1, 0], ![-2, 5, 2], ![-16, 54, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-39, -3, 1]] ![![47, 0, 0], ![5, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![235, 47, 0]], ![![-1833, -141, 47], ![-470, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![5, 1, 0]]], ![![![-39, -3, 1]], ![![-10, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![4, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![4, 1, 0]] 
 ![![53, 0, 0], ![4, 1, 0], ![19, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![4, 1, 0], ![1, 4, 2], ![-272, 54, 5]]]
  hmulB := by decide  
  f := ![![![-1107, -4477, -2240], ![-159, 59360, 0]], ![![-84, -336, -168], ![1, 4452, 0]], ![![-397, -1605, -803], ![-55, 21280, 0]]]
  g := ![![![1, 0, 0], ![-4, 53, 0], ![-19, 0, 53]], ![![0, 1, 0], ![-1, 4, 2], ![-11, 54, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -4, -1]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![23, -4, -1]] 
 ![![53, 0, 0], ![44, 1, 0], ![13, 0, 1]] where
  M :=![![![23, -4, -1], ![268, -31, -9], ![1197, -107, -35]]]
  hmulB := by decide  
  f := ![![![-122, 33, -5]], ![![-75, 20, -3]], ![![-189, 52, -8]]]
  g := ![![![4, -4, -1], ![33, -31, -9], ![120, -107, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![4, 1, 0]] ![![53, 0, 0], ![4, 1, 0]]
  ![![-122, 33, -5]] where
 M := ![![![2809, 0, 0], ![212, 53, 0]], ![![212, 53, 0], ![17, 8, 2]]]
 hmul := by decide  
 g := ![![![![1219, -212, -53]], ![![360, -47, -13]]], ![![![360, -47, -13]], ![![93, -10, -3]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-122, 33, -5]] ![![23, -4, -1]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![25, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![25, 1, 0]] 
 ![![59, 0, 0], ![25, 1, 0], ![42, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![25, 1, 0], ![1, 25, 2], ![-272, 54, 26]]]
  hmulB := by decide  
  f := ![![![-25, -650, -52], ![0, 1534, 0]], ![![-11, -275, -22], ![1, 649, 0]], ![![-25, -463, -37], ![17, 1092, 0]]]
  g := ![![![1, 0, 0], ![-25, 59, 0], ![-42, 0, 59]], ![![0, 1, 0], ![-12, 25, 2], ![-46, 54, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-23, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-23, 1, 0]] 
 ![![59, 0, 0], ![36, 1, 0], ![31, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-23, 1, 0], ![1, -23, 2], ![-272, 54, -22]]]
  hmulB := by decide  
  f := ![![![1422, -44299, 3854], ![-1298, -113693, 0]], ![![877, -27012, 2350], ![-766, -69325, 0]], ![![753, -23276, 2025], ![-667, -59737, 0]]]
  g := ![![![1, 0, 0], ![-36, 59, 0], ![-31, 0, 59]], ![![-1, 1, 0], ![13, -23, 2], ![-26, 54, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-82, 5, 2]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-82, 5, 2]] 
 ![![59, 0, 0], ![56, 1, 0], ![55, 0, 1]] where
  M :=![![![-82, 5, 2], ![-539, 26, 12], ![-1578, 52, 31]]]
  hmulB := by decide  
  f := ![![![-182, 51, -8]], ![![-135, 38, -6]], ![![-390, 109, -17]]]
  g := ![![![-8, 5, 2], ![-45, 26, 12], ![-105, 52, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![25, 1, 0]] ![![59, 0, 0], ![-23, 1, 0]]
  ![![-182, 51, -8]] where
 M := ![![![3481, 0, 0], ![-1357, 59, 0]], ![![1475, 59, 0], ![-574, 2, 2]]]
 hmul := by decide  
 g := ![![![![-4838, 295, 118]], ![![1347, -89, -34]]], ![![![-2589, 151, 62]], ![![726, -46, -18]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-182, 51, -8]] ![![-82, 5, 2]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 10, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 10, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![34, 10, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 10, 1], ![-262, 27, 21], ![-2829, 431, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -10, 61]], ![![-1, 0, 1], ![-16, -3, 21], ![-67, 1, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [44, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 60], [0, 1]]
 g := ![![[25, 60], [34], [2, 15], [8, 14], [59, 1]], ![[27, 1], [34], [33, 46], [41, 47], [57, 60]]]
 h' := ![![[59, 60], [26, 11], [34, 20], [14, 36], [27, 21], [0, 1]], ![[0, 1], [4, 50], [55, 41], [3, 25], [46, 40], [59, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [22, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [44, 2, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1480, -220, 222]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-148, -40, 222]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-21, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-21, 1, 0]] 
 ![![61, 0, 0], ![40, 1, 0], ![24, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-21, 1, 0], ![1, -21, 2], ![-272, 54, -20]]]
  hmulB := by decide  
  f := ![![![-234, 6695, -638], ![244, 19459, 0]], ![![-145, 4386, -418], ![184, 12749, 0]], ![![-90, 2634, -251], ![102, 7656, 0]]]
  g := ![![![1, 0, 0], ![-40, 61, 0], ![-24, 0, 61]], ![![-1, 1, 0], ![13, -21, 2], ![-32, 54, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-27, 10, 1]] ![![61, 0, 0], ![-21, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1281, 61, 0]], ![![-1647, 610, 61], ![305, -183, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-21, 1, 0]]], ![![![-27, 10, 1]], ![![5, -3, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-58, 15, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-58, 15, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![9, 15, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-58, 15, 1], ![-257, -4, 31], ![-4189, 701, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -15, 67]], ![![-1, 0, 1], ![-8, -7, 31], ![-64, 8, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [54, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 66], [0, 1]]
 g := ![![[51, 36], [29, 4], [1], [54], [49], [1]], ![[0, 31], [1, 63], [1], [54], [49], [1]]]
 h' := ![![[60, 66], [42, 6], [36, 65], [36, 1], [2, 11], [13, 60], [0, 1]], ![[0, 1], [0, 61], [50, 2], [29, 66], [59, 56], [62, 7], [60, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [53, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [54, 7, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31556, 5384, 1355]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-653, -223, 1355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-31, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-31, 1, 0]] 
 ![![67, 0, 0], ![36, 1, 0], ![56, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-31, 1, 0], ![1, -31, 2], ![-272, 54, -30]]]
  hmulB := by decide  
  f := ![![![940, -43509, 2808], ![-1005, -94068, 0]], ![![507, -23366, 1508], ![-535, -50518, 0]], ![![763, -36365, 2347], ![-889, -78624, 0]]]
  g := ![![![1, 0, 0], ![-36, 67, 0], ![-56, 0, 67]], ![![-1, 1, 0], ![15, -31, 2], ![-8, 54, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-58, 15, 1]] ![![67, 0, 0], ![-31, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2077, 67, 0]], ![![-3886, 1005, 67], ![1541, -469, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-31, 1, 0]]], ![![![-58, 15, 1]], ![![23, -7, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![15, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![15, 1, 0]] 
 ![![71, 0, 0], ![15, 1, 0], ![30, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![15, 1, 0], ![1, 15, 2], ![-272, 54, 16]]]
  hmulB := by decide  
  f := ![![![-326, -5129, -684], ![-71, 24282, 0]], ![![-72, -1080, -144], ![1, 5112, 0]], ![![-135, -2167, -289], ![-43, 10260, 0]]]
  g := ![![![1, 0, 0], ![-15, 71, 0], ![-30, 0, 71]], ![![0, 1, 0], ![-4, 15, 2], ![-22, 54, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-10, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-10, 1, 0]] 
 ![![71, 0, 0], ![61, 1, 0], ![57, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-10, 1, 0], ![1, -10, 2], ![-272, 54, -9]]]
  hmulB := by decide  
  f := ![![![-301, 3218, -644], ![142, 22862, 0]], ![![-255, 2758, -552], ![143, 19596, 0]], ![![-247, 2584, -517], ![76, 18354, 0]]]
  g := ![![![1, 0, 0], ![-61, 71, 0], ![-57, 0, 71]], ![![-1, 1, 0], ![7, -10, 2], ![-43, 54, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![71, 0, 0], ![65, 1, 0], ![18, 0, 1]] where
  M :=![![![-6, 1, 0], ![1, -6, 2], ![-272, 54, -5]]]
  hmulB := by decide  
  f := ![![![78, -5, -2]], ![![79, -5, -2]], ![![42, -2, -1]]]
  g := ![![![-1, 1, 0], ![5, -6, 2], ![-52, 54, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![15, 1, 0]] ![![71, 0, 0], ![-10, 1, 0]]
  ![![78, -5, -2]] where
 M := ![![![5041, 0, 0], ![-710, 71, 0]], ![![1065, 71, 0], ![-149, 5, 2]]]
 hmul := by decide  
 g := ![![![![-426, 71, 0]], ![![61, -16, 2]]], ![![![-89, 9, 2]], ![![5, -1, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![78, -5, -2]] ![![-6, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3612, 1003, -155]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-3612, 1003, -155]] 
 ![![73, 0, 0], ![0, 73, 0], ![12, 67, 1]] where
  M :=![![![-3612, 1003, -155], ![43163, -11982, 1851], ![-255921, 71057, -10979]]]
  hmulB := by decide  
  f := ![![![-327, 26, 9]], ![![-2422, 159, 61]], ![![-2387, 156, 60]]]
  g := ![![![-24, 156, -155], ![287, -1863, 1851], ![-1701, 11050, -10979]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [65, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 72], [0, 1]]
 g := ![![[59, 9], [24], [72], [25, 27], [61], [1]], ![[0, 64], [24], [72], [67, 46], [61], [1]]]
 h' := ![![[34, 72], [44, 3], [61, 43], [54, 46], [41, 63], [8, 34], [0, 1]], ![[0, 1], [0, 70], [63, 30], [12, 27], [66, 10], [69, 39], [34, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [9, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [65, 39, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3915, -1848, 381]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -375, 381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-327, 26, 9]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-327, 26, 9]] 
 ![![73, 0, 0], ![11, 1, 0], ![13, 0, 1]] where
  M :=![![![-327, 26, 9], ![-2422, 159, 61], ![-8053, 423, 185]]]
  hmulB := by decide  
  f := ![![![-3612, 1003, -155]], ![![47, -13, 2]], ![![-4149, 1152, -178]]]
  g := ![![![-10, 26, 9], ![-68, 159, 61], ![-207, 423, 185]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-3612, 1003, -155]] ![![-327, 26, 9]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-28, 32, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-28, 32, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![51, 32, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-28, 32, 1], ![-240, 26, 65], ![-8813, 1619, 58]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -32, 79]], ![![-1, 0, 1], ![-45, -26, 65], ![-149, -3, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [11, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 78], [0, 1]]
 g := ![![[16, 36], [62, 21], [2, 44], [21, 67], [8], [1]], ![[0, 43], [0, 58], [0, 35], [0, 12], [8], [1]]]
 h' := ![![[61, 78], [29, 6], [57, 69], [6, 53], [33, 15], [68, 61], [0, 1]], ![[0, 1], [0, 73], [0, 10], [0, 26], [0, 64], [76, 18], [61, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [40, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [11, 18, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3868, -1290, 962]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-670, -406, 962]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![14, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![14, 1, 0]] 
 ![![79, 0, 0], ![14, 1, 0], ![21, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![14, 1, 0], ![1, 14, 2], ![-272, 54, 15]]]
  hmulB := by decide  
  f := ![![![-858, -12611, -1802], ![-237, 71179, 0]], ![![-159, -2226, -318], ![1, 12561, 0]], ![![-238, -3353, -479], ![-7, 18921, 0]]]
  g := ![![![1, 0, 0], ![-14, 79, 0], ![-21, 0, 79]], ![![0, 1, 0], ![-3, 14, 2], ![-17, 54, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-28, 32, 1]] ![![79, 0, 0], ![14, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1106, 79, 0]], ![![-2212, 2528, 79], ![-632, 474, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![14, 1, 0]]], ![![![-28, 32, 1]], ![![-8, 6, 1]]]]
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


lemma PB188I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB188I1 : PrimesBelowBoundCertificateInterval O 31 79 188 where
  m := 11
  g := ![1, 2, 1, 2, 3, 3, 2, 2, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB188I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
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
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
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
  β := ![I41N1, I47N1, I53N0, I53N1, I59N0, I59N1, I59N2, I61N1, I67N1, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[], [I41N1], [], [I47N1], [I53N0, I53N0, I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
