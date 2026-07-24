
import IdealArithmetic.Examples.NF3_3_455700_1.RI3_3_455700_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-39, 4, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-39, 4, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![35, 4, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-39, 4, 1], ![-248, 15, 13], ![-1074, 150, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -4, 37]], ![![-2, 0, 1], ![-19, -1, 13], ![-47, 2, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [15, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 36], [0, 1]]
 g := ![![[27, 34], [21], [14, 3], [4], [1]], ![[21, 3], [21], [20, 34], [4], [1]]]
 h' := ![![[2, 36], [14, 21], [12, 13], [17, 22], [22, 2], [0, 1]], ![[0, 1], [19, 16], [1, 24], [24, 15], [26, 35], [2, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [33, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [15, 35, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2124, -303, 396]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-432, -51, 396]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-13, 1, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![18, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-13, 1, 0], ![1, -13, 3], ![-252, 54, -12]]]
  hmulB := by decide  
  f := ![![![-265, 4634, -1071], ![259, 13209, 0]], ![![-178, 2999, -693], ![149, 8547, 0]], ![![-124, 2254, -521], ![140, 6426, 0]]]
  g := ![![![1, 0, 0], ![-24, 37, 0], ![-18, 0, 37]], ![![-1, 1, 0], ![7, -13, 3], ![-36, 54, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-39, 4, 1]] ![![37, 0, 0], ![-13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-481, 37, 0]], ![![-1443, 148, 37], ![259, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-13, 1, 0]]], ![![![-39, 4, 1]], ![![7, -1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![279, -32, -11]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![279, -32, -11]] 
 ![![41, 0, 0], ![0, 41, 0], ![38, 29, 1]] where
  M :=![![![279, -32, -11], ![2740, -315, -107], ![8790, -1002, -347]]]
  hmulB := by decide  
  f := ![![![-51, 2, 1]], ![![-250, 3, 7]], ![![-238, 5, 6]]]
  g := ![![![17, 7, -11], ![166, 68, -107], ![536, 221, -347]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [36, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 40], [0, 1]]
 g := ![![[2, 8], [9], [16], [34, 18], [1]], ![[0, 33], [9], [16], [9, 23], [1]]]
 h' := ![![[10, 40], [12, 7], [34, 3], [6, 4], [5, 10], [0, 1]], ![[0, 1], [0, 34], [23, 38], [5, 37], [23, 31], [10, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [24, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [36, 31, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1064355, -1146873, 939404]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-896627, -692429, 939404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![41, 0, 0], ![35, 1, 0], ![2, 0, 1]] where
  M :=![![![-6, 1, 0], ![1, -6, 3], ![-252, 54, -5]]]
  hmulB := by decide  
  f := ![![![-132, 5, 3]], ![![-131, 5, 3]], ![![-42, 2, 1]]]
  g := ![![![-1, 1, 0], ![5, -6, 3], ![-52, 54, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![279, -32, -11]] ![![-6, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1066, -123, -41]]]
 hmul := by decide  
 g := ![![![![26, -3, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-27, 19, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-27, 19, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![16, 19, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-27, 19, 1], ![-233, 27, 58], ![-4854, 960, 46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -19, 43]], ![![-1, 0, 1], ![-27, -25, 58], ![-130, 2, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [28, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[10, 14], [26, 4], [17], [1, 11], [1]], ![[3, 29], [24, 39], [17], [17, 32], [1]]]
 h' := ![![[21, 42], [3, 10], [7, 2], [15, 24], [15, 21], [0, 1]], ![[0, 1], [41, 33], [6, 41], [3, 19], [26, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [33, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [28, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![283, -3972, 2509]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-927, -1201, 2509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-15, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-15, 1, 0]] 
 ![![43, 0, 0], ![28, 1, 0], ![40, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-15, 1, 0], ![1, -15, 3], ![-252, 54, -14]]]
  hmulB := by decide  
  f := ![![![-244, 4795, -960], ![215, 13760, 0]], ![![-162, 3117, -624], ![130, 8944, 0]], ![![-220, 4460, -893], ![220, 12800, 0]]]
  g := ![![![1, 0, 0], ![-28, 43, 0], ![-40, 0, 43]], ![![-1, 1, 0], ![7, -15, 3], ![-28, 54, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-27, 19, 1]] ![![43, 0, 0], ![-15, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-645, 43, 0]], ![![-1161, 817, 43], ![172, -258, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-15, 1, 0]]], ![![![-27, 19, 1]], ![![4, -6, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-26, 10, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-26, 10, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![21, 10, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-26, 10, 1], ![-242, 28, 31], ![-2586, 474, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -10, 47]], ![![-1, 0, 1], ![-19, -6, 31], ![-72, 2, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [25, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 46], [0, 1]]
 g := ![![[43, 32], [18, 34], [14, 24], [10, 36], [1]], ![[0, 15], [34, 13], [17, 23], [38, 11], [1]]]
 h' := ![![[6, 46], [20, 28], [26, 38], [32, 20], [22, 6], [0, 1]], ![[0, 1], [0, 19], [19, 9], [11, 27], [11, 41], [6, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [19, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [25, 41, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2120, -309, 378]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-214, -87, 378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![16, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![16, 1, 0]] 
 ![![47, 0, 0], ![16, 1, 0], ![9, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![16, 1, 0], ![1, 16, 3], ![-252, 54, 17]]]
  hmulB := by decide  
  f := ![![![56, 1390, 261], ![94, -4089, 0]], ![![13, 463, 87], ![48, -1363, 0]], ![![8, 266, 50], ![26, -783, 0]]]
  g := ![![![1, 0, 0], ![-16, 47, 0], ![-9, 0, 47]], ![![0, 1, 0], ![-6, 16, 3], ![-27, 54, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-26, 10, 1]] ![![47, 0, 0], ![16, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![752, 47, 0]], ![![-1222, 470, 47], ![-658, 188, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![16, 1, 0]]], ![![![-26, 10, 1]], ![![-14, 4, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [51, 11, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 37, 27], [46, 15, 26], [0, 1]]
 g := ![![[21, 46, 10], [32, 11], [33, 34, 49], [23, 6], [1]], ![[18, 17, 36, 30], [1, 4], [33, 44, 27, 14], [35, 44], [7, 28, 52, 20]], ![[2, 26, 15, 50], [21, 36], [37, 17, 3, 31], [21, 4], [15, 45, 40, 33]]]
 h' := ![![[42, 37, 27], [21, 25, 13], [13, 32, 45], [50, 33, 46], [2, 42, 35], [0, 1]], ![[46, 15, 26], [44, 12, 22], [28, 5, 2], [28, 37, 44], [8, 1, 16], [42, 37, 27]], ![[0, 1], [29, 16, 18], [27, 16, 6], [14, 36, 16], [5, 10, 2], [46, 15, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 33], []]
 b := ![[], [1, 25, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [51, 11, 18, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25289427, 3424542, 1109449]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-477159, 64614, 20933]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-31, 8, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-31, 8, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![28, 8, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-31, 8, 1], ![-244, 23, 25], ![-2082, 366, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -8, 59]], ![![-1, 0, 1], ![-16, -3, 25], ![-50, 2, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [5, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 58], [0, 1]]
 g := ![![[45, 12], [13, 57], [22], [28, 4], [11, 1]], ![[0, 47], [50, 2], [22], [13, 55], [22, 58]]]
 h' := ![![[11, 58], [53, 22], [20, 23], [37, 9], [4, 57], [0, 1]], ![[0, 1], [0, 37], [37, 36], [18, 50], [41, 2], [11, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [41, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [5, 48, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5832, -3138, 1127]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-436, -206, 1127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-25, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-25, 1, 0]] 
 ![![59, 0, 0], ![34, 1, 0], ![28, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-25, 1, 0], ![1, -25, 3], ![-252, 54, -24]]]
  hmulB := by decide  
  f := ![![![-1313, 47826, -5742], ![1416, 112926, 0]], ![![-751, 27536, -3306], ![827, 65018, 0]], ![![-621, 22697, -2725], ![677, 53592, 0]]]
  g := ![![![1, 0, 0], ![-34, 59, 0], ![-28, 0, 59]], ![![-1, 1, 0], ![13, -25, 3], ![-24, 54, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-31, 8, 1]] ![![59, 0, 0], ![-25, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1475, 59, 0]], ![![-1829, 472, 59], ![531, -177, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-25, 1, 0]]], ![![![-31, 8, 1]], ![![9, -3, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-10, -4, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-10, -4, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![51, 57, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-10, -4, 1], ![-256, 44, -11], ![942, -282, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -57, 61]], ![![-1, -1, 1], ![5, 11, -11], ![-18, -42, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [19, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 60], [0, 1]]
 g := ![![[13, 45], [42], [1, 16], [24, 39], [58, 1]], ![[0, 16], [42], [14, 45], [29, 22], [55, 60]]]
 h' := ![![[58, 60], [51, 17], [42, 46], [32, 57], [57, 51], [0, 1]], ![[0, 1], [0, 44], [26, 15], [44, 4], [26, 10], [58, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [31, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [19, 3, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5370, -1721, 2001]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1761, -1898, 2001]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![11, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![11, 1, 0]] 
 ![![61, 0, 0], ![11, 1, 0], ![21, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![11, 1, 0], ![1, 11, 3], ![-252, 54, 12]]]
  hmulB := by decide  
  f := ![![![-1689, -19790, -5400], ![-610, 109800, 0]], ![![-313, -3563, -972], ![-60, 19764, 0]], ![![-582, -6813, -1859], ![-207, 37800, 0]]]
  g := ![![![1, 0, 0], ![-11, 61, 0], ![-21, 0, 61]], ![![0, 1, 0], ![-3, 11, 3], ![-18, 54, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-10, -4, 1]] ![![61, 0, 0], ![11, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![671, 61, 0]], ![![-610, -244, 61], ![-366, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![11, 1, 0]]], ![![![-10, -4, 1]], ![![-6, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [64, 38, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 36, 15], [53, 30, 52], [0, 1]]
 g := ![![[64, 56, 60], [14, 4, 60], [16, 19], [53, 15], [44, 1], []], ![[30, 16, 35, 35], [10, 53, 31, 49], [23, 19], [44, 35], [31, 29], [59, 24]], ![[44, 26, 7, 46], [15, 54, 23, 7], [], [32, 19], [27, 23], [22, 24]]]
 h' := ![![[58, 36, 15], [42, 5, 23], [18, 33, 23], [29, 17, 35], [65, 6, 22], [0, 0, 1], [0, 1]], ![[53, 30, 52], [35, 21, 28], [27, 24, 46], [62, 3, 32], [59, 61, 13], [57, 63, 30], [58, 36, 15]], ![[0, 1], [35, 41, 16], [21, 10, 65], [50, 47], [50, 0, 32], [61, 4, 36], [53, 30, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 13], []]
 b := ![[], [50, 7, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [64, 38, 23, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13120476, 7075200, -2739630]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-195828, 105600, -40890]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-3, 32, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-3, 32, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![68, 32, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-3, 32, 1], ![-220, 51, 97], ![-8130, 1662, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -32, 71]], ![![-1, 0, 1], ![-96, -43, 97], ![-194, -14, 83]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [68, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 70], [0, 1]]
 g := ![![[51, 15], [16, 38], [7, 16], [32], [50], [1]], ![[3, 56], [8, 33], [41, 55], [32], [50], [1]]]
 h' := ![![[11, 70], [48, 21], [21, 31], [30, 67], [17, 48], [3, 11], [0, 1]], ![[0, 1], [66, 50], [7, 40], [57, 4], [48, 23], [53, 60], [11, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [54, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [68, 60, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44224, -18080, 6180]
  a := ![4, -10, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5296, -3040, 6180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-26, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-26, 1, 0]] 
 ![![71, 0, 0], ![45, 1, 0], ![59, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-26, 1, 0], ![1, -26, 3], ![-252, 54, -25]]]
  hmulB := by decide  
  f := ![![![-1169, 40545, -4680], ![1065, 110760, 0]], ![![-753, 25679, -2964], ![640, 70148, 0]], ![![-989, 33693, -3889], ![837, 92040, 0]]]
  g := ![![![1, 0, 0], ![-45, 71, 0], ![-59, 0, 71]], ![![-1, 1, 0], ![14, -26, 3], ![-17, 54, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-3, 32, 1]] ![![71, 0, 0], ![-26, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1846, 71, 0]], ![![-213, 2272, 71], ![-142, -781, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-26, 1, 0]]], ![![![-3, 32, 1]], ![![-2, -11, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-7, -32, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-7, -32, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![66, 41, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-7, -32, 1], ![-284, 47, -95], ![7998, -1794, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -41, 73]], ![![-1, -1, 1], ![82, 54, -95], ![96, -33, 15]]]
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
  c := ![-39681, -58738, 48259]
  a := ![14, -1, 29]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44175, -27909, 48259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![22, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![22, 1, 0]] 
 ![![73, 0, 0], ![22, 1, 0], ![58, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![22, 1, 0], ![1, 22, 3], ![-252, 54, 23]]]
  hmulB := by decide  
  f := ![![![539, 14734, 2010], ![438, -48910, 0]], ![![157, 4420, 603], ![147, -14673, 0]], ![![440, 11707, 1597], ![309, -38860, 0]]]
  g := ![![![1, 0, 0], ![-22, 73, 0], ![-58, 0, 73]], ![![0, 1, 0], ![-9, 22, 3], ![-38, 54, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-7, -32, 1]] ![![73, 0, 0], ![22, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1606, 73, 0]], ![![-511, -2336, 73], ![-438, -657, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![22, 1, 0]]], ![![![-7, -32, 1]], ![![-6, -9, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-44, -2, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-44, -2, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![35, 77, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-44, -2, 1], ![-254, 10, -5], ![438, -174, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -77, 79]], ![![-1, -1, 1], ![-1, 5, -5], ![2, -10, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [75, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 78], [0, 1]]
 g := ![![[48, 4], [45, 45], [50, 9], [37, 9], [50], [1]], ![[26, 75], [74, 34], [40, 70], [27, 70], [50], [1]]]
 h' := ![![[34, 78], [22, 77], [42, 19], [69, 76], [58, 76], [4, 34], [0, 1]], ![[0, 1], [33, 2], [56, 60], [46, 3], [35, 3], [54, 45], [34, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [46, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [75, 45, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1991, 186, 65]
  a := ![0, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -61, 65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![5, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![5, 1, 0]] 
 ![![79, 0, 0], ![5, 1, 0], ![71, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![5, 1, 0], ![1, 5, 3], ![-252, 54, 6]]]
  hmulB := by decide  
  f := ![![![-575, -2880, -1728], ![0, 45504, 0]], ![![-36, -180, -108], ![1, 2844, 0]], ![![-515, -2588, -1553], ![-28, 40896, 0]]]
  g := ![![![1, 0, 0], ![-5, 79, 0], ![-71, 0, 79]], ![![0, 1, 0], ![-3, 5, 3], ![-12, 54, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-44, -2, 1]] ![![79, 0, 0], ![5, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![395, 79, 0]], ![![-3476, -158, 79], ![-474, 0, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![5, 1, 0]]], ![![![-44, -2, 1]], ![![-6, 0, 0]]]]
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


lemma PB151I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB151I1 : PrimesBelowBoundCertificateInterval O 31 79 151 where
  m := 11
  g := ![2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB151I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
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
      exact NI37N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
      exact NI79N1
  β := ![I37N1, I41N1, I43N1, I47N1, I59N1, I61N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [], [I59N1], [I61N1], [], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
