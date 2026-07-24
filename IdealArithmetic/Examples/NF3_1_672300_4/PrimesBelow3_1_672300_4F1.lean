
import IdealArithmetic.Examples.NF3_1_672300_4.RI3_1_672300_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, 1, 0]] 
 ![![37, 0, 0], ![15, 1, 0], ![2, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, 1, 0], ![2, 14, 7], ![156, -9, 16]]]
  hmulB := by decide  
  f := ![![![221, 1956, 980], ![148, -5180, 0]], ![![82, 782, 392], ![75, -2072, 0]], ![![1, 105, 53], ![35, -280, 0]]]
  g := ![![![1, 0, 0], ![-15, 37, 0], ![-2, 0, 37]], ![![0, 1, 0], ![-6, 14, 7], ![7, -9, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, -8, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![67, -8, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![6, 0, 1]] where
  M :=![![![67, -8, 0], ![-16, 75, -56], ![-1248, 72, 59]]]
  hmulB := by decide  
  f := ![![![-8457, -472, -448]], ![![-7400, -413, -392]], ![![-3870, -216, -205]]]
  g := ![![![7, -8, 0], ![-40, 75, -56], ![-90, 72, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-2, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-2, 1, 0]] 
 ![![37, 0, 0], ![35, 1, 0], ![10, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-2, 1, 0], ![2, -3, 7], ![156, -9, -1]]]
  hmulB := by decide  
  f := ![![![647, -971, 2268], ![-37, -11988, 0]], ![![611, -917, 2142], ![-36, -11322, 0]], ![![176, -263, 613], ![11, -3240, 0]]]
  g := ![![![1, 0, 0], ![-35, 37, 0], ![-10, 0, 37]], ![![-1, 1, 0], ![1, -3, 7], ![13, -9, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, 1, 0]] ![![67, -8, 0]]
  ![![37, 0, 0], ![20, 16, 1]] where
 M := ![![![2479, -296, 0]], ![![989, -45, -56]]]
 hmul := by decide  
 g := ![![![![47, -24, -1], ![37, 0, 0]]], ![![![17, -9, -2], ![18, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![20, 16, 1]] ![![37, 0, 0], ![-2, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-74, 37, 0]], ![![740, 592, 37], ![148, -37, 111]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-2, 1, 0]]], ![![![20, 16, 1]], ![![4, -1, 3]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![4, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![4, 1, 0]] 
 ![![41, 0, 0], ![4, 1, 0], ![22, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![4, 1, 0], ![2, 3, 7], ![156, -9, 5]]]
  hmulB := by decide  
  f := ![![![1527, 2319, 5425], ![246, -31775, 0]], ![![146, 224, 525], ![42, -3075, 0]], ![![818, 1244, 2911], ![146, -17050, 0]]]
  g := ![![![1, 0, 0], ![-4, 41, 0], ![-22, 0, 41]], ![![0, 1, 0], ![-4, 3, 7], ![2, -9, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![27, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![2, 13, 7], ![156, -9, 15]]]
  hmulB := by decide  
  f := ![![![23, 233, 126], ![41, -738, 0]], ![![-2, 77, 42], ![42, -246, 0]], ![![9, 153, 83], ![45, -486, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-27, 0, 41]], ![![0, 1, 0], ![-9, 13, 7], ![-3, -9, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-18, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-18, 1, 0]] 
 ![![41, 0, 0], ![23, 1, 0], ![10, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-18, 1, 0], ![2, -19, 7], ![156, -9, -17]]]
  hmulB := by decide  
  f := ![![![717, -9012, 3325], ![-533, -19475, 0]], ![![407, -5047, 1862], ![-286, -10906, 0]], ![![192, -2199, 811], ![-91, -4750, 0]]]
  g := ![![![1, 0, 0], ![-23, 41, 0], ![-10, 0, 41]], ![![-1, 1, 0], ![9, -19, 7], ![13, -9, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![4, 1, 0]] ![![41, 0, 0], ![14, 1, 0]]
  ![![41, 0, 0], ![20, 20, 1]] where
 M := ![![![1681, 0, 0], ![574, 41, 0]], ![![164, 41, 0], ![58, 17, 7]]]
 hmul := by decide  
 g := ![![![![21, -20, -1], ![41, 0, 0]], ![![-6, -19, -1], ![41, 0, 0]]], ![![![-16, -19, -1], ![41, 0, 0]], ![![-2, -3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![20, 20, 1]] ![![41, 0, 0], ![-18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-738, 41, 0]], ![![820, 820, 41], ![-164, -369, 123]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-18, 1, 0]]], ![![![20, 20, 1]], ![![-4, -9, 3]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![0, 8, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![0, 8, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 8, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![0, 8, 1], ![172, -17, 57], ![1290, -51, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, -7, -1], ![43, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -8, 43]], ![![0, 0, 1], ![4, -11, 57], ![30, -1, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 14, 1] where
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
 g := ![![[32, 24], [27, 14], [16], [31, 24], [1]], ![[40, 19], [3, 29], [16], [39, 19], [1]]]
 h' := ![![[29, 42], [7, 14], [34, 33], [16, 4], [13, 29], [0, 1]], ![[0, 1], [26, 29], [2, 10], [3, 39], [37, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [10, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2064, 1029, -511]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 119, -511]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 1, 0]] 
 ![![43, 0, 0], ![29, 1, 0], ![1, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 1, 0], ![2, -15, 7], ![156, -9, -13]]]
  hmulB := by decide  
  f := ![![![-203, 1842, -861], ![129, 5289, 0]], ![![-135, 1228, -574], ![87, 3526, 0]], ![![7, 42, -20], ![39, 123, 0]]]
  g := ![![![1, 0, 0], ![-29, 43, 0], ![-1, 0, 43]], ![![-1, 1, 0], ![10, -15, 7], ![10, -9, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![0, 8, 1]] ![![43, 0, 0], ![-14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-602, 43, 0]], ![![0, 344, 43], ![172, -129, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-14, 1, 0]]], ![![![0, 8, 1]], ![![4, -3, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![0, 16, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![0, 16, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 16, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![0, 16, 1], ![188, -25, 113], ![2538, -123, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, -15, -1], ![47, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -16, 47]], ![![0, 0, 1], ![4, -39, 113], ![54, -5, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [29, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 46], [0, 1]]
 g := ![![[20, 9], [5, 37], [28, 32], [28, 21], [1]], ![[17, 38], [24, 10], [33, 15], [21, 26], [1]]]
 h' := ![![[31, 46], [43, 3], [34, 15], [34, 19], [18, 31], [0, 1]], ![[0, 1], [42, 44], [29, 32], [12, 28], [39, 16], [31, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [16, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [29, 16, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14288, 8269, -2453]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-304, 1011, -2453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-19, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-19, 1, 0]] 
 ![![47, 0, 0], ![28, 1, 0], ![40, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-19, 1, 0], ![2, -20, 7], ![156, -9, -18]]]
  hmulB := by decide  
  f := ![![![930, -11747, 4116], ![-611, -27636, 0]], ![![568, -6993, 2450], ![-328, -16450, 0]], ![![802, -9998, 3503], ![-494, -23520, 0]]]
  g := ![![![1, 0, 0], ![-28, 47, 0], ![-40, 0, 47]], ![![-1, 1, 0], ![6, -20, 7], ![24, -9, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![0, 16, 1]] ![![47, 0, 0], ![-19, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-893, 47, 0]], ![![0, 752, 47], ![188, -329, 94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-19, 1, 0]]], ![![![0, 16, 1]], ![![4, -7, 2]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, 21, 20]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![379, 21, 20]] 
 ![![53, 0, 0], ![0, 53, 0], ![11, 9, 1]] where
  M :=![![![379, 21, 20], ![3162, 178, 167], ![4116, 231, 220]]]
  hmulB := by decide  
  f := ![![![11, 0, -1]], ![![-156, 20, -1]], ![![-25, 3, 0]]]
  g := ![![![3, -3, 20], ![25, -25, 167], ![32, -33, 220]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [21, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 52], [0, 1]]
 g := ![![[48, 9], [1], [43, 17], [29], [52, 1]], ![[39, 44], [1], [26, 36], [29], [51, 52]]]
 h' := ![![[52, 52], [36, 3], [51, 52], [44, 32], [21, 33], [0, 1]], ![[0, 1], [33, 50], [52, 1], [12, 21], [41, 20], [52, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [23, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [21, 1, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1543385, 838519, -331108]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![97841, 72047, -331108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 0, 1]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-11, 0, 1]] 
 ![![53, 0, 0], ![42, 1, 0], ![42, 0, 1]] where
  M :=![![![-11, 0, 1], ![156, -20, 1], ![42, 21, -20]]]
  hmulB := by decide  
  f := ![![![-379, -21, -20]], ![![-360, -20, -19]], ![![-378, -21, -20]]]
  g := ![![![-1, 0, 1], ![18, -20, 1], ![0, 21, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![379, 21, 20]] ![![-11, 0, 1]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [53, 37, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 58, 22], [34, 0, 37], [0, 1]]
 g := ![![[36, 24, 41], [13, 46, 1], [24, 51], [25, 56, 19], [1]], ![[47, 57, 13, 53], [25, 6, 44, 29], [54, 26], [42, 51, 42, 41], [56, 49, 2, 28]], ![[31, 47, 47, 40], [46, 22, 44, 37], [45, 1], [31, 20, 23, 55], [1, 17, 21, 31]]]
 h' := ![![[39, 58, 22], [19, 57, 49], [47, 16, 1], [32, 37, 13], [6, 22, 14], [0, 1]], ![[34, 0, 37], [6, 40, 15], [45, 51, 57], [4, 8, 47], [6, 31, 12], [39, 58, 22]], ![[0, 1], [23, 21, 54], [41, 51, 1], [40, 14, 58], [16, 6, 33], [34, 0, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 56], []]
 b := ![[], [1, 43, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [53, 37, 45, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22509916, 2703616, -332052]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-381524, 45824, -5628]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![12, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![12, 1, 0]] 
 ![![61, 0, 0], ![12, 1, 0], ![25, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![12, 1, 0], ![2, 11, 7], ![156, -9, 13]]]
  hmulB := by decide  
  f := ![![![3381, 19695, 12544], ![1037, -109312, 0]], ![![656, 3868, 2464], ![245, -21472, 0]], ![![1389, 8072, 5141], ![408, -44800, 0]]]
  g := ![![![1, 0, 0], ![-12, 61, 0], ![-25, 0, 61]], ![![0, 1, 0], ![-5, 11, 7], ![-1, -9, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![19, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![19, 1, 0]] 
 ![![61, 0, 0], ![19, 1, 0], ![56, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![19, 1, 0], ![2, 18, 7], ![156, -9, 20]]]
  hmulB := by decide  
  f := ![![![858, 8903, 3465], ![427, -30195, 0]], ![![251, 2769, 1078], ![184, -9394, 0]], ![![783, 8173, 3181], ![407, -27720, 0]]]
  g := ![![![1, 0, 0], ![-19, 61, 0], ![-56, 0, 61]], ![![0, 1, 0], ![-12, 18, 7], ![-13, -9, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![30, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![30, 1, 0]] 
 ![![61, 0, 0], ![30, 1, 0], ![59, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![30, 1, 0], ![2, 29, 7], ![156, -9, 31]]]
  hmulB := by decide  
  f := ![![![3077, 63264, 15281], ![2623, -133163, 0]], ![![1516, 31096, 7511], ![1282, -65453, 0]], ![![2983, 61190, 14780], ![2523, -128797, 0]]]
  g := ![![![1, 0, 0], ![-30, 61, 0], ![-59, 0, 61]], ![![0, 1, 0], ![-21, 29, 7], ![-23, -9, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![12, 1, 0]] ![![61, 0, 0], ![19, 1, 0]]
  ![![61, 0, 0], ![-2, 13, 1]] where
 M := ![![![3721, 0, 0], ![1159, 61, 0]], ![![732, 61, 0], ![230, 30, 7]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![19, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![4, -1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-2, 13, 1]] ![![61, 0, 0], ![30, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1830, 61, 0]], ![![-122, 793, 61], ![122, 366, 122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![30, 1, 0]]], ![![![-2, 13, 1]], ![![2, 6, 2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![2, 24, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![2, 24, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![2, 24, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![2, 24, 1], ![204, -31, 169], ![3786, -195, 17]]]
  hmulB := by decide  
  f := ![![![-1, -24, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -24, 67]], ![![0, 0, 1], ![-2, -61, 169], ![56, -9, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [4, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 66], [0, 1]]
 g := ![![[57, 17], [5, 25], [65], [29], [59], [1]], ![[0, 50], [0, 42], [65], [29], [59], [1]]]
 h' := ![![[40, 66], [47, 34], [1, 5], [44, 20], [48, 30], [63, 40], [0, 1]], ![[0, 1], [0, 33], [0, 62], [40, 47], [42, 37], [55, 27], [40, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [43, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [4, 27, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2012, 1029, -602]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 231, -602]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![32, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![32, 1, 0]] 
 ![![67, 0, 0], ![32, 1, 0], ![50, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![32, 1, 0], ![2, 31, 7], ![156, -9, 33]]]
  hmulB := by decide  
  f := ![![![-1279, -27265, -6160], ![-1005, 58960, 0]], ![![-616, -13013, -2940], ![-468, 28140, 0]], ![![-954, -20347, -4597], ![-751, 44000, 0]]]
  g := ![![![1, 0, 0], ![-32, 67, 0], ![-50, 0, 67]], ![![0, 1, 0], ![-20, 31, 7], ![-18, -9, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![2, 24, 1]] ![![67, 0, 0], ![32, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2144, 67, 0]], ![![134, 1608, 67], ![268, 737, 201]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![32, 1, 0]]], ![![![2, 24, 1]], ![![4, 11, 3]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-26, -28, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-26, -28, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![45, 43, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-26, -28, 1], ![100, -7, -195], ![-4326, 273, -63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -43, 71]], ![![-1, -1, 1], ![125, 118, -195], ![-21, 42, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [57, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 70], [0, 1]]
 g := ![![[50, 5], [2, 57], [28, 20], [4], [29], [1]], ![[0, 66], [0, 14], [41, 51], [4], [29], [1]]]
 h' := ![![[61, 70], [28, 17], [37, 25], [5, 37], [34, 69], [14, 61], [0, 1]], ![[0, 1], [0, 54], [0, 46], [61, 34], [54, 2], [43, 10], [61, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [50, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [57, 10, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61104, -1176, 1888]
  a := ![3, 18, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-336, -1160, 1888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-18, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-18, 1, 0]] 
 ![![71, 0, 0], ![53, 1, 0], ![63, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-18, 1, 0], ![2, -19, 7], ![156, -9, -17]]]
  hmulB := by decide  
  f := ![![![7071, -73795, 27202], ![-2769, -275906, 0]], ![![5279, -55071, 20300], ![-2058, -205900, 0]], ![![6273, -65480, 24137], ![-2462, -244818, 0]]]
  g := ![![![1, 0, 0], ![-53, 71, 0], ![-63, 0, 71]], ![![-1, 1, 0], ![8, -19, 7], ![24, -9, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-26, -28, 1]] ![![71, 0, 0], ![-18, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1278, 71, 0]], ![![-1846, -1988, 71], ![568, 497, -213]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-18, 1, 0]]], ![![![-26, -28, 1]], ![![8, 7, -3]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-17, 4, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-17, 4, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![56, 4, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-17, 4, 1], ![164, -30, 29], ![666, -15, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -4, 73]], ![![-1, 0, 1], ![-20, -2, 29], ![26, 1, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [69, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 72], [0, 1]]
 g := ![![[69, 18], [55], [46], [1, 27], [37], [1]], ![[0, 55], [55], [46], [7, 46], [37], [1]]]
 h' := ![![[57, 72], [70, 50], [54, 37], [4, 51], [18, 10], [4, 57], [0, 1]], ![[0, 1], [0, 23], [46, 36], [64, 22], [4, 63], [41, 16], [57, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [30, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [69, 16, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8218, 2844, -968]
  a := ![-3, 4, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![630, 92, -968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-29, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-29, 1, 0]] 
 ![![73, 0, 0], ![44, 1, 0], ![22, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-29, 1, 0], ![2, -30, 7], ![156, -9, -28]]]
  hmulB := by decide  
  f := ![![![-332, 6297, -1470], ![219, 15330, 0]], ![![-193, 3778, -882], ![147, 9198, 0]], ![![-79, 1897, -443], ![119, 4620, 0]]]
  g := ![![![1, 0, 0], ![-44, 73, 0], ![-22, 0, 73]], ![![-1, 1, 0], ![16, -30, 7], ![16, -9, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-17, 4, 1]] ![![73, 0, 0], ![-29, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2117, 73, 0]], ![![-1241, 292, 73], ![657, -146, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-29, 1, 0]]], ![![![-17, 4, 1]], ![![9, -2, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-19, -13, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-19, -13, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![60, 66, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-19, -13, 1], ![130, -15, -90], ![-1986, 138, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -66, 79]], ![![-1, -1, 1], ![70, 75, -90], ![6, 36, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [38, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 78], [0, 1]]
 g := ![![[2, 52], [34, 9], [71, 22], [45, 32], [9], [1]], ![[0, 27], [61, 70], [58, 57], [62, 47], [9], [1]]]
 h' := ![![[3, 78], [51, 62], [67, 3], [28, 41], [75, 36], [41, 3], [0, 1]], ![[0, 1], [0, 17], [76, 76], [72, 38], [25, 43], [50, 76], [3, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [16, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [38, 76, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4224, 4283, -609]
  a := ![4, -1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![516, 563, -609]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![11, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![11, 1, 0]] 
 ![![79, 0, 0], ![11, 1, 0], ![41, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![11, 1, 0], ![2, 10, 7], ![156, -9, 12]]]
  hmulB := by decide  
  f := ![![![-4558, -23389, -16380], ![-869, 184860, 0]], ![![-639, -3249, -2275], ![-78, 25675, 0]], ![![-2370, -12139, -8501], ![-419, 95940, 0]]]
  g := ![![![1, 0, 0], ![-11, 79, 0], ![-41, 0, 79]], ![![0, 1, 0], ![-5, 10, 7], ![-3, -9, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-19, -13, 1]] ![![79, 0, 0], ![11, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![869, 79, 0]], ![![-1501, -1027, 79], ![-79, -158, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![11, 1, 0]]], ![![![-19, -13, 1]], ![![-1, -2, -1]]]]
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


lemma PB233I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB233I1 : PrimesBelowBoundCertificateInterval O 31 79 233 where
  m := 11
  g := ![3, 3, 2, 2, 2, 1, 3, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB233I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
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
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
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
      exact NI61N1
      exact NI61N2
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I41N2, I43N1, I47N1, I53N1, I61N0, I61N1, I61N2, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [I53N1], [], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
