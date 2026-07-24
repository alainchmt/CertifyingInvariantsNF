
import IdealArithmetic.Examples.NF3_1_588735_1.RI3_1_588735_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![4, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![4, 1, 0]] 
 ![![37, 0, 0], ![4, 1, 0], ![35, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![4, 1, 0], ![2, 3, 5], ![55, -30, 5]]]
  hmulB := by decide  
  f := ![![![1653, 2513, 4200], ![259, -31080, 0]], ![![176, 269, 450], ![38, -3330, 0]], ![![1563, 2377, 3973], ![251, -29400, 0]]]
  g := ![![![1, 0, 0], ![-4, 37, 0], ![-35, 0, 37]], ![![0, 1, 0], ![-5, 3, 5], ![0, -30, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![8, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![8, 1, 0]] 
 ![![37, 0, 0], ![8, 1, 0], ![4, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![8, 1, 0], ![2, 7, 5], ![55, -30, 9]]]
  hmulB := by decide  
  f := ![![![-791, -2934, -2100], ![-222, 15540, 0]], ![![-172, -629, -450], ![-36, 3330, 0]], ![![-92, -318, -227], ![6, 1680, 0]]]
  g := ![![![1, 0, 0], ![-8, 37, 0], ![-4, 0, 37]], ![![0, 1, 0], ![-2, 7, 5], ![7, -30, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, 1, 0]] 
 ![![37, 0, 0], ![25, 1, 0], ![21, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, 1, 0], ![2, -13, 5], ![55, -30, -11]]]
  hmulB := by decide  
  f := ![![![1, 77, -30], ![37, 222, 0]], ![![5, 51, -20], ![38, 148, 0]], ![![-3, 44, -17], ![10, 126, 0]]]
  g := ![![![1, 0, 0], ![-25, 37, 0], ![-21, 0, 37]], ![![-1, 1, 0], ![6, -13, 5], ![28, -30, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![4, 1, 0]] ![![37, 0, 0], ![8, 1, 0]]
  ![![37, 0, 0], ![29, 17, 1]] where
 M := ![![![1369, 0, 0], ![296, 37, 0]], ![![148, 37, 0], ![34, 11, 5]]]
 hmul := by decide  
 g := ![![![![8, -17, -1], ![37, 0, 0]], ![![-21, -16, -1], ![37, 0, 0]]], ![![![-25, -16, -1], ![37, 0, 0]], ![![-3, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![29, 17, 1]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-444, 37, 0]], ![![1073, 629, 37], ![-259, -222, 74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-12, 1, 0]]], ![![![29, 17, 1]], ![![-7, -6, 2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [10, 27, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 8, 1], [8, 32, 40], [0, 1]]
 g := ![![[37, 28, 16], [], [12, 16], [22, 7, 1], []], ![[11, 18, 8, 20], [10, 4], [11, 5], [36, 15, 28, 40], [23, 1]], ![[25, 8, 14, 8], [18, 4], [37, 2], [5, 25, 22, 18], [25, 1]]]
 h' := ![![[40, 8, 1], [37, 10, 4], [23, 2], [26, 33, 37], [0, 0, 1], [0, 1]], ![[8, 32, 40], [13, 34, 15], [21, 16, 2], [7, 23, 28], [17, 9, 32], [40, 8, 1]], ![[0, 1], [29, 38, 22], [39, 23, 39], [9, 26, 17], [19, 32, 8], [8, 32, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 27], []]
 b := ![[], [35, 30, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [10, 27, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10209, 41000, -134890]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![249, 1000, -3290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [36, 34, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 32, 30], [17, 10, 13], [0, 1]]
 g := ![![[5, 5, 21], [32, 16, 13], [9, 25], [4, 9, 1], []], ![[28, 36, 29, 8], [2, 9, 36, 5], [22, 16], [42, 37, 30, 33], [1, 40]], ![[11, 27, 34, 13], [28, 31, 7, 16], [27, 38], [22, 31, 7, 25], [18, 40]]]
 h' := ![![[35, 32, 30], [9, 10, 8], [30, 38, 23], [28, 13, 38], [0, 0, 1], [0, 1]], ![[17, 10, 13], [24, 41, 36], [26, 0, 37], [42, 26, 39], [28, 35, 10], [35, 32, 30]], ![[0, 1], [16, 35, 42], [30, 5, 26], [23, 4, 9], [28, 8, 32], [17, 10, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 11], []]
 b := ![[], [14, 29, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [36, 34, 34, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3799566, -2652240, 1634817]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![88362, -61680, 38019]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![7, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![7, 1, 0]] 
 ![![47, 0, 0], ![7, 1, 0], ![39, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![7, 1, 0], ![2, 6, 5], ![55, -30, 8]]]
  hmulB := by decide  
  f := ![![![2408, 7441, 6210], ![517, -58374, 0]], ![![354, 1102, 920], ![95, -8648, 0]], ![![1995, 6174, 5153], ![450, -48438, 0]]]
  g := ![![![1, 0, 0], ![-7, 47, 0], ![-39, 0, 47]], ![![0, 1, 0], ![-5, 6, 5], ![-1, -30, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![16, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![16, 1, 0]] 
 ![![47, 0, 0], ![16, 1, 0], ![37, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![16, 1, 0], ![2, 15, 5], ![55, -30, 17]]]
  hmulB := by decide  
  f := ![![![95, 943, 315], ![94, -2961, 0]], ![![26, 314, 105], ![48, -987, 0]], ![![69, 742, 248], ![91, -2331, 0]]]
  g := ![![![1, 0, 0], ![-16, 47, 0], ![-37, 0, 47]], ![![0, 1, 0], ![-9, 15, 5], ![-2, -30, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-23, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-23, 1, 0]] 
 ![![47, 0, 0], ![24, 1, 0], ![31, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-23, 1, 0], ![2, -24, 5], ![55, -30, -22]]]
  hmulB := by decide  
  f := ![![![-98, 2013, -420], ![141, 3948, 0]], ![![-37, 1006, -210], ![95, 1974, 0]], ![![-71, 1328, -277], ![80, 2604, 0]]]
  g := ![![![1, 0, 0], ![-24, 47, 0], ![-31, 0, 47]], ![![-1, 1, 0], ![9, -24, 5], ![31, -30, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![7, 1, 0]] ![![47, 0, 0], ![16, 1, 0]]
  ![![47, 0, 0], ![4, -5, 1]] where
 M := ![![![2209, 0, 0], ![752, 47, 0]], ![![329, 47, 0], ![114, 22, 5]]]
 hmul := by decide  
 g := ![![![![43, 5, -1], ![47, 0, 0]], ![![12, 6, -1], ![47, 0, 0]]], ![![![3, 6, -1], ![47, 0, 0]], ![![2, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![4, -5, 1]] ![![47, 0, 0], ![-23, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-1081, 47, 0]], ![![188, -235, 47], ![-47, 94, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-23, 1, 0]]], ![![![4, -5, 1]], ![![-1, 2, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![8, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![8, 1, 0]] 
 ![![53, 0, 0], ![8, 1, 0], ![21, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![8, 1, 0], ![2, 7, 5], ![55, -30, 9]]]
  hmulB := by decide  
  f := ![![![-1743, -6293, -4500], ![-371, 47700, 0]], ![![-262, -944, -675], ![-52, 7155, 0]], ![![-695, -2494, -1783], ![-118, 18900, 0]]]
  g := ![![![1, 0, 0], ![-8, 53, 0], ![-21, 0, 53]], ![![0, 1, 0], ![-3, 7, 5], ![2, -30, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![17, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![17, 1, 0]] 
 ![![53, 0, 0], ![17, 1, 0], ![52, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![17, 1, 0], ![2, 16, 5], ![55, -30, 18]]]
  hmulB := by decide  
  f := ![![![-1694, -15585, -4875], ![-795, 51675, 0]], ![![-539, -4987, -1560], ![-264, 16536, 0]], ![![-1663, -15291, -4783], ![-777, 50700, 0]]]
  g := ![![![1, 0, 0], ![-17, 53, 0], ![-52, 0, 53]], ![![0, 1, 0], ![-10, 16, 5], ![-7, -30, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-25, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-25, 1, 0]] 
 ![![53, 0, 0], ![28, 1, 0], ![40, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-25, 1, 0], ![2, -26, 5], ![55, -30, -24]]]
  hmulB := by decide  
  f := ![![![1066, -18705, 3600], ![-795, -38160, 0]], ![![561, -9872, 1900], ![-423, -20140, 0]], ![![805, -14117, 2717], ![-599, -28800, 0]]]
  g := ![![![1, 0, 0], ![-28, 53, 0], ![-40, 0, 53]], ![![-1, 1, 0], ![10, -26, 5], ![35, -30, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![8, 1, 0]] ![![53, 0, 0], ![17, 1, 0]]
  ![![53, 0, 0], ![17, 26, 1]] where
 M := ![![![2809, 0, 0], ![901, 53, 0]], ![![424, 53, 0], ![138, 24, 5]]]
 hmul := by decide  
 g := ![![![![36, -26, -1], ![53, 0, 0]], ![![0, -25, -1], ![53, 0, 0]]], ![![![-9, -25, -1], ![53, 0, 0]], ![![1, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![17, 26, 1]] ![![53, 0, 0], ![-25, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1325, 53, 0]], ![![901, 1378, 53], ![-318, -689, 106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-25, 1, 0]]], ![![![17, 26, 1]], ![![-6, -13, 2]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-29, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-29, 1, 0]] 
 ![![59, 0, 0], ![30, 1, 0], ![27, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-29, 1, 0], ![2, -30, 5], ![55, -30, -28]]]
  hmulB := by decide  
  f := ![![![-73, 1978, -330], ![118, 3894, 0]], ![![-36, 989, -165], ![60, 1947, 0]], ![![-28, 905, -151], ![65, 1782, 0]]]
  g := ![![![1, 0, 0], ![-30, 59, 0], ![-27, 0, 59]], ![![-1, 1, 0], ![13, -30, 5], ![29, -30, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-17, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-17, 1, 0]] 
 ![![59, 0, 0], ![42, 1, 0], ![10, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-17, 1, 0], ![2, -18, 5], ![55, -30, -16]]]
  hmulB := by decide  
  f := ![![![4050, -41153, 11440], ![-1829, -134992, 0]], ![![2883, -29282, 8140], ![-1297, -96052, 0]], ![![685, -6975, 1939], ![-315, -22880, 0]]]
  g := ![![![1, 0, 0], ![-42, 59, 0], ![-10, 0, 59]], ![![-1, 1, 0], ![12, -18, 5], ![25, -30, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-13, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-13, 1, 0]] 
 ![![59, 0, 0], ![46, 1, 0], ![23, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-13, 1, 0], ![2, -14, 5], ![55, -30, -12]]]
  hmulB := by decide  
  f := ![![![-392, 3021, -1080], ![177, 12744, 0]], ![![-309, 2350, -840], ![119, 9912, 0]], ![![-144, 1177, -421], ![109, 4968, 0]]]
  g := ![![![1, 0, 0], ![-46, 59, 0], ![-23, 0, 59]], ![![-1, 1, 0], ![9, -14, 5], ![29, -30, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-29, 1, 0]] ![![59, 0, 0], ![-17, 1, 0]]
  ![![59, 0, 0], ![40, 26, 1]] where
 M := ![![![3481, 0, 0], ![-1003, 59, 0]], ![![-1711, 59, 0], ![495, -47, 5]]]
 hmul := by decide  
 g := ![![![![19, -26, -1], ![59, 0, 0]], ![![-17, 1, 0], ![0, 0, 0]]], ![![![-29, 1, 0], ![0, 0, 0]], ![![5, -3, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![40, 26, 1]] ![![59, 0, 0], ![-13, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-767, 59, 0]], ![![2360, 1534, 59], ![-413, -354, 118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-13, 1, 0]]], ![![![40, 26, 1]], ![![-7, -6, 2]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![26, 15, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![26, 15, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![26, 15, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![26, 15, 1], ![85, -19, 76], ![835, -445, 11]]]
  hmulB := by decide  
  f := ![![![-25, -15, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -15, 61]], ![![0, 0, 1], ![-31, -19, 76], ![9, -10, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [12, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 60], [0, 1]]
 g := ![![[45, 56], [4], [55, 14], [7, 3], [9, 1]], ![[0, 5], [4], [59, 47], [34, 58], [18, 60]]]
 h' := ![![[9, 60], [12, 19], [11, 2], [38, 40], [14, 8], [0, 1]], ![[0, 1], [0, 42], [29, 59], [32, 21], [25, 53], [9, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [28, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [12, 52, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148574, 104241, -520542]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![224306, 129711, -520542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-15, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-15, 1, 0]] 
 ![![61, 0, 0], ![46, 1, 0], ![50, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-15, 1, 0], ![2, -16, 5], ![55, -30, -14]]]
  hmulB := by decide  
  f := ![![![-193, 1790, -560], ![122, 6832, 0]], ![![-152, 1343, -420], ![62, 5124, 0]], ![![-155, 1467, -459], ![113, 5600, 0]]]
  g := ![![![1, 0, 0], ![-46, 61, 0], ![-50, 0, 61]], ![![-1, 1, 0], ![8, -16, 5], ![35, -30, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![26, 15, 1]] ![![61, 0, 0], ![-15, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-915, 61, 0]], ![![1586, 915, 61], ![-305, -244, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-15, 1, 0]]], ![![![26, 15, 1]], ![![-5, -4, 1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-1, -8, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-1, -8, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![66, 59, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-1, -8, 1], ![39, -23, -39], ![-430, 245, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -59, 67]], ![![-1, -1, 1], ![39, 34, -39], ![32, 38, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [55, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 66], [0, 1]]
 g := ![![[7, 39], [13, 15], [36], [47], [21], [1]], ![[0, 28], [0, 52], [36], [47], [21], [1]]]
 h' := ![![[17, 66], [22, 46], [39, 45], [64, 61], [61, 28], [12, 17], [0, 1]], ![[0, 1], [0, 21], [0, 22], [29, 6], [1, 39], [33, 50], [17, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [42, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [55, 50, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4168, 4109, -5614]
  a := ![-5, 4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5468, 5005, -5614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 1, 0]] 
 ![![67, 0, 0], ![39, 1, 0], ![39, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 1, 0], ![2, -29, 5], ![55, -30, -27]]]
  hmulB := by decide  
  f := ![![![3421, -63765, 11000], ![-2345, -147400, 0]], ![![2001, -37100, 6400], ![-1339, -85760, 0]], ![![1993, -37117, 6403], ![-1361, -85800, 0]]]
  g := ![![![1, 0, 0], ![-39, 67, 0], ![-39, 0, 67]], ![![-1, 1, 0], ![14, -29, 5], ![34, -30, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-1, -8, 1]] ![![67, 0, 0], ![-28, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1876, 67, 0]], ![![-67, -536, 67], ![67, 201, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-28, 1, 0]]], ![![![-1, -8, 1]], ![![1, 3, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![2, -20, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![2, -20, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![2, 51, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![2, -20, 1], ![15, -8, -99], ![-1090, 605, -48]]]
  hmulB := by decide  
  f := ![![![-1, 20, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -51, 71]], ![![0, -1, 1], ![3, 71, -99], ![-14, 43, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [12, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 70], [0, 1]]
 g := ![![[19, 6], [6, 43], [20, 25], [24], [12], [1]], ![[0, 65], [0, 28], [0, 46], [24], [12], [1]]]
 h' := ![![[56, 70], [70, 52], [44, 55], [67, 66], [0, 38], [59, 56], [0, 1]], ![[0, 1], [0, 19], [0, 16], [0, 5], [69, 33], [0, 15], [56, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [30, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [12, 15, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![236, 125, -805]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, 580, -805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![28, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![28, 1, 0]] 
 ![![71, 0, 0], ![28, 1, 0], ![48, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![28, 1, 0], ![2, 27, 5], ![55, -30, 29]]]
  hmulB := by decide  
  f := ![![![-2721, -45418, -8415], ![-1633, 119493, 0]], ![![-1074, -17892, -3315], ![-638, 47073, 0]], ![![-1836, -30705, -5689], ![-1113, 80784, 0]]]
  g := ![![![1, 0, 0], ![-28, 71, 0], ![-48, 0, 71]], ![![0, 1, 0], ![-14, 27, 5], ![-7, -30, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![2, -20, 1]] ![![71, 0, 0], ![28, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1988, 71, 0]], ![![142, -1420, 71], ![71, -568, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![28, 1, 0]]], ![![![2, -20, 1]], ![![1, -8, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![14, 21, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![14, 21, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![14, 21, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![14, 21, 1], ![97, -37, 106], ![1165, -625, 5]]]
  hmulB := by decide  
  f := ![![![-13, -21, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -21, 73]], ![![0, 0, 1], ![-19, -31, 106], ![15, -10, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [66, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 72], [0, 1]]
 g := ![![[70, 38], [27], [46], [68, 64], [3], [1]], ![[2, 35], [27], [46], [38, 9], [3], [1]]]
 h' := ![![[52, 72], [20, 29], [14, 63], [38, 51], [70, 8], [7, 52], [0, 1]], ![[0, 1], [68, 44], [5, 10], [62, 22], [48, 65], [10, 21], [52, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [37, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [66, 21, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15136, -7153, 591]
  a := ![3, 18, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![94, -268, 591]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-33, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-33, 1, 0]] 
 ![![73, 0, 0], ![40, 1, 0], ![68, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-33, 1, 0], ![2, -34, 5], ![55, -30, -32]]]
  hmulB := by decide  
  f := ![![![3754, -85641, 12600], ![-2847, -183960, 0]], ![![2068, -46899, 6900], ![-1532, -100740, 0]], ![![3491, -79775, 11737], ![-2665, -171360, 0]]]
  g := ![![![1, 0, 0], ![-40, 73, 0], ![-68, 0, 73]], ![![-1, 1, 0], ![14, -34, 5], ![47, -30, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![14, 21, 1]] ![![73, 0, 0], ![-33, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2409, 73, 0]], ![![1022, 1533, 73], ![-365, -730, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-33, 1, 0]]], ![![![14, 21, 1]], ![![-5, -10, 1]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [27, 28, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 78, 24], [78, 0, 55], [0, 1]]
 g := ![![[14, 35, 23], [77, 70, 42], [24, 27, 23], [68, 50, 2], [16, 1], []], ![[63, 12, 68, 75], [35, 47, 4, 68], [27, 66, 32, 37], [20, 28, 36, 78], [], [4, 23]], ![[76, 58, 49, 1], [73, 69, 40, 51], [27, 61, 12, 65], [65, 8, 12, 13], [62, 1], [52, 23]]]
 h' := ![![[17, 78, 24], [54, 2, 55], [63, 66, 11], [60, 11, 24], [42, 78, 70], [0, 0, 1], [0, 1]], ![[78, 0, 55], [10, 78, 48], [16, 29, 4], [9, 67, 27], [55, 31, 55], [23, 23], [17, 78, 24]], ![[0, 1], [70, 78, 55], [48, 63, 64], [31, 1, 28], [30, 49, 33], [19, 56, 78], [78, 0, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 21], []]
 b := ![[], [59, 28, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [27, 28, 63, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1074242, 708946, -342544]
  a := ![-3, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13598, 8974, -4336]
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



lemma PB218I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB218I1 : PrimesBelowBoundCertificateInterval O 31 79 218 where
  m := 11
  g := ![3, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB218I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I47N0, I47N1, I47N2, I53N0, I53N1, I53N2, I59N0, I59N1, I59N2, I61N1, I67N1, I71N1, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [], [], [I47N0, I47N1, I47N2], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
