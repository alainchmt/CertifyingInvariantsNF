
import IdealArithmetic.Examples.NF3_1_916300_1.RI3_1_916300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![16, -3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![16, -3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![16, 34, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![16, -3, 1], ![153, -31, -2], ![-306, 247, -33]]]
  hmulB := by decide  
  f := ![![![-15, 3, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -34, 37]], ![![0, -1, 1], ![5, 1, -2], ![6, 37, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [24, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 36], [0, 1]]
 g := ![![[30, 36], [16], [8, 26], [30], [1]], ![[10, 1], [16], [10, 11], [30], [1]]]
 h' := ![![[20, 36], [35, 6], [30, 33], [4, 10], [13, 20], [0, 1]], ![[0, 1], [7, 31], [24, 4], [19, 27], [6, 17], [20, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [21, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [24, 17, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![483, -5, -60]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39, 55, -60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![2, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![2, 1, 0]] 
 ![![37, 0, 0], ![2, 1, 0], ![33, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![2, 1, 0], ![0, 2, 1], ![153, -47, 3]]]
  hmulB := by decide  
  f := ![![![35, 17, 0], ![-629, 0, 0]], ![![-2, -1, 0], ![38, 0, 0]], ![![31, 15, 0], ![-557, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 37, 0], ![-33, 0, 37]], ![![0, 1, 0], ![-1, 2, 1], ![4, -47, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![16, -3, 1]] ![![37, 0, 0], ![2, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![74, 37, 0]], ![![592, -111, 37], ![185, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![2, 1, 0]]], ![![![16, -3, 1]], ![![5, -1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [37, 16, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 20, 15], [30, 20, 26], [0, 1]]
 g := ![![[24, 28, 37], [17, 4], [40, 2], [34, 3, 1], []], ![[39, 26, 19, 7], [40, 5], [19, 32], [29, 12, 17, 14], [4, 20]], ![[27, 13, 9, 13], [5, 39], [29, 9], [11, 32, 15, 27], [34, 20]]]
 h' := ![![[14, 20, 15], [28, 8, 23], [1, 9, 39], [13, 1, 17], [0, 0, 1], [0, 1]], ![[30, 20, 26], [14, 1, 6], [31, 12, 13], [23, 13, 27], [7, 2, 20], [14, 20, 15]], ![[0, 1], [29, 32, 12], [3, 20, 30], [25, 27, 38], [11, 39, 20], [30, 20, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 24], []]
 b := ![[], [19, 2, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [37, 16, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![616189, -333740, 44280]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15029, -8140, 1080]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![14, 13, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![14, 13, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![14, 13, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![14, 13, 1], ![153, -33, 14], ![2142, -505, -19]]]
  hmulB := by decide  
  f := ![![![-13, -13, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -13, 43]], ![![0, 0, 1], ![-1, -5, 14], ![56, -6, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [25, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 42], [0, 1]]
 g := ![![[13, 31], [6, 11], [31], [18, 17], [1]], ![[0, 12], [0, 32], [31], [40, 26], [1]]]
 h' := ![![[19, 42], [22, 26], [12, 22], [23, 26], [18, 19], [0, 1]], ![[0, 1], [0, 17], [0, 21], [1, 17], [35, 24], [19, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [35, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [25, 24, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2432, 96, 57]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, -15, 57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 1, 0]] 
 ![![43, 0, 0], ![29, 1, 0], ![19, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 1, 0], ![0, -14, 1], ![153, -47, -13]]]
  hmulB := by decide  
  f := ![![![589, -42, 0], ![1806, 0, 0]], ![![407, -29, 0], ![1248, 0, 0]], ![![285, -20, 0], ![874, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 43, 0], ![-19, 0, 43]], ![![-1, 1, 0], ![9, -14, 1], ![41, -47, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![14, 13, 1]] ![![43, 0, 0], ![-14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-602, 43, 0]], ![![602, 559, 43], ![-43, -215, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-14, 1, 0]]], ![![![14, 13, 1]], ![![-1, -5, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-22, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-22, 1, 0]] 
 ![![47, 0, 0], ![25, 1, 0], ![33, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-22, 1, 0], ![0, -22, 1], ![153, -47, -21]]]
  hmulB := by decide  
  f := ![![![507, -23, 0], ![1081, 0, 0]], ![![309, -14, 0], ![659, 0, 0]], ![![385, -17, 0], ![821, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 47, 0], ![-33, 0, 47]], ![![-1, 1, 0], ![11, -22, 1], ![43, -47, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-19, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-19, 1, 0]] 
 ![![47, 0, 0], ![28, 1, 0], ![15, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-19, 1, 0], ![0, -19, 1], ![153, -47, -18]]]
  hmulB := by decide  
  f := ![![![172, -9, 0], ![423, 0, 0]], ![![96, -5, 0], ![236, 0, 0]], ![![84, -4, 0], ![207, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 47, 0], ![-15, 0, 47]], ![![-1, 1, 0], ![11, -19, 1], ![37, -47, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-7, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-7, 1, 0]] 
 ![![47, 0, 0], ![40, 1, 0], ![45, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-7, 1, 0], ![0, -7, 1], ![153, -47, -6]]]
  hmulB := by decide  
  f := ![![![218, -31, 0], ![1457, 0, 0]], ![![190, -27, 0], ![1270, 0, 0]], ![![212, -30, 0], ![1417, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 47, 0], ![-45, 0, 47]], ![![-1, 1, 0], ![5, -7, 1], ![49, -47, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-22, 1, 0]] ![![47, 0, 0], ![-19, 1, 0]]
  ![![47, 0, 0], ![42, 6, 1]] where
 M := ![![![2209, 0, 0], ![-893, 47, 0]], ![![-1034, 47, 0], ![418, -41, 1]]]
 hmul := by decide  
 g := ![![![![5, -6, -1], ![47, 0, 0]], ![![-19, 1, 0], ![0, 0, 0]]], ![![![-22, 1, 0], ![0, 0, 0]], ![![-34, -7, -1], ![48, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![42, 6, 1]] ![![47, 0, 0], ![-7, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-329, 47, 0]], ![![1974, 282, 47], ![-141, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-7, 1, 0]]], ![![![42, 6, 1]], ![![-3, -1, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![18, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![18, 1, 0]] 
 ![![53, 0, 0], ![18, 1, 0], ![47, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![18, 1, 0], ![0, 18, 1], ![153, -47, 19]]]
  hmulB := by decide  
  f := ![![![19, 1, 0], ![-53, 0, 0]], ![![-18, -1, 0], ![54, 0, 0]], ![![25, 1, 0], ![-71, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 53, 0], ![-47, 0, 53]], ![![0, 1, 0], ![-7, 18, 1], ![2, -47, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![47, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![0, -18, 1], ![153, -47, -17]]]
  hmulB := by decide  
  f := ![![![91, -5, 0], ![265, 0, 0]], ![![73, -4, 0], ![213, 0, 0]], ![![97, -5, 0], ![283, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-47, 0, 53]], ![![-1, 1, 0], ![11, -18, 1], ![49, -47, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-1, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-1, 1, 0]] 
 ![![53, 0, 0], ![52, 1, 0], ![52, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-1, 1, 0], ![0, -1, 1], ![153, -47, 0]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![159, 0, 0]], ![![2, -1, 0], ![54, 0, 0]], ![![2, -1, 0], ![54, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 53, 0], ![-52, 0, 53]], ![![-1, 1, 0], ![0, -1, 1], ![49, -47, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![18, 1, 0]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0], ![47, 0, 1]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![954, 53, 0], ![-324, 0, 1]]]
 hmul := by decide  
 g := ![![![![6, 0, -1], ![53, 0, 0]], ![![-18, 1, 0], ![0, 0, 0]]], ![![![-29, 1, -1], ![53, 0, 0]], ![![-7, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![47, 0, 1]] ![![53, 0, 0], ![-1, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-53, 53, 0]], ![![2491, 0, 53], ![106, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-1, 1, 0]]], ![![![47, 0, 1]], ![![2, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [3, 34, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 38, 30], [10, 20, 29], [0, 1]]
 g := ![![[27, 1, 22], [10, 14, 46], [8, 41], [19, 32, 26], [1]], ![[1, 3, 55, 13], [26, 19, 8, 38], [21, 36], [1, 43, 42, 14], [39, 7, 27, 37]], ![[43, 33, 43, 45], [11, 49, 53, 28], [57, 20], [7, 53, 37, 16], [42, 25, 46, 22]]]
 h' := ![![[37, 38, 30], [29, 18, 9], [39, 36, 39], [2, 34, 49], [56, 25, 47], [0, 1]], ![[10, 20, 29], [35, 9, 12], [45, 36, 31], [7, 36, 53], [32, 21, 38], [37, 38, 30]], ![[0, 1], [19, 32, 38], [28, 46, 48], [9, 48, 16], [48, 13, 33], [10, 20, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 28], []]
 b := ![[], [49, 19, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [3, 34, 12, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-432175, 346271, -68558]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7325, 5869, -1162]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![30, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![30, 1, 0]] 
 ![![61, 0, 0], ![30, 1, 0], ![15, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![30, 1, 0], ![0, 30, 1], ![153, -47, 31]]]
  hmulB := by decide  
  f := ![![![391, 13, 0], ![-793, 0, 0]], ![![150, 5, 0], ![-304, 0, 0]], ![![45, 1, 0], ![-91, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 61, 0], ![-15, 0, 61]], ![![0, 1, 0], ![-15, 30, 1], ![18, -47, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-23, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-23, 1, 0]] 
 ![![61, 0, 0], ![38, 1, 0], ![20, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-23, 1, 0], ![0, -23, 1], ![153, -47, -22]]]
  hmulB := by decide  
  f := ![![![323, -14, 0], ![854, 0, 0]], ![![208, -9, 0], ![550, 0, 0]], ![![124, -5, 0], ![328, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 61, 0], ![-20, 0, 61]], ![![-1, 1, 0], ![14, -23, 1], ![39, -47, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-8, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-8, 1, 0]] 
 ![![61, 0, 0], ![53, 1, 0], ![58, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-8, 1, 0], ![0, -8, 1], ![153, -47, -7]]]
  hmulB := by decide  
  f := ![![![217, -27, 0], ![1647, 0, 0]], ![![193, -24, 0], ![1465, 0, 0]], ![![210, -26, 0], ![1594, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 61, 0], ![-58, 0, 61]], ![![-1, 1, 0], ![6, -8, 1], ![50, -47, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![30, 1, 0]] ![![61, 0, 0], ![-23, 1, 0]]
  ![![61, 0, 0], ![42, 7, 1]] where
 M := ![![![3721, 0, 0], ![-1403, 61, 0]], ![![1830, 61, 0], ![-690, 7, 1]]]
 hmul := by decide  
 g := ![![![![19, -7, -1], ![61, 0, 0]], ![![-23, 1, 0], ![0, 0, 0]]], ![![![-12, -6, -1], ![61, 0, 0]], ![![-12, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![42, 7, 1]] ![![61, 0, 0], ![-8, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-488, 61, 0]], ![![2562, 427, 61], ![-183, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-8, 1, 0]]], ![![![42, 7, 1]], ![![-3, -1, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [19, 64, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 40, 15], [21, 26, 52], [0, 1]]
 g := ![![[28, 62, 59], [31, 65, 14], [18, 39], [0, 22], [25, 1], []], ![[62, 61, 26, 22], [20, 17, 13, 33], [34, 64], [7, 55], [49, 6], [58, 24]], ![[55, 43, 66, 50], [62, 42, 9, 32], [50, 37], [64, 6], [43, 59], [21, 24]]]
 h' := ![![[4, 40, 15], [14, 52, 27], [16, 27, 58], [36, 49, 21], [61, 56, 25], [0, 0, 1], [0, 1]], ![[21, 26, 52], [45, 24, 8], [49, 1, 37], [5, 11, 8], [2, 41, 16], [53, 38, 26], [4, 40, 15]], ![[0, 1], [29, 58, 32], [4, 39, 39], [4, 7, 38], [9, 37, 26], [42, 29, 40], [21, 26, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 23], []]
 b := ![[], [66, 25, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [19, 64, 42, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30619, 3082, -4288]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![457, 46, -64]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![16, 13, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![16, 13, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![16, 13, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![16, 13, 1], ![153, -31, 14], ![2142, -505, -17]]]
  hmulB := by decide  
  f := ![![![-15, -13, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -13, 71]], ![![0, 0, 1], ![-1, -3, 14], ![34, -4, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [54, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 70], [0, 1]]
 g := ![![[2, 25], [10, 54], [28, 15], [29], [20], [1]], ![[0, 46], [0, 17], [41, 56], [29], [20], [1]]]
 h' := ![![[34, 70], [28, 66], [50, 57], [25, 50], [61, 61], [17, 34], [0, 1]], ![[0, 1], [0, 5], [0, 14], [21, 21], [5, 10], [37, 37], [34, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [2, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [54, 37, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6059, -939, 392]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -85, 392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-14, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-14, 1, 0]] 
 ![![71, 0, 0], ![57, 1, 0], ![17, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-14, 1, 0], ![0, -14, 1], ![153, -47, -13]]]
  hmulB := by decide  
  f := ![![![953, -68, 0], ![4828, 0, 0]], ![![771, -55, 0], ![3906, 0, 0]], ![![255, -18, 0], ![1292, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 71, 0], ![-17, 0, 71]], ![![-1, 1, 0], ![11, -14, 1], ![43, -47, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![16, 13, 1]] ![![71, 0, 0], ![-14, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-994, 71, 0]], ![![1136, 923, 71], ![-71, -213, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-14, 1, 0]]], ![![![16, 13, 1]], ![![-1, -3, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [67, 15, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 52, 49], [28, 20, 24], [0, 1]]
 g := ![![[23, 45, 54], [38, 46], [3, 55], [35, 36, 35], [20, 1], []], ![[13, 53, 6, 70], [39, 64], [66, 6], [64, 14, 50, 9], [39, 35], [45, 65]], ![[58, 16, 18, 37], [14, 50], [6, 46], [60, 36, 71, 65], [12, 3], [70, 65]]]
 h' := ![![[65, 52, 49], [28, 25, 45], [26, 30, 51], [64, 2, 36], [47, 71, 20], [0, 0, 1], [0, 1]], ![[28, 20, 24], [39, 18, 8], [30, 0, 8], [27, 42, 15], [27, 40, 10], [42, 51, 20], [65, 52, 49]], ![[0, 1], [12, 30, 20], [1, 43, 14], [29, 29, 22], [54, 35, 43], [36, 22, 52], [28, 20, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 43], []]
 b := ![[], [13, 68, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [67, 15, 53, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-110668, 45698, -2628]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1516, 626, -36]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [44, 41, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 56, 65], [40, 22, 14], [0, 1]]
 g := ![![[50, 25, 2], [31, 60, 46], [1, 5, 20], [49, 19, 55], [52, 1], []], ![[72, 78, 9, 36], [48, 45, 51, 5], [24, 7, 71, 72], [3, 22, 23, 62], [3, 10], [13, 38]], ![[46, 32, 58, 39], [65, 43, 49, 39], [58, 76, 26, 34], [42, 42, 25, 30], [68, 55], [64, 38]]]
 h' := ![![[12, 56, 65], [58, 0, 9], [35, 31, 21], [56, 8, 39], [3, 36, 56], [0, 0, 1], [0, 1]], ![[40, 22, 14], [77, 72, 40], [30, 8, 28], [50, 49, 35], [9, 15, 17], [46, 8, 22], [12, 56, 65]], ![[0, 1], [16, 7, 30], [71, 40, 30], [36, 22, 5], [23, 28, 6], [48, 71, 56], [40, 22, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 29], []]
 b := ![[], [56, 66, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [44, 41, 27, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23147, -44082, 14694]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![293, -558, 186]
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



lemma PB271I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB271I1 : PrimesBelowBoundCertificateInterval O 31 79 271 where
  m := 11
  g := ![2, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB271I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
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
      exact NI53N2
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
  β := ![I37N1, I43N1, I47N0, I47N1, I47N2, I53N0, I53N1, I53N2, I61N0, I61N1, I61N2, I71N1]
  Il := ![[I37N1], [], [I43N1], [I47N0, I47N1, I47N2], [I53N0, I53N1, I53N2], [], [I61N0, I61N1, I61N2], [], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
