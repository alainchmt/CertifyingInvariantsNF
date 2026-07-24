
import IdealArithmetic.Examples.NF3_1_466796_1.RI3_1_466796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![1, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![1, 1, 0]] 
 ![![37, 0, 0], ![1, 1, 0], ![36, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![1, 1, 0], ![0, 1, 1], ![-679, 137, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![37, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![36, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 37, 0], ![-36, 0, 37]], ![![0, 1, 0], ![-1, 1, 1], ![-24, 137, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![4, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![4, 1, 0]] 
 ![![37, 0, 0], ![4, 1, 0], ![21, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![4, 1, 0], ![0, 4, 1], ![-679, 137, 5]]]
  hmulB := by decide  
  f := ![![![89, 22, 0], ![-814, 0, 0]], ![![4, 1, 0], ![-36, 0, 0]], ![![49, 12, 0], ![-448, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 37, 0], ![-21, 0, 37]], ![![0, 1, 0], ![-1, 4, 1], ![-36, 137, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![37, 0, 0], ![31, 1, 0], ![1, 0, 1]] where
  M :=![![![-6, 1, 0], ![0, -6, 1], ![-679, 137, -5]]]
  hmulB := by decide  
  f := ![![![107, -5, -1]], ![![108, -5, -1]], ![![113, -4, -1]]]
  g := ![![![-1, 1, 0], ![5, -6, 1], ![-133, 137, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![1, 1, 0]] ![![37, 0, 0], ![4, 1, 0]]
  ![![-107, 5, 1]] where
 M := ![![![1369, 0, 0], ![148, 37, 0]], ![![37, 37, 0], ![4, 5, 1]]]
 hmul := by decide  
 g := ![![![![222, -37, 0]], ![![24, 2, -1]]], ![![![6, 5, -1]], ![![19, -3, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-107, 5, 1]] ![![-6, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-104, -13, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-104, -13, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![19, 28, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-104, -13, 1], ![-679, 33, -12], ![8148, -2323, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -28, 41]], ![![-3, -1, 1], ![-11, 9, -12], ![189, -71, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [12, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 40], [0, 1]]
 g := ![![[12, 31], [31], [39], [17, 31], [1]], ![[17, 10], [31], [39], [22, 10], [1]]]
 h' := ![![[20, 40], [7, 21], [25, 20], [1, 30], [29, 20], [0, 1]], ![[0, 1], [17, 20], [15, 21], [27, 11], [19, 21], [20, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [35, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [12, 21, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2025, -289, 120]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-105, -89, 120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![0, 12, 1], ![-679, 137, 13]]]
  hmulB := by decide  
  f := ![![![193, 16, 0], ![-656, 0, 0]], ![![36, 3, 0], ![-122, 0, 0]], ![![76, 6, 0], ![-258, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-20, 0, 41]], ![![0, 1, 0], ![-4, 12, 1], ![-63, 137, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-104, -13, 1]] ![![41, 0, 0], ![12, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![492, 41, 0]], ![![-4264, -533, 41], ![-1927, -123, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![12, 1, 0]]], ![![![-104, -13, 1]], ![![-47, -3, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-104, 20, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-104, 20, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![25, 20, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-104, 20, 1], ![-679, 33, 21], ![-14259, 2198, 54]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -20, 43]], ![![-3, 0, 1], ![-28, -9, 21], ![-363, 26, 54]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [25, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 42], [0, 1]]
 g := ![![[27, 31], [14, 36], [1], [42, 40], [1]], ![[0, 12], [9, 7], [1], [3, 3], [1]]]
 h' := ![![[13, 42], [37, 17], [41, 6], [25, 42], [18, 13], [0, 1]], ![[0, 1], [0, 26], [33, 37], [12, 1], [15, 30], [13, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [22, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [25, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2033, -6578, 1318]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-719, -766, 1318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-21, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-21, 1, 0]] 
 ![![43, 0, 0], ![22, 1, 0], ![32, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-21, 1, 0], ![0, -21, 1], ![-679, 137, -20]]]
  hmulB := by decide  
  f := ![![![904, -43, 0], ![1849, 0, 0]], ![![484, -23, 0], ![990, 0, 0]], ![![704, -33, 0], ![1440, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 43, 0], ![-32, 0, 43]], ![![-1, 1, 0], ![10, -21, 1], ![-71, 137, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-104, 20, 1]] ![![43, 0, 0], ![-21, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-903, 43, 0]], ![![-4472, 860, 43], ![1505, -387, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-21, 1, 0]]], ![![![-104, 20, 1]], ![![35, -9, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![13, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![13, 1, 0]] 
 ![![47, 0, 0], ![13, 1, 0], ![19, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![13, 1, 0], ![0, 13, 1], ![-679, 137, 14]]]
  hmulB := by decide  
  f := ![![![248, 19, 0], ![-893, 0, 0]], ![![52, 4, 0], ![-187, 0, 0]], ![![82, 6, 0], ![-295, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 47, 0], ![-19, 0, 47]], ![![0, 1, 0], ![-4, 13, 1], ![-58, 137, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-9, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-9, 1, 0]] 
 ![![47, 0, 0], ![38, 1, 0], ![13, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-9, 1, 0], ![0, -9, 1], ![-679, 137, -8]]]
  hmulB := by decide  
  f := ![![![244, -27, 0], ![1269, 0, 0]], ![![190, -21, 0], ![988, 0, 0]], ![![74, -8, 0], ![385, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 47, 0], ![-13, 0, 47]], ![![-1, 1, 0], ![7, -9, 1], ![-123, 137, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-5, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-5, 1, 0]] 
 ![![47, 0, 0], ![42, 1, 0], ![22, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-5, 1, 0], ![0, -5, 1], ![-679, 137, -4]]]
  hmulB := by decide  
  f := ![![![116, -23, 0], ![1081, 0, 0]], ![![106, -21, 0], ![988, 0, 0]], ![![56, -11, 0], ![522, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 47, 0], ![-22, 0, 47]], ![![-1, 1, 0], ![4, -5, 1], ![-135, 137, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![13, 1, 0]] ![![47, 0, 0], ![-9, 1, 0]]
  ![![47, 0, 0], ![-117, 4, 1]] where
 M := ![![![2209, 0, 0], ![-423, 47, 0]], ![![611, 47, 0], ![-117, 4, 1]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![108, -3, -1], ![47, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-117, 4, 1]] ![![47, 0, 0], ![-5, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-235, 47, 0]], ![![-5499, 188, 47], ![-94, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-5, 1, 0]]], ![![![-117, 4, 1]], ![![-2, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [49, 48, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 18, 18], [29, 34, 35], [0, 1]]
 g := ![![[22, 40, 10], [6, 17], [49, 43, 29], [10, 15], [1]], ![[28, 18, 6, 12], [36, 11], [43, 22, 37, 12], [34, 10], [32, 0, 28, 2]], ![[6, 50, 36, 19], [29, 46], [48, 16, 29, 23], [49, 4], [11, 16, 7, 51]]]
 h' := ![![[35, 18, 18], [15, 34, 13], [37, 2, 21], [3, 44, 33], [4, 5, 11], [0, 1]], ![[29, 34, 35], [39, 8, 47], [1, 51, 8], [6, 13, 6], [20, 7, 40], [35, 18, 18]], ![[0, 1], [1, 11, 46], [37, 0, 24], [37, 49, 14], [0, 41, 2], [29, 34, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 37], []]
 b := ![[], [44, 17, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [49, 48, 42, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-749049, 334854, -46958]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14133, 6318, -886]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [33, 24, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 28, 47], [24, 30, 12], [0, 1]]
 g := ![![[56, 45, 7], [7, 15, 21], [20, 25], [15, 3, 25], [1]], ![[13, 0, 8, 23], [51, 44, 50, 44], [16, 7], [11, 22, 0, 52], [29, 18, 34, 42]], ![[5, 54, 27, 3], [27, 21, 35, 27], [21, 19], [37, 15, 13, 3], [41, 28, 6, 17]]]
 h' := ![![[40, 28, 47], [5, 37, 40], [46, 41, 32], [36, 40, 54], [26, 35, 5], [0, 1]], ![[24, 30, 12], [1, 29, 48], [15, 12, 55], [22, 29, 19], [31, 6, 25], [40, 28, 47]], ![[0, 1], [41, 52, 30], [18, 6, 31], [11, 49, 45], [22, 18, 29], [24, 30, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 40], []]
 b := ![[], [21, 13, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [33, 24, 54, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10047051, 4196729, -423266]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-170289, 71131, -7174]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![94, -27, 2]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![94, -27, 2]] 
 ![![61, 0, 0], ![0, 61, 0], ![47, 17, 1]] where
  M :=![![![94, -27, 2], ![-1358, 368, -25], ![16975, -4783, 343]]]
  hmulB := by decide  
  f := ![![![109, -5, -1]], ![![679, -28, -6]], ![![340, -14, -3]]]
  g := ![![![0, -1, 2], ![-3, 13, -25], ![14, -174, 343]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [54, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 60], [0, 1]]
 g := ![![[53, 56], [27], [49, 3], [40, 48], [5, 1]], ![[28, 5], [27], [3, 58], [36, 13], [10, 60]]]
 h' := ![![[5, 60], [47, 19], [38, 37], [36, 53], [35, 32], [0, 1]], ![[0, 1], [20, 42], [40, 24], [57, 8], [12, 29], [5, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [7, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [54, 56, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1983, -324, 85]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98, -29, 85]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, 5, 1]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-109, 5, 1]] 
 ![![61, 0, 0], ![43, 1, 0], ![42, 0, 1]] where
  M :=![![![-109, 5, 1], ![-679, 28, 6], ![-4074, 143, 34]]]
  hmulB := by decide  
  f := ![![![-94, 27, -2]], ![![-44, 13, -1]], ![![-343, 97, -7]]]
  g := ![![![-6, 5, 1], ![-35, 28, 6], ![-191, 143, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![94, -27, 2]] ![![-109, 5, 1]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [36, 58, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 47, 20], [14, 19, 47], [0, 1]]
 g := ![![[61, 9, 55], [1, 35, 21], [7, 19], [56, 39], [29, 1], []], ![[58, 49, 12, 5], [6, 59, 6, 12], [10, 23], [15, 62], [10, 26], [13, 65]], ![[9, 55, 18, 19], [8, 23, 24, 14], [44, 1], [0, 49], [51, 65], [53, 65]]]
 h' := ![![[15, 47, 20], [31, 37, 51], [22, 9, 50], [41, 42, 35], [28, 24, 46], [0, 0, 1], [0, 1]], ![[14, 19, 47], [52, 7, 34], [0, 40, 58], [5, 51, 31], [64, 44, 14], [25, 58, 19], [15, 47, 20]], ![[0, 1], [2, 23, 49], [40, 18, 26], [4, 41, 1], [2, 66, 7], [30, 9, 47], [14, 19, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 41], []]
 b := ![[], [40, 47, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [36, 58, 38, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11544904, 1436413, 173262]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-172312, 21439, 2586]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [57, 38, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 15, 70], [2, 55, 1], [0, 1]]
 g := ![![[36, 21, 32], [23, 8, 5], [54, 29, 9], [6, 3], [9, 1], []], ![[57, 6, 67, 31], [43, 50, 6, 21], [49, 42, 55, 7], [39, 25], [59, 43], [50, 1]], ![[9, 34, 36, 25], [28, 26, 54, 3], [18, 1, 33, 50], [18, 24], [49, 12], [48, 1]]]
 h' := ![![[7, 15, 70], [38, 5, 23], [46, 70, 54], [56, 15, 3], [55, 27, 43], [0, 0, 1], [0, 1]], ![[2, 55, 1], [47, 9, 53], [15, 6, 60], [65, 25, 8], [4, 47, 66], [39, 28, 55], [7, 15, 70]], ![[0, 1], [47, 57, 66], [54, 66, 28], [55, 31, 60], [67, 68, 33], [37, 43, 15], [2, 55, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 25], []]
 b := ![[], [31, 39, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [57, 38, 62, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-917249, 250701, -16756]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12919, 3531, -236]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-100, -11, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-100, -11, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![46, 62, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-100, -11, 1], ![-679, 37, -10], ![6790, -2049, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -62, 73]], ![![-2, -1, 1], ![-3, 9, -10], ![76, -51, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [32, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 72], [0, 1]]
 g := ![![[64, 16], [9], [50], [23, 72], [16], [1]], ![[0, 57], [9], [50], [27, 1], [16], [1]]]
 h' := ![![[69, 72], [16, 4], [42, 70], [67, 14], [1, 46], [41, 69], [0, 1]], ![[0, 1], [0, 69], [54, 3], [11, 59], [36, 27], [57, 4], [69, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [60, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [32, 4, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5400, -1616, 565]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-430, -502, 565]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![10, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![10, 1, 0]] 
 ![![73, 0, 0], ![10, 1, 0], ![46, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![10, 1, 0], ![0, 10, 1], ![-679, 137, 11]]]
  hmulB := by decide  
  f := ![![![201, 20, 0], ![-1460, 0, 0]], ![![10, 1, 0], ![-72, 0, 0]], ![![122, 12, 0], ![-886, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 73, 0], ![-46, 0, 73]], ![![0, 1, 0], ![-2, 10, 1], ![-35, 137, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-100, -11, 1]] ![![73, 0, 0], ![10, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![730, 73, 0]], ![![-7300, -803, 73], ![-1679, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![10, 1, 0]]], ![![![-100, -11, 1]], ![![-23, -1, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-74, 37, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-74, 37, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![5, 37, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-74, 37, 1], ![-679, 63, 38], ![-25802, 4527, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -37, 79]], ![![-1, 0, 1], ![-11, -17, 38], ![-333, 10, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [52, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 78], [0, 1]]
 g := ![![[56, 38], [73, 51], [78, 38], [69, 51], [42], [1]], ![[0, 41], [2, 28], [22, 41], [77, 28], [42], [1]]]
 h' := ![![[11, 78], [75, 65], [52, 50], [46, 65], [46, 29], [27, 11], [0, 1]], ![[0, 1], [0, 14], [49, 29], [50, 14], [49, 50], [69, 68], [11, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [48, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [52, 68, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24636, -8368, 756]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![264, -460, 756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-38, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-38, 1, 0]] 
 ![![79, 0, 0], ![41, 1, 0], ![57, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-38, 1, 0], ![0, -38, 1], ![-679, 137, -37]]]
  hmulB := by decide  
  f := ![![![2509, -66, 0], ![5214, 0, 0]], ![![1331, -35, 0], ![2766, 0, 0]], ![![1843, -48, 0], ![3830, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 79, 0], ![-57, 0, 79]], ![![-1, 1, 0], ![19, -38, 1], ![-53, 137, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-74, 37, 1]] ![![79, 0, 0], ![-38, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-3002, 79, 0]], ![![-5846, 2923, 79], ![2133, -1343, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-38, 1, 0]]], ![![![-74, 37, 1]], ![![27, -17, 0]]]]
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


lemma PB194I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB194I1 : PrimesBelowBoundCertificateInterval O 31 79 194 where
  m := 11
  g := ![3, 2, 2, 3, 1, 1, 2, 1, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB194I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I43N1, I47N0, I47N1, I47N2, I61N1, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [], [], [I61N1], [], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
