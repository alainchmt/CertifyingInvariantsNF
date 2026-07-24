
import IdealArithmetic.Examples.NF3_1_542700_2.RI3_1_542700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-18, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-18, 1, 0]] 
 ![![37, 0, 0], ![19, 1, 0], ![20, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-18, 1, 0], ![0, -18, 6], ![210, 30, -18]]]
  hmulB := by decide  
  f := ![![![667, -37, 0], ![1369, 0, 0]], ![![361, -20, 0], ![741, 0, 0]], ![![380, -24, 1], ![780, -6, 0]]]
  g := ![![![1, 0, 0], ![-19, 37, 0], ![-20, 0, 37]], ![![-1, 1, 0], ![6, -18, 6], ![0, 30, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-14, 1, 0]] 
 ![![37, 0, 0], ![23, 1, 0], ![29, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-14, 1, 0], ![0, -14, 6], ![210, 30, -14]]]
  hmulB := by decide  
  f := ![![![197, -14, 0], ![518, 0, 0]], ![![127, -9, 0], ![334, 0, 0]], ![![137, 2, -5], ![360, 31, 0]]]
  g := ![![![1, 0, 0], ![-23, 37, 0], ![-29, 0, 37]], ![![-1, 1, 0], ![4, -14, 6], ![-2, 30, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, 1, 0]] 
 ![![37, 0, 0], ![32, 1, 0], ![2, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, 1, 0], ![0, -5, 6], ![210, 30, -5]]]
  hmulB := by decide  
  f := ![![![96, -19, 0], ![703, 0, 0]], ![![76, -15, 0], ![556, 0, 0]], ![![6, 3, -5], ![44, 31, 0]]]
  g := ![![![1, 0, 0], ![-32, 37, 0], ![-2, 0, 37]], ![![-1, 1, 0], ![4, -5, 6], ![-20, 30, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-18, 1, 0]] ![![37, 0, 0], ![-14, 1, 0]]
  ![![37, 0, 0], ![-32, 7, 1]] where
 M := ![![![1369, 0, 0], ![-518, 37, 0]], ![![-666, 37, 0], ![252, -32, 6]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![18, -6, -1], ![37, 0, 0]]], ![![![14, -6, -1], ![37, 0, 0]], ![![12, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-32, 7, 1]] ![![37, 0, 0], ![-5, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-185, 37, 0]], ![![-1184, 259, 37], ![370, -37, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-5, 1, 0]]], ![![![-32, 7, 1]], ![![10, -1, 1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 13, 5]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![61, 13, 5]] 
 ![![41, 0, 0], ![0, 41, 0], ![4, 19, 1]] where
  M :=![![![61, 13, 5], ![1050, 211, 78], ![2730, 565, 211]]]
  hmulB := by decide  
  f := ![![![11, 2, -1]], ![![-210, -19, 12]], ![![-86, -8, 5]]]
  g := ![![![1, -2, 5], ![18, -31, 78], ![46, -84, 211]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [35, 35, 1] where
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
 g := ![![[1, 4], [2], [21], [1, 36], [1]], ![[25, 37], [2], [21], [12, 5], [1]]]
 h' := ![![[6, 40], [16, 39], [39, 24], [6, 12], [6, 6], [0, 1]], ![[0, 1], [4, 2], [19, 17], [37, 29], [1, 35], [6, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [37, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [35, 35, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![455, 60, 1]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 1, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -2, 1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-11, -2, 1]] 
 ![![41, 0, 0], ![9, 1, 0], ![7, 0, 1]] where
  M :=![![![-11, -2, 1], ![210, 19, -12], ![-420, -25, 19]]]
  hmulB := by decide  
  f := ![![![-61, -13, -5]], ![![-39, -8, -3]], ![![-77, -16, -6]]]
  g := ![![![0, -2, 1], ![3, 19, -12], ![-8, -25, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![61, 13, 5]] ![![-11, -2, 1]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 19, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 19, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![29, 19, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 19, 1], ![210, 16, 114], ![3990, 605, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -19, 43]], ![![-1, 0, 1], ![-72, -50, 114], ![82, 7, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [7, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 42], [0, 1]]
 g := ![![[41, 36], [5, 11], [21], [11, 24], [1]], ![[29, 7], [30, 32], [21], [3, 19], [1]]]
 h' := ![![[14, 42], [8, 6], [20, 21], [9, 35], [36, 14], [0, 1]], ![[0, 1], [6, 37], [13, 22], [26, 8], [17, 29], [14, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [18, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [7, 29, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2541, -99, 375]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-312, -168, 375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![15, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![15, 1, 0]] 
 ![![43, 0, 0], ![15, 1, 0], ![27, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![15, 1, 0], ![0, 15, 6], ![210, 30, 15]]]
  hmulB := by decide  
  f := ![![![226, 15, 0], ![-645, 0, 0]], ![![60, 4, 0], ![-171, 0, 0]], ![![144, -3, -5], ![-411, 36, 0]]]
  g := ![![![1, 0, 0], ![-15, 43, 0], ![-27, 0, 43]], ![![0, 1, 0], ![-9, 15, 6], ![-15, 30, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-14, 19, 1]] ![![43, 0, 0], ![15, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![645, 43, 0]], ![![-602, 817, 43], ![0, 301, 129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![15, 1, 0]]], ![![![-14, 19, 1]], ![![0, 7, 3]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![1, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![1, 1, 0]] 
 ![![47, 0, 0], ![1, 1, 0], ![39, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![1, 1, 0], ![0, 1, 6], ![210, 30, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![47, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![39, 8, 0]]]
  g := ![![![1, 0, 0], ![-1, 47, 0], ![-39, 0, 47]], ![![0, 1, 0], ![-5, 1, 6], ![3, 30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![11, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![11, 1, 0]] 
 ![![47, 0, 0], ![11, 1, 0], ![19, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![11, 1, 0], ![0, 11, 6], ![210, 30, 11]]]
  hmulB := by decide  
  f := ![![![221, 20, 0], ![-940, 0, 0]], ![![55, 5, 0], ![-234, 0, 0]], ![![87, 6, -1], ![-370, 8, 0]]]
  g := ![![![1, 0, 0], ![-11, 47, 0], ![-19, 0, 47]], ![![0, 1, 0], ![-5, 11, 6], ![-7, 30, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-12, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-12, 1, 0]] 
 ![![47, 0, 0], ![35, 1, 0], ![23, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-12, 1, 0], ![0, -12, 6], ![210, 30, -12]]]
  hmulB := by decide  
  f := ![![![73, -6, 0], ![282, 0, 0]], ![![61, -5, 0], ![236, 0, 0]], ![![49, -2, -1], ![190, 8, 0]]]
  g := ![![![1, 0, 0], ![-35, 47, 0], ![-23, 0, 47]], ![![-1, 1, 0], ![6, -12, 6], ![-12, 30, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![1, 1, 0]] ![![47, 0, 0], ![11, 1, 0]]
  ![![47, 0, 0], ![-6, 2, 1]] where
 M := ![![![2209, 0, 0], ![517, 47, 0]], ![![47, 47, 0], ![11, 12, 6]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![11, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-6, 2, 1]] ![![47, 0, 0], ![-12, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-564, 47, 0]], ![![-282, 94, 47], ![282, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-12, 1, 0]]], ![![![-6, 2, 1]], ![![6, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-15, -20, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-15, -20, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![38, 33, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-15, -20, 1], ![210, 15, -120], ![-4200, -565, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -33, 53]], ![![-1, -1, 1], ![90, 75, -120], ![-90, -20, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [12, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 52], [0, 1]]
 g := ![![[], [24], [], [38], [0, 1]], ![[], [24], [], [38], [0, 52]]]
 h' := ![![[0, 52], [30], [0, 17], [21], [0, 41], [0, 1]], ![[0, 1], [30], [0, 36], [21], [0, 12], [0, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [0, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [12, 0, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3688, -153, 164]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -105, 164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![14, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![14, 1, 0]] 
 ![![53, 0, 0], ![14, 1, 0], ![38, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![14, 1, 0], ![0, 14, 6], ![210, 30, 14]]]
  hmulB := by decide  
  f := ![![![211, 15, 0], ![-795, 0, 0]], ![![42, 3, 0], ![-158, 0, 0]], ![![146, 8, -1], ![-550, 9, 0]]]
  g := ![![![1, 0, 0], ![-14, 53, 0], ![-38, 0, 53]], ![![0, 1, 0], ![-8, 14, 6], ![-14, 30, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-15, -20, 1]] ![![53, 0, 0], ![14, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![742, 53, 0]], ![![-795, -1060, 53], ![0, -265, -106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![14, 1, 0]]], ![![![-15, -20, 1]], ![![0, -5, -2]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![28, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![28, 1, 0]] 
 ![![59, 0, 0], ![28, 1, 0], ![7, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![28, 1, 0], ![0, 28, 6], ![210, 30, 28]]]
  hmulB := by decide  
  f := ![![![365, 13, 0], ![-767, 0, 0]], ![![140, 5, 0], ![-294, 0, 0]], ![![-7, -5, -1], ![15, 10, 0]]]
  g := ![![![1, 0, 0], ![-28, 59, 0], ![-7, 0, 59]], ![![0, 1, 0], ![-14, 28, 6], ![-14, 30, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-22, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-22, 1, 0]] 
 ![![59, 0, 0], ![37, 1, 0], ![57, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-22, 1, 0], ![0, -22, 6], ![210, 30, -22]]]
  hmulB := by decide  
  f := ![![![1255, -57, 0], ![3363, 0, 0]], ![![793, -36, 0], ![2125, 0, 0]], ![![1205, -51, -1], ![3229, 10, 0]]]
  g := ![![![1, 0, 0], ![-37, 59, 0], ![-57, 0, 59]], ![![-1, 1, 0], ![8, -22, 6], ![6, 30, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-6, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-6, 1, 0]] 
 ![![59, 0, 0], ![53, 1, 0], ![53, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-6, 1, 0], ![0, -6, 6], ![210, 30, -6]]]
  hmulB := by decide  
  f := ![![![73, -12, 0], ![708, 0, 0]], ![![67, -11, 0], ![650, 0, 0]], ![![67, -10, -1], ![650, 10, 0]]]
  g := ![![![1, 0, 0], ![-53, 59, 0], ![-53, 0, 59]], ![![-1, 1, 0], ![0, -6, 6], ![-18, 30, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![28, 1, 0]] ![![59, 0, 0], ![-22, 1, 0]]
  ![![59, 0, 0], ![-24, 1, 1]] where
 M := ![![![3481, 0, 0], ![-1298, 59, 0]], ![![1652, 59, 0], ![-616, 6, 6]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![2, 0, -1], ![59, 0, 0]]], ![![![28, 1, 0], ![0, 0, 0]], ![![-8, 0, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-24, 1, 1]] ![![59, 0, 0], ![-6, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-354, 59, 0]], ![![-1416, 59, 59], ![354, 0, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-6, 1, 0]]], ![![![-24, 1, 1]], ![![6, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-12, -8, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-12, -8, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![49, 53, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-12, -8, 1], ![210, 18, -48], ![-1680, -205, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -53, 61]], ![![-1, -1, 1], ![42, 42, -48], ![-42, -19, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [8, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 60], [0, 1]]
 g := ![![[40, 60], [34], [44, 39], [31, 58], [46, 1]], ![[55, 1], [34], [8, 22], [15, 3], [31, 60]]]
 h' := ![![[46, 60], [46, 50], [14, 20], [57, 51], [59, 34], [0, 1]], ![[0, 1], [28, 11], [19, 41], [24, 10], [37, 27], [46, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [29, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [8, 15, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1236, 152, 225]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-201, -193, 225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-13, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-13, 1, 0]] 
 ![![61, 0, 0], ![48, 1, 0], ![43, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-13, 1, 0], ![0, -13, 6], ![210, 30, -13]]]
  hmulB := by decide  
  f := ![![![690, -53, 0], ![3233, 0, 0]], ![![534, -41, 0], ![2502, 0, 0]], ![![480, -26, -5], ![2249, 51, 0]]]
  g := ![![![1, 0, 0], ![-48, 61, 0], ![-43, 0, 61]], ![![-1, 1, 0], ![6, -13, 6], ![-11, 30, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-12, -8, 1]] ![![61, 0, 0], ![-13, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-793, 61, 0]], ![![-732, -488, 61], ![366, 122, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-13, 1, 0]]], ![![![-12, -8, 1]], ![![6, 2, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-23, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-23, 1, 0]] 
 ![![67, 0, 0], ![44, 1, 0], ![57, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-23, 1, 0], ![0, -23, 6], ![210, 30, -23]]]
  hmulB := by decide  
  f := ![![![1082, -47, 0], ![3149, 0, 0]], ![![714, -31, 0], ![2078, 0, 0]], ![![926, -21, -5], ![2695, 56, 0]]]
  g := ![![![1, 0, 0], ![-44, 67, 0], ![-57, 0, 67]], ![![-1, 1, 0], ![10, -23, 6], ![3, 30, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-21, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-21, 1, 0]] 
 ![![67, 0, 0], ![46, 1, 0], ![27, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-21, 1, 0], ![0, -21, 6], ![210, 30, -21]]]
  hmulB := by decide  
  f := ![![![505, -24, 0], ![1608, 0, 0]], ![![358, -17, 0], ![1140, 0, 0]], ![![201, 8, -5], ![640, 56, 0]]]
  g := ![![![1, 0, 0], ![-46, 67, 0], ![-27, 0, 67]], ![![-1, 1, 0], ![12, -21, 6], ![-9, 30, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-23, 1, 0]] ![![67, 0, 0], ![-23, 1, 0]]
  ![![67, 0, 0], ![10, -30, 1]] where
 M := ![![![4489, 0, 0], ![-1541, 67, 0]], ![![-1541, 67, 0], ![529, -46, 6]]]
 hmul := by decide  
 g := ![![![![57, 30, -1], ![67, 0, 0]], ![![-23, 1, 0], ![0, 0, 0]]], ![![![-23, 1, 0], ![0, 0, 0]], ![![7, 2, 0], ![6, 0, 0]]]]
 hle2 := by decide  
def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![10, -30, 1]] ![![67, 0, 0], ![-21, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1407, 67, 0]], ![![670, -2010, 67], ![0, 670, -201]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-21, 1, 0]]], ![![![10, -30, 1]], ![![0, 10, -3]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [38, 19, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 29, 40], [37, 41, 31], [0, 1]]
 g := ![![[53, 17, 29], [54, 42, 43], [48, 40, 6], [14, 38], [11, 1], []], ![[19, 17, 13, 27], [61, 66, 61, 43], [56, 58, 54, 4], [36, 40], [24, 48], [40, 38]], ![[25, 68, 20, 14], [58, 44, 29, 26], [43, 45, 44, 21], [44, 27], [45, 60], [49, 38]]]
 h' := ![![[45, 29, 40], [7, 63, 10], [22, 42, 16], [29, 18, 19], [8, 37, 31], [0, 0, 1], [0, 1]], ![[37, 41, 31], [11, 65, 19], [52, 46, 64], [68, 0, 8], [4, 27, 53], [8, 51, 41], [45, 29, 40]], ![[0, 1], [35, 14, 42], [7, 54, 62], [61, 53, 44], [10, 7, 58], [4, 20, 29], [37, 41, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 35], []]
 b := ![[], [19, 47, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [38, 19, 60, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2272, 71, 71]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, 1, 1]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [56, 66, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 51, 53], [61, 21, 20], [0, 1]]
 g := ![![[13, 65, 48], [64, 49], [10, 19], [17, 20, 61], [63, 1], []], ![[34, 14, 39, 53], [29, 18], [69, 9], [27, 6, 69, 29], [59, 3], [19, 35]], ![[31, 4, 27, 33], [65, 24], [38, 38], [2, 70, 58, 13], [33, 46], [52, 35]]]
 h' := ![![[2, 51, 53], [60, 25, 62], [33, 23, 66], [70, 13, 47], [49, 20, 34], [0, 0, 1], [0, 1]], ![[61, 21, 20], [17, 2, 72], [53, 51, 50], [62, 10, 70], [38, 4, 22], [35, 56, 21], [2, 51, 53]], ![[0, 1], [59, 46, 12], [7, 72, 30], [50, 50, 29], [13, 49, 17], [6, 17, 51], [61, 21, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 58], []]
 b := ![[], [8, 32, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [56, 66, 10, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9112663, 1532416, 236447]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![124831, 20992, 3239]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-48, -32, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-48, -32, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![31, 47, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-48, -32, 1], ![210, -18, -192], ![-6720, -925, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -47, 79]], ![![-1, -1, 1], ![78, 114, -192], ![-78, -1, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [3, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 78], [0, 1]]
 g := ![![[19, 51], [15, 73], [70, 20], [61, 2], [10], [1]], ![[35, 28], [41, 6], [36, 59], [26, 77], [10], [1]]]
 h' := ![![[22, 78], [34, 50], [27, 51], [54, 39], [58, 9], [76, 22], [0, 1]], ![[0, 1], [28, 29], [43, 28], [43, 40], [19, 70], [7, 57], [22, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [68, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [3, 57, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1313, 20, 29]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -17, 29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![34, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![34, 1, 0]] 
 ![![79, 0, 0], ![34, 1, 0], ![18, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![34, 1, 0], ![0, 34, 6], ![210, 30, 34]]]
  hmulB := by decide  
  f := ![![![171, 5, 0], ![-395, 0, 0]], ![![34, 1, 0], ![-78, 0, 0]], ![![14, -28, -5], ![-32, 66, 0]]]
  g := ![![![1, 0, 0], ![-34, 79, 0], ![-18, 0, 79]], ![![0, 1, 0], ![-16, 34, 6], ![-18, 30, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-48, -32, 1]] ![![79, 0, 0], ![34, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2686, 79, 0]], ![![-3792, -2528, 79], ![-1422, -1106, -158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![34, 1, 0]]], ![![![-48, -32, 1]], ![![-18, -14, -2]]]]
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


lemma PB209I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB209I1 : PrimesBelowBoundCertificateInterval O 31 79 209 where
  m := 11
  g := ![3, 2, 2, 3, 2, 3, 2, 3, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB209I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N0, I67N1]
    · exact ![I71N0]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
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
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I43N1, I47N0, I47N1, I47N2, I53N1, I59N0, I59N1, I59N2, I61N1, I67N0, I67N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N0, I67N0, I67N1], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
