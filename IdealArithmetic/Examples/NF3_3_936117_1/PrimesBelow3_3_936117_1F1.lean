
import IdealArithmetic.Examples.NF3_3_936117_1.RI3_3_936117_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-324, -279, -32]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-324, -279, -32]] 
 ![![37, 0, 0], ![0, 37, 0], ![24, 33, 1]] where
  M :=![![![-324, -279, -32], ![-2848, -2436, -279], ![-24831, -21262, -2436]]]
  hmulB := by decide  
  f := ![![![54, 20, -3]], ![![-267, -144, 20]], ![![-155, -87, 12]]]
  g := ![![![12, 21, -32], ![104, 183, -279], ![909, 1598, -2436]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 36], [0, 1]]
 g := ![![[4, 21], [33], [34, 16], [7], [1]], ![[0, 16], [33], [1, 21], [7], [1]]]
 h' := ![![[28, 36], [6, 13], [16, 12], [24, 33], [7, 28], [0, 1]], ![[0, 1], [0, 24], [19, 25], [23, 4], [14, 9], [28, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [23, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [30, 9, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![208, 212, 58]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -46, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54, -20, 3]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-54, -20, 3]] 
 ![![37, 0, 0], ![4, 1, 0], ![21, 0, 1]] where
  M :=![![![-54, -20, 3], ![267, 144, -20], ![-1780, -1053, 144]]]
  hmulB := by decide  
  f := ![![![324, 279, 32]], ![![112, 96, 11]], ![![855, 733, 84]]]
  g := ![![![-1, -20, 3], ![3, 144, -20], ![-16, -1053, 144]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-324, -279, -32]] ![![-54, -20, 3]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![3, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![3, 1, 0]] 
 ![![41, 0, 0], ![3, 1, 0], ![32, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![3, 1, 0], ![0, 3, 1], ![89, 66, 3]]]
  hmulB := by decide  
  f := ![![![37, 12, 0], ![-492, 0, 0]], ![![-3, -1, 0], ![42, 0, 0]], ![![28, 9, 0], ![-372, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 41, 0], ![-32, 0, 41]], ![![0, 1, 0], ![-1, 3, 1], ![-5, 66, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![0, 12, 1], ![89, 66, 12]]]
  hmulB := by decide  
  f := ![![![193, 16, 0], ![-656, 0, 0]], ![![36, 3, 0], ![-122, 0, 0]], ![![76, 6, 0], ![-258, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-20, 0, 41]], ![![0, 1, 0], ![-4, 12, 1], ![-23, 66, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-15, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-15, 1, 0]] 
 ![![41, 0, 0], ![26, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-15, 1, 0], ![0, -15, 1], ![89, 66, -15]]]
  hmulB := by decide  
  f := ![![![256, -17, 0], ![697, 0, 0]], ![![166, -11, 0], ![452, 0, 0]], ![![126, -8, 0], ![343, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 41, 0], ![-21, 0, 41]], ![![-1, 1, 0], ![9, -15, 1], ![-32, 66, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![3, 1, 0]] ![![41, 0, 0], ![12, 1, 0]]
  ![![41, 0, 0], ![-46, 15, 1]] where
 M := ![![![1681, 0, 0], ![492, 41, 0]], ![![123, 41, 0], ![36, 15, 1]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![12, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-46, 15, 1]] ![![41, 0, 0], ![-15, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-615, 41, 0]], ![![-1886, 615, 41], ![779, -205, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-15, 1, 0]]], ![![![-46, 15, 1]], ![![19, -5, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-31, 11, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-31, 11, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![12, 11, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-31, 11, 1], ![89, 35, 11], ![979, 815, 35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -11, 43]], ![![-1, 0, 1], ![-1, -2, 11], ![13, 10, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [18, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 42], [0, 1]]
 g := ![![[9, 6], [13, 10], [11], [38, 14], [1]], ![[26, 37], [27, 33], [11], [6, 29], [1]]]
 h' := ![![[10, 42], [24, 7], [33, 28], [4, 22], [25, 10], [0, 1]], ![[0, 1], [8, 36], [12, 15], [9, 21], [39, 33], [10, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [28, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [18, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1082, -53, 691]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-218, -178, 691]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-11, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-11, 1, 0]] 
 ![![43, 0, 0], ![32, 1, 0], ![8, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-11, 1, 0], ![0, -11, 1], ![89, 66, -11]]]
  hmulB := by decide  
  f := ![![![67, -6, 0], ![258, 0, 0]], ![![56, -5, 0], ![216, 0, 0]], ![![14, -1, 0], ![54, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 43, 0], ![-8, 0, 43]], ![![-1, 1, 0], ![8, -11, 1], ![-45, 66, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-31, 11, 1]] ![![43, 0, 0], ![-11, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-473, 43, 0]], ![![-1333, 473, 43], ![430, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-11, 1, 0]]], ![![![-31, 11, 1]], ![![10, -2, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [4, 42, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 0, 15], [6, 46, 32], [0, 1]]
 g := ![![[12, 43, 18], [30, 42, 28], [30, 33, 7], [30, 5, 1], []], ![[33, 17, 23, 35], [37, 35, 2, 43], [20, 25, 6, 30], [5, 44, 30, 15], [44, 37]], ![[42, 27], [39, 18, 38, 8], [46, 6, 21, 8], [20, 25], [27, 37]]]
 h' := ![![[46, 0, 15], [21, 0, 21], [21, 36, 13], [21, 36, 30], [0, 0, 1], [0, 1]], ![[6, 46, 32], [12, 8, 26], [13, 43, 10], [46, 45, 40], [13, 25, 46], [46, 0, 15]], ![[0, 1], [13, 39], [6, 15, 24], [4, 13, 24], [22, 22], [6, 46, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 33], []]
 b := ![[], [29, 42, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [4, 42, 42, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56306, 14523, -21291]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1198, 309, -453]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![255, 6, -4]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![255, 6, -4]] 
 ![![53, 0, 0], ![0, 53, 0], ![29, 25, 1]] where
  M :=![![![255, 6, -4], ![-356, -9, 6], ![534, 40, -9]]]
  hmulB := by decide  
  f := ![![![3, 2, 0]], ![![0, 3, 2]], ![![5, 5, 1]]]
  g := ![![![7, 2, -4], ![-10, -3, 6], ![15, 5, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [45, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 52], [0, 1]]
 g := ![![[23, 13], [25], [45, 17], [9], [25, 1]], ![[30, 40], [25], [46, 36], [9], [50, 52]]]
 h' := ![![[25, 52], [3, 38], [42, 5], [4, 32], [41, 50], [0, 1]], ![[0, 1], [52, 15], [8, 48], [9, 21], [19, 3], [25, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [34, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [45, 28, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-460, 435, 505]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-285, -230, 505]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 2, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![3, 2, 0]] 
 ![![53, 0, 0], ![28, 1, 0], ![11, 0, 1]] where
  M :=![![![3, 2, 0], ![0, 3, 2], ![178, 132, 3]]]
  hmulB := by decide  
  f := ![![![255, 6, -4]], ![![128, 3, -2]], ![![63, 2, -1]]]
  g := ![![![-1, 2, 0], ![-2, 3, 2], ![-67, 132, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![255, 6, -4]] ![![3, 2, 0]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-68, -23, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-68, -23, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![50, 36, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-68, -23, 1], ![89, -2, -23], ![-2047, -1429, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -36, 59]], ![![-2, -1, 1], ![21, 14, -23], ![-33, -23, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [42, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 58], [0, 1]]
 g := ![![[22, 51], [49, 12], [27], [31, 16], [20, 1]], ![[39, 8], [53, 47], [27], [56, 43], [40, 58]]]
 h' := ![![[20, 58], [7, 13], [3, 37], [55, 26], [45, 4], [0, 1]], ![[0, 1], [31, 46], [35, 22], [44, 33], [7, 55], [20, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [54, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [42, 39, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![220, 182, 28]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -14, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![23, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![23, 1, 0]] 
 ![![59, 0, 0], ![23, 1, 0], ![2, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![23, 1, 0], ![0, 23, 1], ![89, 66, 23]]]
  hmulB := by decide  
  f := ![![![323, 14, 0], ![-826, 0, 0]], ![![115, 5, 0], ![-294, 0, 0]], ![![-14, -1, 0], ![36, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 59, 0], ![-2, 0, 59]], ![![0, 1, 0], ![-9, 23, 1], ![-25, 66, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-68, -23, 1]] ![![59, 0, 0], ![23, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1357, 59, 0]], ![![-4012, -1357, 59], ![-1475, -531, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![23, 1, 0]]], ![![![-68, -23, 1]], ![![-25, -9, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-69, 27, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-69, 27, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![53, 27, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-69, 27, 1], ![89, -3, 27], ![2403, 1871, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -27, 61]], ![![-2, 0, 1], ![-22, -12, 27], ![42, 32, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [49, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 60], [0, 1]]
 g := ![![[50, 5], [57], [21, 13], [58, 39], [51, 1]], ![[0, 56], [57], [13, 48], [34, 22], [41, 60]]]
 h' := ![![[51, 60], [16, 26], [8, 22], [25, 14], [2, 51], [0, 1]], ![[0, 1], [0, 35], [32, 39], [7, 47], [41, 10], [51, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [9, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [49, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3442, 2825, 439]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-325, -148, 439]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 1, 0]] 
 ![![61, 0, 0], ![34, 1, 0], ![3, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 1, 0], ![0, -27, 1], ![89, 66, -27]]]
  hmulB := by decide  
  f := ![![![1567, -58, 0], ![3538, 0, 0]], ![![892, -33, 0], ![2014, 0, 0]], ![![93, -3, 0], ![210, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 61, 0], ![-3, 0, 61]], ![![-1, 1, 0], ![15, -27, 1], ![-34, 66, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-69, 27, 1]] ![![61, 0, 0], ![-27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1647, 61, 0]], ![![-4209, 1647, 61], ![1952, -732, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-27, 1, 0]]], ![![![-69, 27, 1]], ![![32, -12, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [31, 6, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 55, 5], [52, 11, 62], [0, 1]]
 g := ![![[19, 64, 36], [39, 62, 36], [24, 49], [24, 25], [66, 1], []], ![[22, 40, 62, 13], [59, 32, 14, 7], [57, 49], [57, 39], [4, 54], [56, 25]], ![[26, 63, 42, 47], [57, 9, 62, 36], [], [3, 55], [35, 10], [66, 25]]]
 h' := ![![[14, 55, 5], [64, 14, 61], [48, 64, 6], [16, 10, 7], [31, 42, 62], [0, 0, 1], [0, 1]], ![[52, 11, 62], [53, 5, 4], [12, 64, 51], [29, 2, 60], [11, 31, 21], [1, 27, 11], [14, 55, 5]], ![[0, 1], [60, 48, 2], [21, 6, 10], [50, 55], [64, 61, 51], [55, 40, 55], [52, 11, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 44], []]
 b := ![[], [6, 26, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [31, 6, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48441, 27470, -5494]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![723, 410, -82]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1186, 1013, 116]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1186, 1013, 116]] 
 ![![71, 0, 0], ![0, 71, 0], ![9, 2, 1]] where
  M :=![![![1186, 1013, 116], ![10324, 8842, 1013], ![90157, 77182, 8842]]]
  hmulB := by decide  
  f := ![![![-62, -54, 7]], ![![623, 400, -54]], ![![-58, -37, 5]]]
  g := ![![![2, 11, 116], ![17, 96, 1013], ![149, 838, 8842]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [13, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 70], [0, 1]]
 g := ![![[46, 10], [30, 49], [2, 27], [15], [48], [1]], ![[30, 61], [51, 22], [44, 44], [15], [48], [1]]]
 h' := ![![[41, 70], [36, 62], [45, 64], [7, 58], [42, 50], [58, 41], [0, 1]], ![[0, 1], [22, 9], [42, 7], [42, 13], [33, 21], [35, 30], [41, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [43, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [13, 30, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![369, 650, 325]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, 0, 325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62, -54, 7]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-62, -54, 7]] 
 ![![71, 0, 0], ![69, 1, 0], ![67, 0, 1]] where
  M :=![![![-62, -54, 7], ![623, 400, -54], ![-4806, -2941, 400]]]
  hmulB := by decide  
  f := ![![![1186, 1013, 116]], ![![1298, 1109, 127]], ![![2389, 2043, 234]]]
  g := ![![![45, -54, 7], ![-329, 400, -54], ![2413, -2941, 400]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1186, 1013, 116]] ![![-62, -54, 7]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![8, 1, 0]] 
 ![![73, 0, 0], ![8, 1, 0], ![9, 0, 1]] where
  M :=![![![8, 1, 0], ![0, 8, 1], ![89, 66, 8]]]
  hmulB := by decide  
  f := ![![![-2, -8, 1]], ![![1, 0, 0]], ![![-10, -7, 1]]]
  g := ![![![0, 1, 0], ![-1, 8, 1], ![-7, 66, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3140, -68, 49]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-3140, -68, 49]] 
 ![![73, 0, 0], ![19, 1, 0], ![4, 0, 1]] where
  M :=![![![-3140, -68, 49], ![4361, 94, -68], ![-6052, -127, 94]]]
  hmulB := by decide  
  f := ![![![200, 169, 18]], ![![74, 63, 7]], ![![217, 184, 20]]]
  g := ![![![-28, -68, 49], ![39, 94, -68], ![-55, -127, 94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5608, -4801, -550]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-5608, -4801, -550]] 
 ![![73, 0, 0], ![46, 1, 0], ![1, 0, 1]] where
  M :=![![![-5608, -4801, -550], ![-48950, -41908, -4801], ![-427289, -365816, -41908]]]
  hmulB := by decide  
  f := ![![![2152, 1508, -201]], ![![1111, 798, -106]], ![![1868, 1139, -155]]]
  g := ![![![2956, -4801, -550], ![25803, -41908, -4801], ![225235, -365816, -41908]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![8, 1, 0]] ![![-3140, -68, 49]]
  ![![-20759, -450, 324]] where
 M := ![![![-20759, -450, 324]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-20759, -450, 324]] ![![-5608, -4801, -550]]
  ![![73, 0, 0]] where
 M := ![![![2336, -1825, -292]]]
 hmul := by decide  
 g := ![![![![32, -25, -4]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [47, 10, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 33, 24], [10, 45, 55], [0, 1]]
 g := ![![[18, 66, 22], [1, 46, 13], [63, 55, 23], [8, 17, 18], [33, 1], []], ![[72, 24, 45, 54], [38, 17, 14, 33], [58, 39, 12, 63], [23, 48, 34, 70], [26, 50], [52, 23]], ![[75, 67, 21, 21], [62, 59, 37, 55], [57, 22, 75, 25], [58, 40, 7, 38], [19, 62], [21, 23]]]
 h' := ![![[23, 33, 24], [32, 62, 38], [41, 69, 31], [19, 41, 55], [29, 18, 52], [0, 0, 1], [0, 1]], ![[10, 45, 55], [25, 77, 38], [12, 20, 49], [75, 27, 62], [8, 70, 7], [60, 75, 45], [23, 33, 24]], ![[0, 1], [47, 19, 3], [15, 69, 78], [71, 11, 41], [63, 70, 20], [61, 4, 33], [10, 45, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 37], []]
 b := ![[], [54, 46, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [47, 10, 46, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-915373, -562164, 83108]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11587, -7116, 1052]
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



lemma PB216I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB216I1 : PrimesBelowBoundCertificateInterval O 31 79 216 where
  m := 11
  g := ![2, 3, 2, 1, 2, 2, 2, 1, 2, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB216I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
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
      exact NI53N1
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
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I53N1, I59N1, I61N1, I71N1, I73N0, I73N1, I73N2]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [], [I53N1], [I59N1], [I61N1], [], [I71N1], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
