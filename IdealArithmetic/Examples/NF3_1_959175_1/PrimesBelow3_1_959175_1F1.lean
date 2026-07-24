
import IdealArithmetic.Examples.NF3_1_959175_1.RI3_1_959175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-39, -14, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-39, -14, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![35, 23, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-39, -14, 1], ![280, -1, -29], ![-4200, -614, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -23, 37]], ![![-2, -1, 1], ![35, 18, -29], ![-140, -34, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [22, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 36], [0, 1]]
 g := ![![[35, 30], [30], [36, 4], [12], [1]], ![[23, 7], [30], [27, 33], [12], [1]]]
 h' := ![![[7, 36], [9, 17], [22, 20], [35, 35], [15, 7], [0, 1]], ![[0, 1], [17, 20], [14, 17], [21, 2], [27, 30], [7, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [15, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [22, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![862, 1594, 383]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-339, -195, 383]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-8, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-8, 1, 0]] 
 ![![37, 0, 0], ![29, 1, 0], ![9, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-8, 1, 0], ![0, -7, 2], ![280, 52, -9]]]
  hmulB := by decide  
  f := ![![![145, -18, 0], ![666, 0, 0]], ![![121, -15, 0], ![556, 0, 0]], ![![37, -1, -1], ![170, 19, 0]]]
  g := ![![![1, 0, 0], ![-29, 37, 0], ![-9, 0, 37]], ![![-1, 1, 0], ![5, -7, 2], ![-31, 52, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-39, -14, 1]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![-1443, -518, 37], ![592, 111, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-8, 1, 0]]], ![![![-39, -14, 1]], ![![16, 3, -1]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [25, 24, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 14, 29], [6, 26, 12], [0, 1]]
 g := ![![[18, 37, 21], [8, 36], [33, 37], [25, 7, 1], []], ![[21, 32, 3, 34], [33, 18], [13, 2], [13, 3, 10, 6], [16, 21]], ![[7, 31, 40, 11], [27, 16], [28, 1], [31, 18, 31, 15], [33, 21]]]
 h' := ![![[1, 14, 29], [10, 33, 12], [13, 7, 6], [31, 4, 23], [0, 0, 1], [0, 1]], ![[6, 26, 12], [11, 17, 39], [4, 19, 31], [1, 6, 17], [11, 21, 26], [1, 14, 29]], ![[0, 1], [6, 32, 31], [36, 15, 4], [30, 31, 1], [31, 20, 14], [6, 26, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 17], []]
 b := ![[], [22, 16, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [25, 24, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1733234, 963295, 190158]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42274, 23495, 4638]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-55, -4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-55, -4, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![31, 39, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-55, -4, 1], ![280, -7, -9], ![-1400, -94, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -39, 43]], ![![-2, -1, 1], ![13, 8, -9], ![-34, -4, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [1, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 42], [0, 1]]
 g := ![![[16, 1], [27, 14], [35], [21, 41], [1]], ![[0, 42], [18, 29], [35], [10, 2], [1]]]
 h' := ![![[27, 42], [16, 1], [19, 10], [22, 11], [42, 27], [0, 1]], ![[0, 1], [0, 42], [31, 33], [18, 32], [40, 16], [27, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [17, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [1, 16, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2793, 114, 165]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -147, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![9, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![9, 1, 0]] 
 ![![43, 0, 0], ![9, 1, 0], ![41, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![9, 1, 0], ![0, 10, 2], ![280, 52, 8]]]
  hmulB := by decide  
  f := ![![![181, 20, 0], ![-860, 0, 0]], ![![27, 3, 0], ![-128, 0, 0]], ![![173, 14, -1], ![-822, 22, 0]]]
  g := ![![![1, 0, 0], ![-9, 43, 0], ![-41, 0, 43]], ![![0, 1, 0], ![-4, 10, 2], ![-12, 52, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-55, -4, 1]] ![![43, 0, 0], ![9, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![387, 43, 0]], ![![-2365, -172, 43], ![-215, -43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![9, 1, 0]]], ![![![-55, -4, 1]], ![![-5, -1, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [16, 44, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 0, 19], [5, 46, 28], [0, 1]]
 g := ![![[30, 4, 34], [46, 41, 16], [7, 42, 7], [28, 42, 1], []], ![[2, 0, 10, 46], [6, 15, 4, 44], [14, 38, 46, 30], [22, 17, 1, 19], [28, 32]], ![[44, 36, 15, 14], [7, 14, 19, 7], [32, 9, 37, 36], [41, 42], [19, 32]]]
 h' := ![![[37, 0, 19], [16, 41, 9], [29, 21, 4], [22, 23, 17], [0, 0, 1], [0, 1]], ![[5, 46, 28], [46, 2, 18], [25, 27, 19], [33, 9, 44], [28, 42, 46], [37, 0, 19]], ![[0, 1], [13, 4, 20], [5, 46, 24], [0, 15, 33], [3, 5], [5, 46, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 23], []]
 b := ![[], [24, 29, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [16, 44, 5, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4359814, -1871352, -324206]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92762, -39816, -6898]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-48, 2, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-48, 2, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![5, 2, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-48, 2, 1], ![280, 6, 3], ![280, 218, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -2, 53]], ![![-1, 0, 1], ![5, 0, 3], ![5, 4, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [46, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 52], [0, 1]]
 g := ![![[48, 15], [44], [10, 15], [10], [18, 1]], ![[0, 38], [44], [15, 38], [10], [36, 52]]]
 h' := ![![[18, 52], [14, 11], [17, 16], [46, 11], [20, 13], [0, 1]], ![[0, 1], [0, 42], [40, 37], [32, 42], [42, 40], [18, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [13, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [46, 35, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![886, 1584, 368]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, 16, 368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-3, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-3, 1, 0]] 
 ![![53, 0, 0], ![50, 1, 0], ![50, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-3, 1, 0], ![0, -2, 2], ![280, 52, -4]]]
  hmulB := by decide  
  f := ![![![61, -20, 0], ![1060, 0, 0]], ![![58, -19, 0], ![1008, 0, 0]], ![![58, -18, -1], ![1008, 27, 0]]]
  g := ![![![1, 0, 0], ![-50, 53, 0], ![-50, 0, 53]], ![![-1, 1, 0], ![0, -2, 2], ![-40, 52, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-48, 2, 1]] ![![53, 0, 0], ![-3, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-159, 53, 0]], ![![-2544, 106, 53], ![424, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-3, 1, 0]]], ![![![-48, 2, 1]], ![![8, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-58, -7, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-58, -7, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![1, 52, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-58, -7, 1], ![280, -13, -15], ![-2240, -250, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -52, 59]], ![![-1, -1, 1], ![5, 13, -15], ![-38, -6, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [1, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 58], [0, 1]]
 g := ![![[13, 1], [13, 1], [16], [11, 22], [46, 1]], ![[0, 58], [0, 58], [16], [20, 37], [33, 58]]]
 h' := ![![[46, 58], [46, 58], [46, 58], [48, 4], [13, 50], [0, 1]], ![[0, 1], [0, 1], [0, 1], [55, 55], [12, 9], [46, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [6, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [1, 13, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111735, 94654, 23648]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1493, -19238, 23648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![15, 1, 0]] 
 ![![59, 0, 0], ![15, 1, 0], ![57, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![15, 1, 0], ![0, 16, 2], ![280, 52, 14]]]
  hmulB := by decide  
  f := ![![![31, 2, 0], ![-118, 0, 0]], ![![-15, -1, 0], ![60, 0, 0]], ![![33, -6, -1], ![-126, 30, 0]]]
  g := ![![![1, 0, 0], ![-15, 59, 0], ![-57, 0, 59]], ![![0, 1, 0], ![-6, 16, 2], ![-22, 52, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-58, -7, 1]] ![![59, 0, 0], ![15, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![885, 59, 0]], ![![-3422, -413, 59], ![-590, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![15, 1, 0]]], ![![![-58, -7, 1]], ![![-10, -2, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-33, -25, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-33, -25, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![28, 36, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-33, -25, 1], ![280, -6, -51], ![-7280, -1186, 45]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -36, 61]], ![![-1, -1, 1], ![28, 30, -51], ![-140, -46, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [24, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 60], [0, 1]]
 g := ![![[34, 49], [42], [24, 13], [43, 45], [38, 1]], ![[5, 12], [42], [30, 48], [45, 16], [15, 60]]]
 h' := ![![[38, 60], [26, 54], [34, 15], [5, 14], [3, 17], [0, 1]], ![[0, 1], [4, 7], [55, 46], [49, 47], [39, 44], [38, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [47, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [24, 23, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![842, 368, 78]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -40, 78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-10, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-10, 1, 0]] 
 ![![61, 0, 0], ![51, 1, 0], ![16, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-10, 1, 0], ![0, -9, 2], ![280, 52, -11]]]
  hmulB := by decide  
  f := ![![![571, -57, 0], ![3477, 0, 0]], ![![481, -48, 0], ![2929, 0, 0]], ![![156, -11, -1], ![950, 31, 0]]]
  g := ![![![1, 0, 0], ![-51, 61, 0], ![-16, 0, 61]], ![![-1, 1, 0], ![7, -9, 2], ![-36, 52, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-33, -25, 1]] ![![61, 0, 0], ![-10, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-610, 61, 0]], ![![-2013, -1525, 61], ![610, 244, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-10, 1, 0]]], ![![![-33, -25, 1]], ![![10, 4, -1]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [11, 48, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 29, 39], [55, 37, 28], [0, 1]]
 g := ![![[6], [25, 36, 54], [30, 26], [46, 36], [56, 1], []], ![[40, 59, 36, 10], [28, 0, 2, 37], [66, 65], [63, 21], [16, 29], [3, 47]], ![[7, 17, 56, 57], [41, 32, 8, 3], [19, 1], [54, 60], [62, 37], [14, 47]]]
 h' := ![![[1, 29, 39], [60, 26], [9, 14, 56], [65, 34, 48], [54, 48, 6], [0, 0, 1], [0, 1]], ![[55, 37, 28], [19, 17, 9], [40, 4, 5], [37, 48, 20], [44, 52, 17], [35, 0, 37], [1, 29, 39]], ![[0, 1], [16, 24, 58], [18, 49, 6], [48, 52, 66], [21, 34, 44], [57, 0, 29], [55, 37, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 52], []]
 b := ![[], [14, 49, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [11, 48, 11, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5466731, 2168388, 370108]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![81593, 32364, 5524]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-8, -17, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-8, -17, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![63, 54, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-8, -17, 1], ![280, 27, -35], ![-5040, -770, 62]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-63, -54, 71]], ![![-1, -1, 1], ![35, 27, -35], ![-126, -58, 62]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [29, 37, 1] where
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
 g := ![![[38, 49], [18, 12], [2, 25], [54], [20], [1]], ![[0, 22], [0, 59], [0, 46], [54], [20], [1]]]
 h' := ![![[34, 70], [46, 7], [13, 56], [28, 66], [48, 57], [42, 34], [0, 1]], ![[0, 1], [0, 64], [0, 15], [0, 5], [69, 14], [62, 37], [34, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [10, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [29, 37, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16907, 8832, 1694]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1265, -1164, 1694]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![35, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![35, 1, 0]] 
 ![![71, 0, 0], ![35, 1, 0], ![9, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![35, 1, 0], ![0, 36, 2], ![280, 52, 34]]]
  hmulB := by decide  
  f := ![![![2346, 67, 0], ![-4757, 0, 0]], ![![1120, 32, 0], ![-2271, 0, 0]], ![![254, -11, -1], ![-515, 36, 0]]]
  g := ![![![1, 0, 0], ![-35, 71, 0], ![-9, 0, 71]], ![![0, 1, 0], ![-18, 36, 2], ![-26, 52, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-8, -17, 1]] ![![71, 0, 0], ![35, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2485, 71, 0]], ![![-568, -1207, 71], ![0, -568, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![35, 1, 0]]], ![![![-8, -17, 1]], ![![0, -8, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-71, 34, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-71, 34, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![2, 34, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-71, 34, 1], ![280, 15, 67], ![9240, 1882, -52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -34, 73]], ![![-1, 0, 1], ![2, -31, 67], ![128, 50, -52]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [19, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 72], [0, 1]]
 g := ![![[48, 50], [35], [4], [6, 54], [55], [1]], ![[0, 23], [35], [4], [33, 19], [55], [1]]]
 h' := ![![[37, 72], [66, 14], [72, 20], [32, 71], [46, 45], [54, 37], [0, 1]], ![[0, 1], [0, 59], [9, 53], [31, 2], [32, 28], [36, 36], [37, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [33, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [19, 36, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![376, 114, 115]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -52, 115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![6, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![6, 1, 0]] 
 ![![73, 0, 0], ![6, 1, 0], ![52, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![6, 1, 0], ![0, 7, 2], ![280, 52, 5]]]
  hmulB := by decide  
  f := ![![![343, 57, 0], ![-4161, 0, 0]], ![![18, 3, 0], ![-218, 0, 0]], ![![244, 37, -1], ![-2960, 37, 0]]]
  g := ![![![1, 0, 0], ![-6, 73, 0], ![-52, 0, 73]], ![![0, 1, 0], ![-2, 7, 2], ![-4, 52, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-71, 34, 1]] ![![73, 0, 0], ![6, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![438, 73, 0]], ![![-5183, 2482, 73], ![-146, 219, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![6, 1, 0]]], ![![![-71, 34, 1]], ![![-2, 3, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-41, -27, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-41, -27, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![38, 52, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-41, -27, 1], ![280, -16, -55], ![-7840, -1290, 39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -52, 79]], ![![-1, -1, 1], ![30, 36, -55], ![-118, -42, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [68, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 78], [0, 1]]
 g := ![![[11, 25], [59, 32], [50, 46], [12, 22], [26], [1]], ![[34, 54], [60, 47], [7, 33], [67, 57], [26], [1]]]
 h' := ![![[42, 78], [17, 74], [76, 43], [53, 21], [12, 41], [11, 42], [0, 1]], ![[0, 1], [44, 5], [65, 36], [66, 58], [75, 38], [37, 37], [42, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [48, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [68, 37, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6826, 7054, 1664]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-714, -1006, 1664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-24, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-24, 1, 0]] 
 ![![79, 0, 0], ![55, 1, 0], ![40, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-24, 1, 0], ![0, -23, 2], ![280, 52, -25]]]
  hmulB := by decide  
  f := ![![![1585, -66, 0], ![5214, 0, 0]], ![![1081, -45, 0], ![3556, 0, 0]], ![![808, -22, -1], ![2658, 40, 0]]]
  g := ![![![1, 0, 0], ![-55, 79, 0], ![-40, 0, 79]], ![![-1, 1, 0], ![15, -23, 2], ![-20, 52, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-41, -27, 1]] ![![79, 0, 0], ![-24, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1896, 79, 0]], ![![-3239, -2133, 79], ![1264, 632, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-24, 1, 0]]], ![![![-41, -27, 1]], ![![16, 8, -1]]]]
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


lemma PB278I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB278I1 : PrimesBelowBoundCertificateInterval O 31 79 278 where
  m := 11
  g := ![2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB278I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I53N1, I59N1, I61N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [], [I43N1], [], [I53N1], [I59N1], [I61N1], [], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
