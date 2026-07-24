
import IdealArithmetic.Examples.NF3_3_701244_1.RI3_3_701244_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 117, 20]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![277, 117, 20]] 
 ![![37, 0, 0], ![0, 37, 0], ![12, 4, 1]] where
  M :=![![![277, 117, 20], ![3400, 1417, 234], ![19890, 8369, 1417]]]
  hmulB := by decide  
  f := ![![![-1339, -43, 26]], ![![4420, 143, -86]], ![![-154, -5, 3]]]
  g := ![![![1, 1, 20], ![16, 13, 234], ![78, 73, 1417]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [35, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 36], [0, 1]]
 g := ![![[], [34], [], [], [1]], ![[], [34], [], [], [1]]]
 h' := ![![[0, 36], [31], [0, 16], [4], [2], [0, 1]], ![[0, 1], [31], [0, 21], [4], [2], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [0, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [35, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![375, 199, 59]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -1, 59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1339, 43, -26]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![1339, 43, -26]] 
 ![![37, 0, 0], ![29, 1, 0], ![5, 0, 1]] where
  M :=![![![1339, 43, -26], ![-4420, -143, 86], ![7310, 241, -143]]]
  hmulB := by decide  
  f := ![![![-277, -117, -20]], ![![-309, -130, -22]], ![![-575, -242, -41]]]
  g := ![![![6, 43, -26], ![-19, -143, 86], ![28, 241, -143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![277, 117, 20]] ![![1339, 43, -26]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [30, 4, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 14, 24], [6, 26, 17], [0, 1]]
 g := ![![[34, 22, 40], [25, 37], [12, 2], [35, 11, 1], []], ![[14, 24, 20, 17], [20, 33], [9, 16], [32, 8, 0, 29], [38, 2]], ![[31, 12], [24, 1], [36, 5], [33, 37, 6, 11], [4, 2]]]
 h' := ![![[5, 14, 24], [21, 36, 9], [19, 22, 23], [16, 22, 24], [0, 0, 1], [0, 1]], ![[6, 26, 17], [6, 20, 32], [27, 5, 19], [16, 15, 4], [33, 10, 26], [5, 14, 24]], ![[0, 1], [14, 26], [23, 14, 40], [18, 4, 13], [39, 31, 14], [6, 26, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 24], []]
 b := ![[], [28, 34, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [30, 4, 30, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-190855, 93685, 96555]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4655, 2285, 2355]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![9, 1, 0]] 
 ![![43, 0, 0], ![9, 1, 0], ![24, 0, 1]] where
  M :=![![![9, 1, 0], ![0, 9, 2], ![170, 57, 9]]]
  hmulB := by decide  
  f := ![![![-33, -9, 2]], ![![1, 0, 0]], ![![-54, -13, 3]]]
  g := ![![![0, 1, 0], ![-3, 9, 2], ![-13, 57, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117, -26, 6]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-117, -26, 6]] 
 ![![43, 0, 0], ![25, 1, 0], ![10, 0, 1]] where
  M :=![![![-117, -26, 6], ![1020, 225, -52], ![-4420, -972, 225]]]
  hmulB := by decide  
  f := ![![![81, 18, 2]], ![![55, 15, 2]], ![![90, 32, 5]]]
  g := ![![![11, -26, 6], ![-95, 225, -52], ![410, -972, 225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![9, 1, 0]] ![![9, 1, 0]]
  ![![81, 18, 2]] where
 M := ![![![81, 18, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![81, 18, 2]] ![![-117, -26, 6]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [14, 22, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 8, 15], [42, 38, 32], [0, 1]]
 g := ![![[45, 24, 3], [22, 8, 37], [36, 13, 4], [37, 23, 1], []], ![[11, 3, 17, 15], [3, 19, 4, 33], [30, 40, 19, 41], [24, 11, 15, 40], [10, 37]], ![[42, 5, 43, 18], [27, 15, 21, 32], [42, 9, 26, 1], [15, 46, 5, 27], [40, 37]]]
 h' := ![![[28, 8, 15], [21, 43, 35], [13, 14, 32], [46, 39, 2], [0, 0, 1], [0, 1]], ![[42, 38, 32], [30, 17, 1], [4, 44, 16], [29, 14, 3], [33, 39, 38], [28, 8, 15]], ![[0, 1], [22, 34, 11], [25, 36, 46], [3, 41, 42], [29, 8, 8], [42, 38, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 33], []]
 b := ![[], [8, 12, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [14, 22, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-93154, 13771, -22231]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1982, 293, -473]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-373, -156, -26]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-373, -156, -26]] 
 ![![53, 0, 0], ![22, 1, 0], ![23, 0, 1]] where
  M :=![![![-373, -156, -26], ![-4420, -1855, -312], ![-26520, -11102, -1855]]]
  hmulB := by decide  
  f := ![![![22799, 728, -442]], ![![8046, 257, -156]], ![![12229, 390, -237]]]
  g := ![![![69, -156, -26], ![822, -1855, -312], ![4913, -11102, -1855]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81829, -17967, 4158]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-81829, -17967, 4158]] 
 ![![53, 0, 0], ![38, 1, 0], ![20, 0, 1]] where
  M :=![![![-81829, -17967, 4158], ![706860, 155177, -35934], ![-3054390, -670689, 155177]]]
  hmulB := by decide  
  f := ![![![-20637197, -659703, 400212]], ![![-13512782, -431959, 262050]], ![![-9903650, -316587, 192059]]]
  g := ![![![9769, -17967, 4158], ![-84362, 155177, -35934], ![364684, -670689, 155177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-82421, -35148, -6156]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-82421, -35148, -6156]] 
 ![![53, 0, 0], ![46, 1, 0], ![2, 0, 1]] where
  M :=![![![-82421, -35148, -6156], ![-1046520, -433313, -70296], ![-5975160, -2526696, -433313]]]
  hmulB := by decide  
  f := ![![![-10143533953, -324255252, 196711020]], ![![-8172862046, -261259385, 158494272]], ![![-1422838882, -45483456, 27592759]]]
  g := ![![![29183, -35148, -6156], ![358990, -433313, -70296], ![2096594, -2526696, -433313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-373, -156, -26]] ![![-81829, -17967, 4158]]
  ![![-333803, -68007, 20168]] where
 M := ![![![-333803, -68007, 20168]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-333803, -68007, 20168]] ![![-82421, -35148, -6156]]
  ![![53, 0, 0]] where
 M := ![![![-21823964177, -9757579893, -1903545244]]]
 hmul := by decide  
 g := ![![![![-411772909, -184105281, -35915948]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [15, 4, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 29, 42], [7, 29, 17], [0, 1]]
 g := ![![[27, 19, 29], [47, 22, 17], [56, 5], [55, 10, 48], [1]], ![[14, 18, 42, 43], [2, 22, 31, 24], [29, 53], [40, 28, 49, 6], [15, 56, 5, 43]], ![[53, 4, 12, 57], [8, 8, 57, 53], [53, 22], [51, 23, 1, 41], [8, 3, 13, 16]]]
 h' := ![![[8, 29, 42], [3, 5, 41], [46, 1, 31], [1, 32, 8], [44, 55, 15], [0, 1]], ![[7, 29, 17], [8, 21, 42], [52, 0, 56], [30, 26, 42], [51, 7, 31], [8, 29, 42]], ![[0, 1], [2, 33, 35], [56, 58, 31], [5, 1, 9], [46, 56, 13], [7, 29, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 41], []]
 b := ![[], [17, 23, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [15, 4, 44, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-176056, -155347, -60239]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2984, -2633, -1021]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![551, 121, -28]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![551, 121, -28]] 
 ![![61, 0, 0], ![25, 1, 0], ![23, 0, 1]] where
  M :=![![![551, 121, -28], ![-4760, -1045, 242], ![20570, 4517, -1045]]]
  hmulB := by decide  
  f := ![![![-1089, -31, 22]], ![![-385, -10, 8]], ![![-497, -10, 11]]]
  g := ![![![-30, 121, -28], ![259, -1045, 242], ![-1120, 4517, -1045]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1077, 208, -72]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![1077, 208, -72]] 
 ![![61, 0, 0], ![40, 1, 0], ![54, 0, 1]] where
  M :=![![![1077, 208, -72], ![-12240, -3027, 416], ![35360, 5736, -3027]]]
  hmulB := by decide  
  f := ![![![6776553, 216624, -131416]], ![![4077400, 130341, -79072]], ![![6602622, 211064, -128043]]]
  g := ![![![-55, 208, -72], ![1416, -3027, 416], ![-502, 5736, -3027]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-96343117, -3079771, 1868358]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-96343117, -3079771, 1868358]] 
 ![![61, 0, 0], ![57, 1, 0], ![53, 0, 1]] where
  M :=![![![-96343117, -3079771, 1868358], ![317620860, 10153289, -6159542], ![-523561070, -16736517, 10153289]]]
  hmulB := by decide  
  f := ![![![-1877693, -412267, 95420]], ![![-1488641, -326852, 75646]], ![![-2780379, -610470, 141287]]]
  g := ![![![-324904, -3079771, 1868358], ![1071133, 10153289, -6159542], ![-1765638, -16736517, 10153289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![551, 121, -28]] ![![1077, 208, -72]]
  ![![-1877693, -412267, 95420]] where
 M := ![![![-1877693, -412267, 95420]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-1877693, -412267, 95420]] ![![-96343117, -3079771, 1868358]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [8, 12, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 40, 6], [27, 26, 61], [0, 1]]
 g := ![![[26, 36, 59], [12, 17, 59], [66, 26], [10, 62], [20, 1], []], ![[10, 61, 63, 39], [34, 37, 59, 26], [14, 15], [16, 40], [35, 6], [61, 36]], ![[19, 64, 42, 5], [61, 7, 50, 32], [54, 9], [41, 33], [12, 59], [6, 36]]]
 h' := ![![[60, 40, 6], [38, 21, 27], [57, 7, 27], [60, 19, 48], [41, 20, 53], [0, 0, 1], [0, 1]], ![[27, 26, 61], [31, 55, 24], [14, 31, 7], [27, 27, 22], [17, 6, 24], [30, 28, 26], [60, 40, 6]], ![[0, 1], [31, 58, 16], [7, 29, 33], [29, 21, 64], [25, 41, 57], [11, 39, 40], [27, 26, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 1], []]
 b := ![[], [27, 20, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [8, 12, 47, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27872, -10720, -1340]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-416, -160, -20]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [28, 64, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 57, 65], [29, 13, 6], [0, 1]]
 g := ![![[7, 51, 18], [61, 8, 19], [59, 14, 50], [55, 49], [46, 1], []], ![[15, 2, 42, 44], [29, 44, 20, 22], [69, 21, 23, 52], [7, 10], [47, 27], [49, 36]], ![[66, 60, 67, 30], [64, 15, 5, 10], [41, 56, 40, 32], [48, 43], [1, 54], [37, 36]]]
 h' := ![![[17, 57, 65], [67, 67, 35], [52, 66, 44], [51, 20, 60], [61, 10, 64], [0, 0, 1], [0, 1]], ![[29, 13, 6], [8, 23, 53], [27, 63, 34], [21, 59, 21], [2, 37, 62], [53, 66, 13], [17, 57, 65]], ![[0, 1], [13, 52, 54], [60, 13, 64], [7, 63, 61], [12, 24, 16], [18, 5, 57], [29, 13, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 59], []]
 b := ![[], [66, 2, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [28, 64, 25, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3079838, 1226170, 158330]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43378, 17270, 2230]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [29, 42, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 4, 57], [60, 68, 16], [0, 1]]
 g := ![![[64, 41, 8], [30, 16], [48, 16], [62, 1, 16], [29, 1], []], ![[40, 68, 32, 38], [65, 54], [50, 8], [36, 52, 8, 54], [64, 25], [69, 37]], ![[19, 39, 29, 37], [53, 65], [66, 23], [20, 59, 67, 27], [52, 16], [37, 37]]]
 h' := ![![[42, 4, 57], [42, 34, 9], [67, 36, 69], [27, 52, 69], [35, 67, 69], [0, 0, 1], [0, 1]], ![[60, 68, 16], [67, 52, 68], [45, 11, 28], [20, 2, 64], [1, 62, 43], [55, 15, 68], [42, 4, 57]], ![[0, 1], [5, 60, 69], [3, 26, 49], [47, 19, 13], [6, 17, 34], [45, 58, 4], [60, 68, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 50], []]
 b := ![[], [63, 55, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [29, 42, 44, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![40150, 7373, -1679]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![550, 101, -23]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [3, 12, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 24, 4], [77, 54, 75], [0, 1]]
 g := ![![[55, 67, 25], [54, 30, 21], [61, 7, 25], [24, 2, 21], [70, 1], []], ![[16, 47, 41, 13], [33, 34, 58, 31], [11, 12, 0, 52], [6, 14, 51, 9], [31, 72], [48, 16]], ![[72, 17, 30, 57], [38, 64, 62, 28], [38, 25, 60, 30], [14, 5, 69, 24], [53, 23], [56, 16]]]
 h' := ![![[72, 24, 4], [75, 45, 5], [54, 7, 10], [7, 40, 74], [27, 26, 69], [0, 0, 1], [0, 1]], ![[77, 54, 75], [75, 72, 55], [3, 48, 15], [44, 72, 48], [5, 33, 38], [63, 67, 54], [72, 24, 4]], ![[0, 1], [34, 41, 19], [59, 24, 54], [36, 46, 36], [35, 20, 51], [73, 12, 24], [77, 54, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74], []]
 b := ![[], [9, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [3, 12, 9, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![238343, 122766, 30810]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3017, 1554, 390]
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



lemma PB187I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB187I1 : PrimesBelowBoundCertificateInterval O 31 79 187 where
  m := 11
  g := ![2, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB187I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![357911]
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
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I43N0, I43N1, I53N0, I53N1, I53N2, I61N0, I61N1, I61N2]
  Il := ![[I37N1], [], [I43N0, I43N0, I43N1], [], [I53N0, I53N1, I53N2], [], [I61N0, I61N1, I61N2], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
