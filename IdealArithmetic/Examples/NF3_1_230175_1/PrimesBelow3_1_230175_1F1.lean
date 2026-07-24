
import IdealArithmetic.Examples.NF3_1_230175_1.RI3_1_230175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![244, 20, -19]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![244, 20, -19]] 
 ![![37, 0, 0], ![0, 37, 0], ![30, 34, 1]] where
  M :=![![![244, 20, -19], ![-1995, -41, 100], ![2100, -99, -41]]]
  hmulB := by decide  
  f := ![![![313, 73, 33]], ![![3465, 808, 365]], ![![3645, 850, 384]]]
  g := ![![![22, 18, -19], ![-135, -93, 100], ![90, 35, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [20, 0, 1] where
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
 g := ![![[], [33], [], [], [1]], ![[], [33], [], [], [1]]]
 h' := ![![[0, 36], [6], [0, 12], [30], [17], [0, 1]], ![[0, 1], [6], [0, 25], [30], [17], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [0, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [20, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![230, 51, 20]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -17, 20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-313, -73, -33]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-313, -73, -33]] 
 ![![37, 0, 0], ![15, 1, 0], ![29, 0, 1]] where
  M :=![![![-313, -73, -33], ![-3465, -808, -365], ![-7665, -1788, -808]]]
  hmulB := by decide  
  f := ![![![-244, -20, 19]], ![![-45, -7, 5]], ![![-248, -13, 16]]]
  g := ![![![47, -73, -33], ![520, -808, -365], ![1151, -1788, -808]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![244, 20, -19]] ![![-313, -73, -33]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![1, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![1, 1, 0]] 
 ![![41, 0, 0], ![1, 1, 0], ![8, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![1, 1, 0], ![0, 1, 5], ![105, 15, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![41, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![8, -8, 0]]]
  g := ![![![1, 0, 0], ![-1, 41, 0], ![-8, 0, 41]], ![![0, 1, 0], ![-1, 1, 5], ![2, 15, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![0, 12, 5], ![105, 15, 12]]]
  hmulB := by decide  
  f := ![![![193, 16, 0], ![-656, 0, 0]], ![![36, 3, 0], ![-122, 0, 0]], ![![-4, -10, -4], ![14, 33, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-4, 0, 41]], ![![0, 1, 0], ![-4, 12, 5], ![-3, 15, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![446, 104, 47]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![446, 104, 47]] 
 ![![41, 0, 0], ![28, 1, 0], ![40, 0, 1]] where
  M :=![![![446, 104, 47], ![4935, 1151, 520], ![10920, 2547, 1151]]]
  hmulB := by decide  
  f := ![![![361, 5, -17]], ![![203, 6, -11]], ![![365, -2, -14]]]
  g := ![![![-106, 104, 47], ![-1173, 1151, 520], ![-2596, 2547, 1151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![1, 1, 0]] ![![41, 0, 0], ![12, 1, 0]]
  ![![-361, -5, 17]] where
 M := ![![![1681, 0, 0], ![492, 41, 0]], ![![41, 41, 0], ![12, 13, 5]]]
 hmul := by decide  
 g := ![![![![-18286, -4264, -1927]], ![![-10287, -2399, -1084]]], ![![![-5381, -1255, -567]], ![![-3027, -706, -319]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-361, -5, 17]] ![![446, 104, 47]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [36, 41, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 32, 22], [5, 10, 21], [0, 1]]
 g := ![![[24, 11, 36], [7, 30, 4], [26, 15], [3, 1, 1], []], ![[3, 30, 22, 3], [6, 23, 5, 19], [34, 17], [28, 25, 41, 7], [0, 11]], ![[0, 37, 3, 23], [18, 16, 20, 40], [34, 15], [36, 25, 1, 4], [1, 11]]]
 h' := ![![[39, 32, 22], [6, 20, 37], [21, 15, 41], [21, 13, 12], [0, 0, 1], [0, 1]], ![[5, 10, 21], [2, 37, 36], [15, 21, 9], [32, 31, 19], [16, 36, 10], [39, 32, 22]], ![[0, 1], [0, 29, 13], [32, 7, 36], [40, 42, 12], [32, 7, 32], [5, 10, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 5], []]
 b := ![[], [37, 3, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [36, 41, 42, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78819, 8471, 9030]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1833, 197, 210]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 5, -3]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![19, 5, -3]] 
 ![![47, 0, 0], ![0, 47, 0], ![25, 14, 1]] where
  M :=![![![19, 5, -3], ![-315, -26, 25], ![525, 12, -26]]]
  hmulB := by decide  
  f := ![![![8, 2, 1]], ![![105, 23, 10]], ![![40, 9, 4]]]
  g := ![![![2, 1, -3], ![-20, -8, 25], ![25, 8, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 46], [0, 1]]
 g := ![![[0, 24], [0, 37], [0, 16], [], [1]], ![[0, 23], [0, 10], [0, 31], [], [1]]]
 h' := ![![[0, 46], [0, 20], [0, 15], [0, 4], [45], [0, 1]], ![[0, 1], [0, 27], [0, 32], [0, 43], [45], [0, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [0, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3888, -137, 148]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, -47, 148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, -2, -1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-8, -2, -1]] 
 ![![47, 0, 0], ![24, 1, 0], ![7, 0, 1]] where
  M :=![![![-8, -2, -1], ![-105, -23, -10], ![-210, -51, -23]]]
  hmulB := by decide  
  f := ![![![-19, -5, 3]], ![![-3, -2, 1]], ![![-14, -1, 1]]]
  g := ![![![1, -2, -1], ![11, -23, -10], ![25, -51, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![19, 5, -3]] ![![-8, -2, -1]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [48, 15, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 24, 49], [6, 28, 4], [0, 1]]
 g := ![![[45, 23, 17], [34, 28], [25, 23, 15], [35, 43], [1]], ![[47, 43, 20, 52], [4, 40], [45, 35, 11, 44], [43, 28], [35, 28, 42, 42]], ![[39, 32, 49, 38], [0, 24], [51, 9, 47, 42], [9, 42], [28, 30, 16, 11]]]
 h' := ![![[13, 24, 49], [1, 45, 32], [19, 43, 9], [41, 17, 11], [5, 38, 19], [0, 1]], ![[6, 28, 4], [11, 5, 27], [37, 39, 27], [13, 7, 28], [40, 17, 9], [13, 24, 49]], ![[0, 1], [43, 3, 47], [34, 24, 17], [5, 29, 14], [38, 51, 25], [6, 28, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 4], []]
 b := ![[], [5, 35, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [48, 15, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39697, -8056, 1007]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-749, -152, 19]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![10, 8, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![10, 8, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![10, 8, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![10, 8, 1], ![105, 25, 40], ![840, 141, 25]]]
  hmulB := by decide  
  f := ![![![-9, -8, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -8, 59]], ![![0, 0, 1], ![-5, -5, 40], ![10, -1, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [45, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 58], [0, 1]]
 g := ![![[32, 21], [38, 36], [15], [], [35, 1]], ![[0, 38], [0, 23], [15], [], [11, 58]]]
 h' := ![![[35, 58], [1, 32], [33, 53], [0, 29], [18], [0, 1]], ![[0, 1], [0, 27], [0, 6], [12, 30], [18], [35, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [50, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [45, 24, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![255, 27, -4]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 1, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![19, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![19, 1, 0]] 
 ![![59, 0, 0], ![19, 1, 0], ![34, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![19, 1, 0], ![0, 19, 5], ![105, 15, 19]]]
  hmulB := by decide  
  f := ![![![381, 20, 0], ![-1180, 0, 0]], ![![95, 5, 0], ![-294, 0, 0]], ![![188, 6, -1], ![-582, 12, 0]]]
  g := ![![![1, 0, 0], ![-19, 59, 0], ![-34, 0, 59]], ![![0, 1, 0], ![-9, 19, 5], ![-14, 15, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![10, 8, 1]] ![![59, 0, 0], ![19, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1121, 59, 0]], ![![590, 472, 59], ![295, 177, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![19, 1, 0]]], ![![![10, 8, 1]], ![![5, 3, 1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [50, 46, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 10, 43], [6, 50, 18], [0, 1]]
 g := ![![[8, 21, 47], [12, 25], [36, 55, 27], [17, 22, 52], [1]], ![[18, 13, 7, 59], [13, 56], [45, 20, 17, 29], [16, 8, 49, 55], [41, 26, 20, 24]], ![[42, 12, 18, 21], [19, 13], [24, 31, 35, 37], [47, 39, 30, 31], [29, 10, 45, 37]]]
 h' := ![![[27, 10, 43], [56, 26, 48], [30, 2, 56], [4, 8, 24], [11, 15, 33], [0, 1]], ![[6, 50, 18], [9, 7, 41], [54, 40, 19], [59, 45, 19], [4, 18, 38], [27, 10, 43]], ![[0, 1], [17, 28, 33], [28, 19, 47], [46, 8, 18], [47, 28, 51], [6, 50, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 9], []]
 b := ![[], [0, 3, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [50, 46, 28, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3816770, 661911, 143960]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![62570, 10851, 2360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [48, 22, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 18, 61], [35, 48, 6], [0, 1]]
 g := ![![[7, 44, 65], [48, 2, 47], [61, 25], [33, 25], [34, 1], []], ![[45, 51, 24, 20], [38, 59, 20, 31], [58, 29], [22, 65], [7, 26], [3, 36]], ![[32, 52, 47, 10], [50, 32, 30, 24], [48, 19], [25, 22], [47, 56], [58, 36]]]
 h' := ![![[66, 18, 61], [41, 24, 47], [29, 62, 39], [64, 35, 5], [43, 8, 62], [0, 0, 1], [0, 1]], ![[35, 48, 6], [63, 48, 35], [18, 29, 26], [51, 56, 30], [13, 48, 47], [58, 46, 48], [66, 18, 61]], ![[0, 1], [35, 62, 52], [23, 43, 2], [60, 43, 32], [11, 11, 25], [49, 21, 18], [35, 48, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 29], []]
 b := ![[], [0, 5, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [48, 22, 33, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7303, -1608, 536]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![109, -24, 8]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, -19, 11]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-59, -19, 11]] 
 ![![71, 0, 0], ![0, 71, 0], ![14, 37, 1]] where
  M :=![![![-59, -19, 11], ![1155, 106, -95], ![-1995, -54, 106]]]
  hmulB := by decide  
  f := ![![![86, 20, 9]], ![![945, 221, 100]], ![![539, 126, 57]]]
  g := ![![![-3, -6, 11], ![35, 51, -95], ![-49, -56, 106]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [5, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 70], [0, 1]]
 g := ![![[65, 57], [8, 32], [56, 24], [16], [48], [1]], ![[0, 14], [45, 39], [66, 47], [16], [48], [1]]]
 h' := ![![[30, 70], [31, 25], [4, 23], [66, 38], [69, 4], [66, 30], [0, 1]], ![[0, 1], [0, 46], [55, 48], [70, 33], [47, 67], [43, 41], [30, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [67, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [5, 41, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![425, 185, 147]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -74, 147]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![86, 20, 9]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![86, 20, 9]] 
 ![![71, 0, 0], ![28, 1, 0], ![42, 0, 1]] where
  M :=![![![86, 20, 9], ![945, 221, 100], ![2100, 489, 221]]]
  hmulB := by decide  
  f := ![![![-59, -19, 11]], ![![-7, -6, 3]], ![![-63, -12, 8]]]
  g := ![![![-12, 20, 9], ![-133, 221, 100], ![-294, 489, 221]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-59, -19, 11]] ![![86, 20, 9]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [69, 25, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 4, 47], [19, 68, 26], [0, 1]]
 g := ![![[30, 33, 72], [71, 8], [0, 46], [72, 34, 65], [66, 1], []], ![[43, 31, 59, 52], [36, 18], [56, 25], [34, 44, 4, 34], [64, 25], [24, 19]], ![[6, 20, 17, 53], [13, 2], [25, 72], [43, 48, 18, 66], [50, 16], [45, 19]]]
 h' := ![![[47, 4, 47], [29, 59, 46], [16, 70, 64], [69, 69, 51], [45, 33, 24], [0, 0, 1], [0, 1]], ![[19, 68, 26], [62, 71, 61], [8, 6, 50], [52, 28, 68], [49, 11, 44], [42, 71, 68], [47, 4, 47]], ![[0, 1], [48, 16, 39], [54, 70, 32], [63, 49, 27], [5, 29, 5], [30, 2, 4], [19, 68, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 6], []]
 b := ![[], [57, 64, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [69, 25, 7, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-750805, -41318, 41610]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10285, -566, 570]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [23, 14, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 77, 41], [36, 1, 38], [0, 1]]
 g := ![![[2, 75, 55], [33, 31, 8], [34, 23, 38], [3, 42, 49], [69, 1], []], ![[55, 67, 56, 3], [24, 17, 13, 34], [12, 0, 77, 39], [27, 32, 67, 61], [65, 1], [11, 22]], ![[2, 39, 64, 22], [45, 41, 46, 16], [13, 3, 56, 9], [76, 76, 13, 62], [31, 4], [14, 22]]]
 h' := ![![[33, 77, 41], [31, 74, 56], [8, 43, 61], [10, 68, 14], [72, 38, 7], [0, 0, 1], [0, 1]], ![[36, 1, 38], [72, 56, 9], [46, 29, 7], [54, 73, 37], [68, 68, 64], [46, 77, 1], [33, 77, 41]], ![[0, 1], [43, 28, 14], [61, 7, 11], [57, 17, 28], [42, 52, 8], [26, 2, 77], [36, 1, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 49], []]
 b := ![[], [58, 47, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [23, 14, 10, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9243, -1027, 1896]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-117, -13, 24]
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



lemma PB136I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB136I1 : PrimesBelowBoundCertificateInterval O 31 79 136 where
  m := 11
  g := ![2, 3, 1, 2, 1, 2, 1, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB136I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
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
      exact NI41N1
      exact NI41N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
  β := ![I37N1, I41N0, I41N1, I41N2, I47N1, I59N1, I71N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [], [I47N1], [], [I59N1], [], [], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
