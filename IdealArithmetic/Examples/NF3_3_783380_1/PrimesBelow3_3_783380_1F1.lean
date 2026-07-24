
import IdealArithmetic.Examples.NF3_3_783380_1.RI3_3_783380_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![13, 1, 0]] 
 ![![37, 0, 0], ![13, 1, 0], ![18, 0, 1]] where
  M :=![![![13, 1, 0], ![0, 13, 5], ![10, 34, 13]]]
  hmulB := by decide  
  f := ![![![-1, -13, 5]], ![![1, 0, 0]], ![![-4, -18, 7]]]
  g := ![![![0, 1, 0], ![-7, 13, 5], ![-18, 34, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -10, 3]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-3, -10, 3]] 
 ![![37, 0, 0], ![28, 1, 0], ![6, 0, 1]] where
  M :=![![![-3, -10, 3], ![30, 99, -50], ![-100, -334, 99]]]
  hmulB := by decide  
  f := ![![![-6899, -12, 203]], ![![-5166, -9, 152]], ![![-1122, -2, 33]]]
  g := ![![![7, -10, 3], ![-66, 99, -50], ![234, -334, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![543, 1, -16]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![543, 1, -16]] 
 ![![37, 0, 0], ![33, 1, 0], ![19, 0, 1]] where
  M :=![![![543, 1, -16], ![-160, -1, 5], ![10, 2, -1]]]
  hmulB := by decide  
  f := ![![![9, 31, 11]], ![![11, 38, 14]], ![![13, 45, 16]]]
  g := ![![![22, 1, -16], ![-6, -1, 5], ![-1, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![13, 1, 0]] ![![-3, -10, 3]]
  ![![-9, -31, -11]] where
 M := ![![![-9, -31, -11]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-9, -31, -11]] ![![543, 1, -16]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![411, 1, -12]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![411, 1, -12]] 
 ![![41, 0, 0], ![0, 41, 0], ![17, 17, 1]] where
  M :=![![![411, 1, -12], ![-120, 3, 5], ![10, 10, 3]]]
  hmulB := by decide  
  f := ![![![1, 3, -1]], ![![-10, -33, 15]], ![![-3, -10, 5]]]
  g := ![![![15, 5, -12], ![-5, -2, 5], ![-1, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [36, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 40], [0, 1]]
 g := ![![[30, 8], [36], [21], [27, 32], [1]], ![[0, 33], [36], [21], [30, 9], [1]]]
 h' := ![![[27, 40], [25, 34], [3, 35], [12, 12], [5, 27], [0, 1]], ![[0, 1], [0, 7], [5, 6], [8, 29], [37, 14], [27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [36, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [36, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56, 56, 25]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -9, 25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -3, 1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-1, -3, 1]] 
 ![![41, 0, 0], ![38, 1, 0], ![31, 0, 1]] where
  M :=![![![-1, -3, 1], ![10, 33, -15], ![-30, -100, 33]]]
  hmulB := by decide  
  f := ![![![-411, -1, 12]], ![![-378, -1, 11]], ![![-311, -1, 9]]]
  g := ![![![2, -3, 1], ![-19, 33, -15], ![67, -100, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![411, 1, -12]] ![![-1, -3, 1]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [1, 39, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 24, 21], [31, 18, 22], [0, 1]]
 g := ![![[2, 0, 31], [39, 42, 16], [5, 17], [28, 29, 1], []], ![[7, 20, 35, 36], [29, 1, 31, 40], [42, 23], [12, 25, 18, 10], [37, 11]], ![[15, 28, 7, 42], [26, 38, 13, 39], [41, 36], [20, 2, 20, 30], [36, 11]]]
 h' := ![![[41, 24, 21], [4, 10, 26], [5, 42, 39], [15, 40, 24], [0, 0, 1], [0, 1]], ![[31, 18, 22], [29, 16, 33], [10, 27, 36], [3, 9, 25], [10, 41, 18], [41, 24, 21]], ![[0, 1], [26, 17, 27], [15, 17, 11], [20, 37, 37], [22, 2, 24], [31, 18, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34], []]
 b := ![[], [38, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [1, 39, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19565, -64070, 40420]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-455, -1490, 940]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![111429, 193, -3279]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![111429, 193, -3279]] 
 ![![47, 0, 0], ![0, 47, 0], ![42, 9, 1]] where
  M :=![![![111429, 193, -3279], ![-32790, -57, 965], ![1930, 4, -57]]]
  hmulB := by decide  
  f := ![![![13, 45, 14]], ![![140, 489, 225]], ![![48, 167, 66]]]
  g := ![![![5301, 632, -3279], ![-1560, -186, 965], ![92, 11, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [35, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 46], [0, 1]]
 g := ![![[45, 18], [32, 12], [11, 37], [29, 12], [1]], ![[36, 29], [26, 35], [16, 10], [23, 35], [1]]]
 h' := ![![[23, 46], [8, 21], [38, 24], [19, 15], [12, 23], [0, 1]], ![[0, 1], [21, 26], [26, 23], [35, 32], [24, 24], [23, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [9, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [35, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2575, -170, 143]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73, -31, 143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 45, 14]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![13, 45, 14]] 
 ![![47, 0, 0], ![2, 1, 0], ![18, 0, 1]] where
  M :=![![![13, 45, 14], ![140, 489, 225], ![450, 1558, 489]]]
  hmulB := by decide  
  f := ![![![111429, 193, -3279]], ![![4044, 7, -119]], ![![42716, 74, -1257]]]
  g := ![![![-7, 45, 14], ![-104, 489, 225], ![-244, 1558, 489]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![111429, 193, -3279]] ![![13, 45, 14]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [1, 8, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10, 52], [9, 42, 1], [0, 1]]
 g := ![![[51, 21, 38], [5, 17], [49, 39, 10], [42, 15], [1]], ![[22, 20, 10, 17], [45, 9], [2, 7, 11, 24], [41, 49], [41, 29, 19, 52]], ![[52, 4, 35, 6], [25, 46], [24, 23, 12, 49], [18, 16], [2, 34, 31, 1]]]
 h' := ![![[2, 10, 52], [11, 32, 41], [4, 31, 21], [12, 36, 13], [52, 45, 11], [0, 1]], ![[9, 42, 1], [25, 48, 47], [21, 44, 3], [41, 1, 33], [20, 28, 46], [2, 10, 52]], ![[0, 1], [43, 26, 18], [42, 31, 29], [48, 16, 7], [38, 33, 49], [9, 42, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 5], []]
 b := ![[], [14, 16, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [1, 8, 42, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6042, 19345, -18762]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![114, 365, -354]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![76119, 132, -2240]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![76119, 132, -2240]] 
 ![![59, 0, 0], ![0, 59, 0], ![34, 7, 1]] where
  M :=![![![76119, 132, -2240], ![-22400, -41, 660], ![1320, 8, -41]]]
  hmulB := by decide  
  f := ![![![61, 212, 80]], ![![800, 2781, 1060]], ![![166, 577, 219]]]
  g := ![![![2581, 268, -2240], ![-760, -79, 660], ![46, 5, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [18, 24, 1] where
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
 g := ![![[21, 1], [16, 16], [12], [50, 21], [35, 1]], ![[56, 58], [45, 43], [12], [18, 38], [11, 58]]]
 h' := ![![[35, 58], [7, 58], [9, 55], [44, 22], [19, 27], [0, 1]], ![[0, 1], [31, 1], [46, 4], [47, 37], [20, 32], [35, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [14, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [18, 24, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38, 46, 15]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -1, 15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -212, -80]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-61, -212, -80]] 
 ![![59, 0, 0], ![24, 1, 0], ![50, 0, 1]] where
  M :=![![![-61, -212, -80], ![-800, -2781, -1060], ![-2120, -7368, -2781]]]
  hmulB := by decide  
  f := ![![![-76119, -132, 2240]], ![![-30584, -53, 900]], ![![-64530, -112, 1899]]]
  g := ![![![153, -212, -80], ![2016, -2781, -1060], ![5318, -7368, -2781]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![76119, 132, -2240]] ![![-61, -212, -80]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9441, -115, -228]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![9441, -115, -228]] 
 ![![61, 0, 0], ![0, 61, 0], ![22, 50, 1]] where
  M :=![![![9441, -115, -228], ![-2280, 1689, -575], ![-1150, -4366, 1689]]]
  hmulB := by decide  
  f := ![![![5611, 19503, 7397]], ![![73970, 257109, 97515]], ![![65852, 228892, 86813]]]
  g := ![![![237, 185, -228], ![170, 499, -575], ![-628, -1456, 1689]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [9, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 60], [0, 1]]
 g := ![![[45, 34], [47], [20, 34], [21, 47], [22, 1]], ![[0, 27], [47], [36, 27], [18, 14], [44, 60]]]
 h' := ![![[22, 60], [13, 41], [3, 48], [55, 20], [46, 48], [0, 1]], ![[0, 1], [0, 20], [22, 13], [7, 41], [4, 13], [22, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [33, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [9, 39, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![429, 2073, 1880]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-671, -1507, 1880]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5611, -19503, -7397]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-5611, -19503, -7397]] 
 ![![61, 0, 0], ![55, 1, 0], ![5, 0, 1]] where
  M :=![![![-5611, -19503, -7397], ![-73970, -257109, -97515], ![-195030, -677896, -257109]]]
  hmulB := by decide  
  f := ![![![-9441, 115, 228]], ![![-8475, 76, 215]], ![![-755, 81, -9]]]
  g := ![![![18099, -19503, -7397], ![238600, -257109, -97515], ![629095, -677896, -257109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![9441, -115, -228]] ![![-5611, -19503, -7397]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [11, 56, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 61, 3], [21, 5, 64], [0, 1]]
 g := ![![[51, 17, 59], [51, 17, 16], [31, 65], [10, 59], [63, 1], []], ![[51, 2, 46, 28], [8, 2, 9, 66], [62, 60], [40, 29], [20, 25], [62, 9]], ![[11, 55, 4, 36], [8, 53, 14, 17], [49, 40], [55, 9], [0, 36], [1, 9]]]
 h' := ![![[42, 61, 3], [42, 63, 27], [15, 52, 4], [17, 48, 47], [44, 12, 27], [0, 0, 1], [0, 1]], ![[21, 5, 64], [10, 13, 56], [28, 4, 42], [24, 8, 44], [14, 51, 37], [10, 12, 5], [42, 61, 3]], ![[0, 1], [44, 58, 51], [13, 11, 21], [63, 11, 43], [47, 4, 3], [28, 55, 61], [21, 5, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 21], []]
 b := ![[], [29, 23, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [11, 56, 4, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4288, 14539, -5628]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![64, 217, -84]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2311, 4, -68]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![2311, 4, -68]] 
 ![![71, 0, 0], ![22, 1, 0], ![31, 0, 1]] where
  M :=![![![2311, 4, -68], ![-680, -1, 20], ![40, 0, -1]]]
  hmulB := by decide  
  f := ![![![1, 4, 12]], ![![2, 7, 4]], ![![1, 4, 11]]]
  g := ![![![61, 4, -68], ![-18, -1, 20], ![1, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-299, 0, 9]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-299, 0, 9]] 
 ![![71, 0, 0], ![23, 1, 0], ![22, 0, 1]] where
  M :=![![![-299, 0, 9], ![90, 7, 0], ![0, 18, 7]]]
  hmulB := by decide  
  f := ![![![-49, -162, 63]], ![![-7, -23, 9]], ![![-38, -126, 49]]]
  g := ![![![-7, 0, 9], ![-1, 7, 0], ![-8, 18, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![436591, 1517527, 575560]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![436591, 1517527, 575560]] 
 ![![71, 0, 0], ![26, 1, 0], ![21, 0, 1]] where
  M :=![![![436591, 1517527, 575560], ![5755600, 20005631, 7587635], ![15175270, 52747038, 20005631]]]
  hmulB := by decide  
  f := ![![![33031, -3257, 285]], ![![12136, -591, -125]], ![![9311, -2515, 686]]]
  g := ![![![-719801, 1517527, 575560], ![-9489171, 20005631, 7587635], ![-25019239, 52747038, 20005631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![2311, 4, -68]] ![![-299, 0, 9]]
  ![![-690629, -1196, 20323]] where
 M := ![![![-690629, -1196, 20323]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-690629, -1196, 20323]] ![![436591, 1517527, 575560]]
  ![![71, 0, 0]] where
 M := ![![![908871, 3164115, 1200113]]]
 hmul := by decide  
 g := ![![![![12801, 44565, 16903]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66371, 120, -1955]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![66371, 120, -1955]] 
 ![![73, 0, 0], ![0, 73, 0], ![10, 44, 1]] where
  M :=![![![66371, 120, -1955], ![-19550, -99, 600], ![1200, 170, -99]]]
  hmulB := by decide  
  f := ![![![1263, 4390, 1665]], ![![16650, 57873, 21950]], ![![10810, 37574, 14251]]]
  g := ![![![1177, 1180, -1955], ![-350, -363, 600], ![30, 62, -99]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [65, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 72], [0, 1]]
 g := ![![[15, 9], [70], [4], [5, 61], [19], [1]], ![[0, 64], [70], [4], [25, 12], [19], [1]]]
 h' := ![![[47, 72], [68, 70], [26, 56], [40, 2], [70, 39], [8, 47], [0, 1]], ![[0, 1], [0, 3], [30, 17], [61, 71], [5, 34], [27, 26], [47, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [41, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [65, 26, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105, 170, 193]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -114, 193]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1263, -4390, -1665]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-1263, -4390, -1665]] 
 ![![73, 0, 0], ![72, 1, 0], ![29, 0, 1]] where
  M :=![![![-1263, -4390, -1665], ![-16650, -57873, -21950], ![-43900, -152590, -57873]]]
  hmulB := by decide  
  f := ![![![-66371, -120, 1955]], ![![-65194, -117, 1920]], ![![-26383, -50, 778]]]
  g := ![![![4974, -4390, -1665], ![65572, -57873, -21950], ![172889, -152590, -57873]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![66371, 120, -1955]] ![![-1263, -4390, -1665]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [69, 77, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 68, 6], [15, 10, 73], [0, 1]]
 g := ![![[68, 8, 52], [18, 75, 20], [56, 26, 4], [34, 78, 46], [63, 1], []], ![[49, 15, 73, 39], [76, 34, 9, 71], [1, 35, 36, 54], [60, 53, 71, 6], [5, 21], [3, 36]], ![[8, 60, 63, 62], [2, 30, 25, 16], [61, 28, 43, 73], [11, 69, 48, 49], [27, 42], [15, 36]]]
 h' := ![![[48, 68, 6], [22, 45, 62], [7, 0, 39], [24, 62, 2], [77, 57, 21], [0, 0, 1], [0, 1]], ![[15, 10, 73], [29, 17, 21], [25, 29, 74], [5, 71, 76], [3, 51, 78], [43, 21, 10], [48, 68, 6]], ![[0, 1], [10, 17, 75], [17, 50, 45], [45, 25, 1], [38, 50, 59], [59, 58, 68], [15, 10, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 71], []]
 b := ![[], [64, 11, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [69, 77, 16, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99145, -332906, 124346]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1255, -4214, 1574]
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



lemma PB197I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB197I1 : PrimesBelowBoundCertificateInterval O 31 79 197 where
  m := 11
  g := ![3, 2, 1, 2, 1, 2, 2, 1, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB197I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
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
      exact NI41N1
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
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I41N1, I47N1, I59N1, I61N1, I71N0, I71N1, I71N2, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [], [I47N1], [], [I59N1], [I61N1], [], [I71N0, I71N1, I71N2], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
