
import IdealArithmetic.Examples.NF3_1_996008_1.RI3_1_996008_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-24, 1, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-24, 1, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![13, 1, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-24, 1, 1], ![198, 1, 1], ![198, 223, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -1, 37]], ![![-1, 0, 1], ![5, 0, 1], ![5, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [23, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 36], [0, 1]]
 g := ![![[29, 7], [1], [3, 27], [1], [1]], ![[22, 30], [1], [13, 10], [1], [1]]]
 h' := ![![[36, 36], [2, 9], [5, 1], [25, 8], [14, 36], [0, 1]], ![[0, 1], [30, 28], [4, 36], [17, 29], [15, 1], [36, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [24, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [23, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2353, 1484, 226]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, 34, 226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-1, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-1, 1, 0]] 
 ![![37, 0, 0], ![36, 1, 0], ![36, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-1, 1, 0], ![0, -1, 1], ![198, 25, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![111, 0, 0]], ![![2, -1, 0], ![38, 0, 0]], ![![2, -1, 0], ![38, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 37, 0], ![-36, 0, 37]], ![![-1, 1, 0], ![0, -1, 1], ![-18, 25, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-24, 1, 1]] ![![37, 0, 0], ![-1, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-37, 37, 0]], ![![-888, 37, 37], ![222, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-1, 1, 0]]], ![![![-24, 1, 1]], ![![6, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![15, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![15, 1, 0]] 
 ![![41, 0, 0], ![15, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![15, 1, 0], ![0, 15, 1], ![198, 25, 15]]]
  hmulB := by decide  
  f := ![![![136, 9, 0], ![-369, 0, 0]], ![![30, 2, 0], ![-81, 0, 0]], ![![66, 4, 0], ![-179, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-6, 15, 1], ![-12, 25, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-12, 1, 0]] 
 ![![41, 0, 0], ![29, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-12, 1, 0], ![0, -12, 1], ![198, 25, -12]]]
  hmulB := by decide  
  f := ![![![361, -30, 0], ![1230, 0, 0]], ![![253, -21, 0], ![862, 0, 0]], ![![196, -16, 0], ![668, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 41, 0], ![-20, 0, 41]], ![![-1, 1, 0], ![8, -12, 1], ![-7, 25, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-3, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-3, 1, 0]] 
 ![![41, 0, 0], ![38, 1, 0], ![32, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-3, 1, 0], ![0, -3, 1], ![198, 25, -3]]]
  hmulB := by decide  
  f := ![![![49, -16, 0], ![656, 0, 0]], ![![46, -15, 0], ![616, 0, 0]], ![![40, -13, 0], ![536, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 41, 0], ![-32, 0, 41]], ![![-1, 1, 0], ![2, -3, 1], ![-16, 25, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![15, 1, 0]] ![![41, 0, 0], ![-12, 1, 0]]
  ![![41, 0, 0], ![-16, 3, 1]] where
 M := ![![![1681, 0, 0], ![-492, 41, 0]], ![![615, 41, 0], ![-180, 3, 1]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![4, -2, -1], ![41, 0, 0]]], ![![![15, 1, 0], ![0, 0, 0]], ![![12, -3, -1], ![42, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-16, 3, 1]] ![![41, 0, 0], ![-3, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-123, 41, 0]], ![![-656, 123, 41], ![246, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-3, 1, 0]]], ![![![-16, 3, 1]], ![![6, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [22, 16, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40, 18], [20, 2, 25], [0, 1]]
 g := ![![[8, 16, 21], [4, 24, 38], [3, 6], [25, 16, 1], []], ![[27, 37], [27, 10, 37, 22], [39, 25], [30, 36, 37, 29], [2, 23]], ![[6, 12, 11, 9], [3, 14, 26, 14], [41, 15], [28, 6, 5, 10], [38, 23]]]
 h' := ![![[39, 40, 18], [41, 20, 35], [15, 1, 9], [9, 22, 36], [0, 0, 1], [0, 1]], ![[20, 2, 25], [13, 10], [17, 15, 36], [31, 6, 38], [15, 2, 2], [39, 40, 18]], ![[0, 1], [16, 13, 8], [24, 27, 41], [18, 15, 12], [37, 41, 40], [20, 2, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 29], []]
 b := ![[], [20, 35, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [22, 16, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-111370, -24166, -13244]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2590, -562, -308]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [10, 35, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 24, 29], [11, 22, 18], [0, 1]]
 g := ![![[44, 29, 21], [11, 33, 36], [10, 37, 36], [1, 41, 1], []], ![[3, 0, 30, 5], [13, 13, 22, 15], [5, 23, 28, 31], [24, 9, 32, 30], [12, 42]], ![[21, 27, 39, 14], [32, 22, 7, 28], [37, 27, 4, 32], [42, 8, 12, 28], [23, 42]]]
 h' := ![![[30, 24, 29], [31, 26, 31], [41, 38, 41], [37, 25, 6], [0, 0, 1], [0, 1]], ![[11, 22, 18], [34, 1, 26], [26, 38, 30], [15, 17, 11], [28, 36, 22], [30, 24, 29]], ![[0, 1], [40, 20, 37], [32, 18, 23], [34, 5, 30], [32, 11, 24], [11, 22, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 27], []]
 b := ![[], [7, 39, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [10, 35, 6, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-935300, -237444, -9870]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19900, -5052, -210]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-34, 16, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-34, 16, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![19, 16, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-34, 16, 1], ![198, -9, 16], ![3168, 598, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -16, 53]], ![![-1, 0, 1], ![-2, -5, 16], ![63, 14, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [23, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 52], [0, 1]]
 g := ![![[18, 4], [13], [27, 29], [46], [10, 1]], ![[5, 49], [13], [52, 24], [46], [20, 52]]]
 h' := ![![[10, 52], [32, 51], [15, 38], [8, 20], [35, 24], [0, 1]], ![[0, 1], [12, 2], [24, 15], [49, 33], [10, 29], [10, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [41, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [23, 43, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![419, 205, -17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 9, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-16, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-16, 1, 0]] 
 ![![53, 0, 0], ![37, 1, 0], ![9, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-16, 1, 0], ![0, -16, 1], ![198, 25, -16]]]
  hmulB := by decide  
  f := ![![![257, -16, 0], ![848, 0, 0]], ![![177, -11, 0], ![584, 0, 0]], ![![69, -4, 0], ![228, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 53, 0], ![-9, 0, 53]], ![![-1, 1, 0], ![11, -16, 1], ![-11, 25, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-34, 16, 1]] ![![53, 0, 0], ![-16, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-848, 53, 0]], ![![-1802, 848, 53], ![742, -265, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-16, 1, 0]]], ![![![-34, 16, 1]], ![![14, -5, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-5, -16, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-5, -16, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![54, 43, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-5, -16, 1], ![198, 20, -16], ![-3168, -202, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -43, 59]], ![![-1, -1, 1], ![18, 12, -16], ![-72, -18, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [44, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 58], [0, 1]]
 g := ![![[46, 4], [0, 16], [26], [38, 48], [41, 1]], ![[33, 55], [7, 43], [26], [0, 11], [23, 58]]]
 h' := ![![[41, 58], [0, 2], [23, 55], [39, 12], [25, 44], [0, 1]], ![[0, 1], [23, 57], [36, 4], [0, 47], [0, 15], [41, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [23, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [44, 18, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7587, 1528, 406]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-243, -270, 406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![16, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![16, 1, 0]] 
 ![![59, 0, 0], ![16, 1, 0], ![39, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![16, 1, 0], ![0, 16, 1], ![198, 25, 16]]]
  hmulB := by decide  
  f := ![![![449, 28, 0], ![-1652, 0, 0]], ![![112, 7, 0], ![-412, 0, 0]], ![![293, 18, 0], ![-1078, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 59, 0], ![-39, 0, 59]], ![![0, 1, 0], ![-5, 16, 1], ![-14, 25, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-5, -16, 1]] ![![59, 0, 0], ![16, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![944, 59, 0]], ![![-295, -944, 59], ![118, -236, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![16, 1, 0]]], ![![![-5, -16, 1]], ![![2, -4, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![7, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![7, 1, 0]] 
 ![![61, 0, 0], ![7, 1, 0], ![12, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![7, 1, 0], ![0, 7, 1], ![198, 25, 7]]]
  hmulB := by decide  
  f := ![![![204, 29, 0], ![-1769, 0, 0]], ![![14, 2, 0], ![-121, 0, 0]], ![![36, 5, 0], ![-312, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 61, 0], ![-12, 0, 61]], ![![0, 1, 0], ![-1, 7, 1], ![-1, 25, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-14, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-14, 1, 0]] 
 ![![61, 0, 0], ![47, 1, 0], ![48, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-14, 1, 0], ![0, -14, 1], ![198, 25, -14]]]
  hmulB := by decide  
  f := ![![![757, -54, 0], ![3294, 0, 0]], ![![575, -41, 0], ![2502, 0, 0]], ![![592, -42, 0], ![2576, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 61, 0], ![-48, 0, 61]], ![![-1, 1, 0], ![10, -14, 1], ![-5, 25, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![7, 1, 0]] ![![61, 0, 0], ![7, 1, 0]]
  ![![61, 0, 0], ![-12, 14, 1]] where
 M := ![![![3721, 0, 0], ![427, 61, 0]], ![![427, 61, 0], ![49, 14, 1]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![7, 1, 0], ![0, 0, 0]]], ![![![7, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-12, 14, 1]] ![![61, 0, 0], ![-14, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-854, 61, 0]], ![![-732, 854, 61], ![366, -183, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-14, 1, 0]]], ![![![-12, 14, 1]], ![![6, -3, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N0
    exact isPrimeI61N1
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [21, 7, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 0, 51], [66, 66, 16], [0, 1]]
 g := ![![[28, 36, 16], [57, 57, 29], [62, 60], [48, 10], [14, 1], []], ![[52, 17, 42, 5], [30, 28, 63, 2], [], [29, 59], [39, 1], [33, 55]], ![[13, 46, 46, 29], [2, 44, 1, 36], [36, 60], [49, 47], [], [1, 55]]]
 h' := ![![[15, 0, 51], [9, 10, 4], [47, 65, 37], [3, 14, 44], [41, 15, 55], [0, 0, 1], [0, 1]], ![[66, 66, 16], [29, 17, 37], [54, 40, 62], [56, 53], [53, 16, 40], [1, 21, 66], [15, 0, 51]], ![[0, 1], [53, 40, 26], [46, 29, 35], [47, 0, 23], [65, 36, 39], [47, 46], [66, 66, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 20], []]
 b := ![[], [36, 37, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [21, 7, 53, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-48642, -6834, 2278]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-726, -102, 34]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-20, -17, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-20, -17, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![51, 54, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-20, -17, 1], ![198, 5, -17], ![-3366, -227, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -54, 71]], ![![-1, -1, 1], ![15, 13, -17], ![-51, -7, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [48, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 70], [0, 1]]
 g := ![![[17, 37], [55, 32], [36, 5], [30], [18], [1]], ![[0, 34], [0, 39], [3, 66], [30], [18], [1]]]
 h' := ![![[36, 70], [58, 26], [47, 48], [25, 17], [20, 32], [23, 36], [0, 1]], ![[0, 1], [0, 45], [0, 23], [69, 54], [36, 39], [41, 35], [36, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [61, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [48, 35, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![840, 927, 171]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-111, -117, 171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![17, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![17, 1, 0]] 
 ![![71, 0, 0], ![17, 1, 0], ![66, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![17, 1, 0], ![0, 17, 1], ![198, 25, 17]]]
  hmulB := by decide  
  f := ![![![545, 32, 0], ![-2272, 0, 0]], ![![119, 7, 0], ![-496, 0, 0]], ![![498, 29, 0], ![-2076, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 71, 0], ![-66, 0, 71]], ![![0, 1, 0], ![-5, 17, 1], ![-19, 25, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-20, -17, 1]] ![![71, 0, 0], ![17, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1207, 71, 0]], ![![-1420, -1207, 71], ![-142, -284, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![17, 1, 0]]], ![![![-20, -17, 1]], ![![-2, -4, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [44, 28, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 63, 12], [29, 9, 61], [0, 1]]
 g := ![![[53, 48, 55], [], [32, 36], [10, 20, 61], [33, 1], []], ![[27, 69, 42, 4], [7, 1], [58, 49], [70, 18, 60, 70], [18, 8], [59, 71]], ![[8, 68, 38, 55], [68, 1], [69, 1], [61, 52, 5, 67], [58, 27], [10, 71]]]
 h' := ![![[4, 63, 12], [70, 15, 36], [56, 6], [71, 72, 67], [8, 54, 39], [0, 0, 1], [0, 1]], ![[29, 9, 61], [33, 15, 66], [7, 13, 72], [71, 19, 7], [52, 22, 50], [48, 35, 9], [4, 63, 12]], ![[0, 1], [49, 43, 44], [11, 54, 1], [45, 55, 72], [58, 70, 57], [36, 38, 63], [29, 9, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 51], []]
 b := ![[], [16, 9, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [44, 28, 40, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-842420, 86432, 5840]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11540, 1184, 80]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-4, -10, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-4, -10, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![75, 69, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-4, -10, 1], ![198, 21, -10], ![-1980, -52, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -69, 79]], ![![-1, -1, 1], ![12, 9, -10], ![-45, -19, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [73, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 78], [0, 1]]
 g := ![![[47, 13], [44, 1], [46, 10], [53, 72], [50], [1]], ![[0, 66], [10, 78], [22, 69], [54, 7], [50], [1]]]
 h' := ![![[45, 78], [27, 31], [39, 1], [2, 57], [20, 25], [6, 45], [0, 1]], ![[0, 1], [0, 48], [5, 78], [39, 22], [39, 54], [56, 34], [45, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [70, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [73, 34, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![288, 88, 86]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-78, -74, 86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![10, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![10, 1, 0]] 
 ![![79, 0, 0], ![10, 1, 0], ![58, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![10, 1, 0], ![0, 10, 1], ![198, 25, 10]]]
  hmulB := by decide  
  f := ![![![61, 6, 0], ![-474, 0, 0]], ![![-10, -1, 0], ![80, 0, 0]], ![![42, 4, 0], ![-326, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 79, 0], ![-58, 0, 79]], ![![0, 1, 0], ![-2, 10, 1], ![-8, 25, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-4, -10, 1]] ![![79, 0, 0], ![10, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![790, 79, 0]], ![![-316, -790, 79], ![158, -79, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![10, 1, 0]]], ![![![-4, -10, 1]], ![![2, -1, 0]]]]
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


lemma PB283I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB283I1 : PrimesBelowBoundCertificateInterval O 31 79 283 where
  m := 11
  g := ![2, 3, 1, 1, 2, 2, 3, 1, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB283I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![5041, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I53N1, I59N1, I61N0, I61N1, I71N1, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [], [], [I53N1], [I59N1], [I61N0, I61N0, I61N1], [], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
