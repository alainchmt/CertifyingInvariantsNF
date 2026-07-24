
import IdealArithmetic.Examples.NF3_1_703404_2.RI3_1_703404_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [36, 26, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 25, 25], [31, 11, 12], [0, 1]]
 g := ![![[22, 33, 4], [9, 21], [5, 8, 27], [16, 1], []], ![[25, 20, 36, 30], [31, 3], [15, 22, 10, 25], [3, 10], [2, 33]], ![[18, 13, 21, 25], [19, 7], [17, 21, 0, 33], [17, 33], [15, 33]]]
 h' := ![![[22, 25, 25], [34, 17, 35], [5, 23, 13], [16, 29, 8], [0, 0, 1], [0, 1]], ![[31, 11, 12], [28, 2, 33], [21, 13, 15], [28, 12, 36], [5, 8, 11], [22, 25, 25]], ![[0, 1], [15, 18, 6], [12, 1, 9], [28, 33, 30], [14, 29, 25], [31, 11, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 19], []]
 b := ![[], [30, 5, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [36, 26, 21, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-109742, -40256, -3959]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2966, -1088, -107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![6, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![6, 1, 0]] 
 ![![41, 0, 0], ![6, 1, 0], ![5, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![6, 1, 0], ![0, 6, 1], ![262, 66, 6]]]
  hmulB := by decide  
  f := ![![![31, 5, 0], ![-205, 0, 0]], ![![-6, -1, 0], ![42, 0, 0]], ![![-5, -1, 0], ![35, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 41, 0], ![-5, 0, 41]], ![![0, 1, 0], ![-1, 6, 1], ![-4, 66, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![8, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![8, 1, 0]] 
 ![![41, 0, 0], ![8, 1, 0], ![18, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![8, 1, 0], ![0, 8, 1], ![262, 66, 8]]]
  hmulB := by decide  
  f := ![![![193, 24, 0], ![-984, 0, 0]], ![![24, 3, 0], ![-122, 0, 0]], ![![82, 10, 0], ![-418, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 41, 0], ![-18, 0, 41]], ![![0, 1, 0], ![-2, 8, 1], ![-10, 66, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-14, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-14, 1, 0]] 
 ![![41, 0, 0], ![27, 1, 0], ![9, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-14, 1, 0], ![0, -14, 1], ![262, 66, -14]]]
  hmulB := by decide  
  f := ![![![71, -5, 0], ![205, 0, 0]], ![![57, -4, 0], ![165, 0, 0]], ![![19, -1, 0], ![55, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 41, 0], ![-9, 0, 41]], ![![-1, 1, 0], ![9, -14, 1], ![-34, 66, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![6, 1, 0]] ![![41, 0, 0], ![8, 1, 0]]
  ![![41, 0, 0], ![-34, 14, 1]] where
 M := ![![![1681, 0, 0], ![328, 41, 0]], ![![246, 41, 0], ![48, 14, 1]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![8, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-34, 14, 1]] ![![41, 0, 0], ![-14, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-574, 41, 0]], ![![-1394, 574, 41], ![738, -164, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-14, 1, 0]]], ![![![-34, 14, 1]], ![![18, -4, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-52, -10, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-52, -10, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![34, 33, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-52, -10, 1], ![262, 14, -10], ![-2620, -398, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -33, 43]], ![![-2, -1, 1], ![14, 8, -10], ![-72, -20, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [40, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 42], [0, 1]]
 g := ![![[39, 14], [3, 11], [23], [6, 15], [1]], ![[0, 29], [0, 32], [23], [41, 28], [1]]]
 h' := ![![[31, 42], [9, 33], [6, 22], [18, 25], [3, 31], [0, 1]], ![[0, 1], [0, 10], [0, 21], [19, 18], [18, 12], [31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [33, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [40, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3115, 1546, 628]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-569, -446, 628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, 1, 0]] 
 ![![43, 0, 0], ![10, 1, 0], ![29, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, 1, 0], ![0, 10, 1], ![262, 66, 10]]]
  hmulB := by decide  
  f := ![![![111, 11, 0], ![-473, 0, 0]], ![![10, 1, 0], ![-42, 0, 0]], ![![73, 7, 0], ![-311, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 43, 0], ![-29, 0, 43]], ![![0, 1, 0], ![-3, 10, 1], ![-16, 66, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-52, -10, 1]] ![![43, 0, 0], ![10, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![430, 43, 0]], ![![-2236, -430, 43], ![-258, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![10, 1, 0]]], ![![![-52, -10, 1]], ![![-6, -2, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-54, -24, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-54, -24, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![40, 23, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-54, -24, 1], ![262, 12, -24], ![-6288, -1322, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -23, 47]], ![![-2, -1, 1], ![26, 12, -24], ![-144, -34, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [16, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 46], [0, 1]]
 g := ![![[14, 3], [20, 25], [41, 42], [39, 27], [1]], ![[0, 44], [13, 22], [33, 5], [7, 20], [1]]]
 h' := ![![[11, 46], [9, 12], [2, 42], [34, 18], [31, 11], [0, 1]], ![[0, 1], [0, 35], [41, 5], [44, 29], [11, 36], [11, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [34, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [16, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1284, 38, 159]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108, -77, 159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-23, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-23, 1, 0]] 
 ![![47, 0, 0], ![24, 1, 0], ![35, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-23, 1, 0], ![0, -23, 1], ![262, 66, -23]]]
  hmulB := by decide  
  f := ![![![1082, -47, 0], ![2209, 0, 0]], ![![576, -25, 0], ![1176, 0, 0]], ![![840, -36, 0], ![1715, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 47, 0], ![-35, 0, 47]], ![![-1, 1, 0], ![11, -23, 1], ![-11, 66, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-54, -24, 1]] ![![47, 0, 0], ![-23, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-1081, 47, 0]], ![![-2538, -1128, 47], ![1504, 564, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-23, 1, 0]]], ![![![-54, -24, 1]], ![![32, 12, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-20, -29, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-20, -29, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![33, 24, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-20, -29, 1], ![262, 46, -29], ![-7598, -1652, 46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -24, 53]], ![![-1, -1, 1], ![23, 14, -29], ![-172, -52, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [4, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 52], [0, 1]]
 g := ![![[17, 40], [46], [49, 46], [28], [38, 1]], ![[0, 13], [46], [48, 7], [28], [23, 52]]]
 h' := ![![[38, 52], [19, 26], [16, 29], [43, 24], [7, 9], [0, 1]], ![[0, 1], [0, 27], [5, 24], [1, 29], [31, 44], [38, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [5, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [4, 15, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1552, 1979, 544]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-368, -209, 544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-24, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-24, 1, 0]] 
 ![![53, 0, 0], ![29, 1, 0], ![7, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-24, 1, 0], ![0, -24, 1], ![262, 66, -24]]]
  hmulB := by decide  
  f := ![![![1201, -50, 0], ![2650, 0, 0]], ![![649, -27, 0], ![1432, 0, 0]], ![![155, -6, 0], ![342, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 53, 0], ![-7, 0, 53]], ![![-1, 1, 0], ![13, -24, 1], ![-28, 66, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-20, -29, 1]] ![![53, 0, 0], ![-24, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1272, 53, 0]], ![![-1060, -1537, 53], ![742, 742, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-24, 1, 0]]], ![![![-20, -29, 1]], ![![14, 14, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [48, 23, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 52, 37], [5, 6, 22], [0, 1]]
 g := ![![[9, 11, 35], [20, 46, 22], [9, 45], [38, 24, 19], [1]], ![[23, 36, 9, 30], [53, 32, 8, 40], [4, 36], [22, 54, 17, 47], [47, 17, 22, 31]], ![[7, 16, 19, 15], [20, 37, 34, 57], [46, 15], [28, 41, 29, 19], [14, 10, 1, 28]]]
 h' := ![![[40, 52, 37], [43, 23, 25], [6, 0, 9], [5, 42, 35], [11, 36, 45], [0, 1]], ![[5, 6, 22], [49, 30, 57], [5, 31, 54], [16, 56, 53], [30, 21, 9], [40, 52, 37]], ![[0, 1], [43, 6, 36], [0, 28, 55], [54, 20, 30], [43, 2, 5], [5, 6, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 46], []]
 b := ![[], [33, 3, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [48, 23, 14, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-113398, -43011, -4425]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1922, -729, -75]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [35, 23, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 45, 23], [8, 15, 38], [0, 1]]
 g := ![![[26, 6, 46], [53, 58], [42, 16, 4], [49, 13, 47], [1]], ![[45, 5, 19, 40], [9, 52], [57, 17, 45, 35], [12, 50, 53, 6], [0, 16, 43, 28]], ![[48, 46, 50, 35], [22, 1], [37, 14, 2, 53], [22, 13, 13, 29], [58, 49, 17, 33]]]
 h' := ![![[5, 45, 23], [11, 18, 31], [55, 48, 34], [54, 9, 59], [26, 38, 13], [0, 1]], ![[8, 15, 38], [6, 29, 25], [57, 48, 28], [52, 52, 55], [3, 9, 32], [5, 45, 23]], ![[0, 1], [37, 14, 5], [40, 26, 60], [49, 0, 8], [7, 14, 16], [8, 15, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 12], []]
 b := ![[], [23, 5, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [35, 23, 48, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3359209, 1162904, 112667]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55069, 19064, 1847]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [37, 22, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 6, 59], [45, 60, 8], [0, 1]]
 g := ![![[61, 62, 33], [34, 62, 26], [56, 23], [55, 39], [66, 1], []], ![[49, 65, 38, 19], [14, 63, 0, 40], [26, 29], [53, 1], [60, 49], [41, 64]], ![[27, 49, 53, 50], [16, 52, 1, 66], [22, 36], [24, 15], [0, 36], [25, 64]]]
 h' := ![![[21, 6, 59], [15, 12, 57], [21, 40, 48], [4, 56, 36], [37, 52, 46], [0, 0, 1], [0, 1]], ![[45, 60, 8], [39, 35, 41], [66, 29, 14], [31, 27, 37], [7, 40, 66], [63, 64, 60], [21, 6, 59]], ![[0, 1], [7, 20, 36], [16, 65, 5], [48, 51, 61], [47, 42, 22], [28, 3, 6], [45, 60, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 16], []]
 b := ![[], [47, 47, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [37, 22, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![97217, -335, -3953]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1451, -5, -59]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [69, 24, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 66, 7], [13, 4, 64], [0, 1]]
 g := ![![[19, 48, 24], [0, 61, 8], [43, 9, 60], [64, 15], [51, 1], []], ![[36, 66, 57, 44], [63, 25, 65, 26], [13, 47, 46, 26], [48, 15], [11, 16], [15, 49]], ![[45, 69, 32, 49], [28, 34, 23, 1], [55, 50, 4, 1], [], [38, 25], [29, 49]]]
 h' := ![![[38, 66, 7], [0, 63, 38], [15, 59, 47], [24, 49, 29], [31, 56, 21], [0, 0, 1], [0, 1]], ![[13, 4, 64], [44, 68, 25], [38, 61, 33], [44, 23, 33], [27, 12, 50], [54, 68, 4], [38, 66, 7]], ![[0, 1], [2, 11, 8], [20, 22, 62], [2, 70, 9], [59, 3], [14, 3, 66], [13, 4, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 41], []]
 b := ![[], [52, 7, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [69, 24, 20, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![777947, 356846, 43736]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10957, 5026, 616]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [39, 18, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 43, 40], [71, 29, 33], [0, 1]]
 g := ![![[8, 62, 4], [12, 48], [2, 1], [58, 43, 54], [51, 1], []], ![[26, 9, 61, 34], [55, 12], [1, 4], [5, 16, 53, 59], [29, 38], [68, 67]], ![[66, 20, 17, 40], [24, 12], [35, 1], [5, 23, 64, 45], [27, 24], [2, 67]]]
 h' := ![![[53, 43, 40], [59, 72, 71], [69, 22, 11], [1, 12, 1], [55, 65, 28], [0, 0, 1], [0, 1]], ![[71, 29, 33], [57, 48, 48], [42, 44, 31], [64, 69, 71], [12, 61, 54], [11, 64, 29], [53, 43, 40]], ![[0, 1], [63, 26, 27], [14, 7, 31], [49, 65, 1], [43, 20, 64], [72, 9, 43], [71, 29, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 36], []]
 b := ![[], [0, 18, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [39, 18, 22, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2081157, -200604, 53436]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28509, -2748, 732]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-20, -21, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-20, -21, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![59, 58, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-20, -21, 1], ![262, 46, -21], ![-5502, -1124, 46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -58, 79]], ![![-1, -1, 1], ![19, 16, -21], ![-104, -48, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [76, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 78], [0, 1]]
 g := ![![[4, 26], [10, 65], [31, 4], [8, 52], [65], [1]], ![[0, 53], [0, 14], [0, 75], [0, 27], [65], [1]]]
 h' := ![![[12, 78], [30, 37], [14, 12], [24, 77], [46, 62], [3, 12], [0, 1]], ![[0, 1], [0, 42], [0, 67], [0, 2], [0, 17], [68, 67], [12, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [73, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [76, 67, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![592, 37, 160]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-112, -117, 160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![21, 1, 0]] 
 ![![79, 0, 0], ![21, 1, 0], ![33, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![21, 1, 0], ![0, 21, 1], ![262, 66, 21]]]
  hmulB := by decide  
  f := ![![![799, 38, 0], ![-3002, 0, 0]], ![![189, 9, 0], ![-710, 0, 0]], ![![321, 15, 0], ![-1206, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 79, 0], ![-33, 0, 79]], ![![0, 1, 0], ![-6, 21, 1], ![-23, 66, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-20, -21, 1]] ![![79, 0, 0], ![21, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1659, 79, 0]], ![![-1580, -1659, 79], ![-158, -395, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![21, 1, 0]]], ![![![-20, -21, 1]], ![![-2, -5, 0]]]]
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


lemma PB238I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB238I1 : PrimesBelowBoundCertificateInterval O 31 79 238 where
  m := 11
  g := ![1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB238I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
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
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
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
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
      exact NI79N1
  β := ![I41N0, I41N1, I41N2, I43N1, I47N1, I53N1, I79N1]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [I53N1], [], [], [], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
