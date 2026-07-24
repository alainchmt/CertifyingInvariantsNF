
import IdealArithmetic.Examples.NF3_1_369800_2.RI3_1_369800_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-40, 11, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-40, 11, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![34, 11, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-40, 11, 1], ![338, 31, 23], ![3796, 980, 42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -11, 37]], ![![-2, 0, 1], ![-12, -6, 23], ![64, 14, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [11, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 36], [0, 1]]
 g := ![![[13, 27], [27], [20, 3], [25], [1]], ![[0, 10], [27], [35, 34], [25], [1]]]
 h' := ![![[5, 36], [3, 29], [2, 29], [31, 15], [26, 5], [0, 1]], ![[0, 1], [0, 8], [36, 8], [32, 22], [14, 32], [5, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [27, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [11, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2085, 1050, 230]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-155, -40, 230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![32, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![1, 14, 2], ![327, 71, 15]]]
  hmulB := by decide  
  f := ![![![179, 3467, 496], ![185, -9176, 0]], ![![65, 1300, 186], ![75, -3441, 0]], ![![148, 2998, 429], ![178, -7936, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-32, 0, 37]], ![![0, 1, 0], ![-7, 14, 2], ![-31, 71, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-40, 11, 1]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![-1480, 407, 37], ![-222, 185, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![14, 1, 0]]], ![![![-40, 11, 1]], ![![-6, 5, 1]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [17, 4, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 27, 36], [24, 13, 5], [0, 1]]
 g := ![![[39, 37, 21], [15, 20], [33, 16], [39, 17, 1], []], ![[38, 12, 4, 2], [24, 18], [2, 33], [24, 38, 36, 16], [32, 25]], ![[5, 12, 25, 9], [3, 10], [10, 20], [15, 14, 19, 37], [22, 25]]]
 h' := ![![[34, 27, 36], [22, 14, 12], [21, 4, 26], [34, 6, 4], [0, 0, 1], [0, 1]], ![[24, 13, 5], [11, 30, 4], [38, 10, 31], [21, 5, 22], [38, 12, 13], [34, 27, 36]], ![[0, 1], [35, 38, 25], [39, 27, 25], [2, 30, 15], [38, 29, 27], [24, 13, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 38], []]
 b := ![[], [21, 34, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [17, 4, 24, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6359797, 2875412, 671539]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![155117, 70132, 16379]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![14, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![14, 1, 0]] 
 ![![43, 0, 0], ![14, 1, 0], ![10, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![14, 1, 0], ![1, 14, 2], ![327, 71, 15]]]
  hmulB := by decide  
  f := ![![![-171, -2798, -400], ![-86, 8600, 0]], ![![-65, -910, -130], ![1, 2795, 0]], ![![-44, -651, -93], ![-7, 2000, 0]]]
  g := ![![![1, 0, 0], ![-14, 43, 0], ![-10, 0, 43]], ![![0, 1, 0], ![-5, 14, 2], ![-19, 71, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![14, 1, 0]] ![![43, 0, 0], ![14, 1, 0]]
  ![![43, 0, 0], ![-52, 14, 1]] where
 M := ![![![1849, 0, 0], ![602, 43, 0]], ![![602, 43, 0], ![197, 28, 2]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![7, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-52, 14, 1]] ![![43, 0, 0], ![14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![602, 43, 0]], ![![-2236, 602, 43], ![-387, 215, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![14, 1, 0]]], ![![![-52, 14, 1]], ![![-9, 5, 1]]]]
 hle2 := by decide  

def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-100, -7, 2]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-100, -7, 2]] 
 ![![47, 0, 0], ![0, 47, 0], ![44, 20, 1]] where
  M :=![![![-100, -7, 2], ![647, 42, -12], ![-1891, -99, 35]]]
  hmulB := by decide  
  f := ![![![6, 1, 0]], ![![1, 6, 2]], ![![13, 5, 1]]]
  g := ![![![-4, -1, 2], ![25, 6, -12], ![-73, -17, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [5, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 46], [0, 1]]
 g := ![![[23, 17], [40, 24], [14, 37], [20, 18], [1]], ![[42, 30], [6, 23], [36, 10], [18, 29], [1]]]
 h' := ![![[26, 46], [35, 39], [24, 27], [41, 32], [42, 26], [0, 1]], ![[0, 1], [15, 8], [21, 20], [27, 15], [13, 21], [26, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [34, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [5, 21, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![826546, 857363, 316340]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-278562, -116371, 316340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![6, 1, 0]] 
 ![![47, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![6, 1, 0], ![1, 6, 2], ![327, 71, 7]]]
  hmulB := by decide  
  f := ![![![-100, -7, 2]], ![![1, 0, 0]], ![![-53, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 6, 2], ![-3, 71, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-100, -7, 2]] ![![6, 1, 0]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-30, 15, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-30, 15, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![23, 15, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-30, 15, 1], ![342, 41, 31], ![5104, 1264, 56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -15, 53]], ![![-1, 0, 1], ![-7, -8, 31], ![72, 8, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [50, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 52], [0, 1]]
 g := ![![[22, 40], [24], [5, 7], [10], [13, 1]], ![[12, 13], [24], [43, 46], [10], [26, 52]]]
 h' := ![![[13, 52], [32, 27], [15, 17], [14, 31], [39, 13], [0, 1]], ![[0, 1], [12, 26], [24, 36], [46, 22], [49, 40], [13, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [3, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [50, 40, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1680, 4301, 1587]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-657, -368, 1587]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![22, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![22, 1, 0]] 
 ![![53, 0, 0], ![22, 1, 0], ![50, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![22, 1, 0], ![1, 22, 2], ![327, 71, 23]]]
  hmulB := by decide  
  f := ![![![-419, -12621, -1148], ![-371, 30422, 0]], ![![-172, -5233, -476], ![-158, 12614, 0]], ![![-382, -11906, -1083], ![-382, 28700, 0]]]
  g := ![![![1, 0, 0], ![-22, 53, 0], ![-50, 0, 53]], ![![0, 1, 0], ![-11, 22, 2], ![-45, 71, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-30, 15, 1]] ![![53, 0, 0], ![22, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1166, 53, 0]], ![![-1590, 795, 53], ![-318, 371, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![22, 1, 0]]], ![![![-30, 15, 1]], ![![-6, 7, 1]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [42, 24, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 58, 16], [47, 0, 43], [0, 1]]
 g := ![![[15, 16, 19], [30, 54, 29], [58, 29], [41, 7, 49], [1]], ![[57, 7, 22, 57], [48, 21, 20, 53], [14, 26], [11, 34, 49, 4], [45, 36, 56, 25]], ![[4, 18, 42, 32], [45, 45, 47, 44], [32, 36], [5, 20, 20, 32], [24, 12, 2, 34]]]
 h' := ![![[19, 58, 16], [38, 40, 45], [45, 32, 41], [48, 14, 18], [17, 35, 7], [0, 1]], ![[47, 0, 43], [12, 42, 50], [47, 6, 40], [35, 7, 47], [13, 42, 29], [19, 58, 16]], ![[0, 1], [35, 36, 23], [13, 21, 37], [0, 38, 53], [37, 41, 23], [47, 0, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 31], []]
 b := ![[], [50, 54, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [42, 24, 52, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-814436, -238478, -35636]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13804, -4042, -604]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-64, -21, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-64, -21, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![58, 40, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-64, -21, 1], ![306, 7, -41], ![-6668, -1292, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -40, 61]], ![![-2, -1, 1], ![44, 27, -41], ![-96, -12, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [26, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 60], [0, 1]]
 g := ![![[45, 4], [9], [6, 13], [22, 58], [50, 1]], ![[1, 57], [9], [46, 48], [55, 3], [39, 60]]]
 h' := ![![[50, 60], [7, 2], [27, 3], [38, 14], [42, 34], [0, 1]], ![[0, 1], [46, 59], [55, 58], [6, 47], [34, 27], [50, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [46, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [26, 11, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39482, 10170, 1520]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-798, -830, 1520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-20, 1, 0]] 
 ![![61, 0, 0], ![41, 1, 0], ![14, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-20, 1, 0], ![1, -20, 2], ![327, 71, -19]]]
  hmulB := by decide  
  f := ![![![-3, 479, -48], ![61, 1464, 0]], ![![5, 319, -32], ![62, 976, 0]], ![![-2, 110, -11], ![10, 336, 0]]]
  g := ![![![1, 0, 0], ![-41, 61, 0], ![-14, 0, 61]], ![![-1, 1, 0], ![13, -20, 2], ![-38, 71, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-64, -21, 1]] ![![61, 0, 0], ![-20, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1220, 61, 0]], ![![-3904, -1281, 61], ![1586, 427, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-20, 1, 0]]], ![![![-64, -21, 1]], ![![26, 7, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-26, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-26, 1, 0]] 
 ![![67, 0, 0], ![41, 1, 0], ![31, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-26, 1, 0], ![1, -26, 2], ![327, 71, -25]]]
  hmulB := by decide  
  f := ![![![-419, 14970, -1152], ![402, 38592, 0]], ![![-247, 9148, -704], ![269, 23584, 0]], ![![-183, 6926, -533], ![214, 17856, 0]]]
  g := ![![![1, 0, 0], ![-41, 67, 0], ![-31, 0, 67]], ![![-1, 1, 0], ![15, -26, 2], ![-27, 71, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-22, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-22, 1, 0]] 
 ![![67, 0, 0], ![45, 1, 0], ![60, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-22, 1, 0], ![1, -22, 2], ![327, 71, -21]]]
  hmulB := by decide  
  f := ![![![-132, 3892, -354], ![134, 11859, 0]], ![![-73, 2594, -236], ![135, 7906, 0]], ![![-110, 3485, -317], ![145, 10620, 0]]]
  g := ![![![1, 0, 0], ![-45, 67, 0], ![-60, 0, 67]], ![![-1, 1, 0], ![13, -22, 2], ![-24, 71, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-20, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-20, 1, 0]] 
 ![![67, 0, 0], ![47, 1, 0], ![35, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-20, 1, 0], ![1, -20, 2], ![327, 71, -19]]]
  hmulB := by decide  
  f := ![![![-299, 7596, -760], ![268, 25460, 0]], ![![-205, 5317, -532], ![202, 17822, 0]], ![![-155, 3968, -397], ![144, 13300, 0]]]
  g := ![![![1, 0, 0], ![-47, 67, 0], ![-35, 0, 67]], ![![-1, 1, 0], ![13, -20, 2], ![-35, 71, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-26, 1, 0]] ![![67, 0, 0], ![-22, 1, 0]]
  ![![67, 0, 0], ![-15, -24, 1]] where
 M := ![![![4489, 0, 0], ![-1474, 67, 0]], ![![-1742, 67, 0], ![573, -48, 2]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![-7, 25, -1], ![67, 0, 0]]], ![![![-11, 25, -1], ![67, 0, 0]], ![![9, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-15, -24, 1]] ![![67, 0, 0], ![-20, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1340, 67, 0]], ![![-1005, -1608, 67], ![603, 536, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-20, 1, 0]]], ![![![-15, -24, 1]], ![![9, 8, -1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-43, -32, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-43, -32, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![28, 39, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-43, -32, 1], ![295, 28, -63], ![-10265, -2073, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -39, 71]], ![![-1, -1, 1], ![29, 35, -63], ![-143, -27, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [35, 37, 1] where
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
 g := ![![[68, 24], [1, 9], [64, 27], [16], [20], [1]], ![[32, 47], [23, 62], [59, 44], [16], [20], [1]]]
 h' := ![![[34, 70], [36, 33], [32, 3], [11, 58], [28, 4], [36, 34], [0, 1]], ![[0, 1], [22, 38], [63, 68], [66, 13], [22, 67], [56, 37], [34, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [8, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [35, 37, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4121, 612, 540]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-271, -288, 540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-8, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-8, 1, 0]] 
 ![![71, 0, 0], ![63, 1, 0], ![4, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-8, 1, 0], ![1, -8, 2], ![327, 71, -7]]]
  hmulB := by decide  
  f := ![![![-4227, 34706, -8680], ![994, 308140, 0]], ![![-3745, 30787, -7700], ![924, 273350, 0]], ![![-236, 1955, -489], ![75, 17360, 0]]]
  g := ![![![1, 0, 0], ![-63, 71, 0], ![-4, 0, 71]], ![![-1, 1, 0], ![7, -8, 2], ![-58, 71, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-43, -32, 1]] ![![71, 0, 0], ![-8, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-568, 71, 0]], ![![-3053, -2272, 71], ![639, 284, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-8, 1, 0]]], ![![![-43, -32, 1]], ![![9, 4, -1]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [5, 28, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 22, 71], [33, 50, 2], [0, 1]]
 g := ![![[23, 20, 72], [55, 71], [28, 19], [42, 25, 35], [64, 1], []], ![[69, 37, 71, 69], [60, 69], [43, 4], [35, 40, 41, 24], [3, 18], [22, 4]], ![[69, 72, 37, 50], [61, 12], [4, 65], [3, 3, 26, 65], [39, 46], [18, 4]]]
 h' := ![![[31, 22, 71], [67, 34, 27], [14, 35, 12], [9, 67, 26], [45, 28, 53], [0, 0, 1], [0, 1]], ![[33, 50, 2], [8, 37, 41], [69, 16, 19], [49, 35, 71], [26, 72, 39], [48, 71, 50], [31, 22, 71]], ![[0, 1], [57, 2, 5], [17, 22, 42], [16, 44, 49], [42, 46, 54], [50, 2, 22], [33, 50, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 10], []]
 b := ![[], [45, 53, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [5, 28, 9, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6285446, 2121307, 389820]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![86102, 29059, 5340]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-9, -26, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-9, -26, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![70, 53, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-9, -26, 1], ![301, 62, -51], ![-8303, -1647, 36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -53, 79]], ![![-1, -1, 1], ![49, 35, -51], ![-137, -45, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [45, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 78], [0, 1]]
 g := ![![[12, 72], [63, 62], [1, 73], [], [11], [1]], ![[0, 7], [0, 17], [2, 6], [], [11], [1]]]
 h' := ![![[13, 78], [9, 54], [34, 46], [0, 51], [29], [34, 13], [0, 1]], ![[0, 1], [0, 25], [0, 33], [31, 28], [29], [45, 66], [13, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [6, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [45, 66, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4715, 4975, 1495]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1265, -940, 1495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-28, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-28, 1, 0]] 
 ![![79, 0, 0], ![51, 1, 0], ![43, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-28, 1, 0], ![1, -28, 2], ![327, 71, -27]]]
  hmulB := by decide  
  f := ![![![-1792, 65081, -4650], ![1501, 183675, 0]], ![![-1163, 41988, -3000], ![949, 118500, 0]], ![![-980, 35424, -2531], ![804, 99975, 0]]]
  g := ![![![1, 0, 0], ![-51, 79, 0], ![-43, 0, 79]], ![![-1, 1, 0], ![17, -28, 2], ![-27, 71, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-9, -26, 1]] ![![79, 0, 0], ![-28, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2212, 79, 0]], ![![-711, -2054, 79], ![553, 790, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-28, 1, 0]]], ![![![-9, -26, 1]], ![![7, 10, -1]]]]
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


lemma PB173I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB173I1 : PrimesBelowBoundCertificateInterval O 31 79 173 where
  m := 11
  g := ![2, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB173I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
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
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N0
      exact NI43N0
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
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
  β := ![I37N1, I43N0, I47N1, I53N1, I61N1, I67N0, I67N1, I67N2, I71N1, I79N1]
  Il := ![[I37N1], [], [I43N0, I43N0, I43N0], [I47N1], [I53N1], [], [I61N1], [I67N0, I67N1, I67N2], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
