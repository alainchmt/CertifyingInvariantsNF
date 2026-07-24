
import IdealArithmetic.Examples.NF3_1_455455_1.RI3_1_455455_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 4, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 4, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![13, 4, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 4, 1], ![-132, 22, 24], ![-506, -2, 18]]]
  hmulB := by decide  
  f := ![![![-12, -4, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -4, 37]], ![![0, 0, 1], ![-12, -2, 24], ![-20, -2, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [34, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 36], [0, 1]]
 g := ![![[20, 12], [9], [30, 34], [11], [1]], ![[0, 25], [9], [35, 3], [11], [1]]]
 h' := ![![[23, 36], [24, 7], [16, 3], [5, 21], [3, 23], [0, 1]], ![[0, 1], [0, 30], [11, 34], [7, 16], [14, 14], [23, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [1, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [34, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3112, -2466, 475]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, -118, 475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 1, 0]] 
 ![![37, 0, 0], ![13, 1, 0], ![19, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 1, 0], ![0, 14, 6], ![-132, 5, 13]]]
  hmulB := by decide  
  f := ![![![209, 16, 0], ![-592, 0, 0]], ![![65, 5, 0], ![-184, 0, 0]], ![![101, -4, -5], ![-286, 31, 0]]]
  g := ![![![1, 0, 0], ![-13, 37, 0], ![-19, 0, 37]], ![![0, 1, 0], ![-8, 14, 6], ![-12, 5, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![13, 4, 1]] ![![37, 0, 0], ![13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![481, 37, 0]], ![![481, 148, 37], ![37, 74, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![13, 1, 0]]], ![![![13, 4, 1]], ![![1, 2, 1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, -7, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, -7, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![9, 34, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, -7, 1], ![-132, 7, -42], ![946, -57, 14]]]
  hmulB := by decide  
  f := ![![![-8, 7, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -34, 41]], ![![0, -1, 1], ![6, 35, -42], ![20, -13, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [7, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40], [0, 1]]
 g := ![![[28, 20], [31], [39], [29, 40], [1]], ![[3, 21], [31], [39], [20, 1], [1]]]
 h' := ![![[9, 40], [25, 15], [18, 20], [2, 30], [34, 9], [0, 1]], ![[0, 1], [37, 26], [34, 21], [26, 11], [33, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [11, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [7, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-728, -1297, 566]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-142, -501, 566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![1, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![1, 1, 0]] 
 ![![41, 0, 0], ![1, 1, 0], ![27, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![1, 1, 0], ![0, 2, 6], ![-132, 5, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![41, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![27, 7, 0]]]
  g := ![![![1, 0, 0], ![-1, 41, 0], ![-27, 0, 41]], ![![0, 1, 0], ![-4, 2, 6], ![-4, 5, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![9, -7, 1]] ![![41, 0, 0], ![1, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![41, 41, 0]], ![![369, -287, 41], ![-123, 0, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![1, 1, 0]]], ![![![9, -7, 1]], ![![-3, 0, -1]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [16, 26, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 13, 33], [19, 29, 10], [0, 1]]
 g := ![![[38, 24, 24], [24, 3, 9], [], [14, 13, 1], []], ![[8, 8, 23, 33], [25, 14, 16, 2], [19, 1], [1, 34, 37, 18], [8, 14]], ![[32, 42, 14, 13], [31, 28, 25, 24], [36, 1], [5, 41, 11, 13], [31, 14]]]
 h' := ![![[37, 13, 33], [3, 41, 29], [38, 19, 40], [34, 30], [0, 0, 1], [0, 1]], ![[19, 29, 10], [13, 36, 1], [28, 33, 24], [26, 3, 1], [37, 14, 29], [37, 13, 33]], ![[0, 1], [6, 9, 13], [30, 34, 22], [2, 10, 42], [37, 29, 13], [19, 29, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 9], []]
 b := ![[], [17, 42, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [16, 26, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-147490, 3784, -9331]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3430, 88, -217]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-3, 23, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-3, 23, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![44, 23, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-3, 23, 1], ![-132, 25, 138], ![-3014, 93, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -23, 47]], ![![-1, 0, 1], ![-132, -67, 138], ![-66, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [2, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 46], [0, 1]]
 g := ![![[8, 24], [19, 27], [22, 6], [10, 21], [1]], ![[0, 23], [10, 20], [20, 41], [3, 26], [1]]]
 h' := ![![[31, 46], [9, 27], [3, 36], [27, 37], [45, 31], [0, 1]], ![[0, 1], [0, 20], [38, 11], [46, 10], [19, 16], [31, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [6, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [2, 16, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3127, -3490, 635]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-661, -385, 635]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, 1, 0]] 
 ![![47, 0, 0], ![3, 1, 0], ![45, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, 1, 0], ![0, 4, 6], ![-132, 5, 3]]]
  hmulB := by decide  
  f := ![![![43, 14, 0], ![-658, 0, 0]], ![![-3, -1, 0], ![48, 0, 0]], ![![39, 12, -1], ![-596, 8, 0]]]
  g := ![![![1, 0, 0], ![-3, 47, 0], ![-45, 0, 47]], ![![0, 1, 0], ![-6, 4, 6], ![-6, 5, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-3, 23, 1]] ![![47, 0, 0], ![3, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![141, 47, 0]], ![![-141, 1081, 47], ![-141, 94, 141]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![3, 1, 0]]], ![![![-3, 23, 1]], ![![-3, 2, 3]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![16, -8, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![16, -8, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![16, 45, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![16, -8, 1], ![-132, 13, -48], ![1078, -62, 21]]]
  hmulB := by decide  
  f := ![![![-15, 8, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -45, 53]], ![![0, -1, 1], ![12, 41, -48], ![14, -19, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [33, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 52], [0, 1]]
 g := ![![[25, 37], [43], [10, 42], [43], [23, 1]], ![[28, 16], [43], [22, 11], [43], [46, 52]]]
 h' := ![![[23, 52], [50, 14], [41, 34], [36, 25], [36, 19], [0, 1]], ![[0, 1], [1, 39], [28, 19], [28, 28], [49, 34], [23, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [7, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [33, 30, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3113, -2498, 299]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-149, -301, 299]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-5, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-5, 1, 0]] 
 ![![53, 0, 0], ![48, 1, 0], ![32, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-5, 1, 0], ![0, -4, 6], ![-132, 5, -5]]]
  hmulB := by decide  
  f := ![![![181, -36, 0], ![1908, 0, 0]], ![![166, -33, 0], ![1750, 0, 0]], ![![114, -22, -1], ![1202, 9, 0]]]
  g := ![![![1, 0, 0], ![-48, 53, 0], ![-32, 0, 53]], ![![-1, 1, 0], ![0, -4, 6], ![-4, 5, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![16, -8, 1]] ![![53, 0, 0], ![-5, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-265, 53, 0]], ![![848, -424, 53], ![-212, 53, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-5, 1, 0]]], ![![![16, -8, 1]], ![![-4, 1, -1]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [20, 25, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 48, 12], [6, 10, 47], [0, 1]]
 g := ![![[46, 58, 20], [49], [25, 51], [0, 12, 15], [1]], ![[38, 51, 0, 12], [57, 11, 58, 7], [41, 46], [18, 16], [10, 24, 6, 17]], ![[34, 37, 46, 13], [19, 11, 14, 52], [17, 49], [58, 24, 36, 56], [17, 24, 34, 42]]]
 h' := ![![[24, 48, 12], [23, 31, 16], [31, 7], [0, 42, 46], [39, 34, 30], [0, 1]], ![[6, 10, 47], [33, 42, 1], [22, 41, 25], [4, 27, 20], [54, 27], [24, 48, 12]], ![[0, 1], [29, 45, 42], [14, 11, 34], [0, 49, 52], [53, 57, 29], [6, 10, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 15], []]
 b := ![[], [0, 36, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [20, 25, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2685148233, -233029704, -26966127]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45510987, -3949656, -457053]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-16, 9, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-16, 9, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![45, 9, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-16, 9, 1], ![-132, -2, 54], ![-1166, 23, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -9, 61]], ![![-1, 0, 1], ![-42, -8, 54], ![-11, 2, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [46, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 60], [0, 1]]
 g := ![![[42, 4], [58], [18, 5], [11, 22], [20, 1]], ![[0, 57], [58], [57, 56], [24, 39], [40, 60]]]
 h' := ![![[20, 60], [21, 2], [26, 27], [43, 26], [56, 49], [0, 1]], ![[0, 1], [0, 59], [17, 34], [14, 35], [60, 12], [20, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [8, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [46, 41, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2964, -1520, 780]
  a := ![-1, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-624, -140, 780]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![7, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![7, 1, 0]] 
 ![![61, 0, 0], ![7, 1, 0], ![11, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![7, 1, 0], ![0, 8, 6], ![-132, 5, 7]]]
  hmulB := by decide  
  f := ![![![218, 31, 0], ![-1891, 0, 0]], ![![14, 2, 0], ![-121, 0, 0]], ![![40, -1, -5], ![-347, 51, 0]]]
  g := ![![![1, 0, 0], ![-7, 61, 0], ![-11, 0, 61]], ![![0, 1, 0], ![-2, 8, 6], ![-4, 5, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-16, 9, 1]] ![![61, 0, 0], ![7, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![427, 61, 0]], ![![-976, 549, 61], ![-244, 61, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![7, 1, 0]]], ![![![-16, 9, 1]], ![![-4, 1, 1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-15, -3, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-15, -3, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![52, 64, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-15, -3, 1], ![-132, -13, -18], ![418, -37, -10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -64, 67]], ![![-1, -1, 1], ![12, 17, -18], ![14, 9, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [29, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 66], [0, 1]]
 g := ![![[51, 37], [62, 15], [22], [23], [25], [1]], ![[0, 30], [54, 52], [22], [23], [25], [1]]]
 h' := ![![[62, 66], [11, 29], [29, 22], [59, 42], [49, 31], [38, 62], [0, 1]], ![[0, 1], [0, 38], [53, 45], [50, 25], [28, 36], [63, 5], [62, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [3, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [29, 5, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7077, -5824, 1584]
  a := ![0, 3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1335, -1600, 1584]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![18, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![18, 1, 0]] 
 ![![67, 0, 0], ![18, 1, 0], ![10, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![18, 1, 0], ![0, 19, 6], ![-132, 5, 18]]]
  hmulB := by decide  
  f := ![![![379, 21, 0], ![-1407, 0, 0]], ![![90, 5, 0], ![-334, 0, 0]], ![![34, -14, -5], ![-126, 56, 0]]]
  g := ![![![1, 0, 0], ![-18, 67, 0], ![-10, 0, 67]], ![![0, 1, 0], ![-6, 19, 6], ![-6, 5, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-15, -3, 1]] ![![67, 0, 0], ![18, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1206, 67, 0]], ![![-1005, -201, 67], ![-402, -67, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![18, 1, 0]]], ![![![-15, -3, 1]], ![![-6, -1, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [65, 17, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 38, 19], [42, 32, 52], [0, 1]]
 g := ![![[24], [53, 13, 20], [36, 56, 36], [48, 4], [44, 1], []], ![[68, 23, 54, 38], [36, 36, 2, 10], [47, 16, 11, 1], [9, 8], [54, 30], [4, 6]], ![[8, 57, 11, 33], [24, 31, 23, 17], [37, 67, 38, 65], [48, 37], [30, 24], [42, 6]]]
 h' := ![![[2, 38, 19], [34, 38], [3, 66, 37], [49, 62, 6], [51, 39, 2], [0, 0, 1], [0, 1]], ![[42, 32, 52], [39, 24, 12], [35, 61, 24], [57, 23, 21], [43, 18, 24], [28, 49, 32], [2, 38, 19]], ![[0, 1], [68, 9, 59], [48, 15, 10], [52, 57, 44], [41, 14, 45], [28, 22, 38], [42, 32, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 29], []]
 b := ![[], [11, 49, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [65, 17, 27, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-143705633, 11169152, 2019382]
  a := ![2, -8, -38]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2024023, 157312, 28442]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![20, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![20, 1, 0]] 
 ![![73, 0, 0], ![20, 1, 0], ![3, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![20, 1, 0], ![0, 21, 6], ![-132, 5, 20]]]
  hmulB := by decide  
  f := ![![![181, 9, 0], ![-657, 0, 0]], ![![20, 1, 0], ![-72, 0, 0]], ![![-9, -18, -5], ![33, 61, 0]]]
  g := ![![![1, 0, 0], ![-20, 73, 0], ![-3, 0, 73]], ![![0, 1, 0], ![-6, 21, 6], ![-4, 5, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-14, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-14, 1, 0]] 
 ![![73, 0, 0], ![59, 1, 0], ![67, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-14, 1, 0], ![0, -13, 6], ![-132, 5, -14]]]
  hmulB := by decide  
  f := ![![![743, -53, 0], ![3869, 0, 0]], ![![617, -44, 0], ![3213, 0, 0]], ![![685, -38, -5], ![3567, 61, 0]]]
  g := ![![![1, 0, 0], ![-59, 73, 0], ![-67, 0, 73]], ![![-1, 1, 0], ![5, -13, 6], ![7, 5, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-7, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-7, 1, 0]] 
 ![![73, 0, 0], ![66, 1, 0], ![66, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-7, 1, 0], ![0, -6, 6], ![-132, 5, -7]]]
  hmulB := by decide  
  f := ![![![204, -29, 0], ![2117, 0, 0]], ![![190, -27, 0], ![1972, 0, 0]], ![![190, -22, -5], ![1972, 61, 0]]]
  g := ![![![1, 0, 0], ![-66, 73, 0], ![-66, 0, 73]], ![![-1, 1, 0], ![0, -6, 6], ![0, 5, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![20, 1, 0]] ![![73, 0, 0], ![-14, 1, 0]]
  ![![73, 0, 0], ![2, -11, 1]] where
 M := ![![![5329, 0, 0], ![-1022, 73, 0]], ![![1460, 73, 0], ![-280, 7, 6]]]
 hmul := by decide  
 g := ![![![![71, 11, -1], ![73, 0, 0]], ![![-14, 1, 0], ![0, 0, 0]]], ![![![18, 12, -1], ![73, 0, 0]], ![![-4, 1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![2, -11, 1]] ![![73, 0, 0], ![-7, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-511, 73, 0]], ![![146, -803, 73], ![-146, 73, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-7, 1, 0]]], ![![![2, -11, 1]], ![![-2, 1, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![24, 32, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![24, 32, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![24, 32, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![24, 32, 1], ![-132, 61, 192], ![-4202, 138, 29]]]
  hmulB := by decide  
  f := ![![![-23, -32, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -32, 79]], ![![0, 0, 1], ![-60, -77, 192], ![-62, -10, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [2, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 78], [0, 1]]
 g := ![![[36, 40], [4, 22], [54, 64], [37, 1], [49], [1]], ![[0, 39], [0, 57], [28, 15], [44, 78], [49], [1]]]
 h' := ![![[7, 78], [71, 35], [50, 38], [5, 8], [64, 78], [77, 7], [0, 1]], ![[0, 1], [0, 44], [0, 41], [61, 71], [57, 1], [47, 72], [7, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [31, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [2, 72, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1129, -22, 103]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -42, 103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-34, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-34, 1, 0]] 
 ![![79, 0, 0], ![45, 1, 0], ![50, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-34, 1, 0], ![0, -33, 6], ![-132, 5, -34]]]
  hmulB := by decide  
  f := ![![![511, -15, 0], ![1185, 0, 0]], ![![341, -10, 0], ![791, 0, 0]], ![![326, 18, -5], ![756, 66, 0]]]
  g := ![![![1, 0, 0], ![-45, 79, 0], ![-50, 0, 79]], ![![-1, 1, 0], ![15, -33, 6], ![17, 5, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![24, 32, 1]] ![![79, 0, 0], ![-34, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2686, 79, 0]], ![![1896, 2528, 79], ![-948, -1027, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-34, 1, 0]]], ![![![24, 32, 1]], ![![-12, -13, 2]]]]
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


lemma PB191I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB191I1 : PrimesBelowBoundCertificateInterval O 31 79 191 where
  m := 11
  g := ![2, 2, 1, 2, 2, 1, 2, 2, 1, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB191I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![73, 73, 73]
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I47N1, I53N1, I61N1, I67N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N1], [I41N1], [], [I47N1], [I53N1], [], [I61N1], [I67N1], [], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
