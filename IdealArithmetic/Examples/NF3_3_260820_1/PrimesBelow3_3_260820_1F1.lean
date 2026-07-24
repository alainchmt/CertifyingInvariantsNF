
import IdealArithmetic.Examples.NF3_3_260820_1.RI3_3_260820_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [21, 12, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 21, 5], [6, 15, 32], [0, 1]]
 g := ![![[26, 1, 12], [29, 7], [8, 23, 7], [15, 1], []], ![[31, 0, 20, 17], [4, 12], [25, 30, 6, 23], [5, 3], [30, 25]], ![[32, 8, 18, 8], [19, 34], [27, 23, 27, 17], [11, 34], [3, 25]]]
 h' := ![![[9, 21, 5], [13, 11, 7], [17, 4, 9], [18, 21, 28], [0, 0, 1], [0, 1]], ![[6, 15, 32], [6, 12, 12], [33, 35, 7], [5, 9, 7], [6, 11, 15], [9, 21, 5]], ![[0, 1], [1, 14, 18], [20, 35, 21], [17, 7, 2], [10, 26, 21], [6, 15, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 27], []]
 b := ![[], [6, 21, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [21, 12, 22, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14985, -11174, -1628]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-405, -302, -44]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-48, 0, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-48, 0, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![34, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-48, 0, 1], ![82, 0, 0], ![0, 82, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, 0, 41]], ![![-2, 0, 1], ![2, 0, 0], ![0, 2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 40], [0, 1]]
 g := ![![[14, 36], [18], [1], [5, 1], [1]], ![[19, 5], [18], [1], [4, 40], [1]]]
 h' := ![![[40, 40], [30, 35], [17, 10], [26, 1], [38, 40], [0, 1]], ![[0, 1], [36, 6], [7, 31], [25, 40], [39, 1], [40, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [15, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [3, 1, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-981, 164, 433]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-383, 4, 433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![0, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![0, 1, 0]] 
 ![![41, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![0, 1, 0], ![0, 0, 1], ![82, 48, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![0, 1, 0], ![0, 0, 1], ![2, 48, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-48, 0, 1]] ![![41, 0, 0], ![0, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![0, 41, 0]], ![![-1968, 0, 41], ![82, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![0, 1, 0]]], ![![![-48, 0, 1]], ![![2, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, 1, 0]] 
 ![![43, 0, 0], ![10, 1, 0], ![29, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, 1, 0], ![0, 10, 1], ![82, 48, 10]]]
  hmulB := by decide  
  f := ![![![111, 11, 0], ![-473, 0, 0]], ![![10, 1, 0], ![-42, 0, 0]], ![![73, 7, 0], ![-311, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 43, 0], ![-29, 0, 43]], ![![0, 1, 0], ![-3, 10, 1], ![-16, 48, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-9, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-9, 1, 0]] 
 ![![43, 0, 0], ![34, 1, 0], ![5, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-9, 1, 0], ![0, -9, 1], ![82, 48, -9]]]
  hmulB := by decide  
  f := ![![![271, -30, 0], ![1290, 0, 0]], ![![208, -23, 0], ![990, 0, 0]], ![![47, -5, 0], ![224, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 43, 0], ![-5, 0, 43]], ![![-1, 1, 0], ![7, -9, 1], ![-35, 48, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-1, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-1, 1, 0]] 
 ![![43, 0, 0], ![42, 1, 0], ![42, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-1, 1, 0], ![0, -1, 1], ![82, 48, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![129, 0, 0]], ![![2, -1, 0], ![44, 0, 0]], ![![2, -1, 0], ![44, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 43, 0], ![-42, 0, 43]], ![![-1, 1, 0], ![0, -1, 1], ![-44, 48, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![10, 1, 0]] ![![43, 0, 0], ![-9, 1, 0]]
  ![![43, 0, 0], ![-47, 1, 1]] where
 M := ![![![1849, 0, 0], ![-387, 43, 0]], ![![430, 43, 0], ![-90, 1, 1]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![38, 0, -1], ![43, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![46, -1, -1], ![44, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-47, 1, 1]] ![![43, 0, 0], ![-1, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-43, 43, 0]], ![![-2021, 43, 43], ![129, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-1, 1, 0]]], ![![![-47, 1, 1]], ![![3, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [41, 6, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 15, 38], [35, 31, 9], [0, 1]]
 g := ![![[1, 10, 21], [29, 30, 16], [40, 13, 9], [30, 41, 1], []], ![[21, 21, 29, 33], [4, 38, 40, 5], [27, 38, 9, 46], [5, 45, 43, 46], [43, 34]], ![[16, 11, 31, 12], [32, 9, 46, 36], [46, 16, 46, 6], [4, 23, 3, 4], [25, 34]]]
 h' := ![![[6, 15, 38], [33, 31, 31], [5, 43, 43], [39, 19, 3], [0, 0, 1], [0, 1]], ![[35, 31, 9], [27, 0, 24], [27, 0, 6], [1, 5, 16], [12, 32, 31], [6, 15, 38]], ![[0, 1], [33, 16, 39], [5, 4, 45], [35, 23, 28], [12, 15, 15], [35, 31, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 7], []]
 b := ![[], [43, 44, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [41, 6, 6, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-202241, 12972, -22842]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4303, 276, -486]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [22, 24, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 27, 37], [14, 25, 16], [0, 1]]
 g := ![![[16, 5, 43], [1, 6], [38, 39, 9], [9, 29], [1]], ![[24, 5, 44, 42], [22, 44], [17, 14, 13, 46], [46, 47], [10, 41, 48, 38]], ![[25, 26, 25, 7], [43, 4], [52, 6, 4, 47], [19, 52], [16, 2, 32, 15]]]
 h' := ![![[19, 27, 37], [16, 13, 19], [12, 49, 18], [21, 43, 50], [31, 29, 33], [0, 1]], ![[14, 25, 16], [50, 21, 2], [2, 48, 37], [32, 22, 32], [14, 9, 43], [19, 27, 37]], ![[0, 1], [50, 19, 32], [25, 9, 51], [2, 41, 24], [7, 15, 30], [14, 25, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 3], []]
 b := ![[], [20, 32, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [22, 24, 20, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86443, -140609, -50668]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1631, -2653, -956]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-45, -11, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-45, -11, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![14, 48, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-45, -11, 1], ![82, 3, -11], ![-902, -446, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -48, 59]], ![![-1, -1, 1], ![4, 9, -11], ![-16, -10, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [10, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 58], [0, 1]]
 g := ![![[34, 3], [29, 48], [45], [30, 22], [14, 1]], ![[17, 56], [52, 11], [45], [43, 37], [28, 58]]]
 h' := ![![[14, 58], [5, 11], [47, 44], [54, 35], [37, 9], [0, 1]], ![[0, 1], [41, 48], [14, 15], [13, 24], [45, 50], [14, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [19, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [10, 45, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![174, 133, 4]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -1, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![11, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![11, 1, 0]] 
 ![![59, 0, 0], ![11, 1, 0], ![56, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![11, 1, 0], ![0, 11, 1], ![82, 48, 11]]]
  hmulB := by decide  
  f := ![![![342, 31, 0], ![-1829, 0, 0]], ![![44, 4, 0], ![-235, 0, 0]], ![![322, 29, 0], ![-1722, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 59, 0], ![-56, 0, 59]], ![![0, 1, 0], ![-3, 11, 1], ![-18, 48, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-45, -11, 1]] ![![59, 0, 0], ![11, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![649, 59, 0]], ![![-2655, -649, 59], ![-413, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![11, 1, 0]]], ![![![-45, -11, 1]], ![![-7, -2, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [47, 17, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 31, 20], [58, 29, 41], [0, 1]]
 g := ![![[16, 60, 36], [36, 49], [0, 60, 25], [28, 22, 41], [1]], ![[36, 58, 50, 4], [32, 45], [58, 9, 41, 13], [50, 35, 53, 5], [37, 7, 27, 9]], ![[14, 49, 1, 36], [22, 27], [36, 46, 19, 15], [49, 29, 7, 57], [45, 56, 54, 52]]]
 h' := ![![[41, 31, 20], [16, 13, 6], [0, 52, 54], [26, 28, 56], [14, 44, 38], [0, 1]], ![[58, 29, 41], [2, 38, 7], [15, 35, 44], [54, 3, 49], [21, 8, 30], [41, 31, 20]], ![[0, 1], [17, 10, 48], [21, 35, 24], [51, 30, 17], [54, 9, 54], [58, 29, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 18], []]
 b := ![[], [42, 44, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [47, 17, 23, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![874618, 608048, 69662]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14338, 9968, 1142]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [64, 58, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 39, 29], [32, 27, 38], [0, 1]]
 g := ![![[1, 26, 65], [33, 41, 22], [66, 59], [23, 47], [35, 1], []], ![[64, 58, 18, 9], [0, 45, 20, 26], [62, 26], [37, 25], [27, 59], [6, 37]], ![[44, 50, 27, 31], [30, 55, 25, 31], [40, 39], [54, 60], [3, 47], [64, 37]]]
 h' := ![![[3, 39, 29], [32, 11, 47], [44, 35, 25], [39, 61, 27], [38, 50, 28], [0, 0, 1], [0, 1]], ![[32, 27, 38], [61, 20, 47], [20, 17, 15], [13, 20, 19], [6, 57, 62], [27, 64, 27], [3, 39, 29]], ![[0, 1], [50, 36, 40], [7, 15, 27], [50, 53, 21], [42, 27, 44], [10, 3, 39], [32, 27, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 33], []]
 b := ![[], [40, 25, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [64, 58, 32, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16683, 5963, -1206]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![249, 89, -18]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -15, -2]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-21, -15, -2]] 
 ![![71, 0, 0], ![33, 1, 0], ![47, 0, 1]] where
  M :=![![![-21, -15, -2], ![-164, -117, -15], ![-1230, -884, -117]]]
  hmulB := by decide  
  f := ![![![-429, -13, 9]], ![![-189, -6, 4]], ![![-299, -7, 6]]]
  g := ![![![8, -15, -2], ![62, -117, -15], ![471, -884, -117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 29, -5]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 29, -5]] 
 ![![71, 0, 0], ![51, 1, 0], ![26, 0, 1]] where
  M :=![![![71, 29, -5], ![-410, -169, 29], ![2378, 982, -169]]]
  hmulB := by decide  
  f := ![![![83, -9, -4]], ![![55, -8, -3]], ![![20, -14, -3]]]
  g := ![![![-18, 29, -5], ![105, -169, 29], ![-610, 982, -169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -8, -1]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-11, -8, -1]] 
 ![![71, 0, 0], ![58, 1, 0], ![44, 0, 1]] where
  M :=![![![-11, -8, -1], ![-82, -59, -8], ![-656, -466, -59]]]
  hmulB := by decide  
  f := ![![![247, 6, -5]], ![![196, 5, -4]], ![![160, 2, -3]]]
  g := ![![![7, -8, -1], ![52, -59, -8], ![408, -466, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-21, -15, -2]] ![![71, 29, -5]]
  ![![-97, -38, 8]] where
 M := ![![![-97, -38, 8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-97, -38, 8]] ![![-11, -8, -1]]
  ![![71, 0, 0]] where
 M := ![![![-1065, -710, -71]]]
 hmul := by decide  
 g := ![![![![-15, -10, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -6, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-15, -6, 1]] 
 ![![73, 0, 0], ![27, 1, 0], ![1, 0, 1]] where
  M :=![![![-15, -6, 1], ![82, 33, -6], ![-492, -206, 33]]]
  hmulB := by decide  
  f := ![![![-147, -8, 3]], ![![-51, -3, 1]], ![![-11, -2, 0]]]
  g := ![![![2, -6, 1], ![-11, 33, -6], ![69, -206, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -8, -1]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-13, -8, -1]] 
 ![![73, 0, 0], ![56, 1, 0], ![3, 0, 1]] where
  M :=![![![-13, -8, -1], ![-82, -61, -8], ![-656, -466, -61]]]
  hmulB := by decide  
  f := ![![![7, 22, -3]], ![![2, 15, -2]], ![![25, 12, -2]]]
  g := ![![![6, -8, -1], ![46, -61, -8], ![351, -466, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, 4, -2]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![87, 4, -2]] 
 ![![73, 0, 0], ![63, 1, 0], ![46, 0, 1]] where
  M :=![![![87, 4, -2], ![-164, -9, 4], ![328, 28, -9]]]
  hmulB := by decide  
  f := ![![![31, 20, 2]], ![![29, 19, 2]], ![![42, 28, 3]]]
  g := ![![![-1, 4, -2], ![3, -9, 4], ![-14, 28, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-15, -6, 1]] ![![-13, -8, -1]]
  ![![31, 20, 2]] where
 M := ![![![31, 20, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![31, 20, 2]] ![![87, 4, -2]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![7, 23, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![7, 23, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![7, 23, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![7, 23, 1], ![82, 55, 23], ![1886, 1186, 55]]]
  hmulB := by decide  
  f := ![![![-6, -23, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -23, 79]], ![![0, 0, 1], ![-1, -6, 23], ![19, -1, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [39, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 78], [0, 1]]
 g := ![![[39, 55], [2, 13], [11, 10], [6, 22], [5], [1]], ![[45, 24], [58, 66], [48, 69], [40, 57], [5], [1]]]
 h' := ![![[59, 78], [1, 56], [45, 31], [3, 22], [62, 38], [40, 59], [0, 1]], ![[0, 1], [66, 23], [57, 48], [37, 57], [13, 41], [45, 20], [59, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [31, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [39, 20, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![367, 540, 233]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -61, 233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-23, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-23, 1, 0]] 
 ![![79, 0, 0], ![56, 1, 0], ![24, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-23, 1, 0], ![0, -23, 1], ![82, 48, -23]]]
  hmulB := by decide  
  f := ![![![1496, -65, 0], ![5135, 0, 0]], ![![1082, -47, 0], ![3714, 0, 0]], ![![490, -21, 0], ![1682, 1, 0]]]
  g := ![![![1, 0, 0], ![-56, 79, 0], ![-24, 0, 79]], ![![-1, 1, 0], ![16, -23, 1], ![-26, 48, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![7, 23, 1]] ![![79, 0, 0], ![-23, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1817, 79, 0]], ![![553, 1817, 79], ![-79, -474, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-23, 1, 0]]], ![![![7, 23, 1]], ![![-1, -6, 0]]]]
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


lemma PB114I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB114I1 : PrimesBelowBoundCertificateInterval O 31 79 114 where
  m := 11
  g := ![1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB114I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N1, I43N0, I43N1, I43N2, I59N1, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2, I79N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N2], [], [], [I59N1], [], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
