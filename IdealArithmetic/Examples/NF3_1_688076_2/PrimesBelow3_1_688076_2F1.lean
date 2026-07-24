
import IdealArithmetic.Examples.NF3_1_688076_2.RI3_1_688076_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![3, 9, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![3, 9, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![3, 9, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![3, 9, 1], ![-165, 23, 19], ![-1643, 103, 32]]]
  hmulB := by decide  
  f := ![![![-2, -9, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -9, 37]], ![![0, 0, 1], ![-6, -4, 19], ![-47, -5, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [14, 0, 1] where
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
 g := ![![[], [26], [], [], [1]], ![[], [26], [], [], [1]]]
 h' := ![![[0, 36], [6], [0, 10], [11], [23], [0, 1]], ![[0, 1], [6], [0, 27], [11], [23], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [14, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-988, -226, 90]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -28, 90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![18, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![18, 1, 0]] 
 ![![37, 0, 0], ![18, 1, 0], ![5, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![18, 1, 0], ![1, 18, 2], ![-174, 20, 19]]]
  hmulB := by decide  
  f := ![![![-533, -15103, -1680], ![-629, 31080, 0]], ![![-264, -7336, -816], ![-295, 15096, 0]], ![![-73, -2041, -227], ![-83, 4200, 0]]]
  g := ![![![1, 0, 0], ![-18, 37, 0], ![-5, 0, 37]], ![![0, 1, 0], ![-9, 18, 2], ![-17, 20, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![3, 9, 1]] ![![37, 0, 0], ![18, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![666, 37, 0]], ![![111, 333, 37], ![-111, 185, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![18, 1, 0]]], ![![![3, 9, 1]], ![![-3, 5, 1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-13, 9, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-13, 9, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![28, 9, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-13, 9, 1], ![-165, 7, 19], ![-1643, 103, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -9, 41]], ![![-1, 0, 1], ![-17, -4, 19], ![-51, -1, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [11, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 40], [0, 1]]
 g := ![![[19, 9], [16], [5], [24, 16], [1]], ![[24, 32], [16], [5], [1, 25], [1]]]
 h' := ![![[37, 40], [25, 38], [23, 4], [23, 13], [30, 37], [0, 1]], ![[0, 1], [37, 3], [7, 37], [12, 28], [5, 4], [37, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [11, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1582, -2341, 528]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-322, -173, 528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-19, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-19, 1, 0]] 
 ![![41, 0, 0], ![22, 1, 0], ![25, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-19, 1, 0], ![1, -19, 2], ![-174, 20, -18]]]
  hmulB := by decide  
  f := ![![![630, -18071, 1904], ![-697, -39032, 0]], ![![340, -9681, 1020], ![-368, -20910, 0]], ![![386, -11019, 1161], ![-421, -23800, 0]]]
  g := ![![![1, 0, 0], ![-22, 41, 0], ![-25, 0, 41]], ![![-1, 1, 0], ![9, -19, 2], ![-4, 20, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-13, 9, 1]] ![![41, 0, 0], ![-19, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-779, 41, 0]], ![![-533, 369, 41], ![82, -164, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-19, 1, 0]]], ![![![-13, 9, 1]], ![![2, -4, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [28, 7, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 14, 15], [17, 28, 28], [0, 1]]
 g := ![![[2, 18, 13], [37, 31, 11], [0, 13], [9, 4, 1], []], ![[17, 16, 13, 15], [42, 28, 15, 11], [19, 9], [33, 12, 18, 21], [30, 10]], ![[32, 29, 7, 3], [1, 40, 27, 2], [31, 13], [20, 27, 32, 27], [17, 10]]]
 h' := ![![[30, 14, 15], [39, 40, 20], [36, 30, 22], [6, 40, 23], [0, 0, 1], [0, 1]], ![[17, 28, 28], [31, 35, 42], [20, 36, 34], [6, 10, 40], [17, 6, 28], [30, 14, 15]], ![[0, 1], [32, 11, 24], [1, 20, 30], [40, 36, 23], [28, 37, 14], [17, 28, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 20], []]
 b := ![[], [37, 5, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [28, 7, 39, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3406949469, 942482901, -86556076]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-79231383, 21918207, -2012932]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [25, 28, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 2, 28], [37, 44, 19], [0, 1]]
 g := ![![[36, 37, 28], [25, 20, 21], [46, 31, 34], [26, 30, 1], []], ![[11, 21, 45, 1], [7, 30, 4, 21], [0, 20, 25, 25], [22, 38, 6, 17], [38, 32]], ![[25, 1, 30, 5], [2, 1, 20, 20], [13, 32, 15, 5], [33, 24, 31, 29], [0, 32]]]
 h' := ![![[40, 2, 28], [33, 36, 13], [25, 22, 31], [8, 26, 9], [0, 0, 1], [0, 1]], ![[37, 44, 19], [6, 10, 29], [46, 1, 6], [36, 38, 43], [39, 35, 44], [40, 2, 28]], ![[0, 1], [33, 1, 5], [38, 24, 10], [37, 30, 42], [6, 12, 2], [37, 44, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 44], []]
 b := ![[], [17, 23, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [25, 28, 17, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1749058, 388173, -35861]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37214, 8259, -763]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-35, -7, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-35, -7, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![18, 46, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-35, -7, 1], ![-181, -15, -13], ![1141, -217, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -46, 53]], ![![-1, -1, 1], ![1, 11, -13], ![29, 15, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [1, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 52], [0, 1]]
 g := ![![[34, 1], [28], [3, 37], [15], [19, 1]], ![[0, 52], [28], [17, 16], [15], [38, 52]]]
 h' := ![![[19, 52], [34, 1], [50, 9], [28, 14], [34, 42], [0, 1]], ![[0, 1], [0, 52], [9, 44], [29, 39], [37, 11], [19, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [10, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [1, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1035, -260, 22]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, -24, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![13, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![13, 1, 0]] 
 ![![53, 0, 0], ![13, 1, 0], ![22, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![13, 1, 0], ![1, 13, 2], ![-174, 20, 14]]]
  hmulB := by decide  
  f := ![![![-1228, -17825, -2744], ![-583, 72716, 0]], ![![-310, -4366, -672], ![-105, 17808, 0]], ![![-509, -7399, -1139], ![-245, 30184, 0]]]
  g := ![![![1, 0, 0], ![-13, 53, 0], ![-22, 0, 53]], ![![0, 1, 0], ![-4, 13, 2], ![-14, 20, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-35, -7, 1]] ![![53, 0, 0], ![13, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![689, 53, 0]], ![![-1855, -371, 53], ![-636, -106, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![13, 1, 0]]], ![![![-35, -7, 1]], ![![-12, -2, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [55, 15, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 48, 7], [16, 10, 52], [0, 1]]
 g := ![![[47, 22, 3], [1, 20, 17], [35, 46], [55, 52, 21], [1]], ![[11, 14, 12, 35], [43, 28, 42, 12], [20, 25], [44, 38, 43, 5], [14, 22, 33, 48]], ![[43, 3, 51, 55], [29, 18, 52, 2], [11, 35], [0, 45, 22, 18], [18, 6, 56, 11]]]
 h' := ![![[11, 48, 7], [4, 0, 11], [42, 11, 31], [43, 48, 20], [4, 44, 27], [0, 1]], ![[16, 10, 52], [25, 11, 51], [13, 28, 33], [46, 23, 5], [30, 15, 47], [11, 48, 7]], ![[0, 1], [2, 48, 56], [30, 20, 54], [35, 47, 34], [38, 0, 44], [16, 10, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 11], []]
 b := ![[], [9, 26, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [55, 15, 32, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5158016, -73337, 123900]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-87424, -1243, 2100]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![7, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![7, 1, 0]] 
 ![![61, 0, 0], ![7, 1, 0], ![37, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![7, 1, 0], ![1, 7, 2], ![-174, 20, 8]]]
  hmulB := by decide  
  f := ![![![-818, -5877, -1680], ![-183, 51240, 0]], ![![-96, -672, -192], ![1, 5856, 0]], ![![-498, -3565, -1019], ![-95, 31080, 0]]]
  g := ![![![1, 0, 0], ![-7, 61, 0], ![-37, 0, 61]], ![![0, 1, 0], ![-2, 7, 2], ![-10, 20, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-5, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-5, 1, 0]] 
 ![![61, 0, 0], ![56, 1, 0], ![49, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-5, 1, 0], ![1, -5, 2], ![-174, 20, -4]]]
  hmulB := by decide  
  f := ![![![-210, 1079, -432], ![61, 13176, 0]], ![![-192, 989, -396], ![62, 12078, 0]], ![![-170, 867, -347], ![33, 10584, 0]]]
  g := ![![![1, 0, 0], ![-56, 61, 0], ![-49, 0, 61]], ![![-1, 1, 0], ![3, -5, 2], ![-18, 20, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-3, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-3, 1, 0]] 
 ![![61, 0, 0], ![58, 1, 0], ![57, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-3, 1, 0], ![1, -3, 2], ![-174, 20, -2]]]
  hmulB := by decide  
  f := ![![![-156, 479, -320], ![61, 9760, 0]], ![![-148, 455, -304], ![62, 9272, 0]], ![![-147, 448, -299], ![32, 9120, 0]]]
  g := ![![![1, 0, 0], ![-58, 61, 0], ![-57, 0, 61]], ![![-1, 1, 0], ![1, -3, 2], ![-20, 20, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![7, 1, 0]] ![![61, 0, 0], ![-5, 1, 0]]
  ![![61, 0, 0], ![-17, 1, 1]] where
 M := ![![![3721, 0, 0], ![-305, 61, 0]], ![![427, 61, 0], ![-34, 2, 2]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![12, 0, -1], ![61, 0, 0]]], ![![![7, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-17, 1, 1]] ![![61, 0, 0], ![-3, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-183, 61, 0]], ![![-1037, 61, 61], ![-122, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-3, 1, 0]]], ![![![-17, 1, 1]], ![![-2, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![28, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![28, 1, 0]] 
 ![![67, 0, 0], ![28, 1, 0], ![44, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![28, 1, 0], ![1, 28, 2], ![-174, 20, 29]]]
  hmulB := by decide  
  f := ![![![169, 7053, 504], ![201, -16884, 0]], ![![49, 2938, 210], ![135, -7035, 0]], ![![116, 4632, 331], ![120, -11088, 0]]]
  g := ![![![1, 0, 0], ![-28, 67, 0], ![-44, 0, 67]], ![![0, 1, 0], ![-13, 28, 2], ![-30, 20, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-21, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-21, 1, 0]] 
 ![![67, 0, 0], ![46, 1, 0], ![48, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-21, 1, 0], ![1, -21, 2], ![-174, 20, -20]]]
  hmulB := by decide  
  f := ![![![1684, -42823, 4080], ![-1139, -136680, 0]], ![![1170, -29389, 2800], ![-736, -93800, 0]], ![![1203, -30679, 2923], ![-827, -97920, 0]]]
  g := ![![![1, 0, 0], ![-46, 67, 0], ![-48, 0, 67]], ![![-1, 1, 0], ![13, -21, 2], ![-2, 20, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-8, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-8, 1, 0]] 
 ![![67, 0, 0], ![59, 1, 0], ![2, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-8, 1, 0], ![1, -8, 2], ![-174, 20, -7]]]
  hmulB := by decide  
  f := ![![![-1576, 12994, -3250], ![402, 108875, 0]], ![![-1381, 11434, -2860], ![403, 95810, 0]], ![![-40, 387, -97], ![71, 3250, 0]]]
  g := ![![![1, 0, 0], ![-59, 67, 0], ![-2, 0, 67]], ![![-1, 1, 0], ![7, -8, 2], ![-20, 20, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![28, 1, 0]] ![![67, 0, 0], ![-21, 1, 0]]
  ![![67, 0, 0], ![8, -30, 1]] where
 M := ![![![4489, 0, 0], ![-1407, 67, 0]], ![![1876, 67, 0], ![-587, 7, 2]]]
 hmul := by decide  
 g := ![![![![59, 30, -1], ![67, 0, 0]], ![![-21, 1, 0], ![0, 0, 0]]], ![![![20, 31, -1], ![67, 0, 0]], ![![-9, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![8, -30, 1]] ![![67, 0, 0], ![-8, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-536, 67, 0]], ![![536, -2010, 67], ![-268, 268, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-8, 1, 0]]], ![![![8, -30, 1]], ![![-4, 4, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-29, -18, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-29, -18, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![42, 53, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-29, -18, 1], ![-192, -9, -35], ![3055, -437, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -53, 71]], ![![-1, -1, 1], ![18, 26, -35], ![59, 14, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [45, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 70], [0, 1]]
 g := ![![[70, 30], [32, 20], [53, 64], [60], [37], [1]], ![[0, 41], [9, 51], [22, 7], [60], [37], [1]]]
 h' := ![![[45, 70], [51, 32], [29, 34], [23, 8], [5, 29], [26, 45], [0, 1]], ![[0, 1], [0, 39], [68, 37], [28, 63], [32, 42], [63, 26], [45, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [26, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [45, 26, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2445, -987, 114]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -99, 114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![35, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![35, 1, 0]] 
 ![![71, 0, 0], ![35, 1, 0], ![27, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![35, 1, 0], ![1, 35, 2], ![-174, 20, 36]]]
  hmulB := by decide  
  f := ![![![-991, -55528, -3174], ![-1207, 112677, 0]], ![![-502, -27362, -1564], ![-567, 55522, 0]], ![![-402, -21117, -1207], ![-408, 42849, 0]]]
  g := ![![![1, 0, 0], ![-35, 71, 0], ![-27, 0, 71]], ![![0, 1, 0], ![-18, 35, 2], ![-26, 20, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-29, -18, 1]] ![![71, 0, 0], ![35, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2485, 71, 0]], ![![-2059, -1278, 71], ![-1207, -639, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![35, 1, 0]]], ![![![-29, -18, 1]], ![![-17, -9, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-12, 24, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-12, 24, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![61, 24, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-12, 24, 1], ![-150, 8, 49], ![-4253, 403, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -24, 73]], ![![-1, 0, 1], ![-43, -16, 49], ![-85, -5, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [57, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 72], [0, 1]]
 g := ![![[54, 41], [54], [36], [42, 25], [71], [1]], ![[0, 32], [54], [36], [34, 48], [71], [1]]]
 h' := ![![[61, 72], [65, 48], [71, 45], [15, 67], [5, 5], [16, 61], [0, 1]], ![[0, 1], [0, 25], [42, 28], [14, 6], [18, 68], [14, 12], [61, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [21, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [57, 12, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2538, -1056, 394]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-364, -144, 394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![24, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![24, 1, 0]] 
 ![![73, 0, 0], ![24, 1, 0], ![41, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![24, 1, 0], ![1, 24, 2], ![-174, 20, 25]]]
  hmulB := by decide  
  f := ![![![-1529, -45345, -3780], ![-1095, 137970, 0]], ![![-501, -14899, -1242], ![-364, 45333, 0]], ![![-865, -25468, -2123], ![-596, 77490, 0]]]
  g := ![![![1, 0, 0], ![-24, 73, 0], ![-41, 0, 73]], ![![0, 1, 0], ![-9, 24, 2], ![-23, 20, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-12, 24, 1]] ![![73, 0, 0], ![24, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1752, 73, 0]], ![![-876, 1752, 73], ![-438, 584, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![24, 1, 0]]], ![![![-12, 24, 1]], ![![-6, 8, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-28, -21, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-28, -21, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![51, 58, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-28, -21, 1], ![-195, -8, -41], ![3577, -497, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -58, 79]], ![![-1, -1, 1], ![24, 30, -41], ![64, 15, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [55, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 78], [0, 1]]
 g := ![![[28, 23], [40, 8], [23, 4], [22, 50], [20], [1]], ![[0, 56], [44, 71], [25, 75], [47, 29], [20], [1]]]
 h' := ![![[40, 78], [12, 55], [78, 61], [54, 77], [29, 34], [24, 40], [0, 1]], ![[0, 1], [0, 24], [69, 18], [53, 2], [46, 45], [44, 39], [40, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [63, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [55, 39, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2040, -1925, 355]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-255, -285, 355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-38, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-38, 1, 0]] 
 ![![79, 0, 0], ![41, 1, 0], ![29, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-38, 1, 0], ![1, -38, 2], ![-174, 20, -37]]]
  hmulB := by decide  
  f := ![![![-1027, 63595, -3348], ![1343, 132246, 0]], ![![-525, 32975, -1736], ![712, 68572, 0]], ![![-377, 23345, -1229], ![493, 48546, 0]]]
  g := ![![![1, 0, 0], ![-41, 79, 0], ![-29, 0, 79]], ![![-1, 1, 0], ![19, -38, 2], ![1, 20, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-28, -21, 1]] ![![79, 0, 0], ![-38, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-3002, 79, 0]], ![![-2212, -1659, 79], ![869, 790, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-38, 1, 0]]], ![![![-28, -21, 1]], ![![11, 10, -1]]]]
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


lemma PB235I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB235I1 : PrimesBelowBoundCertificateInterval O 31 79 235 where
  m := 11
  g := ![2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB235I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
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
      exact NI41N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I53N1, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [], [], [I53N1], [], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
