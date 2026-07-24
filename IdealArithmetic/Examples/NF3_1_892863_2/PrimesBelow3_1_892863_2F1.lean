
import IdealArithmetic.Examples.NF3_1_892863_2.RI3_1_892863_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [17, 29, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 21, 20], [32, 15, 17], [0, 1]]
 g := ![![[16, 9, 4], [22, 9], [13, 8, 1], [19, 1], []], ![[5, 13, 29, 29], [10, 30], [14, 23, 8, 14], [10, 3], [4, 30]], ![[33, 7, 22, 19], [1, 30], [26, 12, 11, 29], [31, 34], [7, 30]]]
 h' := ![![[24, 21, 20], [34, 11, 2], [1, 31, 34], [10, 24, 36], [0, 0, 1], [0, 1]], ![[32, 15, 17], [19, 33, 28], [35, 23, 20], [4, 11, 21], [27, 12, 15], [24, 21, 20]], ![[0, 1], [13, 30, 7], [17, 20, 20], [21, 2, 17], [17, 25, 21], [32, 15, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 18], []]
 b := ![[], [10, 31, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [17, 29, 18, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1065711, 363932, -173604]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28803, 9836, -4692]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![27, 21, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![27, 21, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![27, 21, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![27, 21, 1], ![191, 21, 83], ![3041, -523, -21]]]
  hmulB := by decide  
  f := ![![![-26, -21, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -21, 41]], ![![0, 0, 1], ![-50, -42, 83], ![88, -2, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [20, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 40], [0, 1]]
 g := ![![[6, 39], [33], [37], [30, 9], [1]], ![[0, 2], [33], [37], [16, 32], [1]]]
 h' := ![![[3, 40], [33, 30], [18, 22], [15, 23], [21, 3], [0, 1]], ![[0, 1], [0, 11], [2, 19], [2, 18], [30, 38], [3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [4, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [20, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2100, 1100, -465]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![255, 265, -465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-1, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-1, 1, 0]] 
 ![![41, 0, 0], ![40, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-1, 1, 0], ![2, 0, 4], ![149, -27, -2]]]
  hmulB := by decide  
  f := ![![![1681, 0, 3360], ![0, -34440, 0]], ![![1639, 0, 3276], ![1, -33579, 0]], ![![861, 0, 1721], ![0, -17640, 0]]]
  g := ![![![1, 0, 0], ![-40, 41, 0], ![-21, 0, 41]], ![![-1, 1, 0], ![-2, 0, 4], ![31, -27, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![27, 21, 1]] ![![41, 0, 0], ![-1, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-41, 41, 0]], ![![1107, 861, 41], ![164, 0, 82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-1, 1, 0]]], ![![![27, 21, 1]], ![![4, 0, 2]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![31, 5, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![31, 5, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![31, 5, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![31, 5, 1], ![159, 9, 19], ![657, -91, -1]]]
  hmulB := by decide  
  f := ![![![-30, -5, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -5, 43]], ![![0, 0, 1], ![-10, -2, 19], ![16, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [14, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 42], [0, 1]]
 g := ![![[8, 40], [25, 17], [41], [8, 31], [1]], ![[0, 3], [13, 26], [41], [19, 12], [1]]]
 h' := ![![[17, 42], [37, 13], [16, 24], [17, 27], [29, 17], [0, 1]], ![[0, 1], [0, 30], [37, 19], [3, 16], [17, 26], [17, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [32, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [14, 26, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![409493, 1004464, -979612]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![715755, 137268, -979612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![1, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![2, -18, 4], ![149, -27, -20]]]
  hmulB := by decide  
  f := ![![![-69, 970, -216], ![86, 2322, 0]], ![![-40, 539, -120], ![44, 1290, 0]], ![![9, 22, -5], ![26, 54, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-1, 0, 43]], ![![-1, 1, 0], ![10, -18, 4], ![19, -27, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![31, 5, 1]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![1333, 215, 43], ![-430, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-19, 1, 0]]], ![![![31, 5, 1]], ![![-10, -2, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![29, 23, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![29, 23, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![29, 23, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![29, 23, 1], ![195, 25, 91], ![3339, -577, -21]]]
  hmulB := by decide  
  f := ![![![-28, -23, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -23, 47]], ![![0, 0, 1], ![-52, -44, 91], ![84, -2, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [11, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 46], [0, 1]]
 g := ![![[14, 18], [31, 27], [21, 32], [16, 28], [1]], ![[15, 29], [9, 20], [28, 15], [28, 19], [1]]]
 h' := ![![[34, 46], [35, 21], [4, 36], [12, 28], [36, 34], [0, 1]], ![[0, 1], [44, 26], [6, 11], [24, 19], [17, 13], [34, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [39, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [11, 13, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2243, 1772, -1382]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![805, 714, -1382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, 1, 0]] 
 ![![47, 0, 0], ![3, 1, 0], ![21, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, 1, 0], ![2, 4, 4], ![149, -27, 2]]]
  hmulB := by decide  
  f := ![![![-1334, -2685, -2688], ![-141, 31584, 0]], ![![-84, -168, -168], ![1, 1974, 0]], ![![-597, -1200, -1201], ![-48, 14112, 0]]]
  g := ![![![1, 0, 0], ![-3, 47, 0], ![-21, 0, 47]], ![![0, 1, 0], ![-2, 4, 4], ![4, -27, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![29, 23, 1]] ![![47, 0, 0], ![3, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![141, 47, 0]], ![![1363, 1081, 47], ![282, 94, 94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![3, 1, 0]]], ![![![29, 23, 1]], ![![6, 2, 2]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [9, 8, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 44, 26], [17, 8, 27], [0, 1]]
 g := ![![[14, 9, 46], [27, 47], [36, 0, 24], [21, 9], [1]], ![[24, 14], [34, 28], [28, 19, 39, 45], [31, 29], [20, 36, 40, 33]], ![[25, 1, 14, 23], [16, 1], [40, 17, 10, 35], [35, 52], [5, 18, 52, 20]]]
 h' := ![![[33, 44, 26], [5, 13, 24], [47, 34, 43], [51, 1, 36], [44, 45, 50], [0, 1]], ![[17, 8, 27], [37, 48], [5, 36, 9], [45, 0, 49], [35, 5, 33], [33, 44, 26]], ![[0, 1], [31, 45, 29], [4, 36, 1], [14, 52, 21], [45, 3, 23], [17, 8, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 11], []]
 b := ![[], [38, 13, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [9, 8, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1072031, 349694, -159318]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20227, 6598, -3006]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-2, 3, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-2, 3, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![57, 3, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-2, 3, 1], ![155, -26, 11], ![359, -37, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -3, 59]], ![![-1, 0, 1], ![-8, -1, 11], ![37, 1, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [26, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 58], [0, 1]]
 g := ![![[52, 25], [24, 7], [21], [29, 1], [5, 1]], ![[0, 34], [0, 52], [21], [34, 58], [10, 58]]]
 h' := ![![[5, 58], [25, 54], [36, 40], [13, 27], [47, 58], [0, 1]], ![[0, 1], [0, 5], [0, 19], [30, 32], [42, 1], [5, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [44, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [26, 54, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106089, 40611, -50301]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50394, 3246, -50301]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-11, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-11, 1, 0]] 
 ![![59, 0, 0], ![48, 1, 0], ![32, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-11, 1, 0], ![2, -10, 4], ![149, -27, -12]]]
  hmulB := by decide  
  f := ![![![-1575, 8312, -3328], ![472, 49088, 0]], ![![-1285, 6754, -2704], ![355, 39884, 0]], ![![-852, 4508, -1805], ![268, 26624, 0]]]
  g := ![![![1, 0, 0], ![-48, 59, 0], ![-32, 0, 59]], ![![-1, 1, 0], ![6, -10, 4], ![31, -27, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-2, 3, 1]] ![![59, 0, 0], ![-11, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-649, 59, 0]], ![![-118, 177, 59], ![177, -59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-11, 1, 0]]], ![![![-2, 3, 1]], ![![3, -1, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![38, -26, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![38, -26, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![38, 35, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![38, -26, 1], ![97, -15, -105], ![-3962, 746, 37]]]
  hmulB := by decide  
  f := ![![![-37, 26, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -35, 61]], ![![0, -1, 1], ![67, 60, -105], ![-88, -9, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [7, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 60], [0, 1]]
 g := ![![[42, 58], [34], [23, 4], [45, 3], [11, 1]], ![[9, 3], [34], [6, 57], [17, 58], [22, 60]]]
 h' := ![![[11, 60], [2, 34], [22, 20], [51, 59], [45, 53], [0, 1]], ![[0, 1], [10, 27], [59, 41], [29, 2], [18, 8], [11, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [48, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [7, 50, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-426, 147, -69]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 42, -69]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-17, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-17, 1, 0]] 
 ![![61, 0, 0], ![44, 1, 0], ![24, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-17, 1, 0], ![2, -16, 4], ![149, -27, -18]]]
  hmulB := by decide  
  f := ![![![4462, -39873, 9976], ![-1891, -152134, 0]], ![![3223, -28746, 7192], ![-1341, -109678, 0]], ![![1760, -15688, 3925], ![-728, -59856, 0]]]
  g := ![![![1, 0, 0], ![-44, 61, 0], ![-24, 0, 61]], ![![-1, 1, 0], ![10, -16, 4], ![29, -27, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![38, -26, 1]] ![![61, 0, 0], ![-17, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1037, 61, 0]], ![![2318, -1586, 61], ![-549, 427, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-17, 1, 0]]], ![![![38, -26, 1]], ![![-9, 7, -2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![45, -23, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![45, -23, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![45, 44, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![45, -23, 1], ![103, -5, -93], ![-3515, 665, 41]]]
  hmulB := by decide  
  f := ![![![-44, 23, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -44, 67]], ![![0, -1, 1], ![64, 61, -93], ![-80, -17, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [7, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 66], [0, 1]]
 g := ![![[37, 19], [], [], [], [14], [1]], ![[7, 48], [], [], [], [14], [1]]]
 h' := ![![[9, 66], [0, 35], [54], [56], [18], [60, 9], [0, 1]], ![[0, 1], [47, 32], [54], [56], [18], [7, 58], [9, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [52, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [7, 58, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![480, 2993, -2044]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1380, 1387, -2044]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![26, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![26, 1, 0]] 
 ![![67, 0, 0], ![26, 1, 0], ![26, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![26, 1, 0], ![2, 27, 4], ![149, -27, 25]]]
  hmulB := by decide  
  f := ![![![3913, 66112, 9800], ![2546, -164150, 0]], ![![1510, 25635, 3800], ![1006, -63650, 0]], ![![1508, 25655, 3803], ![1015, -63700, 0]]]
  g := ![![![1, 0, 0], ![-26, 67, 0], ![-26, 0, 67]], ![![0, 1, 0], ![-12, 27, 4], ![3, -27, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![45, -23, 1]] ![![67, 0, 0], ![26, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1742, 67, 0]], ![![3015, -1541, 67], ![1273, -603, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![26, 1, 0]]], ![![![45, -23, 1]], ![![19, -9, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![47, -2, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![47, -2, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![47, 69, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![47, -2, 1], ![145, 18, -9], ![-386, 98, 22]]]
  hmulB := by decide  
  f := ![![![-46, 2, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -69, 71]], ![![0, -1, 1], ![8, 9, -9], ![-20, -20, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [62, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 70], [0, 1]]
 g := ![![[9, 15], [34, 18], [32, 38], [19], [29], [1]], ![[17, 56], [1, 53], [57, 33], [19], [29], [1]]]
 h' := ![![[10, 70], [22, 21], [4, 35], [56, 40], [58, 44], [9, 10], [0, 1]], ![[0, 1], [19, 50], [70, 36], [30, 31], [1, 27], [38, 61], [10, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [22, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [62, 61, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2152, 5670, -6740]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4492, 6630, -6740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![9, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![9, 1, 0]] 
 ![![71, 0, 0], ![9, 1, 0], ![49, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![9, 1, 0], ![2, 10, 4], ![149, -27, 8]]]
  hmulB := by decide  
  f := ![![![-191, -960, -384], ![0, 6816, 0]], ![![-24, -120, -48], ![1, 852, 0]], ![![-136, -663, -265], ![33, 4704, 0]]]
  g := ![![![1, 0, 0], ![-9, 71, 0], ![-49, 0, 71]], ![![0, 1, 0], ![-4, 10, 4], ![0, -27, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![47, -2, 1]] ![![71, 0, 0], ![9, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![639, 71, 0]], ![![3337, -142, 71], ![568, 0, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![9, 1, 0]]], ![![![47, -2, 1]], ![![8, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![15, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![15, 1, 0]] 
 ![![73, 0, 0], ![15, 1, 0], ![50, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![15, 1, 0], ![2, 16, 4], ![149, -27, 14]]]
  hmulB := by decide  
  f := ![![![-3878, -33055, -8268], ![-1241, 150891, 0]], ![![-803, -6781, -1696], ![-218, 30952, 0]], ![![-2665, -22641, -5663], ![-807, 103350, 0]]]
  g := ![![![1, 0, 0], ![-15, 73, 0], ![-50, 0, 73]], ![![0, 1, 0], ![-6, 16, 4], ![-2, -27, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![29, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![29, 1, 0]] 
 ![![73, 0, 0], ![29, 1, 0], ![2, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![29, 1, 0], ![2, 30, 4], ![149, -27, 28]]]
  hmulB := by decide  
  f := ![![![4524, 85639, 11424], ![2993, -208488, 0]], ![![1775, 34003, 4536], ![1242, -82782, 0]], ![![116, 2346, 313], ![102, -5712, 0]]]
  g := ![![![1, 0, 0], ![-29, 73, 0], ![-2, 0, 73]], ![![0, 1, 0], ![-12, 30, 4], ![12, -27, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![15, 1, 0]] ![![73, 0, 0], ![29, 1, 0]]
  ![![73, 0, 0], ![18, -7, 1]] where
 M := ![![![5329, 0, 0], ![2117, 73, 0]], ![![1095, 73, 0], ![437, 45, 4]]]
 hmul := by decide  
 g := ![![![![55, 7, -1], ![73, 0, 0]], ![![11, 8, -1], ![73, 0, 0]]], ![![![-3, 8, -1], ![73, 0, 0]], ![![5, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![18, -7, 1]] ![![73, 0, 0], ![29, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2117, 73, 0]], ![![1314, -511, 73], ![657, -219, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![29, 1, 0]]], ![![![18, -7, 1]], ![![9, -3, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![15, 11, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![15, 11, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![15, 11, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![15, 11, 1], ![171, -1, 43], ![1551, -253, -23]]]
  hmulB := by decide  
  f := ![![![-14, -11, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -11, 79]], ![![0, 0, 1], ![-6, -6, 43], ![24, 0, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [11, 34, 1] where
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
 g := ![![[39, 36], [76, 62], [35, 26], [44, 16], [50], [1]], ![[0, 43], [22, 17], [20, 53], [53, 63], [50], [1]]]
 h' := ![![[45, 78], [33, 73], [10, 46], [69, 37], [45, 75], [68, 45], [0, 1]], ![[0, 1], [0, 6], [26, 33], [75, 42], [23, 4], [39, 34], [45, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [47, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [11, 34, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7579, -504, -1080]
  a := ![-2, -6, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![301, 144, -1080]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![36, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![36, 1, 0]] 
 ![![79, 0, 0], ![36, 1, 0], ![23, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![36, 1, 0], ![2, 37, 4], ![149, -27, 35]]]
  hmulB := by decide  
  f := ![![![917, 23596, 2552], ![790, -50402, 0]], ![![400, 10725, 1160], ![396, -22910, 0]], ![![241, 6869, 743], ![287, -14674, 0]]]
  g := ![![![1, 0, 0], ![-36, 79, 0], ![-23, 0, 79]], ![![0, 1, 0], ![-18, 37, 4], ![4, -27, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![15, 11, 1]] ![![79, 0, 0], ![36, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2844, 79, 0]], ![![1185, 869, 79], ![711, 395, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![36, 1, 0]]], ![![![15, 11, 1]], ![![9, 5, 1]]]]
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


lemma PB268I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB268I1 : PrimesBelowBoundCertificateInterval O 31 79 268 where
  m := 11
  g := ![1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB268I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N1]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N1, I43N1, I47N1, I59N1, I61N1, I67N1, I71N1, I73N0, I73N1, I79N1]
  Il := ![[], [I41N1], [I43N1], [I47N1], [], [I59N1], [I61N1], [I67N1], [I71N1], [I73N0, I73N1, I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
