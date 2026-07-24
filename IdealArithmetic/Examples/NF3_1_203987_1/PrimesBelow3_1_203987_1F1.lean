
import IdealArithmetic.Examples.NF3_1_203987_1.RI3_1_203987_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-16, 2, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-16, 2, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![21, 2, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-16, 2, 1], ![88, -11, 13], ![264, 41, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -2, 37]], ![![-1, 0, 1], ![-5, -1, 13], ![6, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [1, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 36], [0, 1]]
 g := ![![[3, 1], [36], [12, 34], [9], [1]], ![[0, 36], [36], [21, 3], [9], [1]]]
 h' := ![![[34, 36], [34, 36], [25, 31], [29, 16], [36, 34], [0, 1]], ![[0, 1], [0, 1], [6, 6], [18, 21], [8, 3], [34, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [29, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [1, 3, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1409, 1031, 645]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-328, -7, 645]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-13, 1, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![35, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-13, 1, 0], ![0, -15, 5], ![88, 9, -10]]]
  hmulB := by decide  
  f := ![![![287, -22, 0], ![814, 0, 0]], ![![196, -15, 0], ![556, 0, 0]], ![![275, -15, -2], ![780, 15, 0]]]
  g := ![![![1, 0, 0], ![-24, 37, 0], ![-35, 0, 37]], ![![-1, 1, 0], ![5, -15, 5], ![6, 9, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-16, 2, 1]] ![![37, 0, 0], ![-13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-481, 37, 0]], ![![-592, 74, 37], ![296, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-13, 1, 0]]], ![![![-16, 2, 1]], ![![8, -1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 32, 22]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![191, 32, 22]] 
 ![![41, 0, 0], ![0, 41, 0], ![18, 35, 1]] where
  M :=![![![191, 32, 22], ![1936, 325, 226], ![4752, 794, 551]]]
  hmulB := by decide  
  f := ![![![-9, -4, 2]], ![![176, 17, -14]], ![![142, 13, -11]]]
  g := ![![![-5, -18, 22], ![-52, -185, 226], ![-126, -451, 551]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [40, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 40], [0, 1]]
 g := ![![[8, 40], [36], [10], [36, 23], [1]], ![[0, 1], [36], [10], [15, 18], [1]]]
 h' := ![![[8, 40], [31, 32], [35, 35], [36, 25], [1, 8], [0, 1]], ![[0, 1], [0, 9], [28, 6], [31, 16], [24, 33], [8, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [17, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [40, 33, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![800, 1059, 1115]
  a := ![-1, -4, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-470, -926, 1115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -4, 2]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-9, -4, 2]] 
 ![![41, 0, 0], ![27, 1, 0], ![29, 0, 1]] where
  M :=![![![-9, -4, 2], ![176, 17, -14], ![-176, 10, 3]]]
  hmulB := by decide  
  f := ![![![191, 32, 22]], ![![173, 29, 20]], ![![251, 42, 29]]]
  g := ![![![1, -4, 2], ![3, 17, -14], ![-13, 10, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![191, 32, 22]] ![![-9, -4, 2]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139, -23, -16]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-139, -23, -16]] 
 ![![43, 0, 0], ![0, 43, 0], ![6, 31, 1]] where
  M :=![![![-139, -23, -16], ![-1408, -237, -163], ![-3432, -575, -400]]]
  hmulB := by decide  
  f := ![![![-25, 0, 1]], ![![88, -16, 3]], ![![62, -11, 2]]]
  g := ![![![-1, 11, -16], ![-10, 112, -163], ![-24, 275, -400]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [7, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 42], [0, 1]]
 g := ![![[15, 21], [6, 25], [17], [29, 17], [1]], ![[3, 22], [4, 18], [17], [7, 26], [1]]]
 h' := ![![[24, 42], [1, 35], [25, 38], [12, 24], [36, 24], [0, 1]], ![[0, 1], [24, 8], [34, 5], [29, 19], [10, 19], [24, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [33, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [7, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2887, -55, 259]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, -188, 259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 0, 1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-25, 0, 1]] 
 ![![43, 0, 0], ![14, 1, 0], ![18, 0, 1]] where
  M :=![![![-25, 0, 1], ![88, -16, 3], ![88, 23, -13]]]
  hmulB := by decide  
  f := ![![![-139, -23, -16]], ![![-78, -13, -9]], ![![-138, -23, -16]]]
  g := ![![![-1, 0, 1], ![6, -16, 3], ![0, 23, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-139, -23, -16]] ![![-25, 0, 1]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![7, 14, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![7, 14, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![7, 14, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![7, 14, 1], ![88, -12, 73], ![1320, 149, 61]]]
  hmulB := by decide  
  f := ![![![-6, -14, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -14, 47]], ![![0, 0, 1], ![-9, -22, 73], ![19, -15, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [22, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 46], [0, 1]]
 g := ![![[3, 25], [35, 18], [3, 2], [40, 32], [1]], ![[45, 22], [22, 29], [12, 45], [43, 15], [1]]]
 h' := ![![[28, 46], [29, 5], [28, 21], [13, 7], [25, 28], [0, 1]], ![[0, 1], [28, 42], [5, 26], [21, 40], [10, 19], [28, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [23, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [22, 19, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2154, 2287, 1241]
  a := ![1, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-139, -321, 1241]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![21, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![21, 1, 0]] 
 ![![47, 0, 0], ![21, 1, 0], ![33, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![21, 1, 0], ![0, 19, 5], ![88, 9, 24]]]
  hmulB := by decide  
  f := ![![![148, 7, 0], ![-329, 0, 0]], ![![42, 2, 0], ![-93, 0, 0]], ![![120, -2, -2], ![-267, 19, 0]]]
  g := ![![![1, 0, 0], ![-21, 47, 0], ![-33, 0, 47]], ![![0, 1, 0], ![-12, 19, 5], ![-19, 9, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![7, 14, 1]] ![![47, 0, 0], ![21, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![987, 47, 0]], ![![329, 658, 47], ![235, 282, 94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![21, 1, 0]]], ![![![7, 14, 1]], ![![5, 6, 2]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [43, 43, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 9, 15], [46, 43, 38], [0, 1]]
 g := ![![[16, 51, 49], [0, 29], [5, 50, 46], [35, 36], [1]], ![[10, 2, 32, 46], [40, 15], [43, 41, 48, 15], [11, 4], [10, 1, 29, 36]], ![[44, 25], [26, 7], [12, 3, 10, 6], [20, 11], [29, 45, 38, 17]]]
 h' := ![![[1, 9, 15], [9, 36, 7], [50, 7, 20], [26, 9, 24], [10, 10, 47], [0, 1]], ![[46, 43, 38], [30, 13, 46], [52, 30, 11], [29, 52, 1], [48, 31, 51], [1, 9, 15]], ![[0, 1], [5, 4], [13, 16, 22], [41, 45, 28], [0, 12, 8], [46, 43, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 6], []]
 b := ![[], [33, 40, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [43, 43, 6, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1005357, -174264, -74995]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18969, -3288, -1415]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [34, 9, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 42, 53], [9, 16, 6], [0, 1]]
 g := ![![[51, 41, 22], [22, 13, 57], [42, 15], [55, 45, 19], [1]], ![[52, 29, 21, 29], [22, 25, 47, 35], [57, 15], [56, 36, 43, 1], [29, 46, 8, 20]], ![[58, 50, 50, 23], [27, 50, 17, 50], [21, 1], [49, 13, 25, 58], [22, 9, 2, 39]]]
 h' := ![![[36, 42, 53], [19, 3, 9], [17, 42, 23], [18, 16, 30], [25, 50, 45], [0, 1]], ![[9, 16, 6], [46, 34, 8], [24, 8, 57], [29, 31, 30], [4, 47, 7], [36, 42, 53]], ![[0, 1], [18, 22, 42], [35, 9, 38], [49, 12, 58], [40, 21, 7], [9, 16, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 34], []]
 b := ![[], [3, 54, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [34, 9, 14, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![497751730, 87378115, 40243192]
  a := ![1, -21, 62]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8436470, 1480985, 682088]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [17, 18, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 51, 20], [42, 9, 41], [0, 1]]
 g := ![![[48, 28, 15], [47, 4], [53, 1, 49], [34, 14, 56], [1]], ![[52, 20, 4, 13], [24, 25], [40, 28, 25, 19], [31, 42, 18, 49], [21, 49, 5, 9]], ![[32, 29, 41, 36], [11, 9], [49, 51, 29, 49], [16, 45, 7, 36], [15, 54, 15, 52]]]
 h' := ![![[38, 51, 20], [7, 21, 36], [14, 53, 59], [32, 49, 54], [44, 43, 19], [0, 1]], ![[42, 9, 41], [20, 41, 12], [1, 22, 5], [15, 39, 2], [42, 60, 55], [38, 51, 20]], ![[0, 1], [15, 60, 13], [18, 47, 58], [47, 34, 5], [23, 19, 48], [42, 9, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 27], []]
 b := ![[], [18, 20, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [17, 18, 42, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![176656, 36356, 19154]
  a := ![-1, -1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2896, 596, 314]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-31, -15, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-31, -15, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![36, 52, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-31, -15, 1], ![88, 8, -72], ![-1232, -112, -64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -52, 67]], ![![-1, -1, 1], ![40, 56, -72], ![16, 48, -64]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [7, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 66], [0, 1]]
 g := ![![[57, 9], [28, 36], [60], [24], [9], [1]], ![[17, 58], [2, 31], [60], [24], [9], [1]]]
 h' := ![![[3, 66], [5, 3], [29, 61], [28, 23], [53, 52], [60, 3], [0, 1]], ![[0, 1], [14, 64], [11, 6], [30, 44], [8, 15], [2, 64], [3, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [21, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [7, 64, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3439, 2347, 2595]
  a := ![0, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1343, -1979, 2595]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![5, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![5, 1, 0]] 
 ![![67, 0, 0], ![5, 1, 0], ![64, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![5, 1, 0], ![0, 3, 5], ![88, 9, 8]]]
  hmulB := by decide  
  f := ![![![126, 25, 0], ![-1675, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![122, 23, -2], ![-1622, 27, 0]]]
  g := ![![![1, 0, 0], ![-5, 67, 0], ![-64, 0, 67]], ![![0, 1, 0], ![-5, 3, 5], ![-7, 9, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-31, -15, 1]] ![![67, 0, 0], ![5, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![335, 67, 0]], ![![-2077, -1005, 67], ![-67, -67, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![5, 1, 0]]], ![![![-31, -15, 1]], ![![-1, -1, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3539, 178, 69]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-3539, 178, 69]] 
 ![![71, 0, 0], ![0, 71, 0], ![30, 53, 1]] where
  M :=![![![-3539, 178, 69], ![6072, -3274, 1097], ![21736, 3189, -2177]]]
  hmulB := by decide  
  f := ![![![51115, 8557, 5932]], ![![522016, 87389, 60581]], ![![429230, 71856, 49813]]]
  g := ![![![-79, -49, 69], ![-378, -865, 1097], ![1226, 1670, -2177]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [38, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 70], [0, 1]]
 g := ![![[37, 43], [47, 27], [4, 19], [8], [54], [1]], ![[0, 28], [70, 44], [57, 52], [8], [54], [1]]]
 h' := ![![[14, 70], [60, 16], [61, 13], [18, 44], [31, 47], [33, 14], [0, 1]], ![[0, 1], [0, 55], [30, 58], [66, 27], [50, 24], [16, 57], [14, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [10, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [38, 57, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14236, 7334, 3040]
  a := ![2, 6, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1084, -2166, 3040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51115, 8557, 5932]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![51115, 8557, 5932]] 
 ![![71, 0, 0], ![16, 1, 0], ![12, 0, 1]] where
  M :=![![![51115, 8557, 5932], ![522016, 87389, 60581], ![1275032, 213449, 147970]]]
  hmulB := by decide  
  f := ![![![-3539, 178, 69]], ![![-712, -6, 31]], ![![-292, 75, -19]]]
  g := ![![![-2211, 8557, 5932], ![-22580, 87389, 60581], ![-55152, 213449, 147970]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-3539, 178, 69]] ![![51115, 8557, 5932]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [12, 58, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 57, 6], [28, 15, 67], [0, 1]]
 g := ![![[20, 10, 70], [55, 65], [21, 1], [50, 61, 8], [7, 1], []], ![[37, 41, 59, 64], [31, 32], [67, 37], [46, 36, 59, 36], [5, 6], [60, 36]], ![[44, 61, 36, 35], [53, 12], [17, 6], [64, 37, 43, 48], [20, 37], [72, 36]]]
 h' := ![![[52, 57, 6], [13, 27, 56], [4, 16, 24], [57, 66, 72], [62, 20, 64], [0, 0, 1], [0, 1]], ![[28, 15, 67], [28, 44, 53], [53, 21, 18], [45, 67, 16], [36, 5, 58], [13, 45, 15], [52, 57, 6]], ![[0, 1], [12, 2, 37], [65, 36, 31], [14, 13, 58], [28, 48, 24], [66, 28, 57], [28, 15, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 20], []]
 b := ![[], [18, 36, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [12, 58, 66, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27229, 5986, 9782]
  a := ![13, -1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![373, 82, 134]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-22, -33, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-22, -33, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![57, 46, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-22, -33, 1], ![88, 53, -162], ![-2816, -274, -109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -46, 79]], ![![-1, -1, 1], ![118, 95, -162], ![43, 60, -109]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [61, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 78], [0, 1]]
 g := ![![[37, 13], [78, 4], [3, 72], [33, 1], [50], [1]], ![[5, 66], [56, 75], [2, 7], [67, 78], [50], [1]]]
 h' := ![![[34, 78], [61, 31], [54, 77], [41, 54], [39, 1], [18, 34], [0, 1]], ![[0, 1], [9, 48], [65, 2], [60, 25], [73, 78], [68, 45], [34, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [21, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [61, 45, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7587, 5021, 2237]
  a := ![1, 6, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1518, -1239, 2237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![4, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![4, 1, 0]] 
 ![![79, 0, 0], ![4, 1, 0], ![30, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![4, 1, 0], ![0, 2, 5], ![88, 9, 7]]]
  hmulB := by decide  
  f := ![![![73, 18, 0], ![-1422, 0, 0]], ![![-4, -1, 0], ![80, 0, 0]], ![![26, 6, -1], ![-506, 16, 0]]]
  g := ![![![1, 0, 0], ![-4, 79, 0], ![-30, 0, 79]], ![![0, 1, 0], ![-2, 2, 5], ![-2, 9, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-22, -33, 1]] ![![79, 0, 0], ![4, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![316, 79, 0]], ![![-1738, -2607, 79], ![0, -79, -158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![4, 1, 0]]], ![![![-22, -33, 1]], ![![0, -1, -2]]]]
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


lemma PB128I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB128I1 : PrimesBelowBoundCertificateInterval O 31 79 128 where
  m := 11
  g := ![2, 2, 2, 2, 1, 1, 1, 2, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB128I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I43N1, I47N1, I67N1, I71N1, I79N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [], [], [], [I67N1], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
