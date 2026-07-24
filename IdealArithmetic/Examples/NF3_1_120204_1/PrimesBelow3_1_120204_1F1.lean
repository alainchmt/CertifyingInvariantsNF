
import IdealArithmetic.Examples.NF3_1_120204_1.RI3_1_120204_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [11, 4, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 12, 29], [14, 24, 8], [0, 1]]
 g := ![![[17, 11, 34], [9, 10], [18, 10, 27], [12, 1], []], ![[35, 14, 22, 15], [26, 25], [28, 27, 35, 24], [10, 21], [21, 27]], ![[5, 5, 21, 19], [27, 34], [25, 12, 27, 20], [36, 33], [5, 27]]]
 h' := ![![[35, 12, 29], [33, 2, 21], [24, 0, 26], [16, 15, 29], [0, 0, 1], [0, 1]], ![[14, 24, 8], [35, 6, 7], [5, 20, 32], [26, 23, 21], [32, 15, 24], [35, 12, 29]], ![[0, 1], [25, 29, 9], [27, 17, 16], [23, 36, 24], [30, 22, 12], [14, 24, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 32], []]
 b := ![[], [10, 33, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [11, 4, 25, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2849, 222, -259]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![77, 6, -7]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [34, 19, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 36, 35], [25, 4, 6], [0, 1]]
 g := ![![[26, 38, 36], [29, 23], [33, 31], [26, 2, 1], []], ![[34, 35], [33, 37], [38, 21], [4, 11, 11, 27], [9, 36]], ![[28, 36, 34, 11], [6, 18], [7, 23], [2, 12, 36, 27], [38, 36]]]
 h' := ![![[18, 36, 35], [31, 4, 6], [22, 22, 8], [18, 12, 21], [0, 0, 1], [0, 1]], ![[25, 4, 6], [6, 1], [29, 0, 23], [38, 34, 12], [18, 24, 4], [18, 36, 35]], ![[0, 1], [24, 36, 35], [33, 19, 10], [5, 36, 8], [30, 17, 36], [25, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 35], []]
 b := ![[], [16, 3, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [34, 19, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30545, 3280, -4920]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![745, 80, -120]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [14, 39, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 32, 24], [41, 10, 19], [0, 1]]
 g := ![![[25, 28, 1], [32, 27, 1], [23, 15], [25, 35, 1], []], ![[24, 31, 41, 16], [6, 9], [5, 25], [4, 9, 12, 35], [24, 17]], ![[14, 40, 5, 29], [31, 5, 9, 19], [3, 31], [36, 17, 9, 20], [29, 17]]]
 h' := ![![[37, 32, 24], [25, 18, 1], [15, 4, 42], [37, 40, 12], [0, 0, 1], [0, 1]], ![[41, 10, 19], [4, 7, 12], [33, 9], [24, 42, 5], [1, 33, 10], [37, 32, 24]], ![[0, 1], [17, 18, 30], [22, 30, 1], [35, 4, 26], [28, 10, 32], [41, 10, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 8], []]
 b := ![[], [12, 26, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [14, 39, 8, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-210012, 5203, -10535]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4884, 121, -245]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![1, 22, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![1, 22, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![1, 22, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![1, 22, 1], ![66, -5, 66], ![1452, -110, -5]]]
  hmulB := by decide  
  f := ![![![0, 9, -1], ![-19, 1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -22, 47]], ![![0, 0, 1], ![0, -31, 66], ![31, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [25, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 46], [0, 1]]
 g := ![![[13, 32], [12, 14], [15, 6], [5, 16], [1]], ![[0, 15], [21, 33], [39, 41], [22, 31], [1]]]
 h' := ![![[4, 46], [29, 28], [1, 25], [16, 10], [22, 4], [0, 1]], ![[0, 1], [0, 19], [7, 22], [9, 37], [38, 43], [4, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [38, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [25, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-327, 279, -186]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 93, -186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-19, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-19, 1, 0]] 
 ![![47, 0, 0], ![28, 1, 0], ![5, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-19, 1, 0], ![0, -19, 3], ![66, -6, -19]]]
  hmulB := by decide  
  f := ![![![172, -9, 0], ![423, 0, 0]], ![![96, -5, 0], ![236, 0, 0]], ![![28, 5, -1], ![69, 16, 0]]]
  g := ![![![1, 0, 0], ![-28, 47, 0], ![-5, 0, 47]], ![![-1, 1, 0], ![11, -19, 3], ![7, -6, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![1, 22, 1]] ![![47, 0, 0], ![-19, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-893, 47, 0]], ![![47, 1034, 47], ![47, -423, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-19, 1, 0]]], ![![![1, 22, 1]], ![![1, -9, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![10, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![10, 1, 0]] 
 ![![53, 0, 0], ![10, 1, 0], ![2, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![10, 1, 0], ![0, 10, 3], ![66, -6, 10]]]
  hmulB := by decide  
  f := ![![![141, 14, 0], ![-742, 0, 0]], ![![10, 1, 0], ![-52, 0, 0]], ![![-6, -4, -1], ![32, 18, 0]]]
  g := ![![![1, 0, 0], ![-10, 53, 0], ![-2, 0, 53]], ![![0, 1, 0], ![-2, 10, 3], ![2, -6, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-20, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-20, 1, 0]] 
 ![![53, 0, 0], ![33, 1, 0], ![8, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-20, 1, 0], ![0, -20, 3], ![66, -6, -20]]]
  hmulB := by decide  
  f := ![![![281, -14, 0], ![742, 0, 0]], ![![181, -9, 0], ![478, 0, 0]], ![![56, 4, -1], ![148, 18, 0]]]
  g := ![![![1, 0, 0], ![-33, 53, 0], ![-8, 0, 53]], ![![-1, 1, 0], ![12, -20, 3], ![8, -6, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![10, 1, 0]] ![![53, 0, 0], ![10, 1, 0]]
  ![![53, 0, 0], ![-2, -11, 1]] where
 M := ![![![2809, 0, 0], ![530, 53, 0]], ![![530, 53, 0], ![100, 20, 3]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![10, 1, 0], ![0, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-2, -11, 1]] ![![53, 0, 0], ![-20, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1060, 53, 0]], ![![-106, -583, 53], ![106, 212, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-20, 1, 0]]], ![![![-2, -11, 1]], ![![2, 4, -1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-25, 18, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-25, 18, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![34, 18, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-25, 18, 1], ![66, -31, 54], ![1188, -86, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -18, 59]], ![![-1, 0, 1], ![-30, -17, 54], ![38, 8, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [12, 24, 1] where
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
 g := ![![[2, 5], [43, 19], [5], [11, 27], [35, 1]], ![[0, 54], [0, 40], [5], [12, 32], [11, 58]]]
 h' := ![![[35, 58], [15, 8], [18, 45], [45, 51], [52, 33], [0, 1]], ![[0, 1], [0, 51], [0, 14], [1, 8], [27, 26], [35, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [8, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [12, 24, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![144, -14, -27]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 8, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![5, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![5, 1, 0]] 
 ![![59, 0, 0], ![5, 1, 0], ![31, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![5, 1, 0], ![0, 5, 3], ![66, -6, 5]]]
  hmulB := by decide  
  f := ![![![51, 10, 0], ![-590, 0, 0]], ![![-5, -1, 0], ![60, 0, 0]], ![![29, 4, -1], ![-336, 20, 0]]]
  g := ![![![1, 0, 0], ![-5, 59, 0], ![-31, 0, 59]], ![![0, 1, 0], ![-2, 5, 3], ![-1, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-25, 18, 1]] ![![59, 0, 0], ![5, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![295, 59, 0]], ![![-1475, 1062, 59], ![-59, 59, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![5, 1, 0]]], ![![![-25, 18, 1]], ![![-1, 1, 1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![8, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![8, 1, 0]] 
 ![![61, 0, 0], ![8, 1, 0], ![60, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![8, 1, 0], ![0, 8, 3], ![66, -6, 8]]]
  hmulB := by decide  
  f := ![![![153, 19, 0], ![-1159, 0, 0]], ![![8, 1, 0], ![-60, 0, 0]], ![![156, 14, -2], ![-1182, 41, 0]]]
  g := ![![![1, 0, 0], ![-8, 61, 0], ![-60, 0, 61]], ![![0, 1, 0], ![-4, 8, 3], ![-6, -6, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![15, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![15, 1, 0]] 
 ![![61, 0, 0], ![15, 1, 0], ![47, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![15, 1, 0], ![0, 15, 3], ![66, -6, 15]]]
  hmulB := by decide  
  f := ![![![466, 31, 0], ![-1891, 0, 0]], ![![90, 6, 0], ![-365, 0, 0]], ![![362, 14, -2], ![-1469, 41, 0]]]
  g := ![![![1, 0, 0], ![-15, 61, 0], ![-47, 0, 61]], ![![0, 1, 0], ![-6, 15, 3], ![-9, -6, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-23, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-23, 1, 0]] 
 ![![61, 0, 0], ![38, 1, 0], ![27, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-23, 1, 0], ![0, -23, 3], ![66, -6, -23]]]
  hmulB := by decide  
  f := ![![![323, -14, 0], ![854, 0, 0]], ![![208, -9, 0], ![550, 0, 0]], ![![149, 9, -2], ![394, 41, 0]]]
  g := ![![![1, 0, 0], ![-38, 61, 0], ![-27, 0, 61]], ![![-1, 1, 0], ![13, -23, 3], ![15, -6, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![8, 1, 0]] ![![61, 0, 0], ![15, 1, 0]]
  ![![61, 0, 0], ![-21, 28, 1]] where
 M := ![![![3721, 0, 0], ![915, 61, 0]], ![![488, 61, 0], ![120, 23, 3]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![15, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![3, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-21, 28, 1]] ![![61, 0, 0], ![-23, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1403, 61, 0]], ![![-1281, 1708, 61], ![549, -671, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-23, 1, 0]]], ![![![-21, 28, 1]], ![![9, -11, 1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-29, -10, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-29, -10, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![38, 57, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-29, -10, 1], ![66, -35, -30], ![-660, 82, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -57, 67]], ![![-1, -1, 1], ![18, 25, -30], ![10, 31, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [63, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 66], [0, 1]]
 g := ![![[65, 40], [13, 25], [10], [59], [64], [1]], ![[13, 27], [14, 42], [10], [59], [64], [1]]]
 h' := ![![[59, 66], [52, 43], [28, 5], [51, 12], [4, 27], [4, 59], [0, 1]], ![[0, 1], [43, 24], [55, 62], [22, 55], [56, 40], [1, 8], [59, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [20, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [63, 8, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2580, -16, 1087]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-578, -925, 1087]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![30, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![30, 1, 0]] 
 ![![67, 0, 0], ![30, 1, 0], ![35, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![30, 1, 0], ![0, 30, 3], ![66, -6, 30]]]
  hmulB := by decide  
  f := ![![![601, 20, 0], ![-1340, 0, 0]], ![![270, 9, 0], ![-602, 0, 0]], ![![305, -10, -2], ![-680, 45, 0]]]
  g := ![![![1, 0, 0], ![-30, 67, 0], ![-35, 0, 67]], ![![0, 1, 0], ![-15, 30, 3], ![-12, -6, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-29, -10, 1]] ![![67, 0, 0], ![30, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2010, 67, 0]], ![![-1943, -670, 67], ![-804, -335, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![30, 1, 0]]], ![![![-29, -10, 1]], ![![-12, -5, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-15, 8, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-15, 8, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![56, 8, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-15, 8, 1], ![66, -21, 24], ![528, -26, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -8, 71]], ![![-1, 0, 1], ![-18, -3, 24], ![24, 2, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [29, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 70], [0, 1]]
 g := ![![[20, 49], [2, 12], [55, 54], [24], [2], [1]], ![[0, 22], [0, 59], [46, 17], [24], [2], [1]]]
 h' := ![![[59, 70], [13, 7], [38, 15], [18, 57], [2, 33], [42, 59], [0, 1]], ![[0, 1], [0, 64], [0, 56], [44, 14], [32, 38], [44, 12], [59, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [30, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [29, 12, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-378, 88, 11]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, 0, 11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-24, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-24, 1, 0]] 
 ![![71, 0, 0], ![47, 1, 0], ![21, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-24, 1, 0], ![0, -24, 3], ![66, -6, -24]]]
  hmulB := by decide  
  f := ![![![121, -5, 0], ![355, 0, 0]], ![![97, -4, 0], ![285, 0, 0]], ![![75, 5, -1], ![221, 24, 0]]]
  g := ![![![1, 0, 0], ![-47, 71, 0], ![-21, 0, 71]], ![![-1, 1, 0], ![15, -24, 3], ![12, -6, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-15, 8, 1]] ![![71, 0, 0], ![-24, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1704, 71, 0]], ![![-1065, 568, 71], ![426, -213, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-24, 1, 0]]], ![![![-15, 8, 1]], ![![6, -3, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![22, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![22, 1, 0]] 
 ![![73, 0, 0], ![22, 1, 0], ![9, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![22, 1, 0], ![0, 22, 3], ![66, -6, 22]]]
  hmulB := by decide  
  f := ![![![177, 8, 0], ![-584, 0, 0]], ![![22, 1, 0], ![-72, 0, 0]], ![![17, -14, -2], ![-56, 49, 0]]]
  g := ![![![1, 0, 0], ![-22, 73, 0], ![-9, 0, 73]], ![![0, 1, 0], ![-7, 22, 3], ![0, -6, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![24, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![24, 1, 0]] 
 ![![73, 0, 0], ![24, 1, 0], ![27, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![24, 1, 0], ![0, 24, 3], ![66, -6, 24]]]
  hmulB := by decide  
  f := ![![![721, 30, 0], ![-2190, 0, 0]], ![![216, 9, 0], ![-656, 0, 0]], ![![243, -6, -2], ![-738, 49, 0]]]
  g := ![![![1, 0, 0], ![-24, 73, 0], ![-27, 0, 73]], ![![0, 1, 0], ![-9, 24, 3], ![-6, -6, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![27, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![27, 1, 0]] 
 ![![73, 0, 0], ![27, 1, 0], ![49, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![27, 1, 0], ![0, 27, 3], ![66, -6, 27]]]
  hmulB := by decide  
  f := ![![![703, 26, 0], ![-1898, 0, 0]], ![![243, 9, 0], ![-656, 0, 0]], ![![463, -1, -2], ![-1250, 49, 0]]]
  g := ![![![1, 0, 0], ![-27, 73, 0], ![-49, 0, 73]], ![![0, 1, 0], ![-12, 27, 3], ![-15, -6, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![22, 1, 0]] ![![73, 0, 0], ![24, 1, 0]]
  ![![73, 0, 0], ![30, -9, 1]] where
 M := ![![![5329, 0, 0], ![1752, 73, 0]], ![![1606, 73, 0], ![528, 46, 3]]]
 hmul := by decide  
 g := ![![![![43, 9, -1], ![73, 0, 0]], ![![-6, 10, -1], ![73, 0, 0]]], ![![![-8, 10, -1], ![73, 0, 0]], ![![6, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![30, -9, 1]] ![![73, 0, 0], ![27, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1971, 73, 0]], ![![2190, -657, 73], ![876, -219, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![27, 1, 0]]], ![![![30, -9, 1]], ![![12, -3, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-14, 21, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-14, 21, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![65, 21, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-14, 21, 1], ![66, -20, 63], ![1386, -104, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -21, 79]], ![![-1, 0, 1], ![-51, -17, 63], ![34, 4, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [57, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 78], [0, 1]]
 g := ![![[23, 9], [5, 16], [15, 19], [17, 13], [76], [1]], ![[74, 70], [43, 63], [70, 60], [38, 66], [76], [1]]]
 h' := ![![[32, 78], [31, 76], [14, 75], [58, 16], [23, 48], [22, 32], [0, 1]], ![[0, 1], [14, 3], [44, 4], [17, 63], [58, 31], [19, 47], [32, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [58, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [57, 47, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![321, 111, 73]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -18, 73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![16, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![16, 1, 0]] 
 ![![79, 0, 0], ![16, 1, 0], ![20, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![16, 1, 0], ![0, 16, 3], ![66, -6, 16]]]
  hmulB := by decide  
  f := ![![![49, 3, 0], ![-237, 0, 0]], ![![-16, -1, 0], ![80, 0, 0]], ![![12, -10, -2], ![-58, 53, 0]]]
  g := ![![![1, 0, 0], ![-16, 79, 0], ![-20, 0, 79]], ![![0, 1, 0], ![-4, 16, 3], ![-2, -6, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-14, 21, 1]] ![![79, 0, 0], ![16, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1264, 79, 0]], ![![-1106, 1659, 79], ![-158, 316, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![16, 1, 0]]], ![![![-14, 21, 1]], ![![-2, 4, 1]]]]
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


lemma PB99I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB99I1 : PrimesBelowBoundCertificateInterval O 31 79 99 where
  m := 11
  g := ![1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB99I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
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
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
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
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I47N1, I53N0, I53N1, I59N1, I61N0, I61N1, I61N2, I67N1, I71N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[], [], [], [I47N1], [I53N0, I53N0, I53N1], [I59N1], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
