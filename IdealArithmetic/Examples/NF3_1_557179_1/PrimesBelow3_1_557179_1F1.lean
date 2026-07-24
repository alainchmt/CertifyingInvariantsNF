
import IdealArithmetic.Examples.NF3_1_557179_1.RI3_1_557179_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [35, 28, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 25, 14], [36, 11, 23], [0, 1]]
 g := ![![[1, 32, 26], [13, 7], [12, 24, 26], [1, 1], []], ![[2, 3, 23, 22], [18, 25], [4, 6, 16, 17], [23, 10], [8, 11]], ![[8, 5, 27, 13], [18, 11], [6, 21, 24, 32], [27, 33], [36, 11]]]
 h' := ![![[2, 25, 14], [10, 4, 10], [24, 12, 28], [2, 11, 10], [0, 0, 1], [0, 1]], ![[36, 11, 23], [33, 5, 18], [16, 34, 32], [2, 32, 5], [20, 9, 11], [2, 25, 14]], ![[0, 1], [33, 28, 9], [21, 28, 14], [18, 31, 22], [36, 28, 25], [36, 11, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 18], []]
 b := ![[], [5, 6, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [35, 28, 36, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11324109, 20646, 175491]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-306057, 558, 4743]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-8, 2, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-8, 2, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![33, 2, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-8, 2, 1], ![-144, -5, 18], ![-272, -14, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -2, 41]], ![![-1, 0, 1], ![-18, -1, 18], ![-1, 0, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [29, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40], [0, 1]]
 g := ![![[34, 36], [20], [2], [26, 4], [1]], ![[3, 5], [20], [2], [18, 37], [1]]]
 h' := ![![[39, 40], [2, 6], [34, 26], [25, 17], [12, 39], [0, 1]], ![[0, 1], [31, 35], [23, 15], [32, 24], [16, 2], [39, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [11, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [29, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1204, -1913, 130]
  a := ![-1, 1, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-134, -53, 130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-18, 1, 0]] 
 ![![41, 0, 0], ![23, 1, 0], ![7, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-18, 1, 0], ![0, -17, 9], ![-144, 1, -18]]]
  hmulB := by decide  
  f := ![![![541, -30, 0], ![1230, 0, 0]], ![![307, -17, 0], ![698, 0, 0]], ![![95, 8, -7], ![216, 32, 0]]]
  g := ![![![1, 0, 0], ![-23, 41, 0], ![-7, 0, 41]], ![![-1, 1, 0], ![8, -17, 9], ![-1, 1, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-8, 2, 1]] ![![41, 0, 0], ![-18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-738, 41, 0]], ![![-328, 82, 41], ![0, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-18, 1, 0]]], ![![![-8, 2, 1]], ![![0, -1, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [33, 16, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 19, 4], [33, 23, 39], [0, 1]]
 g := ![![[16, 13, 11], [9, 24, 14], [0, 1], [38, 21, 1], []], ![[32, 13, 25, 1], [38, 3, 26, 21], [12, 17], [29, 21, 24, 9], [15, 16]], ![[17, 8], [3, 22, 6, 33], [34, 23], [40, 2, 8, 18], [23, 16]]]
 h' := ![![[31, 19, 4], [4, 3, 21], [6, 35, 33], [36, 32, 42], [0, 0, 1], [0, 1]], ![[33, 23, 39], [36, 24, 22], [0, 5, 39], [3, 26, 19], [36, 23, 23], [31, 19, 4]], ![[0, 1], [24, 16], [11, 3, 14], [31, 28, 25], [29, 20, 19], [33, 23, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 41], []]
 b := ![[], [24, 2, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [33, 16, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-178063, 2752, -9675]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4141, 64, -225]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [4, 22, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 34, 4], [38, 12, 43], [0, 1]]
 g := ![![[7, 28, 18], [30, 18, 17], [21, 19, 17], [31, 10, 1], []], ![[40, 18, 37, 8], [2, 38, 39, 14], [31, 43, 20, 1], [27, 41, 26, 12], [9, 16]], ![[35, 36, 14, 13], [3, 3, 35, 13], [14, 37, 36, 10], [38, 29, 8, 29], [17, 16]]]
 h' := ![![[19, 34, 4], [21, 26, 26], [10, 33, 39], [17, 30, 39], [0, 0, 1], [0, 1]], ![[38, 12, 43], [35, 28, 40], [11, 26, 36], [8, 18, 24], [43, 43, 12], [19, 34, 4]], ![[0, 1], [31, 40, 28], [32, 35, 19], [19, 46, 31], [13, 4, 34], [38, 12, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 11], []]
 b := ![[], [38, 13, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [4, 22, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15797264, 21808, 207176]
  a := ![1, -2, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-336112, 464, 4408]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [5, 16, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 40, 30], [52, 12, 23], [0, 1]]
 g := ![![[7, 43, 46], [33, 10], [50, 6, 10], [23, 24], [1]], ![[31, 22, 34, 8], [31, 4], [22, 31, 20, 33], [46, 15], [47, 50, 6, 23]], ![[18, 18, 46, 51], [28, 13], [13, 12, 37, 41], [4, 36], [5, 27, 50, 30]]]
 h' := ![![[18, 40, 30], [7, 10, 24], [15, 9, 13], [16, 43, 40], [48, 37, 17], [0, 1]], ![[52, 12, 23], [41, 20, 5], [14, 4, 2], [52, 9, 21], [32, 36, 42], [18, 40, 30]], ![[0, 1], [4, 23, 24], [12, 40, 38], [20, 1, 45], [27, 33, 47], [52, 12, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 21], []]
 b := ![[], [52, 33, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [5, 16, 36, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11324139, 20670, 175695]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-213663, 390, 3315]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [56, 4, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 50, 52], [8, 8, 7], [0, 1]]
 g := ![![[14, 28, 3], [56, 18, 48], [18, 15], [5, 51, 22], [1]], ![[51, 15, 24, 33], [43, 51, 39, 18], [24, 25], [13, 24, 51, 18], [50, 58, 53, 11]], ![[57, 55, 0, 48], [55, 10, 20, 46], [13, 35], [57, 50, 22, 16], [32, 57, 36, 48]]]
 h' := ![![[42, 50, 52], [50, 27, 48], [43, 44, 44], [15, 24, 29], [3, 55, 50], [0, 1]], ![[8, 8, 7], [22, 30, 18], [49, 46, 44], [53, 19, 5], [16, 18, 15], [42, 50, 52]], ![[0, 1], [35, 2, 52], [21, 28, 30], [49, 16, 25], [18, 45, 53], [8, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 19], []]
 b := ![[], [12, 14, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [56, 4, 9, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9441535062, -164431584, -150842586]
  a := ![1, 20, 161]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![160026018, -2786976, -2556654]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![6, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![6, 1, 0]] 
 ![![61, 0, 0], ![6, 1, 0], ![36, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![6, 1, 0], ![0, 7, 9], ![-144, 1, 6]]]
  hmulB := by decide  
  f := ![![![259, 43, 0], ![-2623, 0, 0]], ![![18, 3, 0], ![-182, 0, 0]], ![![156, 22, -5], ![-1580, 34, 0]]]
  g := ![![![1, 0, 0], ![-6, 61, 0], ![-36, 0, 61]], ![![0, 1, 0], ![-6, 7, 9], ![-6, 1, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![22, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![22, 1, 0]] 
 ![![61, 0, 0], ![22, 1, 0], ![59, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![22, 1, 0], ![0, 23, 9], ![-144, 1, 22]]]
  hmulB := by decide  
  f := ![![![463, 21, 0], ![-1281, 0, 0]], ![![154, 7, 0], ![-426, 0, 0]], ![![481, 9, -5], ![-1331, 34, 0]]]
  g := ![![![1, 0, 0], ![-22, 61, 0], ![-59, 0, 61]], ![![0, 1, 0], ![-17, 23, 9], ![-24, 1, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-29, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-29, 1, 0]] 
 ![![61, 0, 0], ![32, 1, 0], ![25, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-29, 1, 0], ![0, -28, 9], ![-144, 1, -29]]]
  hmulB := by decide  
  f := ![![![1393, -48, 0], ![2928, 0, 0]], ![![726, -25, 0], ![1526, 0, 0]], ![![569, -4, -5], ![1196, 34, 0]]]
  g := ![![![1, 0, 0], ![-32, 61, 0], ![-25, 0, 61]], ![![-1, 1, 0], ![11, -28, 9], ![9, 1, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![6, 1, 0]] ![![61, 0, 0], ![22, 1, 0]]
  ![![61, 0, 0], ![-26, 10, 1]] where
 M := ![![![3721, 0, 0], ![1342, 61, 0]], ![![366, 61, 0], ![132, 29, 9]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![22, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![6, -1, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-26, 10, 1]] ![![61, 0, 0], ![-29, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1769, 61, 0]], ![![-1586, 610, 61], ![610, -305, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-29, 1, 0]]], ![![![-26, 10, 1]], ![![10, -5, 1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [61, 4, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 41, 14], [15, 25, 53], [0, 1]]
 g := ![![[47, 59, 19], [34, 29, 17], [5, 1], [0, 17], [29, 1], []], ![[66, 51, 10, 64], [11, 25, 28, 47], [49, 14], [65, 15], [55, 22], [65, 62]], ![[61, 60, 18, 57], [24, 15, 35, 34], [11, 64], [62, 10], [34, 6], [26, 62]]]
 h' := ![![[14, 41, 14], [3, 30, 32], [27, 62, 33], [59, 12, 66], [40, 24, 33], [0, 0, 1], [0, 1]], ![[15, 25, 53], [13, 10, 14], [66, 36, 18], [43, 36, 9], [16, 19, 22], [50, 54, 25], [14, 41, 14]], ![[0, 1], [49, 27, 21], [63, 36, 16], [59, 19, 59], [42, 24, 12], [46, 13, 41], [15, 25, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 14], []]
 b := ![[], [3, 21, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [61, 4, 38, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7448926, -256208, -127233]
  a := ![-1, 2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![111178, -3824, -1899]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [54, 52, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 16, 43], [0, 54, 28], [0, 1]]
 g := ![![[45, 40, 43], [45, 27, 36], [47, 32, 57], [36, 10], [55, 1], []], ![[31, 13, 66, 50], [18, 26, 34, 16], [39, 39, 52, 24], [30, 8], [50, 5], [50, 3]], ![[0, 58, 12, 66], [20, 57, 65, 56], [12, 48, 63, 69], [12, 12], [65, 43], [65, 3]]]
 h' := ![![[55, 16, 43], [55, 5, 16], [18, 3, 65], [46, 1, 46], [12, 68, 62], [0, 0, 1], [0, 1]], ![[0, 54, 28], [63, 23, 14], [8, 25, 18], [70, 3, 42], [46, 24, 24], [41, 63, 54], [55, 16, 43]], ![[0, 1], [56, 43, 41], [62, 43, 59], [40, 67, 54], [7, 50, 56], [40, 8, 16], [0, 54, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 34], []]
 b := ![[], [51, 39, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [54, 52, 16, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39678918, -826724, -557279]
  a := ![0, 3, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![558858, -11644, -7849]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![13, 10, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![13, 10, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![13, 10, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![13, 10, 1], ![-144, 24, 90], ![-1424, -6, 14]]]
  hmulB := by decide  
  f := ![![![-12, -10, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -10, 73]], ![![0, 0, 1], ![-18, -12, 90], ![-22, -2, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [15, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 72], [0, 1]]
 g := ![![[], [], [55], [], [], [1]], ![[], [], [55], [], [], [1]]]
 h' := ![![[0, 72], [46], [51], [0, 36], [6], [58], [0, 1]], ![[0, 1], [46], [51], [0, 37], [6], [58], [0, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [0, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [15, 0, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81325, -60480, 4172]
  a := ![2, -8, -62]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1857, -1400, 4172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-17, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-17, 1, 0]] 
 ![![73, 0, 0], ![56, 1, 0], ![59, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-17, 1, 0], ![0, -16, 9], ![-144, 1, -17]]]
  hmulB := by decide  
  f := ![![![834, -49, 0], ![3577, 0, 0]], ![![664, -39, 0], ![2848, 0, 0]], ![![668, -25, -8], ![2865, 65, 0]]]
  g := ![![![1, 0, 0], ![-56, 73, 0], ![-59, 0, 73]], ![![-1, 1, 0], ![5, -16, 9], ![11, 1, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![13, 10, 1]] ![![73, 0, 0], ![-17, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1241, 73, 0]], ![![949, 730, 73], ![-365, -146, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-17, 1, 0]]], ![![![13, 10, 1]], ![![-5, -2, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![22, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![22, 1, 0]] 
 ![![79, 0, 0], ![22, 1, 0], ![14, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![22, 1, 0], ![0, 23, 9], ![-144, 1, 22]]]
  hmulB := by decide  
  f := ![![![221, 10, 0], ![-790, 0, 0]], ![![66, 3, 0], ![-236, 0, 0]], ![![18, -12, -5], ![-64, 44, 0]]]
  g := ![![![1, 0, 0], ![-22, 79, 0], ![-14, 0, 79]], ![![0, 1, 0], ![-8, 23, 9], ![-6, 1, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-17, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-17, 1, 0]] 
 ![![79, 0, 0], ![62, 1, 0], ![40, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-17, 1, 0], ![0, -16, 9], ![-144, 1, -17]]]
  hmulB := by decide  
  f := ![![![273, -16, 0], ![1264, 0, 0]], ![![222, -13, 0], ![1028, 0, 0]], ![![152, 0, -5], ![704, 44, 0]]]
  g := ![![![1, 0, 0], ![-62, 79, 0], ![-40, 0, 79]], ![![-1, 1, 0], ![8, -16, 9], ![6, 1, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-6, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-6, 1, 0]] 
 ![![79, 0, 0], ![73, 1, 0], ![23, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-6, 1, 0], ![0, -5, 9], ![-144, 1, -6]]]
  hmulB := by decide  
  f := ![![![409, -68, 0], ![5372, 0, 0]], ![![379, -63, 0], ![4978, 0, 0]], ![![125, -18, -5], ![1642, 44, 0]]]
  g := ![![![1, 0, 0], ![-73, 79, 0], ![-23, 0, 79]], ![![-1, 1, 0], ![2, -5, 9], ![-1, 1, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![22, 1, 0]] ![![79, 0, 0], ![-17, 1, 0]]
  ![![79, 0, 0], ![-24, 27, 1]] where
 M := ![![![6241, 0, 0], ![-1343, 79, 0]], ![![1738, 79, 0], ![-374, 6, 9]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![7, -26, -1], ![79, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![-2, -3, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-24, 27, 1]] ![![79, 0, 0], ![-6, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-474, 79, 0]], ![![-1896, 2133, 79], ![0, -158, 237]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-6, 1, 0]]], ![![![-24, 27, 1]], ![![0, -2, 3]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB212I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB212I1 : PrimesBelowBoundCertificateInterval O 31 79 212 where
  m := 11
  g := ![1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB212I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![79507]
    · exact ![103823]
    · exact ![148877]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I61N0, I61N1, I61N2, I73N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [], [], [], [], [I61N0, I61N1, I61N2], [], [], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
