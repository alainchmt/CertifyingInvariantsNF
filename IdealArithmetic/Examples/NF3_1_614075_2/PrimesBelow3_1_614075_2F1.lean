
import IdealArithmetic.Examples.NF3_1_614075_2.RI3_1_614075_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 16, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 16, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![13, 16, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 16, 1], ![-112, -24, 17], ![-1904, -741, -7]]]
  hmulB := by decide  
  f := ![![![-12, -16, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -16, 37]], ![![0, 0, 1], ![-9, -8, 17], ![-49, -17, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [11, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 36], [0, 1]]
 g := ![![[6, 27], [7], [15, 9], [27], [1]], ![[0, 10], [7], [13, 28], [27], [1]]]
 h' := ![![[8, 36], [27, 29], [20, 28], [9, 3], [26, 8], [0, 1]], ![[0, 1], [0, 8], [22, 9], [33, 34], [16, 29], [8, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [30, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [11, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-325, -252, -62]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 20, -62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-17, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-17, 1, 0]] 
 ![![37, 0, 0], ![20, 1, 0], ![7, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-17, 1, 0], ![0, -17, 1], ![-112, -37, -16]]]
  hmulB := by decide  
  f := ![![![545, -32, 0], ![1184, 0, 0]], ![![290, -17, 0], ![630, 0, 0]], ![![127, -7, 0], ![276, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 37, 0], ![-7, 0, 37]], ![![-1, 1, 0], ![9, -17, 1], ![20, -37, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![13, 16, 1]] ![![37, 0, 0], ![-17, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-629, 37, 0]], ![![481, 592, 37], ![-333, -296, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-17, 1, 0]]], ![![![13, 16, 1]], ![![-9, -8, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [2, 23, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 11, 14], [21, 29, 27], [0, 1]]
 g := ![![[20, 32, 40], [31, 10], [37, 1], [10, 22, 1], []], ![[11, 4, 6, 17], [29, 31], [4, 39], [33, 7, 10, 7], [28, 32]], ![[8, 21, 3, 24], [1, 25], [16, 21], [28, 26, 10, 28], [15, 32]]]
 h' := ![![[1, 11, 14], [24, 3, 9], [39, 21, 16], [21, 13, 40], [0, 0, 1], [0, 1]], ![[21, 29, 27], [24, 9, 16], [0, 38, 20], [7, 9, 30], [27, 11, 29], [1, 11, 14]], ![[0, 1], [14, 29, 16], [4, 23, 5], [6, 19, 12], [1, 30, 11], [21, 29, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 29], []]
 b := ![[], [38, 8, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [2, 23, 19, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![343949, 208403, 31283]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8389, 5083, 763]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![42, -18, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![42, -18, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![42, 25, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![42, -18, 1], ![-112, 5, -17], ![1904, 517, -12]]]
  hmulB := by decide  
  f := ![![![-41, 18, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -25, 43]], ![![0, -1, 1], ![14, 10, -17], ![56, 19, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 42], [0, 1]]
 g := ![![[23, 11], [33, 40], [13], [4, 36], [1]], ![[0, 32], [8, 3], [13], [3, 7], [1]]]
 h' := ![![[37, 42], [40, 21], [32, 13], [27, 20], [39, 37], [0, 1]], ![[0, 1], [0, 22], [40, 30], [36, 23], [32, 6], [37, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [4, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3828, -197, 85]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, -54, 85]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![17, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![17, 1, 0]] 
 ![![43, 0, 0], ![17, 1, 0], ![12, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![17, 1, 0], ![0, 17, 1], ![-112, -37, 18]]]
  hmulB := by decide  
  f := ![![![239, 14, 0], ![-602, 0, 0]], ![![85, 5, 0], ![-214, 0, 0]], ![![58, 3, 0], ![-146, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 43, 0], ![-12, 0, 43]], ![![0, 1, 0], ![-7, 17, 1], ![7, -37, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![42, -18, 1]] ![![43, 0, 0], ![17, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![731, 43, 0]], ![![1806, -774, 43], ![602, -301, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![17, 1, 0]]], ![![![42, -18, 1]], ![![14, -7, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [8, 21, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 30, 4], [8, 16, 43], [0, 1]]
 g := ![![[26, 9, 8], [4, 2, 25], [9, 36, 6], [29, 35, 1], []], ![[41, 44, 43, 17], [30, 10, 21, 3], [41, 26, 36, 36], [30, 34, 4, 37], [1, 16]], ![[9, 23, 24, 20], [33, 27, 39, 43], [30, 23, 34, 29], [32, 31, 1, 19], [9, 16]]]
 h' := ![![[27, 30, 4], [15, 8, 33], [22, 2, 5], [3, 4, 37], [0, 0, 1], [0, 1]], ![[8, 16, 43], [7, 44, 43], [15, 36, 41], [45, 27, 44], [16, 14, 16], [27, 30, 4]], ![[0, 1], [3, 42, 18], [45, 9, 1], [21, 16, 13], [39, 33, 30], [8, 16, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 11], []]
 b := ![[], [22, 4, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [8, 21, 12, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-454678, -276172, -37694]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9674, -5876, -802]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [14, 42, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 23, 46], [42, 29, 7], [0, 1]]
 g := ![![[13, 9, 28], [47, 44], [15, 24, 25], [16, 43], [1]], ![[10, 38, 0, 29], [15, 15], [25, 30, 51, 1], [35, 9], [5, 10, 44, 28]], ![[19, 41, 21, 9], [16, 25], [39, 40, 16, 40], [23, 44], [20, 23, 21, 25]]]
 h' := ![![[30, 23, 46], [35, 21, 9], [2, 30, 16], [25, 8, 48], [39, 11, 19], [0, 1]], ![[42, 29, 7], [30, 28, 8], [44, 46, 42], [23, 1, 11], [6, 5, 50], [30, 23, 46]], ![[0, 1], [17, 4, 36], [33, 30, 48], [13, 44, 47], [32, 37, 37], [42, 29, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 2], []]
 b := ![[], [51, 28, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [14, 42, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43778, -21677, -1537]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-826, -409, -29]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![26, -28, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![26, -28, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![26, 31, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![26, -28, 1], ![-112, -11, -27], ![3024, 887, -38]]]
  hmulB := by decide  
  f := ![![![-25, 28, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -31, 59]], ![![0, -1, 1], ![10, 14, -27], ![68, 35, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [25, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 58], [0, 1]]
 g := ![![[6, 26], [46, 9], [27], [50, 16], [27, 1]], ![[0, 33], [53, 50], [27], [10, 43], [54, 58]]]
 h' := ![![[27, 58], [30, 12], [36, 3], [48, 33], [33, 55], [0, 1]], ![[0, 1], [0, 47], [58, 56], [54, 26], [43, 4], [27, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [37, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [25, 32, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4310, -909, 397]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-248, -224, 397]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![27, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![27, 1, 0]] 
 ![![59, 0, 0], ![27, 1, 0], ![38, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![27, 1, 0], ![0, 27, 1], ![-112, -37, 28]]]
  hmulB := by decide  
  f := ![![![514, 19, 0], ![-1121, 0, 0]], ![![216, 8, 0], ![-471, 0, 0]], ![![310, 11, 0], ![-676, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 59, 0], ![-38, 0, 59]], ![![0, 1, 0], ![-13, 27, 1], ![-3, -37, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![26, -28, 1]] ![![59, 0, 0], ![27, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1593, 59, 0]], ![![1534, -1652, 59], ![590, -767, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![27, 1, 0]]], ![![![26, -28, 1]], ![![10, -13, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![18, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![18, 1, 0]] 
 ![![61, 0, 0], ![18, 1, 0], ![42, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![18, 1, 0], ![0, 18, 1], ![-112, -37, 19]]]
  hmulB := by decide  
  f := ![![![235, 13, 0], ![-793, 0, 0]], ![![54, 3, 0], ![-182, 0, 0]], ![![150, 8, 0], ![-506, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 61, 0], ![-42, 0, 61]], ![![0, 1, 0], ![-6, 18, 1], ![-4, -37, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4051, -308, 89]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![4051, -308, 89]] 
 ![![61, 0, 0], ![20, 1, 0], ![27, 0, 1]] where
  M :=![![![4051, -308, 89], ![-9968, 758, -219], ![24528, -1865, 539]]]
  hmulB := by decide  
  f := ![![![127, 27, -10]], ![![60, 17, -3]], ![![25, 20, 4]]]
  g := ![![![128, -308, 89], ![-315, 758, -219], ![775, -1865, 539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![22, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![22, 1, 0]] 
 ![![61, 0, 0], ![22, 1, 0], ![4, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![22, 1, 0], ![0, 22, 1], ![-112, -37, 23]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-1037, 0, 0]], ![![110, 5, 0], ![-304, 0, 0]], ![![8, 0, 0], ![-22, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 61, 0], ![-4, 0, 61]], ![![0, 1, 0], ![-8, 22, 1], ![10, -37, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![18, 1, 0]] ![![4051, -308, 89]]
  ![![61, 0, 0], ![55, -23, 1]] where
 M := ![![![247111, -18788, 5429]], ![![62950, -4786, 1383]]]
 hmul := by decide  
 g := ![![![![2291, 428, 57], ![1952, 0, 0]]], ![![![555, 121, 14], ![529, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![55, -23, 1]] ![![61, 0, 0], ![22, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1342, 61, 0]], ![![3355, -1403, 61], ![1098, -488, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![22, 1, 0]]], ![![![55, -23, 1]], ![![18, -8, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [53, 55, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 41, 8], [45, 25, 59], [0, 1]]
 g := ![![[2, 50, 35], [63, 40, 9], [45, 26], [37, 26], [6, 1], []], ![[43, 48, 61, 46], [10, 47, 23, 2], [6, 19], [52, 10], [33, 22], [35, 64]], ![[6, 61, 9, 1], [55, 23, 0, 36], [12, 55], [55, 49], [59, 6], [51, 64]]]
 h' := ![![[28, 41, 8], [11, 66, 13], [36, 47, 64], [3, 47, 48], [17, 19, 48], [0, 0, 1], [0, 1]], ![[45, 25, 59], [63, 15, 49], [9, 2, 33], [27, 31, 35], [61, 22, 12], [1, 61, 25], [28, 41, 8]], ![[0, 1], [63, 53, 5], [31, 18, 37], [59, 56, 51], [19, 26, 7], [59, 6, 41], [45, 25, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 16], []]
 b := ![[], [64, 9, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [53, 55, 61, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48106, 7169, -3551]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![718, 107, -53]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![34, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![34, 1, 0]] 
 ![![71, 0, 0], ![34, 1, 0], ![51, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![34, 1, 0], ![0, 34, 1], ![-112, -37, 35]]]
  hmulB := by decide  
  f := ![![![579, 17, 0], ![-1207, 0, 0]], ![![238, 7, 0], ![-496, 0, 0]], ![![391, 11, 0], ![-815, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 71, 0], ![-51, 0, 71]], ![![0, 1, 0], ![-17, 34, 1], ![-9, -37, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-19, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-19, 1, 0]] 
 ![![71, 0, 0], ![52, 1, 0], ![65, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-19, 1, 0], ![0, -19, 1], ![-112, -37, -18]]]
  hmulB := by decide  
  f := ![![![400, -21, 0], ![1491, 0, 0]], ![![324, -17, 0], ![1208, 0, 0]], ![![386, -20, 0], ![1439, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 71, 0], ![-65, 0, 71]], ![![-1, 1, 0], ![13, -19, 1], ![42, -37, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -2, 1]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-11, -2, 1]] 
 ![![71, 0, 0], ![55, 1, 0], ![28, 0, 1]] where
  M :=![![![-11, -2, 1], ![-112, -48, -1], ![112, -75, -49]]]
  hmulB := by decide  
  f := ![![![-2277, 173, -50]], ![![-1685, 128, -37]], ![![-1092, 83, -24]]]
  g := ![![![1, -2, 1], ![36, -48, -1], ![79, -75, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![34, 1, 0]] ![![71, 0, 0], ![-19, 1, 0]]
  ![![-2277, 173, -50]] where
 M := ![![![5041, 0, 0], ![-1349, 71, 0]], ![![2414, 71, 0], ![-646, 15, 1]]]
 hmul := by decide  
 g := ![![![![-781, -142, 71]], ![![97, -10, -20]]], ![![![-486, -116, 33]], ![![78, 7, -10]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-2277, 173, -50]] ![![-11, -2, 1]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![73, 0, 0], ![1, 1, 0], ![72, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![-112, -37, 2]]]
  hmulB := by decide  
  f := ![![![-39, 2, -1]], ![![1, 0, 0]], ![![-40, 3, -1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![-3, -37, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![19, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![19, 1, 0]] 
 ![![73, 0, 0], ![19, 1, 0], ![4, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![19, 1, 0], ![0, 19, 1], ![-112, -37, 20]]]
  hmulB := by decide  
  f := ![![![609, 32, 0], ![-2336, 0, 0]], ![![133, 7, 0], ![-510, 0, 0]], ![![24, 1, 0], ![-92, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 73, 0], ![-4, 0, 73]], ![![0, 1, 0], ![-5, 19, 1], ![7, -37, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-21, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-21, 1, 0]] 
 ![![73, 0, 0], ![52, 1, 0], ![70, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-21, 1, 0], ![0, -21, 1], ![-112, -37, -20]]]
  hmulB := by decide  
  f := ![![![232, -11, 0], ![803, 0, 0]], ![![190, -9, 0], ![658, 0, 0]], ![![238, -11, 0], ![824, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 73, 0], ![-70, 0, 73]], ![![-1, 1, 0], ![14, -21, 1], ![44, -37, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![73, 0, 0], ![19, 1, 0]]
  ![![73, 0, 0], ![19, 20, 1]] where
 M := ![![![73, 73, 0], ![19, 20, 1]]]
 hmul := by decide  
 g := ![![![![-18, -19, -1], ![73, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![19, 20, 1]] ![![73, 0, 0], ![-21, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1533, 73, 0]], ![![1387, 1460, 73], ![-511, -438, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-21, 1, 0]]], ![![![19, 20, 1]], ![![-7, -6, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-676181, 51412, -14856]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-676181, 51412, -14856]] 
 ![![79, 0, 0], ![0, 79, 0], ![5, 24, 1]] where
  M :=![![![-676181, 51412, -14856], ![1663872, -126509, 36556], ![-4094272, 311300, -89953]]]
  hmulB := by decide  
  f := ![![![237, 116, 8]], ![![-896, -59, 124]], ![![-433, -80, 39]]]
  g := ![![![-7619, 5164, -14856], ![18748, -12707, 36556], ![-46133, 31268, -89953]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [23, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 78], [0, 1]]
 g := ![![[48, 55], [2, 18], [59, 72], [25, 25], [4], [1]], ![[0, 24], [38, 61], [45, 7], [75, 54], [4], [1]]]
 h' := ![![[2, 78], [33, 23], [65, 52], [57, 54], [42, 74], [56, 2], [0, 1]], ![[0, 1], [0, 56], [11, 27], [7, 25], [32, 5], [60, 77], [2, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [70, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [23, 77, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-873, -667, 15]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -13, 15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![237, 116, 8]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![237, 116, 8]] 
 ![![79, 0, 0], ![54, 1, 0], ![7, 0, 1]] where
  M :=![![![237, 116, 8], ![-896, -59, 124], ![-13888, -5484, 65]]]
  hmulB := by decide  
  f := ![![![-676181, 51412, -14856]], ![![-441138, 33541, -9692]], ![![-111741, 8496, -2455]]]
  g := ![![![-77, 116, 8], ![18, -59, 124], ![3567, -5484, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-676181, 51412, -14856]] ![![237, 116, 8]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB222I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB222I1 : PrimesBelowBoundCertificateInterval O 31 79 222 where
  m := 11
  g := ![2, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB222I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
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
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
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
      exact NI61N1
      exact NI61N2
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
  β := ![I37N1, I43N1, I59N1, I61N0, I61N1, I61N2, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N1], [], [I43N1], [], [], [I59N1], [I61N0, I61N1, I61N2], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
