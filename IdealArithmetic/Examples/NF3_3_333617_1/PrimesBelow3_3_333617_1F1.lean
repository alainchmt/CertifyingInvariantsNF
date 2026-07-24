
import IdealArithmetic.Examples.NF3_3_333617_1.RI3_3_333617_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [14, 36, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 10, 6], [21, 26, 31], [0, 1]]
 g := ![![[32, 5, 25], [18, 26], [2, 21, 36], [17, 1], []], ![[19, 23, 24, 23], [11, 12], [35, 33, 0, 8], [22, 10], [29, 36]], ![[18, 34, 1, 6], [33, 30], [20, 5, 12, 15], [35, 26], [4, 36]]]
 h' := ![![[33, 10, 6], [14, 5, 32], [9, 1, 10], [21, 3, 31], [0, 0, 1], [0, 1]], ![[21, 26, 31], [20, 13, 11], [27, 10, 7], [18, 30, 10], [17, 0, 26], [33, 10, 6]], ![[0, 1], [7, 19, 31], [32, 26, 20], [31, 4, 33], [15, 0, 10], [21, 26, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 3], []]
 b := ![[], [31, 6, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [14, 36, 20, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8621, -9065, -1591]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-233, -245, -43]
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


def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-17, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-17, 1, 0]] 
 ![![41, 0, 0], ![24, 1, 0], ![39, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-17, 1, 0], ![0, -17, 1], ![55, 47, -17]]]
  hmulB := by decide  
  f := ![![![596, -35, 0], ![1435, 0, 0]], ![![358, -21, 0], ![862, 0, 0]], ![![586, -34, 0], ![1411, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 41, 0], ![-39, 0, 41]], ![![-1, 1, 0], ![9, -17, 1], ![-10, 47, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-7, 1, 0]] 
 ![![41, 0, 0], ![34, 1, 0], ![33, 0, 1]] where
  M :=![![![-7, 1, 0], ![0, -7, 1], ![55, 47, -7]]]
  hmulB := by decide  
  f := ![![![2, 7, 1]], ![![3, 7, 1]], ![![11, 15, 2]]]
  g := ![![![-1, 1, 0], ![5, -7, 1], ![-32, 47, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-17, 1, 0]] ![![41, 0, 0], ![-17, 1, 0]]
  ![![-2, -7, -1]] where
 M := ![![![1681, 0, 0], ![-697, 41, 0]], ![![-697, 41, 0], ![289, -34, 1]]]
 hmul := by decide  
 g := ![![![![287, -41, 0]], ![![-119, 24, -1]]], ![![![-119, 24, -1]], ![![48, -14, 1]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-2, -7, -1]] ![![-7, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [8, 41, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 9, 27], [40, 33, 16], [0, 1]]
 g := ![![[40, 27, 40], [21, 42, 31], [41, 36], [13, 21, 1], []], ![[25, 24, 29, 7], [9, 3, 17, 7], [35, 17], [33, 25, 37, 34], [14, 41]], ![[27, 8, 20, 10], [39, 9, 29, 15], [0, 23], [16, 12, 0, 6], [25, 41]]]
 h' := ![![[24, 9, 27], [4, 23, 30], [39, 4, 26], [25, 30, 6], [0, 0, 1], [0, 1]], ![[40, 33, 16], [28, 39, 20], [30, 28, 20], [3, 30, 19], [34, 3, 33], [24, 9, 27]], ![[0, 1], [10, 24, 36], [6, 11, 40], [36, 26, 18], [24, 40, 9], [40, 33, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25], []]
 b := ![[], [15, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [8, 41, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70907, 20597, 66478]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1649, 479, 1546]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-43, 2, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-43, 2, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![4, 2, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-43, 2, 1], ![55, 4, 2], ![110, 149, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -2, 47]], ![![-1, 0, 1], ![1, 0, 2], ![2, 3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [1, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 46], [0, 1]]
 g := ![![[32, 1], [32, 1], [15, 6], [8, 37], [1]], ![[0, 46], [0, 46], [11, 41], [46, 10], [1]]]
 h' := ![![[15, 46], [15, 46], [32, 1], [39, 37], [46, 15], [0, 1]], ![[0, 1], [0, 1], [0, 46], [30, 10], [36, 32], [15, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [9, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [1, 32, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1939, -135, 144]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, -9, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-2, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-2, 1, 0]] 
 ![![47, 0, 0], ![45, 1, 0], ![43, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-2, 1, 0], ![0, -2, 1], ![55, 47, -2]]]
  hmulB := by decide  
  f := ![![![53, -26, 0], ![1222, 0, 0]], ![![51, -25, 0], ![1176, 0, 0]], ![![49, -24, 0], ![1130, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 47, 0], ![-43, 0, 47]], ![![-1, 1, 0], ![1, -2, 1], ![-42, 47, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-43, 2, 1]] ![![47, 0, 0], ![-2, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-94, 47, 0]], ![![-2021, 94, 47], ![141, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-2, 1, 0]]], ![![![-43, 2, 1]], ![![3, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 38, -12]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![373, 38, -12]] 
 ![![53, 0, 0], ![0, 53, 0], ![44, 41, 1]] where
  M :=![![![373, 38, -12], ![-660, -191, 38], ![2090, 1126, -191]]]
  hmulB := by decide  
  f := ![![![-119, -118, -16]], ![![-880, -871, -118]], ![![-902, -893, -121]]]
  g := ![![![17, 10, -12], ![-44, -33, 38], ![198, 169, -191]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [41, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 52], [0, 1]]
 g := ![![[49, 1], [29], [22, 16], [44], [5, 1]], ![[1, 52], [29], [49, 37], [44], [10, 52]]]
 h' := ![![[5, 52], [31, 52], [52, 20], [47, 49], [7, 37], [0, 1]], ![[0, 1], [26, 1], [46, 33], [27, 4], [33, 16], [5, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [40, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [41, 48, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-240, 263, 274]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-232, -207, 274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119, 118, 16]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![119, 118, 16]] 
 ![![53, 0, 0], ![12, 1, 0], ![15, 0, 1]] where
  M :=![![![119, 118, 16], ![880, 871, 118], ![6490, 6426, 871]]]
  hmulB := by decide  
  f := ![![![-373, -38, 12]], ![![-72, -5, 2]], ![![-145, -32, 7]]]
  g := ![![![-29, 118, 16], ![-214, 871, 118], ![-1579, 6426, 871]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![373, 38, -12]] ![![119, 118, 16]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38, -3, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-38, -3, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![21, 56, 1]] where
  M :=![![![-38, -3, 1], ![55, 9, -3], ![-165, -86, 9]]]
  hmulB := by decide  
  f := ![![![-3, -1, 0]], ![![0, -3, -1]], ![![-2, -4, -1]]]
  g := ![![![-1, -1, 1], ![2, 3, -3], ![-6, -10, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [53, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 58], [0, 1]]
 g := ![![[5, 49], [35, 48], [3], [22, 28], [30, 1]], ![[0, 10], [0, 11], [3], [36, 31], [1, 58]]]
 h' := ![![[30, 58], [33, 52], [37, 44], [14, 11], [3, 21], [0, 1]], ![[0, 1], [0, 7], [0, 15], [49, 48], [43, 38], [30, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [28, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [53, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163, 120, 19]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -16, 19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![59, 0, 0], ![3, 1, 0], ![50, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![55, 47, 3]]]
  hmulB := by decide  
  f := ![![![38, 3, -1]], ![![1, 0, 0]], ![![35, 4, -1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-4, 47, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-38, -3, 1]] ![![3, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-42, -26, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-42, -26, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![19, 35, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-42, -26, 1], ![55, 5, -26], ![-1430, -1167, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -35, 61]], ![![-1, -1, 1], ![9, 15, -26], ![-25, -22, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [49, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 60], [0, 1]]
 g := ![![[3, 5], [42], [8, 5], [40, 58], [36, 1]], ![[0, 56], [42], [5, 56], [54, 3], [11, 60]]]
 h' := ![![[36, 60], [21, 35], [35, 46], [53, 26], [5, 27], [0, 1]], ![[0, 1], [0, 26], [44, 15], [13, 35], [1, 34], [36, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [18, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [49, 25, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2165, 2354, 435]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-100, -211, 435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![26, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![26, 1, 0]] 
 ![![61, 0, 0], ![26, 1, 0], ![56, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![26, 1, 0], ![0, 26, 1], ![55, 47, 26]]]
  hmulB := by decide  
  f := ![![![469, 18, 0], ![-1098, 0, 0]], ![![182, 7, 0], ![-426, 0, 0]], ![![428, 16, 0], ![-1002, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 61, 0], ![-56, 0, 61]], ![![0, 1, 0], ![-12, 26, 1], ![-43, 47, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-42, -26, 1]] ![![61, 0, 0], ![26, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1586, 61, 0]], ![![-2562, -1586, 61], ![-1037, -671, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![26, 1, 0]]], ![![![-42, -26, 1]], ![![-17, -11, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [13, 60, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 25, 61], [46, 41, 6], [0, 1]]
 g := ![![[11, 62, 64], [18, 1, 1], [10, 16], [4, 23], [37, 1], []], ![[46, 55, 36, 27], [31, 8, 60, 57], [53, 23], [], [7, 6], [27, 36]], ![[21, 35, 66, 23], [35, 30, 46, 62], [49, 19], [34, 23], [12, 22], [15, 36]]]
 h' := ![![[58, 25, 61], [34, 52, 59], [26, 49, 1], [25, 56, 63], [55, 45, 36], [0, 0, 1], [0, 1]], ![[46, 41, 6], [51, 30, 30], [52, 27, 15], [65, 28, 36], [47, 6], [65, 8, 41], [58, 25, 61]], ![[0, 1], [56, 52, 45], [47, 58, 51], [9, 50, 35], [60, 16, 31], [45, 59, 25], [46, 41, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 5], []]
 b := ![[], [33, 27, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [13, 60, 30, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12797, 8375, -1474]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![191, 125, -22]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-149, -18, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-149, -18, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![64, 53, 1]] where
  M :=![![![-149, -18, 1], ![55, -102, -18], ![-990, -791, -102]]]
  hmulB := by decide  
  f := ![![![-54, -37, 6]], ![![330, 228, -37]], ![![169, 117, -19]]]
  g := ![![![-3, -1, 1], ![17, 12, -18], ![78, 65, -102]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [8, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 70], [0, 1]]
 g := ![![[2, 9], [6, 27], [26, 12], [36], [43], [1]], ![[0, 62], [0, 44], [47, 59], [36], [43], [1]]]
 h' := ![![[55, 70], [23, 68], [5, 58], [12, 15], [4, 65], [63, 55], [0, 1]], ![[0, 1], [0, 3], [0, 13], [56, 56], [29, 6], [35, 16], [55, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [5, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [8, 16, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![228, 424, 221]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-196, -159, 221]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54, -37, 6]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-54, -37, 6]] 
 ![![71, 0, 0], ![18, 1, 0], ![31, 0, 1]] where
  M :=![![![-54, -37, 6], ![330, 228, -37], ![-2035, -1409, 228]]]
  hmulB := by decide  
  f := ![![![-149, -18, 1]], ![![-37, -6, 0]], ![![-79, -19, -1]]]
  g := ![![![6, -37, 6], ![-37, 228, -37], ![229, -1409, 228]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-149, -18, 1]] ![![-54, -37, 6]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![232, 94, -17]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![232, 94, -17]] 
 ![![73, 0, 0], ![0, 73, 0], ![25, 46, 1]] where
  M :=![![![232, 94, -17], ![-935, -567, 94], ![5170, 3483, -567]]]
  hmulB := by decide  
  f := ![![![-81, -81, -11]], ![![-605, -598, -81]], ![![-470, -465, -63]]]
  g := ![![![9, 12, -17], ![-45, -67, 94], ![265, 405, -567]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [31, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 72], [0, 1]]
 g := ![![[26, 19], [70], [36], [70, 23], [9], [1]], ![[42, 54], [70], [36], [1, 50], [9], [1]]]
 h' := ![![[70, 72], [70, 47], [14, 17], [20, 67], [25, 13], [42, 70], [0, 1]], ![[0, 1], [2, 26], [36, 56], [38, 6], [59, 60], [51, 3], [70, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [47, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [31, 3, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2159, -1730, 302]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-133, -214, 302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, 81, 11]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![81, 81, 11]] 
 ![![73, 0, 0], ![27, 1, 0], ![1, 0, 1]] where
  M :=![![![81, 81, 11], ![605, 598, 81], ![4455, 4412, 598]]]
  hmulB := by decide  
  f := ![![![-232, -94, 17]], ![![-73, -27, 5]], ![![-74, -49, 8]]]
  g := ![![![-29, 81, 11], ![-214, 598, 81], ![-1579, 4412, 598]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![232, 94, -17]] ![![81, 81, 11]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![11, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![11, 1, 0]] 
 ![![79, 0, 0], ![11, 1, 0], ![37, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![11, 1, 0], ![0, 11, 1], ![55, 47, 11]]]
  hmulB := by decide  
  f := ![![![331, 30, 0], ![-2370, 0, 0]], ![![33, 3, 0], ![-236, 0, 0]], ![![145, 13, 0], ![-1038, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 79, 0], ![-37, 0, 79]], ![![0, 1, 0], ![-2, 11, 1], ![-11, 47, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32, -1, -1]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![32, -1, -1]] 
 ![![79, 0, 0], ![57, 1, 0], ![69, 0, 1]] where
  M :=![![![32, -1, -1], ![-55, -15, -1], ![-55, -102, -15]]]
  hmulB := by decide  
  f := ![![![-123, -87, 14]], ![![-79, -56, 9]], ![![-168, -118, 19]]]
  g := ![![![2, -1, -1], ![11, -15, -1], ![86, -102, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![11, 1, 0]] ![![79, 0, 0], ![11, 1, 0]]
  ![![-123, -87, 14]] where
 M := ![![![6241, 0, 0], ![869, 79, 0]], ![![869, 79, 0], ![121, 22, 1]]]
 hmul := by decide  
 g := ![![![![2528, -79, -79]], ![![297, -26, -12]]], ![![![297, -26, -12]], ![![33, -7, -2]]]]
 hle2 := by decide  
def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-123, -87, 14]] ![![32, -1, -1]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB129I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB129I1 : PrimesBelowBoundCertificateInterval O 31 79 129 where
  m := 11
  g := ![1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB129I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N0, I79N1]
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
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
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
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
      exact NI79N0
      exact NI79N1
  β := ![I41N0, I41N1, I47N1, I53N1, I59N1, I61N1, I71N1, I73N1, I79N0, I79N1]
  Il := ![[], [I41N0, I41N0, I41N1], [], [I47N1], [I53N1], [I59N1], [I61N1], [], [I71N1], [I73N1], [I79N0, I79N0, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
