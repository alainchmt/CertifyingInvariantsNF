
import IdealArithmetic.Examples.NF3_1_817452_1.RI3_1_817452_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8665, 1552, 278]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![8665, 1552, 278]] 
 ![![83, 0, 0], ![0, 83, 0], ![4, 2, 1]] where
  M :=![![![8665, 1552, 278], ![48372, 8665, 1552], ![270048, 48372, 8665]]]
  hmulB := by decide  
  f := ![![![107, -8, -2]], ![![-348, 107, -8]], ![![-20, -2, 1]]]
  g := ![![![91, 12, 278], ![508, 67, 1552], ![2836, 374, 8665]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [12, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 82], [0, 1]]
 g := ![![[41, 7], [8, 4], [1], [69], [72, 36], [1]], ![[0, 76], [32, 79], [1], [69], [39, 47], [1]]]
 h' := ![![[6, 82], [70, 16], [4, 81], [79, 1], [49, 61], [71, 6], [0, 1]], ![[0, 1], [0, 67], [75, 2], [2, 82], [0, 22], [24, 77], [6, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [41, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [12, 77, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![360, 97, -76]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 3, -76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, 8, 2]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-107, 8, 2]] 
 ![![83, 0, 0], ![81, 1, 0], ![79, 0, 1]] where
  M :=![![![-107, 8, 2], ![348, -107, 8], ![1392, 348, -107]]]
  hmulB := by decide  
  f := ![![![-8665, -1552, -278]], ![![-9039, -1619, -290]], ![![-11501, -2060, -369]]]
  g := ![![![-11, 8, 2], ![101, -107, 8], ![-221, 348, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![8665, 1552, 278]] ![![-107, 8, 2]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![32, 11, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![32, 11, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![32, 11, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![32, 11, 1], ![174, 32, 11], ![1914, 174, 32]]]
  hmulB := by decide  
  f := ![![![-31, -11, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -11, 89]], ![![0, 0, 1], ![-2, -1, 11], ![10, -2, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [50, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 88], [0, 1]]
 g := ![![[30, 73], [55], [79], [79, 47], [7, 80], [1]], ![[0, 16], [55], [79], [67, 42], [68, 9], [1]]]
 h' := ![![[13, 88], [77, 42], [54, 77], [55, 48], [6, 15], [39, 13], [0, 1]], ![[0, 1], [0, 47], [76, 12], [56, 41], [23, 74], [30, 76], [13, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [57, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [50, 76, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2113, 1418, 226]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-105, -12, 226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-11, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-11, 1, 0]] 
 ![![89, 0, 0], ![78, 1, 0], ![57, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-11, 1, 0], ![0, -11, 1], ![174, 0, -11]]]
  hmulB := by decide  
  f := ![![![914, -83, 0], ![7387, 0, 0]], ![![804, -73, 0], ![6498, 0, 0]], ![![596, -54, 0], ![4817, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 89, 0], ![-57, 0, 89]], ![![-1, 1, 0], ![9, -11, 1], ![9, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![32, 11, 1]] ![![89, 0, 0], ![-11, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-979, 89, 0]], ![![2848, 979, 89], ![-178, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-11, 1, 0]]], ![![![32, 11, 1]], ![![-2, -1, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-42, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-42, 1, 0]] 
 ![![97, 0, 0], ![55, 1, 0], ![79, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-42, 1, 0], ![0, -42, 1], ![174, 0, -42]]]
  hmulB := by decide  
  f := ![![![3487, -83, 0], ![8051, 0, 0]], ![![2017, -48, 0], ![4657, 0, 0]], ![![2833, -67, 0], ![6541, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 97, 0], ![-79, 0, 97]], ![![-1, 1, 0], ![23, -42, 1], ![36, 0, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-40, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-40, 1, 0]] 
 ![![97, 0, 0], ![57, 1, 0], ![49, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-40, 1, 0], ![0, -40, 1], ![174, 0, -40]]]
  hmulB := by decide  
  f := ![![![1081, -27, 0], ![2619, 0, 0]], ![![641, -16, 0], ![1553, 0, 0]], ![![617, -15, 0], ![1495, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 97, 0], ![-49, 0, 97]], ![![-1, 1, 0], ![23, -40, 1], ![22, 0, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-15, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-15, 1, 0]] 
 ![![97, 0, 0], ![82, 1, 0], ![66, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-15, 1, 0], ![0, -15, 1], ![174, 0, -15]]]
  hmulB := by decide  
  f := ![![![256, -17, 0], ![1649, 0, 0]], ![![226, -15, 0], ![1456, 0, 0]], ![![198, -13, 0], ![1276, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 97, 0], ![-66, 0, 97]], ![![-1, 1, 0], ![12, -15, 1], ![12, 0, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-42, 1, 0]] ![![97, 0, 0], ![-40, 1, 0]]
  ![![97, 0, 0], ![31, 15, 1]] where
 M := ![![![9409, 0, 0], ![-3880, 97, 0]], ![![-4074, 97, 0], ![1680, -82, 1]]]
 hmul := by decide  
 g := ![![![![66, -15, -1], ![97, 0, 0]], ![![-40, 1, 0], ![0, 0, 0]]], ![![![-42, 1, 0], ![0, 0, 0]], ![![-14, -16, -1], ![98, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![31, 15, 1]] ![![97, 0, 0], ![-15, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1455, 97, 0]], ![![3007, 1455, 97], ![-291, -194, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-15, 1, 0]]], ![![![31, 15, 1]], ![![-3, -2, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1031, 274, -16]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1031, 274, -16]] 
 ![![101, 0, 0], ![0, 101, 0], ![96, 46, 1]] where
  M :=![![![-1031, 274, -16], ![-2784, -1031, 274], ![47676, -2784, -1031]]]
  hmulB := by decide  
  f := ![![![18077, 3238, 580]], ![![100920, 18077, 3238]], ![![68724, 12310, 2205]]]
  g := ![![![5, 10, -16], ![-288, -135, 274], ![1452, 442, -1031]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [80, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 100], [0, 1]]
 g := ![![[54, 24], [54], [20, 95], [88], [5], [23, 1]], ![[0, 77], [54], [84, 6], [88], [5], [46, 100]]]
 h' := ![![[23, 100], [77, 23], [16, 85], [16, 87], [84, 54], [79, 45], [0, 1]], ![[0, 1], [0, 78], [52, 16], [98, 14], [13, 47], [3, 56], [23, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [61, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [80, 78, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1164, 124, 51]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, -22, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18077, -3238, -580]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-18077, -3238, -580]] 
 ![![101, 0, 0], ![55, 1, 0], ![5, 0, 1]] where
  M :=![![![-18077, -3238, -580], ![-100920, -18077, -3238], ![-563412, -100920, -18077]]]
  hmulB := by decide  
  f := ![![![1031, -274, 16]], ![![589, -139, 6]], ![![-421, 14, 11]]]
  g := ![![![1613, -3238, -580], ![9005, -18077, -3238], ![50273, -100920, -18077]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1031, 274, -16]] ![![-18077, -3238, -580]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [54, 24, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 42, 23], [54, 60, 80], [0, 1]]
 g := ![![[41, 21, 66], [4, 32, 16], [35, 19, 15], [56, 36], [89, 9], [1]], ![[53, 28, 22, 15], [10, 52, 57, 16], [68, 92, 83, 38], [62, 91], [33, 55], [72, 41, 52, 13]], ![[82, 44, 22, 65], [85, 97, 36, 73], [78, 97, 5, 90], [28, 58], [76, 98], [84, 68, 9, 90]]]
 h' := ![![[52, 42, 23], [93, 90, 90], [67, 2, 99], [23, 5, 18], [67, 73, 97], [49, 79, 3], [0, 1]], ![[54, 60, 80], [95, 32, 54], [31, 40, 12], [89, 99, 62], [48, 13, 83], [39, 55, 40], [52, 42, 23]], ![[0, 1], [44, 84, 62], [59, 61, 95], [94, 102, 23], [24, 17, 26], [76, 72, 60], [54, 60, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 10], []]
 b := ![[], [89, 38, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [54, 24, 100, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-924631, 159959, 4120]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8977, 1553, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![27, -53, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![27, -53, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![27, 54, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![27, -53, 1], ![174, 27, -53], ![-9222, 174, 27]]]
  hmulB := by decide  
  f := ![![![-26, 53, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -54, 107]], ![![0, -1, 1], ![15, 27, -53], ![-93, -12, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [47, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 106], [0, 1]]
 g := ![![[103, 41], [11, 44], [40], [], [62], [81, 1]], ![[0, 66], [44, 63], [40], [], [62], [55, 106]]]
 h' := ![![[81, 106], [18, 83], [46, 30], [0, 19], [74], [45, 94], [0, 1]], ![[0, 1], [0, 24], [15, 77], [41, 88], [74], [62, 13], [81, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [103, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [47, 26, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![395, 148, -25]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 14, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![53, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![53, 1, 0]] 
 ![![107, 0, 0], ![53, 1, 0], ![80, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![53, 1, 0], ![0, 53, 1], ![174, 0, 53]]]
  hmulB := by decide  
  f := ![![![1220, 23, 0], ![-2461, 0, 0]], ![![530, 10, 0], ![-1069, 0, 0]], ![![822, 15, 0], ![-1658, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 107, 0], ![-80, 0, 107]], ![![0, 1, 0], ![-27, 53, 1], ![-38, 0, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![27, -53, 1]] ![![107, 0, 0], ![53, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5671, 107, 0]], ![![2889, -5671, 107], ![1605, -2782, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![53, 1, 0]]], ![![![27, -53, 1]], ![![15, -26, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [108, 4, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 48, 64], [35, 60, 45], [0, 1]]
 g := ![![[77, 22, 73], [63, 49], [24, 21, 20], [100, 76, 25], [3, 9], [1]], ![[82, 38, 108, 61], [88, 97], [16, 84, 21, 48], [49, 79, 62, 66], [98, 108], [32, 63, 22, 108]], ![[75, 38, 78, 104], [44, 105], [98, 85, 84, 20], [94, 95, 28, 73], [24, 97], [100, 61, 7, 1]]]
 h' := ![![[77, 48, 64], [94, 85, 20], [24, 6, 102], [100, 19, 42], [4, 98, 104], [1, 105, 3], [0, 1]], ![[35, 60, 45], [89, 27, 100], [108, 77, 73], [16, 107, 30], [86, 22, 86], [73, 23, 33], [77, 48, 64]], ![[0, 1], [47, 106, 98], [60, 26, 43], [65, 92, 37], [102, 98, 28], [29, 90, 73], [35, 60, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 30], []]
 b := ![[], [25, 14, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [108, 4, 106, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1944669, 211569, 49486]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17841, 1941, 454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-2, 26, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-2, 26, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![111, 26, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-2, 26, 1], ![174, -2, 26], ![4524, 174, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-111, -26, 113]], ![![-1, 0, 1], ![-24, -6, 26], ![42, 2, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [24, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 112], [0, 1]]
 g := ![![[107, 30], [9], [82], [28], [23, 72], [31, 1]], ![[20, 83], [9], [82], [28], [108, 41], [62, 112]]]
 h' := ![![[31, 112], [1, 97], [68, 110], [62, 46], [13, 64], [47, 33], [0, 1]], ![[0, 1], [70, 16], [88, 3], [19, 67], [76, 49], [53, 80], [31, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [24, 82, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1101, 414, -71]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![60, 20, -71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-26, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-26, 1, 0]] 
 ![![113, 0, 0], ![87, 1, 0], ![2, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-26, 1, 0], ![0, -26, 1], ![174, 0, -26]]]
  hmulB := by decide  
  f := ![![![2757, -106, 0], ![11978, 0, 0]], ![![2107, -81, 0], ![9154, 0, 0]], ![![58, -2, 0], ![252, 1, 0]]]
  g := ![![![1, 0, 0], ![-87, 113, 0], ![-2, 0, 113]], ![![-1, 1, 0], ![20, -26, 1], ![2, 0, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-2, 26, 1]] ![![113, 0, 0], ![-26, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2938, 113, 0]], ![![-226, 2938, 113], ![226, -678, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-26, 1, 0]]], ![![![-2, 26, 1]], ![![2, -6, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-49, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-49, 1, 0]] 
 ![![127, 0, 0], ![78, 1, 0], ![12, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-49, 1, 0], ![0, -49, 1], ![174, 0, -49]]]
  hmulB := by decide  
  f := ![![![4509, -92, 0], ![11684, 0, 0]], ![![2794, -57, 0], ![7240, 0, 0]], ![![460, -9, 0], ![1192, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 127, 0], ![-12, 0, 127]], ![![-1, 1, 0], ![30, -49, 1], ![6, 0, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-42, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-42, 1, 0]] 
 ![![127, 0, 0], ![85, 1, 0], ![14, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-42, 1, 0], ![0, -42, 1], ![174, 0, -42]]]
  hmulB := by decide  
  f := ![![![5293, -126, 0], ![16002, 0, 0]], ![![3571, -85, 0], ![10796, 0, 0]], ![![602, -14, 0], ![1820, 1, 0]]]
  g := ![![![1, 0, 0], ![-85, 127, 0], ![-14, 0, 127]], ![![-1, 1, 0], ![28, -42, 1], ![6, 0, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-36, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-36, 1, 0]] 
 ![![127, 0, 0], ![91, 1, 0], ![101, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-36, 1, 0], ![0, -36, 1], ![174, 0, -36]]]
  hmulB := by decide  
  f := ![![![2809, -78, 0], ![9906, 0, 0]], ![![1981, -55, 0], ![6986, 0, 0]], ![![2243, -62, 0], ![7910, 1, 0]]]
  g := ![![![1, 0, 0], ![-91, 127, 0], ![-101, 0, 127]], ![![-1, 1, 0], ![25, -36, 1], ![30, 0, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-49, 1, 0]] ![![127, 0, 0], ![-42, 1, 0]]
  ![![127, 0, 0], ![26, 36, 1]] where
 M := ![![![16129, 0, 0], ![-5334, 127, 0]], ![![-6223, 127, 0], ![2058, -91, 1]]]
 hmul := by decide  
 g := ![![![![101, -36, -1], ![127, 0, 0]], ![![-42, 1, 0], ![0, 0, 0]]], ![![![-49, 1, 0], ![0, 0, 0]], ![![-10, -37, -1], ![128, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![26, 36, 1]] ![![127, 0, 0], ![-36, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-4572, 127, 0]], ![![3302, 4572, 127], ![-762, -1270, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-36, 1, 0]]], ![![![26, 36, 1]], ![![-6, -10, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![41, 33, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![41, 33, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![41, 33, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![41, 33, 1], ![174, 41, 33], ![5742, 174, 41]]]
  hmulB := by decide  
  f := ![![![-40, -33, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -33, 131]], ![![0, 0, 1], ![-9, -8, 33], ![31, -9, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [129, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 130], [0, 1]]
 g := ![![[8, 65], [112, 21], [77], [9], [107], [125], [1]], ![[0, 66], [55, 110], [77], [9], [107], [125], [1]]]
 h' := ![![[16, 130], [93, 117], [36, 26], [12, 48], [16, 128], [123, 99], [2, 16], [0, 1]], ![[0, 1], [0, 14], [59, 105], [125, 83], [99, 3], [4, 32], [127, 115], [16, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [8, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [129, 115, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![825, 811, 231]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -52, 231]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-33, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-33, 1, 0]] 
 ![![131, 0, 0], ![98, 1, 0], ![90, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-33, 1, 0], ![0, -33, 1], ![174, 0, -33]]]
  hmulB := by decide  
  f := ![![![199, -6, 0], ![786, 0, 0]], ![![166, -5, 0], ![656, 0, 0]], ![![174, -5, 0], ![688, 1, 0]]]
  g := ![![![1, 0, 0], ![-98, 131, 0], ![-90, 0, 131]], ![![-1, 1, 0], ![24, -33, 1], ![24, 0, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![41, 33, 1]] ![![131, 0, 0], ![-33, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-4323, 131, 0]], ![![5371, 4323, 131], ![-1179, -1048, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-33, 1, 0]]], ![![![41, 33, 1]], ![![-9, -8, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-1, -37, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-1, -37, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![136, 100, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-1, -37, 1], ![174, -1, -37], ![-6438, 174, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -100, 137]], ![![-1, -1, 1], ![38, 27, -37], ![-46, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [49, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 136], [0, 1]]
 g := ![![[27, 14], [60], [68], [19, 17], [19], [17], [1]], ![[0, 123], [60], [68], [133, 120], [19], [17], [1]]]
 h' := ![![[47, 136], [85, 39], [55, 103], [28, 94], [50, 47], [61, 29], [88, 47], [0, 1]], ![[0, 1], [0, 98], [101, 34], [62, 43], [67, 90], [54, 108], [105, 90], [47, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [100, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [49, 90, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6727, -244, 288]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-335, -212, 288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![37, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![37, 1, 0]] 
 ![![137, 0, 0], ![37, 1, 0], ![1, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![37, 1, 0], ![0, 37, 1], ![174, 0, 37]]]
  hmulB := by decide  
  f := ![![![2295, 62, 0], ![-8494, 0, 0]], ![![629, 17, 0], ![-2328, 0, 0]], ![![-27, -1, 0], ![100, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 137, 0], ![-1, 0, 137]], ![![0, 1, 0], ![-10, 37, 1], ![1, 0, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-1, -37, 1]] ![![137, 0, 0], ![37, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![5069, 137, 0]], ![![-137, -5069, 137], ![137, -1370, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![37, 1, 0]]], ![![![-1, -37, 1]], ![![1, -10, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB256I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB256I2 : PrimesBelowBoundCertificateInterval O 79 137 256 where
  m := 11
  g := ![2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB256I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N1, I107N1, I113N1, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [], [I107N1], [], [I113N1], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
