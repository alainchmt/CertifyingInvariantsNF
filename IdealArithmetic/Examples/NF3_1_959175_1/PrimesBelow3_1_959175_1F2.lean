
import IdealArithmetic.Examples.NF3_1_959175_1.RI3_1_959175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-52, 1, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-52, 1, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![31, 1, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-52, 1, 1], ![280, 1, 1], ![0, 166, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -1, 83]], ![![-1, 0, 1], ![3, 0, 1], ![0, 2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [69, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 82], [0, 1]]
 g := ![![[31, 77], [58, 30], [68], [30], [4, 29], [1]], ![[0, 6], [47, 53], [68], [30], [57, 54], [1]]]
 h' := ![![[19, 82], [65, 49], [42, 69], [70, 63], [56, 14], [14, 19], [0, 1]], ![[0, 1], [0, 34], [25, 14], [22, 20], [73, 69], [43, 64], [19, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [51, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [69, 64, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![909, 1526, 281]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94, 15, 281]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-1, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-1, 1, 0]] 
 ![![83, 0, 0], ![82, 1, 0], ![0, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-1, 1, 0], ![0, 0, 2], ![280, 52, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 42, 0]]]
  g := ![![![1, 0, 0], ![-82, 83, 0], ![0, 0, 83]], ![![-1, 1, 0], ![0, 0, 2], ![-48, 52, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-52, 1, 1]] ![![83, 0, 0], ![-1, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-83, 83, 0]], ![![-4316, 83, 83], ![332, 0, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-1, 1, 0]]], ![![![-52, 1, 1]], ![![4, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![38, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![38, 1, 0]] 
 ![![89, 0, 0], ![38, 1, 0], ![60, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![38, 1, 0], ![0, 39, 2], ![280, 52, 37]]]
  hmulB := by decide  
  f := ![![![2661, 70, 0], ![-6230, 0, 0]], ![![1102, 29, 0], ![-2580, 0, 0]], ![![1776, 27, -1], ![-4158, 45, 0]]]
  g := ![![![1, 0, 0], ![-38, 89, 0], ![-60, 0, 89]], ![![0, 1, 0], ![-18, 39, 2], ![-44, 52, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-20, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-20, 1, 0]] 
 ![![89, 0, 0], ![69, 1, 0], ![77, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-20, 1, 0], ![0, -19, 2], ![280, 52, -21]]]
  hmulB := by decide  
  f := ![![![1261, -63, 0], ![5607, 0, 0]], ![![1001, -50, 0], ![4451, 0, 0]], ![![1113, -46, -1], ![4949, 45, 0]]]
  g := ![![![1, 0, 0], ![-69, 89, 0], ![-77, 0, 89]], ![![-1, 1, 0], ![13, -19, 2], ![-19, 52, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-18, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-18, 1, 0]] 
 ![![89, 0, 0], ![71, 1, 0], ![25, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-18, 1, 0], ![0, -17, 2], ![280, 52, -19]]]
  hmulB := by decide  
  f := ![![![235, -13, 0], ![1157, 0, 0]], ![![181, -10, 0], ![891, 0, 0]], ![![83, 4, -1], ![409, 45, 0]]]
  g := ![![![1, 0, 0], ![-71, 89, 0], ![-25, 0, 89]], ![![-1, 1, 0], ![13, -17, 2], ![-33, 52, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![38, 1, 0]] ![![89, 0, 0], ![-20, 1, 0]]
  ![![89, 0, 0], ![-24, -35, 1]] where
 M := ![![![7921, 0, 0], ![-1780, 89, 0]], ![![3382, 89, 0], ![-760, 19, 2]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![4, 36, -1], ![89, 0, 0]]], ![![![38, 1, 0], ![0, 0, 0]], ![![-8, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-24, -35, 1]] ![![89, 0, 0], ![-18, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1602, 89, 0]], ![![-2136, -3115, 89], ![712, 623, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-18, 1, 0]]], ![![![-24, -35, 1]], ![![8, 7, -1]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-12, 5, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-12, 5, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![85, 5, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-12, 5, 1], ![280, 45, 9], ![1120, 374, 36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -5, 97]], ![![-1, 0, 1], ![-5, 0, 9], ![-20, 2, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [30, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 96], [0, 1]]
 g := ![![[72, 25], [50], [91], [11], [22], [71, 1]], ![[4, 72], [50], [91], [11], [22], [45, 96]]]
 h' := ![![[71, 96], [83, 92], [82, 70], [22, 73], [35, 37], [4, 64], [0, 1]], ![[0, 1], [19, 5], [8, 27], [64, 24], [43, 60], [86, 33], [71, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [1, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [30, 26, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2235, 2265, 938]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-845, -25, 938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-9, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-9, 1, 0]] 
 ![![97, 0, 0], ![88, 1, 0], ![61, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-9, 1, 0], ![0, -8, 2], ![280, 52, -10]]]
  hmulB := by decide  
  f := ![![![559, -62, 0], ![6014, 0, 0]], ![![496, -55, 0], ![5336, 0, 0]], ![![343, -34, -1], ![3690, 49, 0]]]
  g := ![![![1, 0, 0], ![-88, 97, 0], ![-61, 0, 97]], ![![-1, 1, 0], ![6, -8, 2], ![-38, 52, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-12, 5, 1]] ![![97, 0, 0], ![-9, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-873, 97, 0]], ![![-1164, 485, 97], ![388, 0, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-9, 1, 0]]], ![![![-12, 5, 1]], ![![4, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [95, 93, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 27, 24], [70, 73, 77], [0, 1]]
 g := ![![[23, 44, 5], [46, 47], [96, 7, 47], [0, 22], [9, 36], [1]], ![[14, 67, 76, 6], [45, 87], [63, 64, 28, 4], [45, 22], [94, 71], [94, 70, 17, 88]], ![[77, 85, 39, 45], [54, 19], [98, 23, 61, 54], [90, 88], [11, 92], [26, 10, 73, 13]]]
 h' := ![![[37, 27, 24], [65, 63, 45], [71, 99, 59], [20, 67, 59], [90, 81, 74], [6, 8, 6], [0, 1]], ![[70, 73, 77], [4, 67, 50], [21, 84, 17], [99, 28, 57], [58, 97, 74], [10, 52, 24], [37, 27, 24]], ![[0, 1], [16, 72, 6], [46, 19, 25], [78, 6, 86], [12, 24, 54], [59, 41, 71], [70, 73, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 68], []]
 b := ![[], [77, 55, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [95, 93, 95, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![131199, -23028, -7777]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1299, -228, -77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [8, 99, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 57, 50], [57, 45, 53], [0, 1]]
 g := ![![[8, 95, 49], [1, 64, 52], [2, 56, 13], [67, 8], [13, 49], [1]], ![[25, 76, 101, 72], [102, 7, 10, 4], [35, 15, 20, 52], [95, 59], [5, 41], [95, 36, 35, 61]], ![[5, 73, 102, 69], [50, 26, 75, 54], [27, 53, 75, 27], [44, 36], [15, 52], [75, 18, 87, 42]]]
 h' := ![![[39, 57, 50], [95, 57, 96], [87, 98, 19], [34, 79, 42], [63, 8, 27], [95, 4, 96], [0, 1]], ![[57, 45, 53], [62, 39, 63], [12, 26, 90], [68, 73, 72], [101, 36, 70], [55, 5, 91], [39, 57, 50]], ![[0, 1], [51, 7, 47], [44, 82, 97], [90, 54, 92], [66, 59, 6], [17, 94, 19], [57, 45, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 78], []]
 b := ![[], [9, 96, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [8, 99, 7, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4362565, -1863682, -321875]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42355, -18094, -3125]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-15, 9, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-15, 9, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![92, 9, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-15, 9, 1], ![280, 46, 17], ![2240, 582, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -9, 107]], ![![-1, 0, 1], ![-12, -1, 17], ![-4, 3, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [46, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 106], [0, 1]]
 g := ![![[74, 9], [88, 76], [9], [81, 64], [19], [20, 1]], ![[40, 98], [3, 31], [9], [77, 43], [19], [40, 106]]]
 h' := ![![[20, 106], [18, 3], [54, 66], [19, 104], [12, 8], [43, 33], [0, 1]], ![[0, 1], [78, 104], [90, 41], [66, 3], [65, 99], [61, 74], [20, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [10, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [46, 87, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![886, 1480, 212]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-174, -4, 212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-17, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-17, 1, 0]] 
 ![![107, 0, 0], ![90, 1, 0], ![78, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-17, 1, 0], ![0, -16, 2], ![280, 52, -18]]]
  hmulB := by decide  
  f := ![![![1276, -75, 0], ![8025, 0, 0]], ![![1072, -63, 0], ![6742, 0, 0]], ![![920, -46, -1], ![5786, 54, 0]]]
  g := ![![![1, 0, 0], ![-90, 107, 0], ![-78, 0, 107]], ![![-1, 1, 0], ![12, -16, 2], ![-28, 52, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-15, 9, 1]] ![![107, 0, 0], ![-17, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1819, 107, 0]], ![![-1605, 963, 107], ![535, -107, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-17, 1, 0]]], ![![![-15, 9, 1]], ![![5, -1, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [36, 60, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 75, 10], [98, 33, 99], [0, 1]]
 g := ![![[8, 14, 64], [96, 5], [43, 91, 80], [55, 62, 12], [62, 21], [1]], ![[58, 87, 8, 8], [84, 60], [98, 90, 26, 13], [55, 100, 77, 59], [55, 9], [77, 57, 33, 19]], ![[53, 32, 90, 79], [28, 64], [41, 0, 106, 76], [29, 26, 52, 8], [46, 80], [85, 100, 103, 90]]]
 h' := ![![[39, 75, 10], [80, 66, 8], [87, 27, 88], [91, 90, 25], [45, 62, 98], [73, 49, 28], [0, 1]], ![[98, 33, 99], [56, 84, 52], [30, 56, 13], [33, 73, 90], [13, 32, 39], [85, 51, 106], [39, 75, 10]], ![[0, 1], [70, 68, 49], [36, 26, 8], [85, 55, 103], [68, 15, 81], [78, 9, 84], [98, 33, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 65], []]
 b := ![[], [69, 88, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [36, 60, 81, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![557652938, 195211806, 31606512]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5116082, 1790934, 289968]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![19, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![19, 1, 0]] 
 ![![113, 0, 0], ![19, 1, 0], ![36, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![19, 1, 0], ![0, 20, 2], ![280, 52, 18]]]
  hmulB := by decide  
  f := ![![![77, 4, 0], ![-452, 0, 0]], ![![-19, -1, 0], ![114, 0, 0]], ![![2, -10, -1], ![-10, 57, 0]]]
  g := ![![![1, 0, 0], ![-19, 113, 0], ![-36, 0, 113]], ![![0, 1, 0], ![-4, 20, 2], ![-12, 52, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![25, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![25, 1, 0]] 
 ![![113, 0, 0], ![25, 1, 0], ![14, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![25, 1, 0], ![0, 26, 2], ![280, 52, 24]]]
  hmulB := by decide  
  f := ![![![1551, 62, 0], ![-7006, 0, 0]], ![![325, 13, 0], ![-1468, 0, 0]], ![![178, -6, -1], ![-804, 57, 0]]]
  g := ![![![1, 0, 0], ![-25, 113, 0], ![-14, 0, 113]], ![![0, 1, 0], ![-6, 26, 2], ![-12, 52, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-44, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-44, 1, 0]] 
 ![![113, 0, 0], ![69, 1, 0], ![71, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-44, 1, 0], ![0, -43, 2], ![280, 52, -45]]]
  hmulB := by decide  
  f := ![![![3081, -70, 0], ![7910, 0, 0]], ![![1893, -43, 0], ![4860, 0, 0]], ![![1967, -23, -1], ![5050, 57, 0]]]
  g := ![![![1, 0, 0], ![-69, 113, 0], ![-71, 0, 113]], ![![-1, 1, 0], ![25, -43, 2], ![-1, 52, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![19, 1, 0]] ![![113, 0, 0], ![25, 1, 0]]
  ![![113, 0, 0], ![-45, -34, 1]] where
 M := ![![![12769, 0, 0], ![2825, 113, 0]], ![![2147, 113, 0], ![475, 45, 2]]]
 hmul := by decide  
 g := ![![![![113, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-45, -34, 1]] ![![113, 0, 0], ![-44, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-4972, 113, 0]], ![![-5085, -3842, 113], ![2260, 1469, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-44, 1, 0]]], ![![![-45, -34, 1]], ![![20, 13, -1]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![13, -62, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![13, -62, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![13, 65, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![13, -62, 1], ![280, 3, -125], ![-17640, -3110, 128]]]
  hmulB := by decide  
  f := ![![![-12, 62, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -65, 127]], ![![0, -1, 1], ![15, 64, -125], ![-152, -90, 128]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [26, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 126], [0, 1]]
 g := ![![[6, 44], [21, 62], [90, 62], [68, 61], [114, 15], [98, 1]], ![[0, 83], [1, 65], [70, 65], [77, 66], [60, 112], [69, 126]]]
 h' := ![![[98, 126], [89, 60], [73, 69], [10, 69], [84, 51], [119, 53], [0, 1]], ![[0, 1], [0, 67], [104, 58], [41, 58], [2, 76], [106, 74], [98, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [118, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [26, 29, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![838, 380, 84]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -40, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-2, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-2, 1, 0]] 
 ![![127, 0, 0], ![125, 1, 0], ![126, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-2, 1, 0], ![0, -1, 2], ![280, 52, -3]]]
  hmulB := by decide  
  f := ![![![3, 62, -126], ![127, 8001, 0]], ![![1, 62, -124], ![1, 7874, 0]], ![![2, 62, -125], ![64, 7938, 0]]]
  g := ![![![1, 0, 0], ![-125, 127, 0], ![-126, 0, 127]], ![![-1, 1, 0], ![-1, -1, 2], ![-46, 52, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![13, -62, 1]] ![![127, 0, 0], ![-2, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-254, 127, 0]], ![![1651, -7874, 127], ![254, 127, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-2, 1, 0]]], ![![![13, -62, 1]], ![![2, 1, -1]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![14, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![14, 1, 0]] 
 ![![131, 0, 0], ![14, 1, 0], ![26, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![14, 1, 0], ![0, 15, 2], ![280, 52, 13]]]
  hmulB := by decide  
  f := ![![![1331, 95, 0], ![-12445, 0, 0]], ![![126, 9, 0], ![-1178, 0, 0]], ![![246, 10, -1], ![-2300, 66, 0]]]
  g := ![![![1, 0, 0], ![-14, 131, 0], ![-26, 0, 131]], ![![0, 1, 0], ![-2, 15, 2], ![-6, 52, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![51, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![51, 1, 0]] 
 ![![131, 0, 0], ![51, 1, 0], ![115, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![51, 1, 0], ![0, 52, 2], ![280, 52, 50]]]
  hmulB := by decide  
  f := ![![![613, 12, 0], ![-1572, 0, 0]], ![![153, 3, 0], ![-392, 0, 0]], ![![521, -16, -1], ![-1336, 66, 0]]]
  g := ![![![1, 0, 0], ![-51, 131, 0], ![-115, 0, 131]], ![![0, 1, 0], ![-22, 52, 2], ![-62, 52, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-65, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-65, 1, 0]] 
 ![![131, 0, 0], ![66, 1, 0], ![16, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-65, 1, 0], ![0, -64, 2], ![280, 52, -66]]]
  hmulB := by decide  
  f := ![![![66, 5503, -172], ![131, 11266, 0]], ![![66, 2751, -86], ![132, 5633, 0]], ![![16, 672, -21], ![32, 1376, 0]]]
  g := ![![![1, 0, 0], ![-66, 131, 0], ![-16, 0, 131]], ![![-1, 1, 0], ![32, -64, 2], ![-16, 52, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![14, 1, 0]] ![![131, 0, 0], ![51, 1, 0]]
  ![![131, 0, 0], ![-36, 33, 1]] where
 M := ![![![17161, 0, 0], ![6681, 131, 0]], ![![1834, 131, 0], ![714, 66, 2]]]
 hmul := by decide  
 g := ![![![![131, 0, 0], ![0, 0, 0]], ![![51, 1, 0], ![0, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![6, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-36, 33, 1]] ![![131, 0, 0], ![-65, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-8515, 131, 0]], ![![-4716, 4323, 131], ![2620, -2096, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-65, 1, 0]]], ![![![-36, 33, 1]], ![![20, -16, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-57, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-57, 1, 0]] 
 ![![137, 0, 0], ![80, 1, 0], ![48, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-57, 1, 0], ![0, -56, 2], ![280, 52, -58]]]
  hmulB := by decide  
  f := ![![![7582, -133, 0], ![18221, 0, 0]], ![![4504, -79, 0], ![10824, 0, 0]], ![![2748, -20, -1], ![6604, 69, 0]]]
  g := ![![![1, 0, 0], ![-80, 137, 0], ![-48, 0, 137]], ![![-1, 1, 0], ![32, -56, 2], ![-8, 52, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-50, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-50, 1, 0]] 
 ![![137, 0, 0], ![87, 1, 0], ![8, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-50, 1, 0], ![0, -49, 2], ![280, 52, -51]]]
  hmulB := by decide  
  f := ![![![4001, -80, 0], ![10960, 0, 0]], ![![2551, -51, 0], ![6988, 0, 0]], ![![284, 19, -1], ![778, 69, 0]]]
  g := ![![![1, 0, 0], ![-87, 137, 0], ![-8, 0, 137]], ![![-1, 1, 0], ![31, -49, 2], ![-28, 52, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-30, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-30, 1, 0]] 
 ![![137, 0, 0], ![107, 1, 0], ![113, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-30, 1, 0], ![0, -29, 2], ![280, 52, -31]]]
  hmulB := by decide  
  f := ![![![1501, -50, 0], ![6850, 0, 0]], ![![1171, -39, 0], ![5344, 0, 0]], ![![1249, -27, -1], ![5700, 69, 0]]]
  g := ![![![1, 0, 0], ![-107, 137, 0], ![-113, 0, 137]], ![![-1, 1, 0], ![21, -29, 2], ![-13, 52, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-57, 1, 0]] ![![137, 0, 0], ![-50, 1, 0]]
  ![![137, 0, 0], ![-82, -53, 1]] where
 M := ![![![18769, 0, 0], ![-6850, 137, 0]], ![![-7809, 137, 0], ![2850, -106, 2]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![32, 54, -1], ![137, 0, 0]]], ![![![25, 54, -1], ![137, 0, 0]], ![![22, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-82, -53, 1]] ![![137, 0, 0], ![-30, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-4110, 137, 0]], ![![-11234, -7261, 137], ![2740, 1507, -137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-30, 1, 0]]], ![![![-82, -53, 1]], ![![20, 11, -1]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB278I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB278I2 : PrimesBelowBoundCertificateInterval O 79 137 278 where
  m := 11
  g := ![2, 3, 2, 1, 1, 2, 1, 3, 2, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB278I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
    · exact ![137, 137, 137]
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
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
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I89N0, I89N1, I89N2, I97N1, I107N1, I113N0, I113N1, I113N2, I127N1, I131N0, I131N1, I131N2, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N1], [], [], [I107N1], [], [I113N0, I113N1, I113N2], [I127N1], [I131N0, I131N1, I131N2], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
