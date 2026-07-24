
import IdealArithmetic.Examples.NF3_1_561295_1.RI3_1_561295_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-26, -16, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-26, -16, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![57, 67, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-26, -16, 1], ![-95, -1, -140], ![1200, 349, -110]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -67, 83]], ![![-1, -1, 1], ![95, 113, -140], ![90, 93, -110]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [26, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 82], [0, 1]]
 g := ![![[22, 16], [5, 64], [40], [36], [12, 81], [1]], ![[0, 67], [0, 19], [40], [36], [77, 2], [1]]]
 h' := ![![[9, 82], [36, 79], [72, 75], [45, 66], [20, 6], [57, 9], [0, 1]], ![[0, 1], [0, 4], [0, 8], [58, 17], [74, 77], [55, 74], [9, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [79, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [26, 74, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2383, -579, -2376]
  a := ![-1, 2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1603, 1911, -2376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-26, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-26, 1, 0]] 
 ![![83, 0, 0], ![57, 1, 0], ![27, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-26, 1, 0], ![1, -29, 9], ![-79, -23, -22]]]
  hmulB := by decide  
  f := ![![![2794, -99069, 30753], ![-1992, -283611, 0]], ![![1905, -68017, 21114], ![-1410, -194718, 0]], ![![902, -32227, 10004], ![-670, -92259, 0]]]
  g := ![![![1, 0, 0], ![-57, 83, 0], ![-27, 0, 83]], ![![-1, 1, 0], ![17, -29, 9], ![22, -23, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-26, -16, 1]] ![![83, 0, 0], ![-26, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2158, 83, 0]], ![![-2158, -1328, 83], ![581, 415, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-26, 1, 0]]], ![![![-26, -16, 1]], ![![7, 5, -2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-21, 7, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-21, 7, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![68, 7, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-21, 7, 1], ![-72, -65, 67], ![-617, -180, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -7, 89]], ![![-1, 0, 1], ![-52, -6, 67], ![3, -1, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [59, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 88], [0, 1]]
 g := ![![[84, 10], [25], [36], [6, 47], [47, 72], [1]], ![[8, 79], [25], [36], [76, 42], [16, 17], [1]]]
 h' := ![![[28, 88], [27, 59], [16, 5], [2, 83], [75, 15], [30, 28], [0, 1]], ![[0, 1], [77, 30], [67, 84], [12, 6], [50, 74], [13, 61], [28, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [2, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [59, 61, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4180, 179, -6624]
  a := ![2, -9, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5108, 523, -6624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![22, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![22, 1, 0]] 
 ![![89, 0, 0], ![22, 1, 0], ![13, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![22, 1, 0], ![1, 19, 9], ![-79, -23, 26]]]
  hmulB := by decide  
  f := ![![![-4401, -93646, -44370], ![-2136, 438770, 0]], ![![-1108, -23137, -10962], ![-444, 108402, 0]], ![![-651, -13679, -6481], ![-279, 64090, 0]]]
  g := ![![![1, 0, 0], ![-22, 89, 0], ![-13, 0, 89]], ![![0, 1, 0], ![-6, 19, 9], ![1, -23, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-21, 7, 1]] ![![89, 0, 0], ![22, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![1958, 89, 0]], ![![-1869, 623, 89], ![-534, 89, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![22, 1, 0]]], ![![![-21, 7, 1]], ![![-6, 1, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![97, 0, 0], ![3, 1, 0], ![54, 0, 1]] where
  M :=![![![3, 1, 0], ![1, 0, 9], ![-79, -23, 7]]]
  hmulB := by decide  
  f := ![![![-207, 7, -9]], ![![1, 0, 0]], ![![-115, 4, -5]]]
  g := ![![![0, 1, 0], ![-5, 0, 9], ![-4, -23, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![32, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![32, 1, 0]] 
 ![![97, 0, 0], ![32, 1, 0], ![91, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![32, 1, 0], ![1, 29, 9], ![-79, -23, 36]]]
  hmulB := by decide  
  f := ![![![-249, -8177, -2538], ![-97, 27354, 0]], ![![-93, -2697, -837], ![1, 9021, 0]], ![![-227, -7671, -2381], ![-111, 25662, 0]]]
  g := ![![![1, 0, 0], ![-32, 97, 0], ![-91, 0, 97]], ![![0, 1, 0], ![-18, 29, 9], ![-27, -23, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-36, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-36, 1, 0]] 
 ![![97, 0, 0], ![61, 1, 0], ![92, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-36, 1, 0], ![1, -39, 9], ![-79, -23, -32]]]
  hmulB := by decide  
  f := ![![![-1524, 80520, -18585], ![1455, 200305, 0]], ![![-937, 50612, -11682], ![971, 125906, 0]], ![![-1428, 76369, -17627], ![1427, 189980, 0]]]
  g := ![![![1, 0, 0], ![-61, 97, 0], ![-92, 0, 97]], ![![-1, 1, 0], ![16, -39, 9], ![44, -23, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![3, 1, 0]] ![![97, 0, 0], ![32, 1, 0]]
  ![![97, 0, 0], ![0, -18, 1]] where
 M := ![![![291, 97, 0], ![97, 32, 9]]]
 hmul := by decide  
 g := ![![![![3, 1, 0], ![0, 0, 0]], ![![1, 2, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![0, -18, 1]] ![![97, 0, 0], ![-36, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3492, 97, 0]], ![![0, -1746, 97], ![-97, 679, -194]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-36, 1, 0]]], ![![![0, -18, 1]], ![![-1, 7, -2]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-12, -34, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-12, -34, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![89, 67, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-12, -34, 1], ![-113, 67, -302], ![2622, 763, -168]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-89, -67, 101]], ![![-1, -1, 1], ![265, 201, -302], ![174, 119, -168]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [89, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 100], [0, 1]]
 g := ![![[75, 71], [88], [63, 78], [65], [64], [92, 1]], ![[42, 30], [88], [68, 23], [65], [64], [83, 100]]]
 h' := ![![[92, 100], [23, 77], [49, 47], [53, 52], [9, 41], [94, 93], [0, 1]], ![[0, 1], [37, 24], [30, 54], [90, 49], [44, 60], [65, 8], [92, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [61, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [89, 9, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6485095, -2062111, -5759139]
  a := ![-65, 132, -521]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5010676, 3800002, -5759139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-1, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-1, 1, 0]] 
 ![![101, 0, 0], ![100, 1, 0], ![67, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-1, 1, 0], ![1, -4, 9], ![-79, -23, 3]]]
  hmulB := by decide  
  f := ![![![6698, -26797, 60300], ![-303, -676700, 0]], ![![6631, -26529, 59697], ![-302, -669933, 0]], ![![4444, -17777, 40001], ![-123, -448900, 0]]]
  g := ![![![1, 0, 0], ![-100, 101, 0], ![-67, 0, 101]], ![![-1, 1, 0], ![-2, -4, 9], ![20, -23, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-12, -34, 1]] ![![101, 0, 0], ![-1, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-101, 101, 0]], ![![-1212, -3434, 101], ![-101, 101, -303]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-1, 1, 0]]], ![![![-12, -34, 1]], ![![-1, 1, -3]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [13, 49, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 57, 94], [52, 45, 9], [0, 1]]
 g := ![![[44, 84, 68], [24, 64, 83], [2, 75, 33], [66, 16], [56, 25], [1]], ![[37, 35, 6, 84], [11, 31, 44, 94], [84, 7, 7, 99], [67, 100], [19, 100], [38, 34, 89, 95]], ![[7, 85, 16, 46], [18, 17, 100, 38], [27, 51, 51, 72], [3, 36], [5, 25], [37, 84, 80, 8]]]
 h' := ![![[46, 57, 94], [100, 7, 45], [77, 98, 86], [48, 18, 41], [59, 59, 99], [90, 54, 98], [0, 1]], ![[52, 45, 9], [9, 42, 5], [90, 49, 1], [90, 69, 35], [31, 85, 10], [22, 62, 10], [46, 57, 94]], ![[0, 1], [64, 54, 53], [94, 59, 16], [13, 16, 27], [84, 62, 97], [47, 90, 98], [52, 45, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 42], []]
 b := ![[], [25, 0, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [13, 49, 5, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4680320, -1407392, -3249547]
  a := ![-2, 8, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45440, -13664, -31549]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![13, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![13, 1, 0]] 
 ![![107, 0, 0], ![13, 1, 0], ![57, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![13, 1, 0], ![1, 10, 9], ![-79, -23, 17]]]
  hmulB := by decide  
  f := ![![![-461, -4620, -4158], ![0, 49434, 0]], ![![-56, -560, -504], ![1, 5992, 0]], ![![-244, -2461, -2215], ![-13, 26334, 0]]]
  g := ![![![1, 0, 0], ![-13, 107, 0], ![-57, 0, 107]], ![![0, 1, 0], ![-6, 10, 9], ![-7, -23, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![16, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![16, 1, 0]] 
 ![![107, 0, 0], ![16, 1, 0], ![84, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![16, 1, 0], ![1, 13, 9], ![-79, -23, 20]]]
  hmulB := by decide  
  f := ![![![-7857, -106294, -73602], ![-2140, 875046, 0]], ![![-1174, -15883, -10998], ![-320, 130754, 0]], ![![-6172, -83446, -57781], ![-1654, 686952, 0]]]
  g := ![![![1, 0, 0], ![-16, 107, 0], ![-84, 0, 107]], ![![0, 1, 0], ![-9, 13, 9], ![-13, -23, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-30, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-30, 1, 0]] 
 ![![107, 0, 0], ![77, 1, 0], ![9, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-30, 1, 0], ![1, -33, 9], ![-79, -23, -26]]]
  hmulB := by decide  
  f := ![![![2801, -108224, 29520], ![-1712, -350960, 0]], ![![2001, -77868, 21240], ![-1283, -252520, 0]], ![![237, -9103, 2483], ![-139, -29520, 0]]]
  g := ![![![1, 0, 0], ![-77, 107, 0], ![-9, 0, 107]], ![![-1, 1, 0], ![23, -33, 9], ![18, -23, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![13, 1, 0]] ![![107, 0, 0], ![16, 1, 0]]
  ![![107, 0, 0], ![47, -9, 1]] where
 M := ![![![11449, 0, 0], ![1712, 107, 0]], ![![1391, 107, 0], ![209, 26, 9]]]
 hmul := by decide  
 g := ![![![![60, 9, -1], ![107, 0, 0]], ![![-31, 10, -1], ![107, 0, 0]]], ![![![-34, 10, -1], ![107, 0, 0]], ![![-2, 1, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![47, -9, 1]] ![![107, 0, 0], ![-30, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3210, 107, 0]], ![![5029, -963, 107], ![-1498, 321, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-30, 1, 0]]], ![![![47, -9, 1]], ![![-14, 3, -1]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![30, -21, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![30, -21, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![30, 88, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![30, -21, 1], ![-100, 70, -185], ![1595, 464, -74]]]
  hmulB := by decide  
  f := ![![![-29, 21, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -88, 109]], ![![0, -1, 1], ![50, 150, -185], ![35, 64, -74]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [39, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 108], [0, 1]]
 g := ![![[34, 27], [61], [97, 97], [8, 43], [20], [91, 1]], ![[93, 82], [61], [95, 12], [106, 66], [20], [73, 108]]]
 h' := ![![[91, 108], [62, 71], [32, 37], [15, 36], [107, 77], [48, 67], [0, 1]], ![[0, 1], [92, 38], [20, 72], [21, 73], [29, 32], [41, 42], [91, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [105, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [39, 18, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2314, -691, -1872]
  a := ![-1, 2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![494, 1505, -1872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-33, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-33, 1, 0]] 
 ![![109, 0, 0], ![76, 1, 0], ![74, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-33, 1, 0], ![1, -36, 9], ![-79, -23, -29]]]
  hmulB := by decide  
  f := ![![![-2144, 93838, -23463], ![1526, 284163, 0]], ![![-1486, 65402, -16353], ![1091, 198053, 0]], ![![-1438, 63706, -15929], ![1094, 192918, 0]]]
  g := ![![![1, 0, 0], ![-76, 109, 0], ![-74, 0, 109]], ![![-1, 1, 0], ![19, -36, 9], ![35, -23, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![30, -21, 1]] ![![109, 0, 0], ![-33, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3597, 109, 0]], ![![3270, -2289, 109], ![-1090, 763, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-33, 1, 0]]], ![![![30, -21, 1]], ![![-10, 7, -2]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![66, 16, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![66, 16, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![66, 16, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![66, 16, 1], ![-63, -5, 148], ![-1328, -387, 110]]]
  hmulB := by decide  
  f := ![![![-65, -16, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -16, 113]], ![![0, 0, 1], ![-87, -21, 148], ![-76, -19, 110]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [102, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 112], [0, 1]]
 g := ![![[111, 41], [53], [95], [51], [95, 41], [91, 1]], ![[0, 72], [53], [95], [51], [97, 72], [69, 112]]]
 h' := ![![[91, 112], [71, 70], [36, 36], [102, 78], [28, 86], [97, 43], [0, 1]], ![[0, 1], [0, 43], [35, 77], [81, 35], [57, 27], [55, 70], [91, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [80, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [102, 22, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55754, -16663, -1670]
  a := ![2, 14, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![482, 89, -1670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-35, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-35, 1, 0]] 
 ![![113, 0, 0], ![78, 1, 0], ![3, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-35, 1, 0], ![1, -38, 9], ![-79, -23, -31]]]
  hmulB := by decide  
  f := ![![![-1602, 75533, -17892], ![1243, 224644, 0]], ![![-1091, 52128, -12348], ![905, 155036, 0]], ![![-32, 2005, -475], ![67, 5964, 0]]]
  g := ![![![1, 0, 0], ![-78, 113, 0], ![-3, 0, 113]], ![![-1, 1, 0], ![26, -38, 9], ![16, -23, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![66, 16, 1]] ![![113, 0, 0], ![-35, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-3955, 113, 0]], ![![7458, 1808, 113], ![-2373, -565, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-35, 1, 0]]], ![![![66, 16, 1]], ![![-21, -5, 1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![68, -33, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![68, -33, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![68, 94, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![68, -33, 1], ![-112, 144, -293], ![2543, 740, -84]]]
  hmulB := by decide  
  f := ![![![-67, 33, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -94, 127]], ![![0, -1, 1], ![156, 218, -293], ![65, 68, -84]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [47, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 126], [0, 1]]
 g := ![![[0, 100], [0, 16], [0, 19], [0, 32], [0, 50], [0, 1]], ![[0, 27], [0, 111], [0, 108], [0, 95], [0, 77], [0, 126]]]
 h' := ![![[0, 126], [0, 10], [0, 123], [0, 20], [0, 63], [0, 80], [0, 1]], ![[0, 1], [0, 117], [0, 4], [0, 107], [0, 64], [0, 47], [0, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [0, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [47, 0, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3107, 541, -6224]
  a := ![-2, 8, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3357, 4611, -6224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![39, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![39, 1, 0]] 
 ![![127, 0, 0], ![39, 1, 0], ![84, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![39, 1, 0], ![1, 36, 9], ![-79, -23, 43]]]
  hmulB := by decide  
  f := ![![![-5444, -233901, -58482], ![-3429, 825246, 0]], ![![-1683, -71812, -17955], ![-1015, 253365, 0]], ![![-3594, -154706, -38681], ![-2290, 545832, 0]]]
  g := ![![![1, 0, 0], ![-39, 127, 0], ![-84, 0, 127]], ![![0, 1, 0], ![-17, 36, 9], ![-22, -23, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![68, -33, 1]] ![![127, 0, 0], ![39, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![4953, 127, 0]], ![![8636, -4191, 127], ![2540, -1143, -254]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![39, 1, 0]]], ![![![68, -33, 1]], ![![20, -9, -2]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![19, -51, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![19, -51, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![19, 80, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![19, -51, 1], ![-130, 149, -455], ![3965, 1154, -205]]]
  hmulB := by decide  
  f := ![![![-18, 51, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -80, 131]], ![![0, -1, 1], ![65, 279, -455], ![60, 134, -205]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [33, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 130], [0, 1]]
 g := ![![[60, 4], [120, 125], [62], [109], [74], [94], [1]], ![[0, 127], [79, 6], [62], [109], [74], [94], [1]]]
 h' := ![![[116, 130], [101, 129], [40, 115], [120, 18], [124, 41], [83, 104], [98, 116], [0, 1]], ![[0, 1], [0, 2], [18, 16], [112, 113], [33, 90], [95, 27], [61, 15], [116, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [59, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [33, 15, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6424, -2186, -6633]
  a := ![2, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![913, 4034, -6633]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![62, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![62, 1, 0]] 
 ![![131, 0, 0], ![62, 1, 0], ![74, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![62, 1, 0], ![1, 59, 9], ![-79, -23, 66]]]
  hmulB := by decide  
  f := ![![![-6433, -588055, -89712], ![-7467, 1305808, 0]], ![![-3043, -278276, -42453], ![-3536, 617927, 0]], ![![-3650, -332184, -50677], ![-4184, 737632, 0]]]
  g := ![![![1, 0, 0], ![-62, 131, 0], ![-74, 0, 131]], ![![0, 1, 0], ![-33, 59, 9], ![-27, -23, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![19, -51, 1]] ![![131, 0, 0], ![62, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![8122, 131, 0]], ![![2489, -6681, 131], ![1048, -3013, -393]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![62, 1, 0]]], ![![![19, -51, 1]], ![![8, -23, -3]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![59, -51, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![59, -51, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![59, 86, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![59, -51, 1], ![-130, 189, -455], ![3965, 1154, -165]]]
  hmulB := by decide  
  f := ![![![-58, 51, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -86, 137]], ![![0, -1, 1], ![195, 287, -455], ![100, 112, -165]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [44, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 136], [0, 1]]
 g := ![![[76, 109], [109], [9], [57, 8], [59], [122], [1]], ![[0, 28], [109], [9], [20, 129], [59], [122], [1]]]
 h' := ![![[81, 136], [3, 71], [135, 66], [95, 3], [56, 62], [130, 14], [93, 81], [0, 1]], ![[0, 1], [0, 66], [1, 71], [64, 134], [9, 75], [31, 123], [78, 56], [81, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [67, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [44, 56, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39311, -11840, -36140]
  a := ![-5, 10, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15277, 22600, -36140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![44, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![44, 1, 0]] 
 ![![137, 0, 0], ![44, 1, 0], ![28, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![44, 1, 0], ![1, 41, 9], ![-79, -23, 48]]]
  hmulB := by decide  
  f := ![![![-12074, -603255, -132435], ![-8220, 2015955, 0]], ![![-3889, -193706, -42525], ![-2602, 647325, 0]], ![![-2468, -123293, -27067], ![-1679, 412020, 0]]]
  g := ![![![1, 0, 0], ![-44, 137, 0], ![-28, 0, 137]], ![![0, 1, 0], ![-15, 41, 9], ![-3, -23, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![59, -51, 1]] ![![137, 0, 0], ![44, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![6028, 137, 0]], ![![8083, -6987, 137], ![2466, -2055, -411]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![44, 1, 0]]], ![![![59, -51, 1]], ![![18, -15, -3]]]]
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


lemma PB212I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB212I2 : PrimesBelowBoundCertificateInterval O 79 137 212 where
  m := 11
  g := ![2, 2, 3, 2, 1, 3, 2, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB212I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N1, I107N0, I107N1, I107N2, I109N1, I113N1, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
