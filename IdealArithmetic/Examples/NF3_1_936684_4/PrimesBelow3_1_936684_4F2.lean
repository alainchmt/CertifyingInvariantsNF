
import IdealArithmetic.Examples.NF3_1_936684_4.RI3_1_936684_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-57, -44, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-57, -44, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![26, 39, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-57, -44, 1], ![350, 27, -44], ![-15400, -3346, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -39, 83]], ![![-1, -1, 1], ![18, 21, -44], ![-194, -53, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [20, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 82], [0, 1]]
 g := ![![[30, 23], [23, 77], [21], [1], [43, 29], [1]], ![[8, 60], [54, 6], [21], [1], [73, 54], [1]]]
 h' := ![![[64, 82], [38, 40], [5, 49], [50, 41], [53, 82], [63, 64], [0, 1]], ![[0, 1], [25, 43], [70, 34], [18, 42], [72, 1], [9, 19], [64, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [2, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [20, 19, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![720, 499, 66]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -25, 66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-39, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-39, 1, 0]] 
 ![![83, 0, 0], ![44, 1, 0], ![56, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-39, 1, 0], ![0, -39, 1], ![350, 84, -39]]]
  hmulB := by decide  
  f := ![![![3043, -78, 0], ![6474, 0, 0]], ![![1600, -41, 0], ![3404, 0, 0]], ![![2086, -53, 0], ![4438, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 83, 0], ![-56, 0, 83]], ![![-1, 1, 0], ![20, -39, 1], ![-14, 84, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-57, -44, 1]] ![![83, 0, 0], ![-39, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3237, 83, 0]], ![![-4731, -3652, 83], ![2573, 1743, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-39, 1, 0]]], ![![![-57, -44, 1]], ![![31, 21, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-83, -1, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-83, -1, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![6, 88, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-83, -1, 1], ![350, 1, -1], ![-350, 266, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -88, 89]], ![![-1, -1, 1], ![4, 1, -1], ![-4, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [81, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 88], [0, 1]]
 g := ![![[51, 11], [73], [81], [11, 32], [19, 34], [1]], ![[0, 78], [73], [81], [73, 57], [7, 55], [1]]]
 h' := ![![[52, 88], [14, 10], [26, 47], [88, 80], [63, 78], [8, 52], [0, 1]], ![[0, 1], [0, 79], [67, 42], [65, 9], [25, 11], [42, 37], [52, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [79, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [81, 37, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4155, 2072, 865]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-105, -832, 865]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![1, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![1, 1, 0]] 
 ![![89, 0, 0], ![1, 1, 0], ![88, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![1, 1, 0], ![0, 1, 1], ![350, 84, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![89, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![88, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 89, 0], ![-88, 0, 89]], ![![0, 1, 0], ![-1, 1, 1], ![2, 84, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-83, -1, 1]] ![![89, 0, 0], ![1, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![89, 89, 0]], ![![-7387, -89, 89], ![267, 0, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![1, 1, 0]]], ![![![-83, -1, 1]], ![![3, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-12, -13, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-12, -13, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![85, 84, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-12, -13, 1], ![350, 72, -13], ![-4550, -742, 72]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -84, 97]], ![![-1, -1, 1], ![15, 12, -13], ![-110, -70, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [93, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 96], [0, 1]]
 g := ![![[20, 24], [35], [35], [73], [4], [80, 1]], ![[0, 73], [35], [35], [73], [4], [63, 96]]]
 h' := ![![[80, 96], [7, 86], [35, 61], [63, 36], [81, 48], [29, 2], [0, 1]], ![[0, 1], [0, 11], [65, 36], [33, 61], [41, 49], [92, 95], [80, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [75, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [93, 17, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2401, 71, 196]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-147, -169, 196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![13, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![13, 1, 0]] 
 ![![97, 0, 0], ![13, 1, 0], ![25, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![13, 1, 0], ![0, 13, 1], ![350, 84, 13]]]
  hmulB := by decide  
  f := ![![![170, 13, 0], ![-1261, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![28, 2, 0], ![-207, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 97, 0], ![-25, 0, 97]], ![![0, 1, 0], ![-2, 13, 1], ![-11, 84, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-12, -13, 1]] ![![97, 0, 0], ![13, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![1261, 97, 0]], ![![-1164, -1261, 97], ![194, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![13, 1, 0]]], ![![![-12, -13, 1]], ![![2, -1, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-89, -55, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-89, -55, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![12, 46, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-89, -55, 1], ![350, -5, -55], ![-19250, -4270, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -46, 101]], ![![-1, -1, 1], ![10, 25, -55], ![-190, -40, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [77, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 100], [0, 1]]
 g := ![![[6, 21], [92], [88, 76], [87], [96], [43, 1]], ![[0, 80], [92], [23, 25], [87], [96], [86, 100]]]
 h' := ![![[43, 100], [67, 83], [92, 30], [52, 51], [61, 84], [22, 55], [0, 1]], ![[0, 1], [0, 18], [69, 71], [23, 50], [37, 17], [64, 46], [43, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [91, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [77, 58, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1964, 2706, 577]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88, -236, 577]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-46, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-46, 1, 0]] 
 ![![101, 0, 0], ![55, 1, 0], ![5, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-46, 1, 0], ![0, -46, 1], ![350, 84, -46]]]
  hmulB := by decide  
  f := ![![![875, -19, 0], ![1919, 0, 0]], ![![553, -12, 0], ![1213, 0, 0]], ![![67, -1, 0], ![147, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 101, 0], ![-5, 0, 101]], ![![-1, 1, 0], ![25, -46, 1], ![-40, 84, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-89, -55, 1]] ![![101, 0, 0], ![-46, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4646, 101, 0]], ![![-8989, -5555, 101], ![4444, 2525, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-46, 1, 0]]], ![![![-89, -55, 1]], ![![44, 25, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-54, -37, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-54, -37, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![49, 66, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-54, -37, 1], ![350, 30, -37], ![-12950, -2758, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -66, 103]], ![![-1, -1, 1], ![21, 24, -37], ![-140, -46, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [40, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 102], [0, 1]]
 g := ![![[43, 49], [29, 72], [96, 49], [34], [36], [31, 1]], ![[17, 54], [98, 31], [70, 54], [34], [36], [62, 102]]]
 h' := ![![[31, 102], [76, 96], [74, 22], [97, 7], [18, 31], [99, 97], [0, 1]], ![[0, 1], [65, 7], [35, 81], [5, 96], [52, 72], [16, 6], [31, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [30, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [40, 72, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![740, 446, 13]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -4, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![37, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![37, 1, 0]] 
 ![![103, 0, 0], ![37, 1, 0], ![73, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![37, 1, 0], ![0, 37, 1], ![350, 84, 37]]]
  hmulB := by decide  
  f := ![![![1074, 29, 0], ![-2987, 0, 0]], ![![370, 10, 0], ![-1029, 0, 0]], ![![754, 20, 0], ![-2097, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 103, 0], ![-73, 0, 103]], ![![0, 1, 0], ![-14, 37, 1], ![-53, 84, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-54, -37, 1]] ![![103, 0, 0], ![37, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3811, 103, 0]], ![![-5562, -3811, 103], ![-1648, -1339, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![37, 1, 0]]], ![![![-54, -37, 1]], ![![-16, -13, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![12, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![12, 1, 0]] 
 ![![107, 0, 0], ![12, 1, 0], ![70, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![12, 1, 0], ![0, 12, 1], ![350, 84, 12]]]
  hmulB := by decide  
  f := ![![![85, 7, 0], ![-749, 0, 0]], ![![-12, -1, 0], ![108, 0, 0]], ![![50, 4, 0], ![-440, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 107, 0], ![-70, 0, 107]], ![![0, 1, 0], ![-2, 12, 1], ![-14, 84, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![40, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![40, 1, 0]] 
 ![![107, 0, 0], ![40, 1, 0], ![5, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![40, 1, 0], ![0, 40, 1], ![350, 84, 40]]]
  hmulB := by decide  
  f := ![![![1481, 37, 0], ![-3959, 0, 0]], ![![520, 13, 0], ![-1390, 0, 0]], ![![55, 1, 0], ![-147, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 107, 0], ![-5, 0, 107]], ![![0, 1, 0], ![-15, 40, 1], ![-30, 84, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-52, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-52, 1, 0]] 
 ![![107, 0, 0], ![55, 1, 0], ![78, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-52, 1, 0], ![0, -52, 1], ![350, 84, -52]]]
  hmulB := by decide  
  f := ![![![2861, -55, 0], ![5885, 0, 0]], ![![1457, -28, 0], ![2997, 0, 0]], ![![2106, -40, 0], ![4332, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 107, 0], ![-78, 0, 107]], ![![-1, 1, 0], ![26, -52, 1], ![-2, 84, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![12, 1, 0]] ![![107, 0, 0], ![40, 1, 0]]
  ![![107, 0, 0], ![-55, -55, 1]] where
 M := ![![![11449, 0, 0], ![4280, 107, 0]], ![![1284, 107, 0], ![480, 52, 1]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![40, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-55, -55, 1]] ![![107, 0, 0], ![-52, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-5564, 107, 0]], ![![-5885, -5885, 107], ![3210, 2889, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-52, 1, 0]]], ![![![-55, -55, 1]], ![![30, 27, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-62, 26, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-62, 26, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![47, 26, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-62, 26, 1], ![350, 22, 26], ![9100, 2534, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -26, 109]], ![![-1, 0, 1], ![-8, -6, 26], ![74, 18, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [80, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 108], [0, 1]]
 g := ![![[67, 15], [100], [81, 48], [14, 31], [45], [90, 1]], ![[0, 94], [100], [41, 61], [79, 78], [45], [71, 108]]]
 h' := ![![[90, 108], [69, 61], [60, 99], [79, 87], [33, 24], [103, 63], [0, 1]], ![[0, 1], [0, 48], [32, 10], [61, 22], [13, 85], [105, 46], [90, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [66, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [80, 19, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13400, 3941, 466]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-78, -75, 466]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-26, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-26, 1, 0]] 
 ![![109, 0, 0], ![83, 1, 0], ![87, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-26, 1, 0], ![0, -26, 1], ![350, 84, -26]]]
  hmulB := by decide  
  f := ![![![755, -29, 0], ![3161, 0, 0]], ![![573, -22, 0], ![2399, 0, 0]], ![![605, -23, 0], ![2533, 1, 0]]]
  g := ![![![1, 0, 0], ![-83, 109, 0], ![-87, 0, 109]], ![![-1, 1, 0], ![19, -26, 1], ![-40, 84, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-62, 26, 1]] ![![109, 0, 0], ![-26, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2834, 109, 0]], ![![-6758, 2834, 109], ![1962, -654, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-26, 1, 0]]], ![![![-62, 26, 1]], ![![18, -6, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-100, -60, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-100, -60, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![13, 53, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-100, -60, 1], ![350, -16, -60], ![-21000, -4690, -16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -53, 113]], ![![-1, -1, 1], ![10, 28, -60], ![-184, -34, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [98, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 112], [0, 1]]
 g := ![![[90, 15], [9], [81], [4], [74, 2], [107, 1]], ![[0, 98], [9], [81], [4], [62, 111], [101, 112]]]
 h' := ![![[107, 112], [75, 69], [36, 110], [8, 9], [93, 2], [23, 51], [0, 1]], ![[0, 1], [0, 44], [54, 3], [67, 104], [81, 111], [56, 62], [107, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [7, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [98, 6, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2007, -142, 89]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -43, 89]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-53, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-53, 1, 0]] 
 ![![113, 0, 0], ![60, 1, 0], ![16, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-53, 1, 0], ![0, -53, 1], ![350, 84, -53]]]
  hmulB := by decide  
  f := ![![![2651, -50, 0], ![5650, 0, 0]], ![![1432, -27, 0], ![3052, 0, 0]], ![![396, -7, 0], ![844, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 113, 0], ![-16, 0, 113]], ![![-1, 1, 0], ![28, -53, 1], ![-34, 84, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-100, -60, 1]] ![![113, 0, 0], ![-53, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5989, 113, 0]], ![![-11300, -6780, 113], ![5650, 3164, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-53, 1, 0]]], ![![![-100, -60, 1]], ![![50, 28, -1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-52, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-52, 1, 0]] 
 ![![127, 0, 0], ![75, 1, 0], ![90, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-52, 1, 0], ![0, -52, 1], ![350, 84, -52]]]
  hmulB := by decide  
  f := ![![![1873, -36, 0], ![4572, 0, 0]], ![![1093, -21, 0], ![2668, 0, 0]], ![![1374, -26, 0], ![3354, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 127, 0], ![-90, 0, 127]], ![![-1, 1, 0], ![30, -52, 1], ![-10, 84, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-45, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-45, 1, 0]] 
 ![![127, 0, 0], ![82, 1, 0], ![7, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-45, 1, 0], ![0, -45, 1], ![350, 84, -45]]]
  hmulB := by decide  
  f := ![![![3061, -68, 0], ![8636, 0, 0]], ![![2026, -45, 0], ![5716, 0, 0]], ![![241, -5, 0], ![680, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 127, 0], ![-7, 0, 127]], ![![-1, 1, 0], ![29, -45, 1], ![-49, 84, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-30, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-30, 1, 0]] 
 ![![127, 0, 0], ![97, 1, 0], ![116, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-30, 1, 0], ![0, -30, 1], ![350, 84, -30]]]
  hmulB := by decide  
  f := ![![![2581, -86, 0], ![10922, 0, 0]], ![![2011, -67, 0], ![8510, 0, 0]], ![![2408, -80, 0], ![10190, 1, 0]]]
  g := ![![![1, 0, 0], ![-97, 127, 0], ![-116, 0, 127]], ![![-1, 1, 0], ![22, -30, 1], ![-34, 84, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-52, 1, 0]] ![![127, 0, 0], ![-45, 1, 0]]
  ![![127, 0, 0], ![-73, 30, 1]] where
 M := ![![![16129, 0, 0], ![-5715, 127, 0]], ![![-6604, 127, 0], ![2340, -97, 1]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![28, -29, -1], ![127, 0, 0]]], ![![![21, -29, -1], ![127, 0, 0]], ![![19, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-73, 30, 1]] ![![127, 0, 0], ![-30, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3810, 127, 0]], ![![-9271, 3810, 127], ![2540, -889, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-30, 1, 0]]], ![![![-73, 30, 1]], ![![20, -7, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-92, 56, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-92, 56, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![39, 56, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-92, 56, 1], ![350, -8, 56], ![19600, 5054, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -56, 131]], ![![-1, 0, 1], ![-14, -24, 56], ![152, 42, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [52, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 130], [0, 1]]
 g := ![![[85, 63], [122, 112], [15], [21], [25], [108], [1]], ![[0, 68], [0, 19], [15], [21], [25], [108], [1]]]
 h' := ![![[34, 130], [75, 71], [31, 80], [5, 88], [124, 26], [101, 5], [79, 34], [0, 1]], ![[0, 1], [0, 60], [0, 51], [115, 43], [91, 105], [9, 126], [56, 97], [34, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [18, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [52, 97, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1452, 1833, 531]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-147, -213, 531]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-56, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-56, 1, 0]] 
 ![![131, 0, 0], ![75, 1, 0], ![8, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-56, 1, 0], ![0, -56, 1], ![350, 84, -56]]]
  hmulB := by decide  
  f := ![![![7281, -130, 0], ![17030, 0, 0]], ![![4201, -75, 0], ![9826, 0, 0]], ![![472, -8, 0], ![1104, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 131, 0], ![-8, 0, 131]], ![![-1, 1, 0], ![32, -56, 1], ![-42, 84, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-92, 56, 1]] ![![131, 0, 0], ![-56, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-7336, 131, 0]], ![![-12052, 7336, 131], ![5502, -3144, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-56, 1, 0]]], ![![![-92, 56, 1]], ![![42, -24, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![14, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![14, 1, 0]] 
 ![![137, 0, 0], ![14, 1, 0], ![78, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![14, 1, 0], ![0, 14, 1], ![350, 84, 14]]]
  hmulB := by decide  
  f := ![![![631, 45, 0], ![-6165, 0, 0]], ![![42, 3, 0], ![-410, 0, 0]], ![![338, 24, 0], ![-3302, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 137, 0], ![-78, 0, 137]], ![![0, 1, 0], ![-2, 14, 1], ![-14, 84, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![31, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![31, 1, 0]] 
 ![![137, 0, 0], ![31, 1, 0], ![135, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![31, 1, 0], ![0, 31, 1], ![350, 84, 31]]]
  hmulB := by decide  
  f := ![![![1861, 60, 0], ![-8220, 0, 0]], ![![403, 13, 0], ![-1780, 0, 0]], ![![1837, 59, 0], ![-8114, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 137, 0], ![-135, 0, 137]], ![![0, 1, 0], ![-8, 31, 1], ![-47, 84, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-45, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-45, 1, 0]] 
 ![![137, 0, 0], ![92, 1, 0], ![30, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-45, 1, 0], ![0, -45, 1], ![350, 84, -45]]]
  hmulB := by decide  
  f := ![![![4006, -89, 0], ![12193, 0, 0]], ![![2656, -59, 0], ![8084, 0, 0]], ![![870, -19, 0], ![2648, 1, 0]]]
  g := ![![![1, 0, 0], ![-92, 137, 0], ![-30, 0, 137]], ![![-1, 1, 0], ![30, -45, 1], ![-44, 84, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![14, 1, 0]] ![![137, 0, 0], ![31, 1, 0]]
  ![![137, 0, 0], ![-114, 45, 1]] where
 M := ![![![18769, 0, 0], ![4247, 137, 0]], ![![1918, 137, 0], ![434, 45, 1]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![31, 1, 0], ![0, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-114, 45, 1]] ![![137, 0, 0], ![-45, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6165, 137, 0]], ![![-15618, 6165, 137], ![5480, -2055, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-45, 1, 0]]], ![![![-114, 45, 1]], ![![40, -15, 0]]]]
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


lemma PB274I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB274I2 : PrimesBelowBoundCertificateInterval O 79 137 274 where
  m := 11
  g := ![2, 2, 2, 2, 2, 3, 2, 2, 3, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB274I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
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
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I89N1, I97N1, I101N1, I103N1, I107N0, I107N1, I107N2, I109N1, I113N1, I127N0, I127N1, I127N2, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
