
import IdealArithmetic.Examples.NF3_1_936091_2.RI3_1_936091_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4763, -112, -141]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-4763, -112, -141]] 
 ![![83, 0, 0], ![0, 83, 0], ![12, 42, 1]] where
  M :=![![![-4763, -112, -141], ![-14158, -334, -419], ![-4656, -111, -139]]]
  hmulB := by decide  
  f := ![![![1, -1, 2]], ![![206, -67, -7]], ![![102, -33, -4]]]
  g := ![![![-37, 70, -141], ![-110, 208, -419], ![-36, 69, -139]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [57, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 82], [0, 1]]
 g := ![![[79, 30], [81, 16], [61], [31], [22, 26], [1]], ![[30, 53], [77, 67], [61], [31], [57, 57], [1]]]
 h' := ![![[62, 82], [31, 69], [21, 4], [57, 12], [74, 60], [26, 62], [0, 1]], ![[0, 1], [76, 14], [20, 79], [54, 71], [59, 23], [52, 21], [62, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [49, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [57, 21, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1945, -372, -910]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![155, 456, -910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, -2]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1, 1, -2]] 
 ![![83, 0, 0], ![40, 1, 0], ![62, 0, 1]] where
  M :=![![![-1, 1, -2], ![-206, 67, 7], ![198, -87, 62]]]
  hmulB := by decide  
  f := ![![![4763, 112, 141]], ![![2466, 58, 73]], ![![3614, 85, 107]]]
  g := ![![![1, 1, -2], ![-40, 67, 7], ![-2, -87, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-4763, -112, -141]] ![![-1, 1, -2]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![23, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![23, 1, 0]] 
 ![![89, 0, 0], ![23, 1, 0], ![27, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![23, 1, 0], ![-2, 25, 5], ![102, -33, 22]]]
  hmulB := by decide  
  f := ![![![-2658, 34103, 6820], ![-267, -121396, 0]], ![![-704, 8800, 1760], ![1, -31328, 0]], ![![-826, 10345, 2069], ![-5, -36828, 0]]]
  g := ![![![1, 0, 0], ![-23, 89, 0], ![-27, 0, 89]], ![![0, 1, 0], ![-8, 25, 5], ![3, -33, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![24, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![24, 1, 0]] 
 ![![89, 0, 0], ![24, 1, 0], ![35, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![24, 1, 0], ![-2, 26, 5], ![102, -33, 23]]]
  hmulB := by decide  
  f := ![![![-415, 5408, 1040], ![0, -18512, 0]], ![![-112, 1456, 280], ![1, -4984, 0]], ![![-181, 2126, 409], ![66, -7280, 0]]]
  g := ![![![1, 0, 0], ![-24, 89, 0], ![-35, 0, 89]], ![![0, 1, 0], ![-9, 26, 5], ![1, -33, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![41, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![41, 1, 0]] 
 ![![89, 0, 0], ![41, 1, 0], ![3, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![41, 1, 0], ![-2, 43, 5], ![102, -33, 40]]]
  hmulB := by decide  
  f := ![![![9476, -222245, -25840], ![1869, 459952, 0]], ![![4350, -102350, -11900], ![891, 211820, 0]], ![![295, -7492, -871], ![116, 15504, 0]]]
  g := ![![![1, 0, 0], ![-41, 89, 0], ![-3, 0, 89]], ![![0, 1, 0], ![-20, 43, 5], ![15, -33, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![23, 1, 0]] ![![89, 0, 0], ![24, 1, 0]]
  ![![89, 0, 0], ![21, -8, 1]] where
 M := ![![![7921, 0, 0], ![2136, 89, 0]], ![![2047, 89, 0], ![550, 49, 5]]]
 hmul := by decide  
 g := ![![![![68, 8, -1], ![89, 0, 0]], ![![3, 9, -1], ![89, 0, 0]]], ![![![2, 9, -1], ![89, 0, 0]], ![![5, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![21, -8, 1]] ![![89, 0, 0], ![41, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3649, 89, 0]], ![![1869, -712, 89], ![979, -356, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![41, 1, 0]]], ![![![21, -8, 1]], ![![11, -4, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![37, -6, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![37, -6, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![37, 91, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![37, -6, 1], ![114, -8, -31], ![-660, 225, 11]]]
  hmulB := by decide  
  f := ![![![-36, 6, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -91, 97]], ![![0, -1, 1], ![13, 29, -31], ![-11, -8, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [3, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 96], [0, 1]]
 g := ![![[92, 65], [64], [81], [43], [8], [15, 1]], ![[0, 32], [64], [81], [43], [8], [30, 96]]]
 h' := ![![[15, 96], [50, 29], [57, 8], [3, 9], [61, 25], [52, 28], [0, 1]], ![[0, 1], [0, 68], [80, 89], [41, 88], [48, 72], [84, 69], [15, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [11, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [3, 82, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2406, 2456, -3772]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1414, 3564, -3772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![31, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![31, 1, 0]] 
 ![![97, 0, 0], ![31, 1, 0], ![86, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![31, 1, 0], ![-2, 33, 5], ![102, -33, 30]]]
  hmulB := by decide  
  f := ![![![5482, -95049, -14400], ![873, 279360, 0]], ![![1747, -30363, -4600], ![292, 89240, 0]], ![![4868, -84270, -12767], ![750, 247680, 0]]]
  g := ![![![1, 0, 0], ![-31, 97, 0], ![-86, 0, 97]], ![![0, 1, 0], ![-15, 33, 5], ![-15, -33, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![37, -6, 1]] ![![97, 0, 0], ![31, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3007, 97, 0]], ![![3589, -582, 97], ![1261, -194, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![31, 1, 0]]], ![![![37, -6, 1]], ![![13, -2, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [84, 40, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 51, 39], [59, 49, 62], [0, 1]]
 g := ![![[29, 91, 4], [27, 25], [28, 34, 70], [6, 80], [73, 88], [1]], ![[13, 69, 30, 44], [43, 92], [56, 42, 63, 57], [3, 14], [72, 84], [62, 30, 99, 32]], ![[93, 32, 72, 42], [54, 13], [46, 53, 0, 93], [16, 100], [22, 21], [99, 39, 85, 69]]]
 h' := ![![[89, 51, 39], [88, 100, 99], [72, 34, 96], [24, 16, 75], [15, 44, 79], [17, 61, 47], [0, 1]], ![[59, 49, 62], [8, 98, 65], [40, 36, 71], [50, 26, 57], [91, 45, 32], [33, 64, 36], [89, 51, 39]], ![[0, 1], [4, 4, 38], [46, 31, 35], [37, 59, 70], [13, 12, 91], [12, 77, 18], [59, 49, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 73], []]
 b := ![[], [6, 86, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [84, 40, 54, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17131632726, -3014165523, -8470249759]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![169620126, -29843223, -83863859]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [7, 96, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 38, 2], [25, 64, 101], [0, 1]]
 g := ![![[67, 92, 15], [33, 66, 33], [96, 60, 26], [67, 25], [53, 97], [1]], ![[78, 93, 40, 50], [100, 88, 71, 2], [100, 35, 35, 4], [11, 1], [47, 58], [17, 91, 97, 8]], ![[100, 98, 86, 75], [55, 70, 77, 77], [51, 62, 29, 20], [92, 16], [60, 36], [64, 65, 97, 95]]]
 h' := ![![[46, 38, 2], [78, 7, 85], [49, 24, 62], [9, 35, 51], [90, 6, 98], [96, 7, 71], [0, 1]], ![[25, 64, 101], [47, 17, 98], [80, 53, 102], [27, 27, 38], [102, 73, 1], [88, 98, 26], [46, 38, 2]], ![[0, 1], [50, 79, 23], [55, 26, 42], [0, 41, 14], [52, 24, 4], [36, 101, 6], [25, 64, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 10], []]
 b := ![[], [28, 98, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [7, 96, 32, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3094120, 1708770, -2027040]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30040, 16590, -19680]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [72, 84, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 41, 85], [10, 65, 22], [0, 1]]
 g := ![![[58, 38, 37], [63, 35, 16], [75, 27], [86, 81, 69], [23, 49], [1]], ![[93, 51, 57, 53], [43, 21, 0, 62], [93, 34], [20, 13, 94, 76], [95, 33], [90, 2, 83, 52]], ![[97, 63, 33, 80], [44, 58, 104, 72], [47, 87], [85, 34, 67, 18], [33, 10], [79, 19, 70, 55]]]
 h' := ![![[104, 41, 85], [65, 22, 12], [39, 84, 4], [14, 7, 53], [104, 2, 60], [35, 23, 7], [0, 1]], ![[10, 65, 22], [61, 52, 82], [93, 22, 17], [35, 46, 81], [87, 5, 4], [20, 37, 56], [104, 41, 85]], ![[0, 1], [79, 33, 13], [97, 1, 86], [48, 54, 80], [57, 100, 43], [20, 47, 44], [10, 65, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 99], []]
 b := ![[], [106, 103, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [72, 84, 100, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![397398, -57459, -219885]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3714, -537, -2055]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91593, 2155, 2712]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![91593, 2155, 2712]] 
 ![![109, 0, 0], ![12, 1, 0], ![75, 0, 1]] where
  M :=![![![91593, 2155, 2712], ![272314, 6407, 8063], ![89634, 2109, 2654]]]
  hmulB := by decide  
  f := ![![![-689, 238, -19]], ![![-98, 30, 9]], ![![-243, 87, -16]]]
  g := ![![![-1263, 2155, 2712], ![-3755, 6407, 8063], ![-1236, 2109, 2654]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![20, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![20, 1, 0]] 
 ![![109, 0, 0], ![20, 1, 0], ![86, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![20, 1, 0], ![-2, 22, 5], ![102, -33, 19]]]
  hmulB := by decide  
  f := ![![![3901, -43563, -9900], ![327, 215820, 0]], ![![706, -7987, -1815], ![110, 39567, 0]], ![![3074, -34371, -7811], ![279, 170280, 0]]]
  g := ![![![1, 0, 0], ![-20, 109, 0], ![-86, 0, 109]], ![![0, 1, 0], ![-8, 22, 5], ![-8, -33, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-33, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-33, 1, 0]] 
 ![![109, 0, 0], ![76, 1, 0], ![13, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-33, 1, 0], ![-2, -31, 5], ![102, -33, -34]]]
  hmulB := by decide  
  f := ![![![-5081, -82871, 13365], ![872, -291357, 0]], ![![-3527, -57759, 9315], ![655, -203067, 0]], ![![-596, -9884, 1594], ![137, -34749, 0]]]
  g := ![![![1, 0, 0], ![-76, 109, 0], ![-13, 0, 109]], ![![-1, 1, 0], ![21, -31, 5], ![28, -33, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![91593, 2155, 2712]] ![![109, 0, 0], ![20, 1, 0]]
  ![![109, 0, 0], ![4, -15, 1]] where
 M := ![![![9983637, 234895, 295608], ![2104174, 49507, 62303]]]
 hmul := by decide  
 g := ![![![![91481, 2575, 2684], ![3052, 0, 0]], ![![19278, 553, 565], ![718, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![4, -15, 1]] ![![109, 0, 0], ![-33, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3597, 109, 0]], ![![436, -1635, 109], ![0, 436, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-33, 1, 0]]], ![![![4, -15, 1]], ![![0, 4, -1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [82, 47, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 41, 61], [69, 71, 52], [0, 1]]
 g := ![![[58, 11, 63], [105, 44], [38, 60], [11, 28], [74, 49, 91], [1]], ![[70, 75, 39, 102], [92, 30], [27, 60], [89, 25], [69, 22, 101, 4], [107, 75, 56, 77]], ![[87, 96, 83, 52], [56, 28], [], [91, 91], [47, 45, 26, 69], [32, 104, 81, 36]]]
 h' := ![![[103, 41, 61], [77, 109, 96], [41, 100, 48], [28, 61, 88], [34, 19, 49], [31, 66, 59], [0, 1]], ![[69, 71, 52], [40, 105, 18], [76, 110, 16], [16, 45, 25], [46, 110, 5], [57, 104, 79], [103, 41, 61]], ![[0, 1], [42, 12, 112], [112, 16, 49], [98, 7], [92, 97, 59], [106, 56, 88], [69, 71, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 73], []]
 b := ![[], [21, 59, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [82, 47, 54, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5252692, 2257175, -789644]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46484, 19975, -6988]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![0, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![0, 1, 0]] 
 ![![127, 0, 0], ![0, 1, 0], ![25, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![0, 1, 0], ![-2, 2, 5], ![102, -33, -1]]]
  hmulB := by decide  
  f := ![![![-127, 127, 320], ![127, -8128, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-25, 25, 63], ![25, -1600, 0]]]
  g := ![![![1, 0, 0], ![0, 127, 0], ![-25, 0, 127]], ![![0, 1, 0], ![-1, 2, 5], ![1, -33, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![52, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![52, 1, 0]] 
 ![![127, 0, 0], ![52, 1, 0], ![73, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![52, 1, 0], ![-2, 54, 5], ![102, -33, 51]]]
  hmulB := by decide  
  f := ![![![-1435, 41582, 3850], ![-254, -97790, 0]], ![![-630, 17010, 1575], ![1, -40005, 0]], ![![-849, 23901, 2213], ![-87, -56210, 0]]]
  g := ![![![1, 0, 0], ![-52, 127, 0], ![-73, 0, 127]], ![![0, 1, 0], ![-25, 54, 5], ![-15, -33, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-53, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-53, 1, 0]] 
 ![![127, 0, 0], ![74, 1, 0], ![94, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-53, 1, 0], ![-2, -51, 5], ![102, -33, -54]]]
  hmulB := by decide  
  f := ![![![22296, 615860, -60375], ![-4445, 1533525, 0]], ![![13011, 358805, -35175], ![-2539, 893445, 0]], ![![16523, 455833, -44687], ![-3241, 1135050, 0]]]
  g := ![![![1, 0, 0], ![-74, 127, 0], ![-94, 0, 127]], ![![-1, 1, 0], ![26, -51, 5], ![60, -33, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![0, 1, 0]] ![![127, 0, 0], ![52, 1, 0]]
  ![![127, 0, 0], ![25, -40, 1]] where
 M := ![![![16129, 0, 0], ![6604, 127, 0]], ![![0, 127, 0], ![-2, 54, 5]]]
 hmul := by decide  
 g := ![![![![102, 40, -1], ![127, 0, 0]], ![![27, 41, -1], ![127, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-1, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![25, -40, 1]] ![![127, 0, 0], ![-53, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-6731, 127, 0]], ![![3175, -5080, 127], ![-1143, 2032, -254]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-53, 1, 0]]], ![![![25, -40, 1]], ![![-9, 16, -2]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![17, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![17, 1, 0]] 
 ![![131, 0, 0], ![17, 1, 0], ![66, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![17, 1, 0], ![-2, 19, 5], ![102, -33, 16]]]
  hmulB := by decide  
  f := ![![![-10515, 100552, 26460], ![-524, -693252, 0]], ![![-1372, 13034, 3430], ![1, -89866, 0]], ![![-5294, 50660, 13331], ![-292, -349272, 0]]]
  g := ![![![1, 0, 0], ![-17, 131, 0], ![-66, 0, 131]], ![![0, 1, 0], ![-5, 19, 5], ![-3, -33, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2143, 705, 48]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-2143, 705, 48]] 
 ![![131, 0, 0], ![29, 1, 0], ![108, 0, 1]] where
  M :=![![![-2143, 705, 48], ![3486, -2317, 3477], ![69606, -21969, -4384]]]
  hmulB := by decide  
  f := ![![![86543941, 2036208, 2562501]], ![![21122725, 496976, 625428]], ![![71995716, 1693917, 2131739]]]
  g := ![![![-212, 705, 48], ![-2327, -2317, 3477], ![9009, -21969, -4384]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-47, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-47, 1, 0]] 
 ![![131, 0, 0], ![84, 1, 0], ![22, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-47, 1, 0], ![-2, -45, 5], ![102, -33, -48]]]
  hmulB := by decide  
  f := ![![![-264, -7021, 780], ![131, -20436, 0]], ![![-152, -4501, 500], ![132, -13100, 0]], ![![-49, -1179, 131], ![9, -3432, 0]]]
  g := ![![![1, 0, 0], ![-84, 131, 0], ![-22, 0, 131]], ![![-1, 1, 0], ![28, -45, 5], ![30, -33, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![17, 1, 0]] ![![-2143, 705, 48]]
  ![![131, 0, 0], ![72, 62, 1]] where
 M := ![![![-280733, 92355, 6288]], ![![-32945, 9668, 4293]]]
 hmul := by decide  
 g := ![![![![-1855, 953, 52], ![-524, 0, 0]]], ![![![-235, 88, 33], ![-30, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![72, 62, 1]] ![![131, 0, 0], ![-47, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-6157, 131, 0]], ![![9432, 8122, 131], ![-3406, -2751, 262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-47, 1, 0]]], ![![![72, 62, 1]], ![![-26, -21, 2]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![7, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![7, 1, 0]] 
 ![![137, 0, 0], ![7, 1, 0], ![124, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![7, 1, 0], ![-2, 9, 5], ![102, -33, 6]]]
  hmulB := by decide  
  f := ![![![386, -1765, -980], ![137, 26852, 0]], ![![20, -90, -50], ![1, 1370, 0]], ![![353, -1597, -887], ![53, 24304, 0]]]
  g := ![![![1, 0, 0], ![-7, 137, 0], ![-124, 0, 137]], ![![0, 1, 0], ![-5, 9, 5], ![-3, -33, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![49, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![49, 1, 0]] 
 ![![137, 0, 0], ![49, 1, 0], ![130, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![49, 1, 0], ![-2, 51, 5], ![102, -33, 48]]]
  hmulB := by decide  
  f := ![![![-2960, 79257, 7770], ![-411, -212898, 0]], ![![-1061, 28306, 2775], ![-136, -76035, 0]], ![![-2827, 75207, 7373], ![-339, -202020, 0]]]
  g := ![![![1, 0, 0], ![-49, 137, 0], ![-130, 0, 137]], ![![0, 1, 0], ![-23, 51, 5], ![-33, -33, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-57, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-57, 1, 0]] 
 ![![137, 0, 0], ![80, 1, 0], ![85, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-57, 1, 0], ![-2, -55, 5], ![102, -33, -58]]]
  hmulB := by decide  
  f := ![![![1903, 55442, -5040], ![-274, 138096, 0]], ![![1120, 32341, -2940], ![-136, 80556, 0]], ![![1199, 34398, -3127], ![-126, 85680, 0]]]
  g := ![![![1, 0, 0], ![-80, 137, 0], ![-85, 0, 137]], ![![-1, 1, 0], ![29, -55, 5], ![56, -33, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![7, 1, 0]] ![![137, 0, 0], ![49, 1, 0]]
  ![![137, 0, 0], ![-14, 39, 1]] where
 M := ![![![18769, 0, 0], ![6713, 137, 0]], ![![959, 137, 0], ![341, 58, 5]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![49, 1, 0], ![0, 0, 0]]], ![![![7, 1, 0], ![0, 0, 0]], ![![3, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-14, 39, 1]] ![![137, 0, 0], ![-57, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-7809, 137, 0]], ![![-1918, 5343, 137], ![822, -2192, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-57, 1, 0]]], ![![![-14, 39, 1]], ![![6, -16, 1]]]]
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
  g := ![2, 3, 2, 1, 1, 1, 3, 1, 3, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB274I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![127, 127, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
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
  β := ![I83N1, I89N0, I89N1, I89N2, I97N1, I109N0, I109N1, I109N2, I127N0, I127N1, I127N2, I131N0, I131N1, I131N2, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N1], [], [], [], [I109N0, I109N1, I109N2], [], [I127N0, I127N1, I127N2], [I131N0, I131N1, I131N2], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
