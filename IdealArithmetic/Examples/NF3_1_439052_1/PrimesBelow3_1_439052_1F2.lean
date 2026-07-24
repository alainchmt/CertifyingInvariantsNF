
import IdealArithmetic.Examples.NF3_1_439052_1.RI3_1_439052_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-56, -26, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-56, -26, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![27, 57, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-56, -26, 1], ![-298, -2, -51], ![6963, -1513, -28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -57, 83]], ![![-1, -1, 1], ![13, 35, -51], ![93, 1, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [57, 77, 1] where
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
 g := ![![[13, 3], [35, 3], [27], [77], [30, 36], [1]], ![[31, 80], [53, 80], [27], [77], [80, 47], [1]]]
 h' := ![![[6, 82], [80, 70], [23, 13], [20, 44], [33, 49], [26, 6], [0, 1]], ![[0, 1], [2, 13], [18, 70], [35, 39], [78, 34], [62, 77], [6, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [70, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [57, 77, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1542, -295, 72]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -53, 72]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-32, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-32, 1, 0]] 
 ![![83, 0, 0], ![51, 1, 0], ![28, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-32, 1, 0], ![1, -32, 2], ![-272, 54, -31]]]
  hmulB := by decide  
  f := ![![![2497, -107493, 6720], ![-2241, -278880, 0]], ![![1553, -66032, 4128], ![-1327, -171312, 0]], ![![852, -36263, 2267], ![-731, -94080, 0]]]
  g := ![![![1, 0, 0], ![-51, 83, 0], ![-28, 0, 83]], ![![-1, 1, 0], ![19, -32, 2], ![-26, 54, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-56, -26, 1]] ![![83, 0, 0], ![-32, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2656, 83, 0]], ![![-4648, -2158, 83], ![1494, 830, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-32, 1, 0]]], ![![![-56, -26, 1]], ![![18, 10, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-61, 35, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-61, 35, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![28, 35, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-61, 35, 1], ![-237, -7, 71], ![-9629, 1781, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -35, 89]], ![![-1, 0, 1], ![-25, -28, 71], ![-117, 9, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [12, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 88], [0, 1]]
 g := ![![[14, 11], [73], [50], [75, 73], [48, 11], [1]], ![[35, 78], [73], [50], [4, 16], [69, 78], [1]]]
 h' := ![![[10, 88], [13, 10], [34, 47], [79, 36], [47, 47], [77, 10], [0, 1]], ![[0, 1], [24, 79], [59, 42], [83, 53], [72, 42], [88, 79], [10, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [31, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [12, 79, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2893, -3971, 1753]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-519, -734, 1753]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![18, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![18, 1, 0]] 
 ![![89, 0, 0], ![18, 1, 0], ![61, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![18, 1, 0], ![1, 18, 2], ![-272, 54, 19]]]
  hmulB := by decide  
  f := ![![![205, 4318, 480], ![178, -21360, 0]], ![![30, 863, 96], ![90, -4272, 0]], ![![149, 2960, 329], ![80, -14640, 0]]]
  g := ![![![1, 0, 0], ![-18, 89, 0], ![-61, 0, 89]], ![![0, 1, 0], ![-5, 18, 2], ![-27, 54, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-61, 35, 1]] ![![89, 0, 0], ![18, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![1602, 89, 0]], ![![-5429, 3115, 89], ![-1335, 623, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![18, 1, 0]]], ![![![-61, 35, 1]], ![![-15, 7, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-74, 15, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-74, 15, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![23, 15, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-74, 15, 1], ![-257, -20, 31], ![-4189, 701, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -15, 97]], ![![-1, 0, 1], ![-10, -5, 31], ![-42, 8, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [60, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 96], [0, 1]]
 g := ![![[72, 96], [89], [16], [70], [43], [45, 1]], ![[27, 1], [89], [16], [70], [43], [90, 96]]]
 h' := ![![[45, 96], [26, 75], [82, 34], [84, 4], [4, 19], [16, 25], [0, 1]], ![[0, 1], [6, 22], [60, 63], [70, 93], [83, 78], [74, 72], [45, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [31, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [60, 52, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-437994, -482010, 240242]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61480, -42120, 240242]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-31, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-31, 1, 0]] 
 ![![97, 0, 0], ![66, 1, 0], ![5, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-31, 1, 0], ![1, -31, 2], ![-272, 54, -30]]]
  hmulB := by decide  
  f := ![![![-525, 20146, -1300], ![388, 63050, 0]], ![![-348, 13699, -884], ![292, 42874, 0]], ![![-13, 1038, -67], ![64, 3250, 0]]]
  g := ![![![1, 0, 0], ![-66, 97, 0], ![-5, 0, 97]], ![![-1, 1, 0], ![21, -31, 2], ![-38, 54, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-74, 15, 1]] ![![97, 0, 0], ![-31, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3007, 97, 0]], ![![-7178, 1455, 97], ![2037, -485, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-31, 1, 0]]], ![![![-74, 15, 1]], ![![21, -5, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-362, 29, 10]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-362, 29, 10]] 
 ![![101, 0, 0], ![13, 1, 0], ![17, 0, 1]] where
  M :=![![![-362, 29, 10], ![-2691, 178, 68], ![-8978, 476, 207]]]
  hmulB := by decide  
  f := ![![![4478, -1243, 192]], ![![47, -13, 2]], ![![3894, -1081, 167]]]
  g := ![![![-9, 29, 10], ![-61, 178, 68], ![-185, 476, 207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![21, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![21, 1, 0]] 
 ![![101, 0, 0], ![21, 1, 0], ![83, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![21, 1, 0], ![1, 21, 2], ![-272, 54, 22]]]
  hmulB := by decide  
  f := ![![![-6516, -148737, -14168], ![-2727, 715484, 0]], ![![-1367, -30907, -2944], ![-504, 148672, 0]], ![![-5346, -122229, -11643], ![-2283, 587972, 0]]]
  g := ![![![1, 0, 0], ![-21, 101, 0], ![-83, 0, 101]], ![![0, 1, 0], ![-6, 21, 2], ![-32, 54, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-35, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-35, 1, 0]] 
 ![![101, 0, 0], ![66, 1, 0], ![95, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-35, 1, 0], ![1, -35, 2], ![-272, 54, -34]]]
  hmulB := by decide  
  f := ![![![3326, -146975, 8400], ![-2525, -424200, 0]], ![![2185, -96024, 5488], ![-1615, -277144, 0]], ![![3135, -138244, 7901], ![-2356, -399000, 0]]]
  g := ![![![1, 0, 0], ![-66, 101, 0], ![-95, 0, 101]], ![![-1, 1, 0], ![21, -35, 2], ![-6, 54, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-362, 29, 10]] ![![101, 0, 0], ![21, 1, 0]]
  ![![101, 0, 0], ![-65, 17, 1]] where
 M := ![![![-36562, 2929, 1010], ![-10293, 787, 278]]]
 hmul := by decide  
 g := ![![![![-232, -5, 8], ![202, 0, 0]], ![![-53, -5, 2], ![76, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-65, 17, 1]] ![![101, 0, 0], ![-35, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3535, 101, 0]], ![![-6565, 1717, 101], ![2020, -606, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-35, 1, 0]]], ![![![-65, 17, 1]], ![![20, -6, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-52, 7, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-52, 7, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![51, 7, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-52, 7, 1], ![-265, 2, 15], ![-2013, 269, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -7, 103]], ![![-1, 0, 1], ![-10, -1, 15], ![-24, 2, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [31, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 102], [0, 1]]
 g := ![![[83, 34], [29, 66], [0, 100], [92], [8], [2, 1]], ![[48, 69], [58, 37], [97, 3], [92], [8], [4, 102]]]
 h' := ![![[2, 102], [28, 72], [0, 90], [10, 93], [94, 68], [41, 76], [0, 1]], ![[0, 1], [69, 31], [77, 13], [93, 10], [24, 35], [90, 27], [2, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [12, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [31, 101, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-171, -3168, 857]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-426, -89, 857]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-15, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-15, 1, 0]] 
 ![![103, 0, 0], ![88, 1, 0], ![94, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-15, 1, 0], ![1, -15, 2], ![-272, 54, -14]]]
  hmulB := by decide  
  f := ![![![-818, 12957, -1728], ![309, 88992, 0]], ![![-692, 11067, -1476], ![310, 76014, 0]], ![![-749, 11825, -1577], ![265, 81216, 0]]]
  g := ![![![1, 0, 0], ![-88, 103, 0], ![-94, 0, 103]], ![![-1, 1, 0], ![11, -15, 2], ![-36, 54, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-52, 7, 1]] ![![103, 0, 0], ![-15, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1545, 103, 0]], ![![-5356, 721, 103], ![515, -103, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-15, 1, 0]]], ![![![-52, 7, 1]], ![![5, -1, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![10, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![10, 1, 0]] 
 ![![107, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![10, 1, 0], ![1, 10, 2], ![-272, 54, 11]]]
  hmulB := by decide  
  f := ![![![-2069, -20997, -4200], ![-321, 224700, 0]], ![![-196, -1960, -392], ![1, 20972, 0]], ![![-78, -785, -157], ![-5, 8400, 0]]]
  g := ![![![1, 0, 0], ![-10, 107, 0], ![-4, 0, 107]], ![![0, 1, 0], ![-1, 10, 2], ![-8, 54, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![26, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![26, 1, 0]] 
 ![![107, 0, 0], ![26, 1, 0], ![37, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![26, 1, 0], ![1, 26, 2], ![-272, 54, 27]]]
  hmulB := by decide  
  f := ![![![-5597, -163773, -12600], ![-2889, 674100, 0]], ![![-1374, -39774, -3060], ![-641, 163710, 0]], ![![-1941, -56632, -4357], ![-976, 233100, 0]]]
  g := ![![![1, 0, 0], ![-26, 107, 0], ![-37, 0, 107]], ![![0, 1, 0], ![-7, 26, 2], ![-25, 54, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-37, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-37, 1, 0]] 
 ![![107, 0, 0], ![70, 1, 0], ![65, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-37, 1, 0], ![1, -37, 2], ![-272, 54, -36]]]
  hmulB := by decide  
  f := ![![![-330, 16351, -884], ![321, 47294, 0]], ![![-214, 10691, -578], ![215, 30923, 0]], ![![-206, 9933, -537], ![179, 28730, 0]]]
  g := ![![![1, 0, 0], ![-70, 107, 0], ![-65, 0, 107]], ![![-1, 1, 0], ![23, -37, 2], ![-16, 54, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![10, 1, 0]] ![![107, 0, 0], ![26, 1, 0]]
  ![![107, 0, 0], ![-30, 18, 1]] where
 M := ![![![11449, 0, 0], ![2782, 107, 0]], ![![1070, 107, 0], ![261, 36, 2]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![26, 1, 0], ![0, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-30, 18, 1]] ![![107, 0, 0], ![-37, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3959, 107, 0]], ![![-3210, 1926, 107], ![856, -642, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-37, 1, 0]]], ![![![-30, 18, 1]], ![![8, -6, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![0, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![0, 1, 0]] 
 ![![109, 0, 0], ![0, 1, 0], ![55, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![0, 1, 0], ![1, 0, 2], ![-272, 54, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -2], ![0, 109, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 55, 0]]]
  g := ![![![1, 0, 0], ![0, 109, 0], ![-55, 0, 109]], ![![0, 1, 0], ![-1, 0, 2], ![-3, 54, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117, 8, 3]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-117, 8, 3]] 
 ![![109, 0, 0], ![108, 1, 0], ![0, 0, 1]] where
  M :=![![![-117, 8, 3], ![-808, 45, 19], ![-2503, 105, 53]]]
  hmulB := by decide  
  f := ![![![-390, 109, -17]], ![![-343, 96, -15]], ![![-255, 71, -11]]]
  g := ![![![-9, 8, 3], ![-52, 45, 19], ![-127, 105, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![0, 1, 0]] ![![109, 0, 0], ![0, 1, 0]]
  ![![-390, 109, -17]] where
 M := ![![![11881, 0, 0], ![0, 109, 0]], ![![0, 109, 0], ![1, 0, 2]]]
 hmul := by decide  
 g := ![![![![-12753, 872, 327]], ![![-808, 45, 19]]], ![![![-808, 45, 19]], ![![-47, 2, 1]]]]
 hle2 := by decide  
def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-390, 109, -17]] ![![-117, 8, 3]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![4, 9, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![4, 9, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![4, 9, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![4, 9, 1], ![-263, 58, 19], ![-2557, 377, 67]]]
  hmulB := by decide  
  f := ![![![-3, -9, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -9, 113]], ![![0, 0, 1], ![-3, -1, 19], ![-25, -2, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [43, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 112], [0, 1]]
 g := ![![[83, 18], [18], [8], [88], [59, 22], [47, 1]], ![[25, 95], [18], [8], [88], [76, 91], [94, 112]]]
 h' := ![![[47, 112], [6, 40], [92, 73], [60, 102], [62, 75], [13, 19], [0, 1]], ![[0, 1], [78, 73], [20, 40], [108, 11], [84, 38], [2, 94], [47, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [91, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [43, 66, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1545, -284, 94]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -10, 94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-19, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-19, 1, 0]] 
 ![![113, 0, 0], ![94, 1, 0], ![46, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-19, 1, 0], ![1, -19, 2], ![-272, 54, -18]]]
  hmulB := by decide  
  f := ![![![2631, -52850, 5564], ![-904, -314366, 0]], ![![2201, -43960, 4628], ![-677, -261482, 0]], ![![1087, -21515, 2265], ![-273, -127972, 0]]]
  g := ![![![1, 0, 0], ![-94, 113, 0], ![-46, 0, 113]], ![![-1, 1, 0], ![15, -19, 2], ![-40, 54, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![4, 9, 1]] ![![113, 0, 0], ![-19, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2147, 113, 0]], ![![452, 1017, 113], ![-339, -113, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-19, 1, 0]]], ![![![4, 9, 1]], ![![-3, -1, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![18, 28, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![18, 28, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![18, 28, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![18, 28, 1], ![-244, 72, 57], ![-7725, 1403, 100]]]
  hmulB := by decide  
  f := ![![![-17, -28, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -28, 127]], ![![0, 0, 1], ![-10, -12, 57], ![-75, -11, 100]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [34, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 126], [0, 1]]
 g := ![![[23, 71], [27, 122], [99, 71], [44, 16], [119, 98], [107, 1]], ![[0, 56], [0, 5], [76, 56], [105, 111], [64, 29], [87, 126]]]
 h' := ![![[107, 126], [98, 43], [63, 73], [28, 43], [18, 123], [45, 112], [0, 1]], ![[0, 1], [0, 84], [0, 54], [57, 84], [98, 4], [91, 15], [107, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [125, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [34, 20, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31550, 5631, 1394]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-446, -263, 1394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-57, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-57, 1, 0]] 
 ![![127, 0, 0], ![70, 1, 0], ![27, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-57, 1, 0], ![1, -57, 2], ![-272, 54, -56]]]
  hmulB := by decide  
  f := ![![![-179, 16756, -588], ![254, 37338, 0]], ![![-104, 9233, -324], ![128, 20574, 0]], ![![-21, 3562, -125], ![92, 7938, 0]]]
  g := ![![![1, 0, 0], ![-70, 127, 0], ![-27, 0, 127]], ![![-1, 1, 0], ![31, -57, 2], ![-20, 54, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![18, 28, 1]] ![![127, 0, 0], ![-57, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-7239, 127, 0]], ![![2286, 3556, 127], ![-1270, -1524, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-57, 1, 0]]], ![![![18, 28, 1]], ![![-10, -12, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [84, 48, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 114, 106], [64, 16, 25], [0, 1]]
 g := ![![[53], [114, 92, 20], [115, 125], [113, 108], [12, 94], [66, 1], []], ![[62, 88, 95, 57], [111, 94, 88, 19], [43, 109], [85, 20], [124, 55], [53, 125], [49, 101]], ![[4, 76, 90, 74], [52, 63, 108, 77], [121, 105], [56, 13], [30, 102], [73, 27], [130, 101]]]
 h' := ![![[2, 114, 106], [118, 70], [68, 55, 46], [54, 70, 115], [101, 76, 34], [89, 23, 116], [0, 0, 1], [0, 1]], ![[64, 16, 25], [127, 120, 84], [59, 128, 16], [93, 92, 90], [91, 12, 85], [114, 74, 102], [80, 100, 16], [2, 114, 106]], ![[0, 1], [13, 72, 47], [23, 79, 69], [10, 100, 57], [103, 43, 12], [38, 34, 44], [119, 31, 114], [64, 16, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 114], []]
 b := ![[], [66, 129, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [84, 48, 65, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1605405, 449985, -65631]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12255, 3435, -501]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-46, 26, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-46, 26, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![91, 26, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-46, 26, 1], ![-246, 8, 53], ![-7181, 1295, 34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -26, 137]], ![![-1, 0, 1], ![-37, -10, 53], ![-75, 3, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [61, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 136], [0, 1]]
 g := ![![[97, 9], [56], [72], [3, 88], [87], [128], [1]], ![[0, 128], [56], [72], [44, 49], [87], [128], [1]]]
 h' := ![![[111, 136], [78, 3], [53, 59], [91, 49], [17, 15], [23, 118], [76, 111], [0, 1]], ![[0, 1], [0, 134], [26, 78], [50, 88], [38, 122], [106, 19], [67, 26], [111, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [64, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [61, 26, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3802, -1282, 994]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-688, -198, 994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-53, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-53, 1, 0]] 
 ![![137, 0, 0], ![84, 1, 0], ![103, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-53, 1, 0], ![1, -53, 2], ![-272, 54, -52]]]
  hmulB := by decide  
  f := ![![![-695, 50928, -1922], ![685, 131657, 0]], ![![-429, 31214, -1178], ![412, 80693, 0]], ![![-526, 38289, -1445], ![506, 98983, 0]]]
  g := ![![![1, 0, 0], ![-84, 137, 0], ![-103, 0, 137]], ![![-1, 1, 0], ![31, -53, 2], ![4, 54, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-46, 26, 1]] ![![137, 0, 0], ![-53, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-7261, 137, 0]], ![![-6302, 3562, 137], ![2192, -1370, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-53, 1, 0]]], ![![![-46, 26, 1]], ![![16, -10, 0]]]]
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


lemma PB188I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB188I2 : PrimesBelowBoundCertificateInterval O 79 137 188 where
  m := 11
  g := ![2, 2, 2, 3, 2, 3, 3, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB188I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
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
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![2248091]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N0, I101N1, I101N2, I103N1, I107N0, I107N1, I107N2, I109N0, I109N1, I113N1, I127N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [I107N0, I107N1, I107N2], [I109N0, I109N0, I109N1], [I113N1], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
