
import IdealArithmetic.Examples.NF3_1_283015_1.RI3_1_283015_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-560641, 160460, 247739]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-560641, 160460, 247739]] 
 ![![83, 0, 0], ![0, 83, 0], ![40, 35, 1]] where
  M :=![![![-560641, 160460, 247739], ![-24526161, -1886615, 1444140], ![-13160411, -3687889, -2047075]]]
  hmulB := by decide  
  f := ![![![-110697233995, 7050123837, -8423070095]], ![![833883939405, -53108689588, 63451114533]], ![![288764246849, -18390917519, 21972378210]]]
  g := ![![![-126147, -102535, 247739], ![-991467, -631705, 1444140], ![827983, 818792, -2047075]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [25, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 82], [0, 1]]
 g := ![![[10, 10], [2, 31], [44], [70], [49, 1], [1]], ![[0, 73], [54, 52], [44], [70], [48, 82], [1]]]
 h' := ![![[82, 82], [33, 33], [48, 60], [61, 58], [20, 53], [58, 82], [0, 1]], ![[0, 1], [0, 50], [71, 23], [3, 25], [50, 30], [59, 1], [82, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [26, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [25, 1, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3528, -3585, -1715]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![784, 680, -1715]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-110697233995, 7050123837, -8423070095]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-110697233995, 7050123837, -8423070095]] 
 ![![83, 0, 0], ![17, 1, 0], ![49, 0, 1]] where
  M :=![![![-110697233995, 7050123837, -8423070095], ![833883939405, -53108689588, 63451114533], ![-790616030908, 50353028023, -60158813425]]]
  hmulB := by decide  
  f := ![![![-560641, 160460, 247739]], ![![-410326, 10135, 68141]], ![![-489540, 50297, 121592]]]
  g := ![![![2194952957, 7050123837, -8423070095], ![-16534613852, -53108689588, 63451114533], ![15676678922, 50353028023, -60158813425]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-560641, 160460, 247739]] ![![-110697233995, 7050123837, -8423070095]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [2, 48, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 26, 17], [9, 62, 72], [0, 1]]
 g := ![![[27, 15, 18], [86, 21], [48, 9], [30, 31, 45], [19, 44, 1], []], ![[52, 6, 31, 79], [38, 49], [31, 1], [33, 12, 32, 22], [81, 11, 34, 22], [72, 22]], ![[85, 48, 81, 36], [54, 87], [10, 16], [78, 76, 25, 8], [37, 45, 66, 78], [17, 22]]]
 h' := ![![[35, 26, 17], [27, 50, 75], [33, 10, 56], [29, 31, 3], [51, 68, 57], [0, 0, 1], [0, 1]], ![[9, 62, 72], [82, 78, 71], [43, 75, 82], [85, 38, 1], [57, 81, 62], [13, 11, 62], [35, 26, 17]], ![[0, 1], [86, 50, 32], [85, 4, 40], [4, 20, 85], [49, 29, 59], [47, 78, 26], [9, 62, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 8], []]
 b := ![[], [31, 85, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [2, 48, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1540768, 123799, -5696]
  a := ![-1, 1, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17312, 1391, -64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![32, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![32, 1, 0]] 
 ![![97, 0, 0], ![32, 1, 0], ![12, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![32, 1, 0], ![0, 33, 9], ![-99, -6, 32]]]
  hmulB := by decide  
  f := ![![![2049, 64, 0], ![-6208, 0, 0]], ![![672, 21, 0], ![-2036, 0, 0]], ![![204, -12, -5], ![-618, 54, 0]]]
  g := ![![![1, 0, 0], ![-32, 97, 0], ![-12, 0, 97]], ![![0, 1, 0], ![-12, 33, 9], ![-3, -6, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-28, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-28, 1, 0]] 
 ![![97, 0, 0], ![69, 1, 0], ![13, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-28, 1, 0], ![0, -27, 9], ![-99, -6, -28]]]
  hmulB := by decide  
  f := ![![![1625, -58, 0], ![5626, 0, 0]], ![![1149, -41, 0], ![3978, 0, 0]], ![![253, 6, -5], ![876, 54, 0]]]
  g := ![![![1, 0, 0], ![-69, 97, 0], ![-13, 0, 97]], ![![-1, 1, 0], ![18, -27, 9], ![7, -6, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -4, -8]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![27, -4, -8]] 
 ![![97, 0, 0], ![92, 1, 0], ![84, 0, 1]] where
  M :=![![![27, -4, -8], ![792, 71, -36], ![308, 112, 75]]]
  hmulB := by decide  
  f := ![![![-9357, 596, -712]], ![![-8148, 519, -620]], ![![-8792, 560, -669]]]
  g := ![![![11, -4, -8], ![-28, 71, -36], ![-168, 112, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![32, 1, 0]] ![![97, 0, 0], ![-28, 1, 0]]
  ![![9357, -596, 712]] where
 M := ![![![9409, 0, 0], ![-2716, 97, 0]], ![![3104, 97, 0], ![-896, 5, 9]]]
 hmul := by decide  
 g := ![![![![-2619, 388, 776]], ![![-36, -183, -188]]], ![![![-1656, 57, 292]], ![![180, -51, -79]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![9357, -596, 712]] ![![27, -4, -8]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [11, 71, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 39, 31], [64, 61, 70], [0, 1]]
 g := ![![[13, 99, 9], [24, 64], [39, 51, 54], [45, 24], [50, 80], [1]], ![[73, 24, 83, 84], [96, 80], [19, 12, 71, 6], [16, 87], [72, 76], [78, 53, 37, 97]], ![[67, 91, 24, 37], [65, 95], [78, 35, 38, 70], [10, 85], [15, 33], [15, 74, 9, 4]]]
 h' := ![![[59, 39, 31], [58, 34, 3], [76, 36, 93], [29, 56, 16], [76, 61, 78], [90, 30, 22], [0, 1]], ![[64, 61, 70], [1, 90, 25], [59, 54, 22], [40, 36, 86], [32, 38, 84], [97, 85, 50], [59, 39, 31]], ![[0, 1], [71, 78, 73], [68, 11, 87], [56, 9, 100], [60, 2, 40], [86, 87, 29], [64, 61, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 30], []]
 b := ![[], [5, 87, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [11, 71, 79, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54641, 1111, -1616]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![541, 11, -16]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [79, 51, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 94, 92], [63, 8, 11], [0, 1]]
 g := ![![[67, 80, 56], [71, 101, 8], [30, 40, 56], [1, 64], [36, 14], [1]], ![[10, 18, 38, 68], [88, 33, 89, 26], [77, 9, 100, 9], [6, 58], [2, 61], [28, 70, 7, 8]], ![[79, 82, 19, 12], [77, 28, 19, 80], [79, 28, 0, 70], [22, 23], [48, 46], [37, 90, 42, 95]]]
 h' := ![![[63, 94, 92], [56, 40, 57], [102, 8, 27], [28, 76, 46], [101, 69, 8], [24, 52, 23], [0, 1]], ![[63, 8, 11], [78, 37, 16], [57, 51, 25], [1, 52, 47], [28, 22, 26], [17, 3, 24], [63, 94, 92]], ![[0, 1], [58, 26, 30], [15, 44, 51], [21, 78, 10], [27, 12, 69], [27, 48, 56], [63, 8, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 9], []]
 b := ![[], [45, 47, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [79, 51, 80, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8590921, -1326537, -276555]
  a := ![1, -2, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83407, -12879, -2685]
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


def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5507020, -350733, 419035]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![5507020, -350733, 419035]] 
 ![![107, 0, 0], ![10, 1, 0], ![71, 0, 1]] where
  M :=![![![5507020, -350733, 419035], ![-41484465, 2642077, -3156597], ![39331952, -2504987, 2992810]]]
  hmulB := by decide  
  f := ![![![17131, 2185, -94]], ![![1688, 390, 175]], ![![9336, 1337, 103]]]
  g := ![![![-193805, -350733, 419035], ![1459936, 2642077, -3156597], ![-1384184, -2504987, 2992810]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![422333493, -26897722, 32135804]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![422333493, -26897722, 32135804]] 
 ![![107, 0, 0], ![48, 1, 0], ![24, 0, 1]] where
  M :=![![![422333493, -26897722, 32135804], ![-3181444596, 202620947, -242079498], ![3016368322, -192107512, 229518669]]]
  hmulB := by decide  
  f := ![![![-29433, 12370, 17168]], ![![-29088, 4427, 8742]], ![![-16282, 316, 2613]]]
  g := ![![![8805279, -26897722, 32135804], ![-66330300, 202620947, -242079498], ![62888606, -192107512, 229518669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![5507020, -350733, 419035]] ![![422333493, -26897722, 32135804]]
  ![![4705600499918998, -299691916903511, 358054139380529]] where
 M := ![![![4705600499918998, -299691916903511, 358054139380529]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![4705600499918998, -299691916903511, 358054139380529]] ![![422333493, -26897722, 32135804]]
  ![![107, 0, 0]] where
 M := ![![![4020809088879293145978908, -256078683978811584601321, 305947633666918093517771]]]
 hmul := by decide  
 g := ![![![![37577655036255076130644, -2393258728773940043003, 2859323679130075640353]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![58, 28, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![58, 28, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![58, 28, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![58, 28, 1], ![-99, 80, 252], ![-2761, -179, 52]]]
  hmulB := by decide  
  f := ![![![-57, -28, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -28, 109]], ![![0, 0, 1], ![-135, -64, 252], ![-53, -15, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [1, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 108], [0, 1]]
 g := ![![[45, 1], [38], [59, 88], [19, 31], [29], [64, 1]], ![[0, 108], [38], [23, 21], [41, 78], [29], [19, 108]]]
 h' := ![![[64, 108], [64, 108], [50, 16], [90, 52], [34, 24], [45, 62], [0, 1]], ![[0, 1], [0, 1], [93, 93], [39, 57], [44, 85], [89, 47], [64, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [99, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [1, 45, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3552, -3673, -2463]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1278, 599, -2463]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-34, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-34, 1, 0]] 
 ![![109, 0, 0], ![75, 1, 0], ![57, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-34, 1, 0], ![0, -33, 9], ![-99, -6, -34]]]
  hmulB := by decide  
  f := ![![![3435, -101, 0], ![11009, 0, 0]], ![![2381, -70, 0], ![7631, 0, 0]], ![![1815, -57, 1], ![5817, -12, 0]]]
  g := ![![![1, 0, 0], ![-75, 109, 0], ![-57, 0, 109]], ![![-1, 1, 0], ![18, -33, 9], ![21, -6, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![58, 28, 1]] ![![109, 0, 0], ![-34, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3706, 109, 0]], ![![6322, 3052, 109], ![-2071, -872, 218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-34, 1, 0]]], ![![![58, 28, 1]], ![![-19, -8, 2]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [26, 32, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 58, 39], [37, 54, 74], [0, 1]]
 g := ![![[14, 11, 106], [75, 100], [43, 81], [90, 111], [80, 56, 31], [1]], ![[86, 90, 80, 5], [38, 56], [81, 52], [97, 53], [91, 97, 19, 89], [15, 53, 49, 107]], ![[17, 80, 55, 65], [105, 77], [3, 109], [44, 100], [52, 99, 68, 48], [43, 44, 21, 6]]]
 h' := ![![[88, 58, 39], [1, 77, 85], [16, 28, 103], [2, 30, 9], [67, 50, 26], [87, 81, 12], [0, 1]], ![[37, 54, 74], [111, 74, 22], [67, 7, 100], [79, 20, 74], [51, 53, 77], [31, 107, 78], [88, 58, 39]], ![[0, 1], [44, 75, 6], [66, 78, 23], [101, 63, 30], [51, 10, 10], [41, 38, 23], [37, 54, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 16], []]
 b := ![[], [30, 41, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [26, 32, 101, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5149310447, 552526608, 16050520]
  a := ![1, 20, 161]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45569119, 4889616, 142040]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [67, 71, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 107, 17], [126, 19, 110], [0, 1]]
 g := ![![[124, 110, 22], [74, 43, 72], [103, 92, 1], [64, 75, 60], [32, 64, 122], [1]], ![[7, 1, 27, 81], [13, 55, 10, 100], [15, 62, 10, 49], [60, 37, 29, 49], [110, 96, 71, 1], [24, 84, 60, 87]], ![[62, 96, 98, 101], [23, 71, 4, 126], [61, 12, 90, 20], [16, 115, 73, 102], [110, 121, 67, 110], [52, 0, 89, 40]]]
 h' := ![![[74, 107, 17], [122, 64, 28], [84, 123, 96], [30, 54, 126], [15, 88, 21], [60, 56, 73], [0, 1]], ![[126, 19, 110], [90, 117, 96], [5, 80, 105], [96, 63, 10], [30, 18, 117], [10, 23, 53], [74, 107, 17]], ![[0, 1], [75, 73, 3], [110, 51, 53], [116, 10, 118], [35, 21, 116], [71, 48, 1], [126, 19, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 104], []]
 b := ![[], [50, 47, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [67, 71, 54, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4070731, 330327, -52197]
  a := ![-1, 2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32053, 2601, -411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23824, -11627, -15599]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![23824, -11627, -15599]] 
 ![![131, 0, 0], ![0, 131, 0], ![28, 23, 1]] where
  M :=![![![23824, -11627, -15599], ![1544301, 105791, -104643], ![979484, 241351, 117418]]]
  hmulB := by decide  
  f := ![![![287614201, -18317673, 21884870]], ![![-2166602130, 137987308, -164859057]], ![![-303240215, 19312868, -23073870]]]
  g := ![![![3516, 2650, -15599], ![34155, 19180, -104643], ![-17620, -18773, 117418]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [66, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 130], [0, 1]]
 g := ![![[122, 74], [100, 117], [49], [7], [129], [53], [1]], ![[62, 57], [37, 14], [49], [7], [129], [53], [1]]]
 h' := ![![[70, 130], [81, 27], [15, 36], [74, 124], [76, 20], [72, 103], [65, 70], [0, 1]], ![[0, 1], [6, 104], [46, 95], [108, 7], [35, 111], [77, 28], [118, 61], [70, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [81, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [66, 61, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7942, -8180, -2389]
  a := ![0, 3, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![450, 357, -2389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![287614201, -18317673, 21884870]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![287614201, -18317673, 21884870]] 
 ![![131, 0, 0], ![55, 1, 0], ![109, 0, 1]] where
  M :=![![![287614201, -18317673, 21884870], ![-2166602130, 137987308, -164859057], ![2054183197, -130827532, 156304981]]]
  hmulB := by decide  
  f := ![![![23824, -11627, -15599]], ![![21791, -4074, -7348]], ![![27300, -7832, -12083]]]
  g := ![![![-8323394, -18317673, 21884870], ![62700253, 137987308, -164859057], ![-59446912, -130827532, 156304981]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![23824, -11627, -15599]] ![![287614201, -18317673, 21884870]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1019213, -64912, 77553]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![1019213, -64912, 77553]] 
 ![![137, 0, 0], ![0, 137, 0], ![106, 102, 1]] where
  M :=![![![1019213, -64912, 77553], ![-7677747, 488983, -584208], ![7279371, -463611, 553895]]]
  hmulB := by decide  
  f := ![![![-119, 61, 81]], ![![-8019, -544, 549]], ![![-6100, -367, 467]]]
  g := ![![![-52565, -58214, 77553], ![395973, 438527, -584208], ![-375427, -415773, 553895]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [40, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 136], [0, 1]]
 g := ![![[95, 120], [19], [14], [27, 119], [123], [63], [1]], ![[31, 17], [19], [14], [64, 18], [123], [63], [1]]]
 h' := ![![[36, 136], [3, 95], [107, 108], [16, 39], [26, 121], [39, 73], [97, 36], [0, 1]], ![[0, 1], [135, 42], [22, 29], [50, 98], [135, 16], [64, 64], [23, 101], [36, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [42, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [40, 101, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55678, -49012, -28998]
  a := ![2, -8, -62]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22030, 21232, -28998]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119, -61, -81]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![119, -61, -81]] 
 ![![137, 0, 0], ![41, 1, 0], ![37, 0, 1]] where
  M :=![![![119, -61, -81], ![8019, 544, -549], ![5148, 1257, 605]]]
  hmulB := by decide  
  f := ![![![-1019213, 64912, -77553]], ![![-248978, 15857, -18945]], ![![-328396, 20915, -24988]]]
  g := ![![![41, -61, -81], ![44, 544, -549], ![-502, 1257, 605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![1019213, -64912, 77553]] ![![119, -61, -81]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB151I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB151I2 : PrimesBelowBoundCertificateInterval O 79 137 151 where
  m := 11
  g := ![2, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB151I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0]
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
    · exact ![704969]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![2048383]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I97N0, I97N1, I97N2, I107N0, I107N1, I109N1, I131N1, I137N1]
  Il := ![[I83N1], [], [I97N0, I97N1, I97N2], [], [], [I107N0, I107N1, I107N1], [I109N1], [], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
