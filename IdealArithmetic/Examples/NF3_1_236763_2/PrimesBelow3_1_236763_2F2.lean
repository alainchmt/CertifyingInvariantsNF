
import IdealArithmetic.Examples.NF3_1_236763_2.RI3_1_236763_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [24, 1, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 25, 75], [45, 57, 8], [0, 1]]
 g := ![![[5, 25, 28], [17, 56, 33], [75, 81], [76, 12], [63, 8, 1], []], ![[57, 65, 68, 78], [18, 6, 56, 65], [70, 49], [17, 31], [32, 60, 18, 70], [29, 64]], ![[27, 14, 66, 72], [75, 1, 41, 32], [52, 4], [19, 77], [7, 64, 81, 20], [13, 64]]]
 h' := ![![[46, 25, 75], [7, 76, 32], [62, 6, 38], [77, 18, 74], [65, 77, 57], [0, 0, 1], [0, 1]], ![[45, 57, 8], [56, 22, 54], [16, 26, 43], [77, 60, 7], [53, 79, 60], [9, 71, 57], [46, 25, 75]], ![[0, 1], [60, 68, 80], [22, 51, 2], [78, 5, 2], [77, 10, 49], [53, 12, 25], [45, 57, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 41], []]
 b := ![[], [15, 62, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [24, 1, 75, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-451769, 68641, -736044]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5443, 827, -8868]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![30, -17, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![30, -17, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![30, 72, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![30, -17, 1], ![13, -40, -139], ![-839, 336, 64]]]
  hmulB := by decide  
  f := ![![![-29, 17, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -72, 89]], ![![0, -1, 1], ![47, 112, -139], ![-31, -48, 64]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [50, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 88], [0, 1]]
 g := ![![[80, 73], [10], [18], [47, 4], [70, 25], [1]], ![[0, 16], [10], [18], [67, 85], [17, 64], [1]]]
 h' := ![![[5, 88], [32, 47], [40, 30], [53, 75], [60, 87], [39, 5], [0, 1]], ![[0, 1], [0, 42], [12, 59], [72, 14], [50, 2], [64, 84], [5, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [61, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [50, 84, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1318, 557, -661]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![208, 541, -661]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-39, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-39, 1, 0]] 
 ![![89, 0, 0], ![50, 1, 0], ![25, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-39, 1, 0], ![2, -36, 8], ![47, -19, -42]]]
  hmulB := by decide  
  f := ![![![2472, -57797, 12848], ![-1691, -142934, 0]], ![![1415, -32462, 7216], ![-889, -80278, 0]], ![![729, -16236, 3609], ![-396, -40150, 0]]]
  g := ![![![1, 0, 0], ![-50, 89, 0], ![-25, 0, 89]], ![![-1, 1, 0], ![18, -36, 8], ![23, -19, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![30, -17, 1]] ![![89, 0, 0], ![-39, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3471, 89, 0]], ![![2670, -1513, 89], ![-1157, 623, -178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-39, 1, 0]]], ![![![30, -17, 1]], ![![-13, 7, -2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![36, -31, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![36, -31, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![36, 66, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![36, -31, 1], ![-15, -76, -251], ![-1497, 602, 112]]]
  hmulB := by decide  
  f := ![![![-35, 31, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -66, 97]], ![![0, -1, 1], ![93, 170, -251], ![-57, -70, 112]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [3, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 96], [0, 1]]
 g := ![![[46, 65], [91], [8], [49], [65], [56, 1]], ![[0, 32], [91], [8], [49], [65], [15, 96]]]
 h' := ![![[56, 96], [72, 68], [65, 24], [63, 69], [93, 7], [26, 29], [0, 1]], ![[0, 1], [0, 29], [51, 73], [47, 28], [0, 90], [1, 68], [56, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [61, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [3, 41, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![113877, -505388, -3600508]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1337445, 2444620, -3600508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-40, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-40, 1, 0]] 
 ![![97, 0, 0], ![57, 1, 0], ![82, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-40, 1, 0], ![2, -37, 8], ![47, -19, -43]]]
  hmulB := by decide  
  f := ![![![4041, -94693, 20480], ![-2619, -248320, 0]], ![![2409, -55633, 12032], ![-1454, -145888, 0]], ![![3426, -80050, 17313], ![-2190, -209920, 0]]]
  g := ![![![1, 0, 0], ![-57, 97, 0], ![-82, 0, 97]], ![![-1, 1, 0], ![15, -37, 8], ![48, -19, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![36, -31, 1]] ![![97, 0, 0], ![-40, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3880, 97, 0]], ![![3492, -3007, 97], ![-1455, 1164, -291]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-40, 1, 0]]], ![![![36, -31, 1]], ![![-15, 12, -3]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![4, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![4, 1, 0]] 
 ![![101, 0, 0], ![4, 1, 0], ![22, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![4, 1, 0], ![2, 7, 8], ![47, -19, 1]]]
  hmulB := by decide  
  f := ![![![5909, 20743, 23712], ![505, -299364, 0]], ![![230, 818, 936], ![102, -11817, 0]], ![![1286, 4518, 5165], ![138, -65208, 0]]]
  g := ![![![1, 0, 0], ![-4, 101, 0], ![-22, 0, 101]], ![![0, 1, 0], ![-2, 7, 8], ![1, -19, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, -4, -1]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![10, -4, -1]] 
 ![![101, 0, 0], ![5, 1, 0], ![71, 0, 1]] where
  M :=![![![10, -4, -1], ![-55, 17, -29], ![-148, 63, 39]]]
  hmulB := by decide  
  f := ![![![2490, 93, 133]], ![![187, 7, 10]], ![![1741, 65, 93]]]
  g := ![![![1, -4, -1], ![19, 17, -29], ![-32, 63, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-9, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-9, 1, 0]] 
 ![![101, 0, 0], ![92, 1, 0], ![44, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-9, 1, 0], ![2, -6, 8], ![47, -19, -12]]]
  hmulB := by decide  
  f := ![![![10533, -31908, 42560], ![-1212, -537320, 0]], ![![9592, -29059, 38760], ![-1110, -489345, 0]], ![![4593, -13901, 18541], ![-479, -234080, 0]]]
  g := ![![![1, 0, 0], ![-92, 101, 0], ![-44, 0, 101]], ![![-1, 1, 0], ![2, -6, 8], ![23, -19, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![4, 1, 0]] ![![10, -4, -1]]
  ![![101, 0, 0], ![28, -49, 1]] where
 M := ![![![1010, -404, -101]], ![![-15, 1, -33]]]
 hmul := by decide  
 g := ![![![![-18, 45, -2], ![101, 0, 0]]], ![![![-19, 33, -1], ![68, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![28, -49, 1]] ![![101, 0, 0], ![-9, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-909, 101, 0]], ![![2828, -4949, 101], ![-303, 303, -404]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-9, 1, 0]]], ![![![28, -49, 1]], ![![-3, 3, -4]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [60, 81, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 36, 64], [9, 66, 39], [0, 1]]
 g := ![![[44, 4, 32], [57, 31, 68], [86, 30, 26], [78, 16], [7, 46], [1]], ![[68, 32, 0, 56], [62, 78, 62, 29], [75, 97, 58, 17], [89, 72], [79, 72], [48, 48, 97, 9]], ![[14, 85, 83, 45], [10, 4, 6, 69], [28, 50, 82, 44], [41, 58], [30, 7], [5, 47, 78, 94]]]
 h' := ![![[38, 36, 64], [82, 9, 54], [93, 18, 58], [21, 59, 51], [90, 7, 99], [43, 22, 47], [0, 1]], ![[9, 66, 39], [21, 78, 20], [100, 29, 36], [57, 72, 35], [12, 7, 81], [80, 40, 81], [38, 36, 64]], ![[0, 1], [70, 16, 29], [75, 56, 9], [35, 75, 17], [34, 89, 26], [17, 41, 78], [9, 66, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 12], []]
 b := ![[], [33, 1, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [60, 81, 56, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1267621, 368431, -827193]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12307, 3577, -8031]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![24, 53, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![24, 53, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![24, 53, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![24, 53, 1], ![153, 164, 421], ![2451, -994, -152]]]
  hmulB := by decide  
  f := ![![![-23, -53, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -53, 107]], ![![0, 0, 1], ![-93, -207, 421], ![57, 66, -152]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [94, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 106], [0, 1]]
 g := ![![[5, 37], [90, 105], [49], [47, 41], [52], [65, 1]], ![[56, 70], [67, 2], [49], [37, 66], [52], [23, 106]]]
 h' := ![![[65, 106], [100, 95], [100, 76], [76, 7], [48, 24], [96, 65], [0, 1]], ![[0, 1], [69, 12], [11, 31], [103, 100], [3, 83], [41, 42], [65, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [14, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [94, 42, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-93, -513, -3040]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![681, 1501, -3040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![7, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![7, 1, 0]] 
 ![![107, 0, 0], ![7, 1, 0], ![45, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![7, 1, 0], ![2, 10, 8], ![47, -19, 4]]]
  hmulB := by decide  
  f := ![![![-7034, -35413, -28336], ![-749, 378994, 0]], ![![-462, -2310, -1848], ![1, 24717, 0]], ![![-2963, -14894, -11917], ![-242, 159390, 0]]]
  g := ![![![1, 0, 0], ![-7, 107, 0], ![-45, 0, 107]], ![![0, 1, 0], ![-4, 10, 8], ![0, -19, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![24, 53, 1]] ![![107, 0, 0], ![7, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![749, 107, 0]], ![![2568, 5671, 107], ![321, 535, 428]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![7, 1, 0]]], ![![![24, 53, 1]], ![![3, 5, 4]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![46, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![46, 1, 0]] 
 ![![109, 0, 0], ![46, 1, 0], ![100, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![46, 1, 0], ![2, 49, 8], ![47, -19, 43]]]
  hmulB := by decide  
  f := ![![![-6807, -216340, -35328], ![-4796, 481344, 0]], ![![-2898, -91269, -14904], ![-1961, 203067, 0]], ![![-6242, -198477, -32411], ![-4407, 441600, 0]]]
  g := ![![![1, 0, 0], ![-46, 109, 0], ![-100, 0, 109]], ![![0, 1, 0], ![-28, 49, 8], ![-31, -19, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-27, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-27, 1, 0]] 
 ![![109, 0, 0], ![82, 1, 0], ![1, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-27, 1, 0], ![2, -24, 8], ![47, -19, -30]]]
  hmulB := by decide  
  f := ![![![-654, 8829, -2944], ![327, 40112, 0]], ![![-497, 6622, -2208], ![219, 30084, 0]], ![![-6, 81, -27], ![3, 368, 0]]]
  g := ![![![1, 0, 0], ![-82, 109, 0], ![-1, 0, 109]], ![![-1, 1, 0], ![18, -24, 8], ![15, -19, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85342, 3185, 4561]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![85342, 3185, 4561]] 
 ![![109, 0, 0], ![90, 1, 0], ![44, 0, 1]] where
  M :=![![![85342, 3185, 4561], ![220737, 8238, 11797], ![-32745, -1222, -1750]]]
  hmulB := by decide  
  f := ![![![-566, 208, -73]], ![![-495, 185, -43]], ![![-112, 39, -29]]]
  g := ![![![-3688, 3185, 4561], ![-9539, 8238, 11797], ![1415, -1222, -1750]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![46, 1, 0]] ![![109, 0, 0], ![-27, 1, 0]]
  ![![566, -208, 73]] where
 M := ![![![11881, 0, 0], ![-2943, 109, 0]], ![![5014, 109, 0], ![-1240, 22, 8]]]
 hmul := by decide  
 g := ![![![![-9302278, -347165, -497149]], ![![2083497, 77757, 111350]]], ![![![-4146469, -154748, -221603]], ![![928714, 34660, 49634]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![566, -208, 73]] ![![85342, 3185, 4561]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [82, 4, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 83, 61], [93, 29, 52], [0, 1]]
 g := ![![[43, 72, 98], [82, 87], [8, 87], [28, 51], [8, 50, 41], [1]], ![[89, 87, 100, 11], [84, 112], [18, 63], [89, 63], [91, 0, 110, 31], [42, 72, 8, 77]], ![[107, 52, 85, 9], [0, 18], [54, 88], [65, 15], [5, 106, 78, 28], [60, 103, 16, 36]]]
 h' := ![![[90, 83, 61], [31, 63, 95], [38, 44, 55], [109, 31, 55], [22, 106, 27], [31, 109, 70], [0, 1]], ![[93, 29, 52], [87, 12, 44], [46, 25, 98], [77, 76, 96], [16, 69, 17], [96, 106, 91], [90, 83, 61]], ![[0, 1], [62, 38, 87], [66, 44, 73], [58, 6, 75], [90, 51, 69], [75, 11, 65], [93, 29, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 3], []]
 b := ![[], [61, 84, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [82, 4, 43, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![71357805, 7957912, 235701389]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![631485, 70424, 2085853]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![11, 60, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![11, 60, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![11, 60, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![11, 60, 1], ![167, 172, 477], ![2780, -1127, -186]]]
  hmulB := by decide  
  f := ![![![-10, -60, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -60, 127]], ![![0, 0, 1], ![-40, -224, 477], ![38, 79, -186]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [26, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 126], [0, 1]]
 g := ![![[76, 44], [115, 100], [125, 120], [21, 49], [49, 34], [56, 1]], ![[0, 83], [0, 27], [114, 7], [98, 78], [48, 93], [112, 126]]]
 h' := ![![[56, 126], [58, 67], [52, 117], [89, 45], [123, 7], [68, 62], [0, 1]], ![[0, 1], [0, 60], [0, 10], [69, 82], [7, 120], [111, 65], [56, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [60, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [26, 71, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-404, 117, -360]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 171, -360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![31, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![31, 1, 0]] 
 ![![127, 0, 0], ![31, 1, 0], ![59, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![31, 1, 0], ![2, 34, 8], ![47, -19, 28]]]
  hmulB := by decide  
  f := ![![![-3379, -62720, -14760], ![-1270, 234315, 0]], ![![-838, -15298, -3600], ![-253, 57150, 0]], ![![-1581, -29138, -6857], ![-544, 108855, 0]]]
  g := ![![![1, 0, 0], ![-31, 127, 0], ![-59, 0, 127]], ![![0, 1, 0], ![-12, 34, 8], ![-8, -19, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![11, 60, 1]] ![![127, 0, 0], ![31, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![3937, 127, 0]], ![![1397, 7620, 127], ![508, 2032, 508]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![31, 1, 0]]], ![![![11, 60, 1]], ![![4, 16, 4]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![18, 33, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![18, 33, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![18, 33, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![18, 33, 1], ![113, 98, 261], ![1511, -614, -98]]]
  hmulB := by decide  
  f := ![![![-17, -33, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -33, 131]], ![![0, 0, 1], ![-35, -65, 261], ![25, 20, -98]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [85, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 130], [0, 1]]
 g := ![![[90, 125], [52, 58], [44], [41], [62], [84], [1]], ![[9, 6], [49, 73], [44], [41], [62], [84], [1]]]
 h' := ![![[79, 130], [34, 16], [107, 78], [21, 100], [121, 98], [85, 18], [46, 79], [0, 1]], ![[0, 1], [119, 115], [112, 53], [61, 31], [3, 33], [66, 113], [130, 52], [79, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [35, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [85, 52, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-462, -192, -6008]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![822, 1512, -6008]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![1, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![1, 1, 0]] 
 ![![131, 0, 0], ![1, 1, 0], ![98, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![1, 1, 0], ![2, 4, 8], ![47, -19, -2]]]
  hmulB := by decide  
  f := ![![![132, 263, 528], ![131, -8646, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![99, 197, 395], ![65, -6468, 0]]]
  g := ![![![1, 0, 0], ![-1, 131, 0], ![-98, 0, 131]], ![![0, 1, 0], ![-6, 4, 8], ![2, -19, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![18, 33, 1]] ![![131, 0, 0], ![1, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![131, 131, 0]], ![![2358, 4323, 131], ![131, 131, 262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![1, 1, 0]]], ![![![18, 33, 1]], ![![1, 1, 2]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2151045, 80278, 114960]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![2151045, 80278, 114960]] 
 ![![137, 0, 0], ![0, 137, 0], ![73, 32, 1]] where
  M :=![![![2151045, 80278, 114960], ![5563676, 207639, 297344], ![-825334, -30802, -44109]]]
  hmulB := by decide  
  f := ![![![301, -114, 16]], ![![524, -345, -960]], ![![239, -124, -213]]]
  g := ![![![-45555, -26266, 114960], ![-117828, -67937, 297344], ![17479, 10078, -44109]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [88, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 136], [0, 1]]
 g := ![![[63, 123], [119], [9], [57, 81], [130], [123], [1]], ![[0, 14], [119], [9], [79, 56], [130], [123], [1]]]
 h' := ![![[73, 136], [14, 73], [99, 16], [53, 3], [40, 9], [71, 104], [49, 73], [0, 1]], ![[0, 1], [0, 64], [34, 121], [135, 134], [12, 128], [128, 33], [35, 64], [73, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [96, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [88, 64, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![348, -4010, -23715]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12639, 5510, -23715]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![301, -114, 16]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![301, -114, 16]] 
 ![![137, 0, 0], ![21, 1, 0], ![40, 0, 1]] where
  M :=![![![301, -114, 16], ![524, -345, -960], ![-5998, 2374, 371]]]
  hmulB := by decide  
  f := ![![![2151045, 80278, 114960]], ![![370333, 13821, 19792]], ![![622018, 23214, 33243]]]
  g := ![![![15, -114, 16], ![337, -345, -960], ![-516, 2374, 371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![2151045, 80278, 114960]] ![![301, -114, 16]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB138I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB138I2 : PrimesBelowBoundCertificateInterval O 79 137 138 where
  m := 11
  g := ![1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB138I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I97N1, I101N0, I101N1, I101N2, I107N1, I109N0, I109N1, I109N2, I127N1, I131N1, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [], [I107N1], [I109N0, I109N1, I109N2], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
