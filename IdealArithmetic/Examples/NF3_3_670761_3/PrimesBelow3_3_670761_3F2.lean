
import IdealArithmetic.Examples.NF3_3_670761_3.RI3_3_670761_3
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [13, 61, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 47, 79], [14, 35, 4], [0, 1]]
 g := ![![[75, 20, 29], [59, 50, 1], [60, 30], [42, 9], [2, 35, 1], []], ![[6, 80, 79, 46], [41, 51, 15, 66], [0, 9], [63, 33], [7, 55, 76, 80], [18, 16]], ![[38, 71, 52, 40], [9, 46, 34, 61], [61, 40], [2, 21], [56, 18, 34, 38], [10, 16]]]
 h' := ![![[21, 47, 79], [63, 59, 19], [18, 49, 1], [47, 18, 14], [57, 4, 80], [0, 0, 1], [0, 1]], ![[14, 35, 4], [6, 27, 14], [9, 66, 5], [3, 72, 3], [18, 10, 45], [41, 4, 35], [21, 47, 79]], ![[0, 1], [68, 80, 50], [23, 51, 77], [61, 76, 66], [81, 69, 41], [66, 79, 47], [14, 35, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 13], []]
 b := ![[], [60, 71, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [13, 61, 48, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3647020, -1039658, -334490]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43940, -12526, -4030]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![42, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![42, 1, 0]] 
 ![![89, 0, 0], ![42, 1, 0], ![13, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![42, 1, 0], ![2, 43, 5], ![309, 54, 41]]]
  hmulB := by decide  
  f := ![![![-4999, -148090, -17225], ![-4005, 306605, 0]], ![![-2368, -69854, -8125], ![-1868, 144625, 0]], ![![-767, -21632, -2516], ![-507, 44785, 0]]]
  g := ![![![1, 0, 0], ![-42, 89, 0], ![-13, 0, 89]], ![![0, 1, 0], ![-21, 43, 5], ![-28, 54, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-35, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-35, 1, 0]] 
 ![![89, 0, 0], ![54, 1, 0], ![65, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-35, 1, 0], ![2, -34, 5], ![309, 54, -36]]]
  hmulB := by decide  
  f := ![![![8341, -176232, 25925], ![-5162, -461465, 0]], ![![5066, -106895, 15725], ![-3114, -279905, 0]], ![![6100, -128709, 18934], ![-3749, -337025, 0]]]
  g := ![![![1, 0, 0], ![-54, 89, 0], ![-65, 0, 89]], ![![-1, 1, 0], ![17, -34, 5], ![-3, 54, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-7, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-7, 1, 0]] 
 ![![89, 0, 0], ![82, 1, 0], ![81, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-7, 1, 0], ![2, -6, 5], ![309, 54, -8]]]
  hmulB := by decide  
  f := ![![![-2859, 8660, -7220], ![356, 128516, 0]], ![![-2631, 7976, -6650], ![357, 118370, 0]], ![![-2598, 7881, -6571], ![375, 116964, 0]]]
  g := ![![![1, 0, 0], ![-82, 89, 0], ![-81, 0, 89]], ![![-1, 1, 0], ![1, -6, 5], ![-39, 54, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![42, 1, 0]] ![![89, 0, 0], ![-35, 1, 0]]
  ![![89, 0, 0], ![-80, -34, 1]] where
 M := ![![![7921, 0, 0], ![-3115, 89, 0]], ![![3738, 89, 0], ![-1468, 8, 5]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![45, 35, -1], ![89, 0, 0]]], ![![![42, 1, 0], ![0, 0, 0]], ![![68, 36, -1], ![94, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-80, -34, 1]] ![![89, 0, 0], ![-7, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-623, 89, 0]], ![![-7120, -3026, 89], ![801, 178, -178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-7, 1, 0]]], ![![![-80, -34, 1]], ![![9, 2, -2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [16, 52, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 13, 79], [40, 83, 18], [0, 1]]
 g := ![![[29, 51, 85], [9, 11], [45, 66], [47, 81], [59, 35], [1]], ![[23, 62, 6, 96], [38, 85], [25, 96], [29, 31], [74, 31], [19, 78, 70, 85]], ![[90, 54, 39, 73], [64, 64], [60, 35], [23, 91], [7, 79], [64, 22, 25, 12]]]
 h' := ![![[21, 13, 79], [94, 1, 52], [23, 33, 37], [8, 87, 39], [88, 73, 9], [81, 45, 61], [0, 1]], ![[40, 83, 18], [62, 89, 30], [31, 13, 52], [25, 24, 22], [2, 22, 15], [33, 25, 82], [21, 13, 79]], ![[0, 1], [91, 7, 15], [57, 51, 8], [85, 83, 36], [29, 2, 73], [23, 27, 51], [40, 83, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 68], []]
 b := ![[], [25, 15, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [16, 52, 36, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21643610, 12540645, 6542068]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![223130, 129285, 67444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [18, 13, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 65, 26], [26, 35, 75], [0, 1]]
 g := ![![[81, 97, 58], [27, 1], [14, 10, 65], [17, 13], [90, 21], [1]], ![[25, 61, 72, 42], [7, 95], [54, 27, 49, 26], [60, 20], [92, 47], [30, 88, 80, 2]], ![[9, 32, 44, 72], [59, 23], [48, 89, 75, 91], [34, 96], [48, 71], [36, 97, 13, 99]]]
 h' := ![![[57, 65, 26], [95, 63, 82], [51, 28, 100], [84, 94, 60], [17, 31, 35], [83, 88, 83], [0, 1]], ![[26, 35, 75], [92, 17, 64], [97, 0, 87], [68, 69, 100], [80, 65, 11], [25, 28, 42], [57, 65, 26]], ![[0, 1], [69, 21, 56], [11, 73, 15], [27, 39, 42], [29, 5, 55], [61, 86, 77], [26, 35, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 20], []]
 b := ![[], [64, 27, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [18, 13, 18, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81834595823, -23594535664, -7799869228]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-810243523, -233609264, -77226428]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![42, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![42, 1, 0]] 
 ![![103, 0, 0], ![42, 1, 0], ![10, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![42, 1, 0], ![2, 43, 5], ![309, 54, 41]]]
  hmulB := by decide  
  f := ![![![-3209, -87055, -10125], ![-2060, 208575, 0]], ![![-1314, -35467, -4125], ![-823, 84975, 0]], ![![-314, -8452, -983], ![-194, 20250, 0]]]
  g := ![![![1, 0, 0], ![-42, 103, 0], ![-10, 0, 103]], ![![0, 1, 0], ![-18, 43, 5], ![-23, 54, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-38, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-38, 1, 0]] 
 ![![103, 0, 0], ![65, 1, 0], ![90, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-38, 1, 0], ![2, -37, 5], ![309, 54, -39]]]
  hmulB := by decide  
  f := ![![![169, -3108, 420], ![0, -8652, 0]], ![![107, -1961, 265], ![1, -5459, 0]], ![![158, -2716, 367], ![28, -7560, 0]]]
  g := ![![![1, 0, 0], ![-65, 103, 0], ![-90, 0, 103]], ![![-1, 1, 0], ![19, -37, 5], ![3, 54, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-4, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-4, 1, 0]] 
 ![![103, 0, 0], ![99, 1, 0], ![101, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-4, 1, 0], ![2, -3, 5], ![309, 54, -5]]]
  hmulB := by decide  
  f := ![![![12605, -18936, 31570], ![-618, -650342, 0]], ![![12113, -18198, 30340], ![-617, -625004, 0]], ![![12359, -18568, 30957], ![-638, -637714, 0]]]
  g := ![![![1, 0, 0], ![-99, 103, 0], ![-101, 0, 103]], ![![-1, 1, 0], ![-2, -3, 5], ![-44, 54, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![42, 1, 0]] ![![103, 0, 0], ![-38, 1, 0]]
  ![![103, 0, 0], ![-51, 1, 1]] where
 M := ![![![10609, 0, 0], ![-3914, 103, 0]], ![![4326, 103, 0], ![-1594, 5, 5]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![13, 0, -1], ![103, 0, 0]]], ![![![42, 1, 0], ![0, 0, 0]], ![![38, -1, -1], ![108, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-51, 1, 1]] ![![103, 0, 0], ![-4, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-412, 103, 0]], ![![-5253, 103, 103], ![515, 0, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-4, 1, 0]]], ![![![-51, 1, 1]], ![![5, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![17, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![17, 1, 0]] 
 ![![107, 0, 0], ![17, 1, 0], ![89, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![17, 1, 0], ![2, 18, 5], ![309, 54, 16]]]
  hmulB := by decide  
  f := ![![![12847, 120174, 33390], ![3210, -714546, 0]], ![![2035, 19075, 5300], ![536, -113420, 0]], ![![10689, 99958, 27773], ![2650, -594342, 0]]]
  g := ![![![1, 0, 0], ![-17, 107, 0], ![-89, 0, 107]], ![![0, 1, 0], ![-7, 18, 5], ![-19, 54, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-16, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-16, 1, 0]] 
 ![![107, 0, 0], ![91, 1, 0], ![38, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-16, 1, 0], ![2, -15, 5], ![309, 54, -17]]]
  hmulB := by decide  
  f := ![![![-2783, 21594, -7200], ![642, 154080, 0]], ![![-2367, 18355, -6120], ![536, 130968, 0]], ![![-974, 7668, -2557], ![324, 54720, 0]]]
  g := ![![![1, 0, 0], ![-91, 107, 0], ![-38, 0, 107]], ![![-1, 1, 0], ![11, -15, 5], ![-37, 54, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-1, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-1, 1, 0]] 
 ![![107, 0, 0], ![106, 1, 0], ![86, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-1, 1, 0], ![2, 0, 5], ![309, 54, -2]]]
  hmulB := by decide  
  f := ![![![11449, 0, 28620], ![0, -612468, 0]], ![![11341, 0, 28350], ![1, -606690, 0]], ![![9202, 0, 23003], ![0, -492264, 0]]]
  g := ![![![1, 0, 0], ![-106, 107, 0], ![-86, 0, 107]], ![![-1, 1, 0], ![-4, 0, 5], ![-49, 54, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![17, 1, 0]] ![![107, 0, 0], ![-16, 1, 0]]
  ![![107, 0, 0], ![-54, -21, 1]] where
 M := ![![![11449, 0, 0], ![-1712, 107, 0]], ![![1819, 107, 0], ![-270, 2, 5]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![38, 22, -1], ![107, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-54, -21, 1]] ![![107, 0, 0], ![-1, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-107, 107, 0]], ![![-5778, -2247, 107], ![321, 0, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-1, 1, 0]]], ![![![-54, -21, 1]], ![![3, 0, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [99, 73, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 56, 107], [56, 52, 2], [0, 1]]
 g := ![![[16, 16, 46], [94, 5], [89, 51, 25], [43, 108, 74], [66, 4], [1]], ![[99, 90, 94, 70], [103, 93], [91, 42], [92, 60, 74, 17], [64, 20], [85, 79, 34, 101]], ![[73, 51, 16, 2], [60, 83], [92, 93, 35, 50], [97, 88, 72, 2], [23, 74], [13, 54, 63, 8]]]
 h' := ![![[51, 56, 107], [65, 4, 68], [18, 44, 21], [103, 21, 5], [106, 84, 69], [10, 36, 107], [0, 1]], ![[56, 52, 2], [84, 4, 40], [97, 75, 23], [72, 57], [17, 31, 41], [85, 22, 42], [51, 56, 107]], ![[0, 1], [83, 101, 1], [30, 99, 65], [36, 31, 104], [39, 103, 108], [38, 51, 69], [56, 52, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 53], []]
 b := ![[], [6, 34, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [99, 73, 2, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30907386, -13696395, -6302816]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-283554, -125655, -57824]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-52, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-52, 1, 0]] 
 ![![113, 0, 0], ![61, 1, 0], ![35, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-52, 1, 0], ![2, -51, 5], ![309, 54, -53]]]
  hmulB := by decide  
  f := ![![![2845, -96372, 9450], ![-2034, -213570, 0]], ![![1521, -52010, 5100], ![-1129, -115260, 0]], ![![895, -29850, 2927], ![-600, -66150, 0]]]
  g := ![![![1, 0, 0], ![-61, 113, 0], ![-35, 0, 113]], ![![-1, 1, 0], ![26, -51, 5], ![-10, 54, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-51, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-51, 1, 0]] 
 ![![113, 0, 0], ![62, 1, 0], ![78, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-51, 1, 0], ![2, -50, 5], ![309, 54, -52]]]
  hmulB := by decide  
  f := ![![![-5158, 173565, -17360], ![3955, 392336, 0]], ![![-2838, 95181, -9520], ![2148, 215152, 0]], ![![-3564, 119806, -11983], ![2722, 270816, 0]]]
  g := ![![![1, 0, 0], ![-62, 113, 0], ![-78, 0, 113]], ![![-1, 1, 0], ![24, -50, 5], ![9, 54, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-10, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-10, 1, 0]] 
 ![![113, 0, 0], ![103, 1, 0], ![5, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-10, 1, 0], ![2, -9, 5], ![309, 54, -11]]]
  hmulB := by decide  
  f := ![![![3595, -16349, 9085], ![-452, -205321, 0]], ![![3283, -14901, 8280], ![-338, -187128, 0]], ![![165, -724, 402], ![47, -9085, 0]]]
  g := ![![![1, 0, 0], ![-103, 113, 0], ![-5, 0, 113]], ![![-1, 1, 0], ![8, -9, 5], ![-46, 54, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-52, 1, 0]] ![![113, 0, 0], ![-51, 1, 0]]
  ![![113, 0, 0], ![11, -43, 1]] where
 M := ![![![12769, 0, 0], ![-5763, 113, 0]], ![![-5876, 113, 0], ![2654, -102, 5]]]
 hmul := by decide  
 g := ![![![![102, 43, -1], ![113, 0, 0]], ![![-51, 1, 0], ![0, 0, 0]]], ![![![-52, 1, 0], ![0, 0, 0]], ![![23, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![11, -43, 1]] ![![113, 0, 0], ![-10, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1130, 113, 0]], ![![1243, -4859, 113], ![113, 452, -226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-10, 1, 0]]], ![![![11, -43, 1]], ![![1, 4, -2]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [115, 19, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 30, 117], [115, 96, 10], [0, 1]]
 g := ![![[19, 15, 18], [102, 50, 61], [11, 56, 4], [34, 67, 34], [122, 39, 47], [1]], ![[125, 50, 33, 88], [66, 38, 21, 11], [116, 109, 107, 104], [70, 102, 6, 115], [58, 20, 1, 99], [48, 76, 10, 16]], ![[69, 31, 7, 58], [89, 114, 59, 45], [15, 53, 50, 24], [28, 55, 52, 90], [67, 29, 28, 59], [28, 103, 71, 111]]]
 h' := ![![[101, 30, 117], [81, 84, 79], [5, 49, 76], [27, 75, 125], [67, 72, 65], [12, 108, 89], [0, 1]], ![[115, 96, 10], [108, 7, 13], [88, 62, 75], [90, 108, 74], [19, 20, 59], [18, 7, 98], [101, 30, 117]], ![[0, 1], [113, 36, 35], [14, 16, 103], [17, 71, 55], [123, 35, 3], [5, 12, 67], [115, 96, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 9], []]
 b := ![[], [69, 108, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [115, 19, 38, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3683254, -1063244, -347980]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29002, -8372, -2740]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![40, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![40, 1, 0]] 
 ![![131, 0, 0], ![40, 1, 0], ![13, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![40, 1, 0], ![2, 41, 5], ![309, 54, 39]]]
  hmulB := by decide  
  f := ![![![13201, 311550, 38000], ![6550, -995600, 0]], ![![4040, 95105, 11600], ![1966, -303920, 0]], ![![1303, 30917, 3771], ![673, -98800, 0]]]
  g := ![![![1, 0, 0], ![-40, 131, 0], ![-13, 0, 131]], ![![0, 1, 0], ![-13, 41, 5], ![-18, 54, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-31, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-31, 1, 0]] 
 ![![131, 0, 0], ![100, 1, 0], ![24, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-31, 1, 0], ![2, -30, 5], ![309, 54, -32]]]
  hmulB := by decide  
  f := ![![![-7677, 125378, -20900], ![2882, 547580, 0]], ![![-5852, 95683, -15950], ![2228, 417890, 0]], ![![-1406, 22970, -3829], ![530, 100320, 0]]]
  g := ![![![1, 0, 0], ![-100, 131, 0], ![-24, 0, 131]], ![![-1, 1, 0], ![22, -30, 5], ![-33, 54, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-9, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-9, 1, 0]] 
 ![![131, 0, 0], ![122, 1, 0], ![117, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-9, 1, 0], ![2, -8, 5], ![309, 54, -10]]]
  hmulB := by decide  
  f := ![![![-106, 463, -290], ![131, 7598, 0]], ![![-98, 431, -270], ![132, 7074, 0]], ![![-99, 414, -259], ![54, 6786, 0]]]
  g := ![![![1, 0, 0], ![-122, 131, 0], ![-117, 0, 131]], ![![-1, 1, 0], ![3, -8, 5], ![-39, 54, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![40, 1, 0]] ![![131, 0, 0], ![-31, 1, 0]]
  ![![131, 0, 0], ![-38, 2, 1]] where
 M := ![![![17161, 0, 0], ![-4061, 131, 0]], ![![5240, 131, 0], ![-1238, 10, 5]]]
 hmul := by decide  
 g := ![![![![131, 0, 0], ![0, 0, 0]], ![![7, -1, -1], ![131, 0, 0]]], ![![![40, 1, 0], ![0, 0, 0]], ![![-8, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-38, 2, 1]] ![![131, 0, 0], ![-9, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-1179, 131, 0]], ![![-4978, 262, 131], ![655, 0, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-9, 1, 0]]], ![![![-38, 2, 1]], ![![5, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [68, 57, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 78, 47], [56, 58, 90], [0, 1]]
 g := ![![[48, 43, 126], [130, 44], [49, 18], [102, 31, 121], [77, 37], [80, 1], []], ![[20, 38, 65, 131], [91, 107], [97, 105], [100, 124, 14, 31], [82, 112], [89, 76], [61, 17]], ![[101, 49, 114, 5], [105, 50], [135, 128], [18, 112, 86, 43], [19, 49], [136, 56], [18, 17]]]
 h' := ![![[24, 78, 47], [126, 95, 20], [91, 78, 110], [51, 20, 44], [63, 16, 11], [40, 30, 41], [0, 0, 1], [0, 1]], ![[56, 58, 90], [14, 42, 8], [41, 84, 45], [91, 119, 67], [63, 100, 20], [76, 4, 89], [127, 70, 58], [24, 78, 47]], ![[0, 1], [120, 0, 109], [100, 112, 119], [85, 135, 26], [71, 21, 106], [104, 103, 7], [131, 67, 78], [56, 58, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 86], []]
 b := ![[], [46, 55, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [68, 57, 57, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73530914, 17374203, 4381671]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![536722, 126819, 31983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB183I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB183I2 : PrimesBelowBoundCertificateInterval O 79 137 183 where
  m := 11
  g := ![1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB183I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0]
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
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
    · exact ![2048383]
    · exact ![131, 131, 131]
    · exact ![2571353]
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N0, I89N1, I89N2, I103N0, I103N1, I103N2, I107N0, I107N1, I107N2, I113N0, I113N1, I113N2, I131N0, I131N1, I131N2]
  Il := ![[], [I89N0, I89N1, I89N2], [], [], [I103N0, I103N1, I103N2], [I107N0, I107N1, I107N2], [], [I113N0, I113N1, I113N2], [], [I131N0, I131N1, I131N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
