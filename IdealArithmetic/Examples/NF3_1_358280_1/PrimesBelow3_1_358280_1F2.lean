
import IdealArithmetic.Examples.NF3_1_358280_1.RI3_1_358280_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [70, 56, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 54, 22], [38, 28, 61], [0, 1]]
 g := ![![[37, 5, 28], [43, 48, 28], [61, 37], [43, 10], [53, 21, 1], []], ![[10, 42, 28, 76], [75, 35, 55, 43], [15, 29], [31, 40], [72, 13, 41, 67], [7, 69]], ![[78, 12, 66, 59], [0, 3, 61, 30], [76, 81], [51, 7], [15, 69, 50, 7], [51, 69]]]
 h' := ![![[66, 54, 22], [61, 70, 32], [32, 24, 51], [22, 5, 28], [25, 44, 33], [0, 0, 1], [0, 1]], ![[38, 28, 61], [75, 32, 29], [80, 64, 47], [36, 20, 64], [31, 36, 66], [48, 80, 28], [66, 54, 22]], ![[0, 1], [10, 64, 22], [3, 78, 68], [29, 58, 74], [14, 3, 67], [32, 3, 54], [38, 28, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 72], []]
 b := ![[], [51, 53, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [70, 56, 62, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24070, 1494, 1494]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-290, 18, 18]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![40, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![40, 1, 0]] 
 ![![89, 0, 0], ![40, 1, 0], ![2, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![40, 1, 0], ![0, 40, 1], ![-142, 30, 41]]]
  hmulB := by decide  
  f := ![![![1081, 27, 0], ![-2403, 0, 0]], ![![520, 13, 0], ![-1156, 0, 0]], ![![18, 0, 0], ![-40, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 89, 0], ![-2, 0, 89]], ![![0, 1, 0], ![-18, 40, 1], ![-16, 30, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-28, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-28, 1, 0]] 
 ![![89, 0, 0], ![61, 1, 0], ![17, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-28, 1, 0], ![0, -28, 1], ![-142, 30, -27]]]
  hmulB := by decide  
  f := ![![![1373, -49, 0], ![4361, 0, 0]], ![![953, -34, 0], ![3027, 0, 0]], ![![261, -9, 0], ![829, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 89, 0], ![-17, 0, 89]], ![![-1, 1, 0], ![19, -28, 1], ![-17, 30, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-13, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-13, 1, 0]] 
 ![![89, 0, 0], ![76, 1, 0], ![9, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-13, 1, 0], ![0, -13, 1], ![-142, 30, -12]]]
  hmulB := by decide  
  f := ![![![729, -56, 0], ![4984, 0, 0]], ![![612, -47, 0], ![4184, 0, 0]], ![![93, -7, 0], ![636, 1, 0]]]
  g := ![![![1, 0, 0], ![-76, 89, 0], ![-9, 0, 89]], ![![-1, 1, 0], ![11, -13, 1], ![-26, 30, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![40, 1, 0]] ![![89, 0, 0], ![-28, 1, 0]]
  ![![89, 0, 0], ![-52, 12, 1]] where
 M := ![![![7921, 0, 0], ![-2492, 89, 0]], ![![3560, 89, 0], ![-1120, 12, 1]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![24, -11, -1], ![89, 0, 0]]], ![![![40, 1, 0], ![0, 0, 0]], ![![40, -12, -1], ![90, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-52, 12, 1]] ![![89, 0, 0], ![-13, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1157, 89, 0]], ![![-4628, 1068, 89], ![534, -178, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-13, 1, 0]]], ![![![-52, 12, 1]], ![![6, -2, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-55, -9, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-55, -9, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![42, 88, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-55, -9, 1], ![-142, -25, -8], ![1136, -382, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -88, 97]], ![![-1, -1, 1], ![2, 7, -8], ![26, 26, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [30, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 96], [0, 1]]
 g := ![![[43, 32], [81], [32], [66], [61], [68, 1]], ![[85, 65], [81], [32], [66], [61], [39, 96]]]
 h' := ![![[68, 96], [13, 56], [42, 9], [56, 56], [22, 58], [94, 35], [0, 1]], ![[0, 1], [38, 41], [72, 88], [81, 41], [86, 39], [49, 62], [68, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [94, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [30, 29, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![428, -1422, 352]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-148, -334, 352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![8, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![8, 1, 0]] 
 ![![97, 0, 0], ![8, 1, 0], ![33, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![8, 1, 0], ![0, 8, 1], ![-142, 30, 9]]]
  hmulB := by decide  
  f := ![![![569, 71, 0], ![-6887, 0, 0]], ![![40, 5, 0], ![-484, 0, 0]], ![![185, 23, 0], ![-2239, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 97, 0], ![-33, 0, 97]], ![![0, 1, 0], ![-1, 8, 1], ![-7, 30, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-55, -9, 1]] ![![97, 0, 0], ![8, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![776, 97, 0]], ![![-5335, -873, 97], ![-582, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![8, 1, 0]]], ![![![-55, -9, 1]], ![![-6, -1, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [54, 21, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 92, 69], [57, 8, 32], [0, 1]]
 g := ![![[45, 73, 22], [82, 96], [50, 45, 6], [64, 6], [17, 76], [1]], ![[40, 12, 47, 63], [98, 85], [23, 21, 37, 90], [68, 77], [89, 52], [67, 69, 4, 57]], ![[93, 39, 63, 28], [43, 23], [72, 73, 27, 61], [0, 45], [85, 97], [4, 16, 55, 44]]]
 h' := ![![[95, 92, 69], [38, 61, 27], [27, 86, 46], [58, 86, 39], [79, 29, 62], [47, 80, 51], [0, 1]], ![[57, 8, 32], [40, 46, 82], [22, 19, 40], [96, 63, 85], [58, 13, 73], [4, 56, 70], [95, 92, 69]], ![[0, 1], [25, 95, 93], [23, 97, 15], [76, 53, 78], [51, 59, 67], [46, 66, 81], [57, 8, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 53], []]
 b := ![[], [48, 80, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [54, 21, 50, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103222, 39895, -11211]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1022, 395, -111]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![111, 30, 2]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![111, 30, 2]] 
 ![![103, 0, 0], ![0, 103, 0], ![4, 15, 1]] where
  M :=![![![111, 30, 2], ![-284, 171, 32], ![-4544, 676, 203]]]
  hmulB := by decide  
  f := ![![![-127, 46, -6]], ![![852, -307, 40]], ![![64, -23, 3]]]
  g := ![![![1, 0, 2], ![-4, -3, 32], ![-52, -23, 203]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [75, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 102], [0, 1]]
 g := ![![[94, 38], [63, 4], [16, 58], [16], [52], [57, 1]], ![[97, 65], [85, 99], [26, 45], [16], [52], [11, 102]]]
 h' := ![![[57, 102], [13, 55], [36, 2], [91, 77], [40, 99], [51, 84], [0, 1]], ![[0, 1], [58, 48], [47, 101], [51, 26], [18, 4], [101, 19], [57, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [50, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [75, 46, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-304, -1140, 130]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -30, 130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, -46, 6]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![127, -46, 6]] 
 ![![103, 0, 0], ![87, 1, 0], ![53, 0, 1]] where
  M :=![![![127, -46, 6], ![-852, 307, -40], ![5680, -2052, 267]]]
  hmulB := by decide  
  f := ![![![-111, -30, -2]], ![![-91, -27, -2]], ![![-13, -22, -3]]]
  g := ![![![37, -46, 6], ![-247, 307, -40], ![1651, -2052, 267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![111, 30, 2]] ![![127, -46, 6]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-15, 37, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-15, 37, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![92, 37, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-15, 37, 1], ![-142, 15, 38], ![-5396, 998, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -37, 107]], ![![-1, 0, 1], ![-34, -13, 38], ![-96, -9, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [16, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 106], [0, 1]]
 g := ![![[45, 87], [38, 102], [100], [29, 86], [105], [29, 1]], ![[0, 20], [0, 5], [100], [62, 21], [105], [58, 106]]]
 h' := ![![[29, 106], [34, 80], [17, 40], [71, 10], [44, 34], [71, 76], [0, 1]], ![[0, 1], [0, 27], [0, 67], [40, 97], [67, 73], [28, 31], [29, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [66, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [16, 78, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-410, -130, -44]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, 14, -44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-38, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-38, 1, 0]] 
 ![![107, 0, 0], ![69, 1, 0], ![54, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-38, 1, 0], ![0, -38, 1], ![-142, 30, -37]]]
  hmulB := by decide  
  f := ![![![1711, -45, 0], ![4815, 0, 0]], ![![1141, -30, 0], ![3211, 0, 0]], ![![926, -24, 0], ![2606, 1, 0]]]
  g := ![![![1, 0, 0], ![-69, 107, 0], ![-54, 0, 107]], ![![-1, 1, 0], ![24, -38, 1], ![-2, 30, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-15, 37, 1]] ![![107, 0, 0], ![-38, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4066, 107, 0]], ![![-1605, 3959, 107], ![428, -1391, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-38, 1, 0]]], ![![![-15, 37, 1]], ![![4, -13, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [4, 3, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 25, 5], [47, 83, 104], [0, 1]]
 g := ![![[100, 12, 46], [91, 75], [89, 25, 106], [35, 86, 20], [20, 22], [1]], ![[43, 37, 69, 108], [81, 66], [95, 43], [3, 97, 87, 49], [30, 49], [105, 35, 42, 16]], ![[44, 70, 10, 61], [1, 15], [26, 80, 56, 15], [4, 69, 87, 38], [35, 34], [78, 72, 101, 93]]]
 h' := ![![[36, 25, 5], [41, 73, 68], [80, 49, 82], [78, 50, 18], [45, 94, 67], [105, 106, 83], [0, 1]], ![[47, 83, 104], [18, 100, 14], [61, 97, 75], [51, 40], [62, 14, 36], [20, 62, 7], [36, 25, 5]], ![[0, 1], [17, 45, 27], [28, 72, 61], [74, 19, 91], [73, 1, 6], [70, 50, 19], [47, 83, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 97], []]
 b := ![[], [51, 26, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [4, 3, 26, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1527744, 153472, 49050]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14016, 1408, 450]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![12, 6, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![12, 6, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![12, 6, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![12, 6, 1], ![-142, 42, 7], ![-994, 68, 49]]]
  hmulB := by decide  
  f := ![![![-11, -6, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -6, 113]], ![![0, 0, 1], ![-2, 0, 7], ![-14, -2, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [47, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 112], [0, 1]]
 g := ![![[68, 81], [62], [13], [15], [14, 18], [81, 1]], ![[75, 32], [62], [13], [15], [3, 95], [49, 112]]]
 h' := ![![[81, 112], [85, 9], [93, 66], [34, 37], [20, 44], [35, 73], [0, 1]], ![[0, 1], [23, 104], [15, 47], [93, 76], [81, 69], [72, 40], [81, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [47, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [47, 32, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![726, -202, 4]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, -2, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-7, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-7, 1, 0]] 
 ![![113, 0, 0], ![106, 1, 0], ![64, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-7, 1, 0], ![0, -7, 1], ![-142, 30, -6]]]
  hmulB := by decide  
  f := ![![![694, -99, 0], ![11187, 0, 0]], ![![652, -93, 0], ![10510, 0, 0]], ![![400, -57, 0], ![6448, 1, 0]]]
  g := ![![![1, 0, 0], ![-106, 113, 0], ![-64, 0, 113]], ![![-1, 1, 0], ![6, -7, 1], ![-26, 30, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![12, 6, 1]] ![![113, 0, 0], ![-7, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-791, 113, 0]], ![![1356, 678, 113], ![-226, 0, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-7, 1, 0]]], ![![![12, 6, 1]], ![![-2, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![2, 55, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![2, 55, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![2, 55, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![2, 55, 1], ![-142, 32, 56], ![-7952, 1538, 88]]]
  hmulB := by decide  
  f := ![![![-1, -55, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -55, 127]], ![![0, 0, 1], ![-2, -24, 56], ![-64, -26, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [52, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 126], [0, 1]]
 g := ![![[112, 22], [88, 17], [94, 21], [53, 32], [76, 70], [18, 1]], ![[0, 105], [13, 110], [91, 106], [121, 95], [66, 57], [36, 126]]]
 h' := ![![[18, 126], [123, 99], [65, 12], [38, 23], [112, 64], [80, 18], [0, 1]], ![[0, 1], [0, 28], [27, 115], [71, 104], [121, 63], [23, 109], [18, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [33, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [52, 109, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1084, -219, 347]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -152, 347]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-56, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-56, 1, 0]] 
 ![![127, 0, 0], ![71, 1, 0], ![39, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-56, 1, 0], ![0, -56, 1], ![-142, 30, -55]]]
  hmulB := by decide  
  f := ![![![6329, -113, 0], ![14351, 0, 0]], ![![3585, -64, 0], ![8129, 0, 0]], ![![1985, -35, 0], ![4501, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 127, 0], ![-39, 0, 127]], ![![-1, 1, 0], ![31, -56, 1], ![-1, 30, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![2, 55, 1]] ![![127, 0, 0], ![-56, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-7112, 127, 0]], ![![254, 6985, 127], ![-254, -3048, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-56, 1, 0]]], ![![![2, 55, 1]], ![![-2, -24, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4250351, 5354529, 706559]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![4250351, 5354529, 706559]] 
 ![![131, 0, 0], ![13, 1, 0], ![93, 0, 1]] where
  M :=![![![4250351, 5354529, 706559], ![-100331378, 25447121, 6061088], ![-860674496, 81501262, 31508209]]]
  hmulB := by decide  
  f := ![![![-307806885823233, 111126168651103, -14474379100913]], ![![-14855936514293, 5363373539036, -698588845509]], ![![-323286980898379, 116714879415175, -15202318516682]]]
  g := ![![![-1000523, 5354529, 706559], ![-7594085, 25447121, 6061088], ![-37026369, 81501262, 31508209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1473465, 508, -32970]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![1473465, 508, -32970]] 
 ![![131, 0, 0], ![33, 1, 0], ![90, 0, 1]] where
  M :=![![![1473465, 508, -32970], ![4681740, 484365, -32462], ![4609604, 3707880, 451903]]]
  hmulB := by decide  
  f := ![![![339251197155, -122478370324, 15953023354]], ![![68167635037, -24610262007, 3205529952]], ![![348543564990, -125833153088, 16389989715]]]
  g := ![![![33771, 508, -32970], ![-63975, 484365, -32462], ![-1209326, 3707880, 451903]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1295, 180, 56]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-1295, 180, 56]] 
 ![![131, 0, 0], ![84, 1, 0], ![18, 0, 1]] where
  M :=![![![-1295, 180, 56], ![-7952, 385, 236], ![-33512, -872, 621]]]
  hmulB := by decide  
  f := ![![![-444877, 160612, -20920]], ![![-262588, 94801, -12348]], ![![-212550, 76736, -9995]]]
  g := ![![![-133, 180, 56], ![-340, 385, 236], ![218, -872, 621]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![4250351, 5354529, 706559]] ![![1473465, 508, -32970]]
  ![![34588213229311, 5215541602313, 5343338909]] where
 M := ![![![34588213229311, 5215541602313, 5343338909]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![34588213229311, 5215541602313, 5343338909]] ![![-1295, 180, 56]]
  ![![131, 0, 0]] where
 M := ![![![-86444788927069129, 8229202506637837, 3171125972449773]]]
 hmul := by decide  
 g := ![![![![-659883884939459, 62818339745327, 24207068491983]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![12, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![12, 1, 0]] 
 ![![137, 0, 0], ![12, 1, 0], ![130, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![12, 1, 0], ![0, 12, 1], ![-142, 30, 13]]]
  hmulB := by decide  
  f := ![![![841, 70, 0], ![-9590, 0, 0]], ![![60, 5, 0], ![-684, 0, 0]], ![![818, 68, 0], ![-9328, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 137, 0], ![-130, 0, 137]], ![![0, 1, 0], ![-2, 12, 1], ![-16, 30, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![33, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![33, 1, 0]] 
 ![![137, 0, 0], ![33, 1, 0], ![7, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![33, 1, 0], ![0, 33, 1], ![-142, 30, 34]]]
  hmulB := by decide  
  f := ![![![1453, 44, 0], ![-6028, 0, 0]], ![![297, 9, 0], ![-1232, 0, 0]], ![![41, 1, 0], ![-170, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 137, 0], ![-7, 0, 137]], ![![0, 1, 0], ![-8, 33, 1], ![-10, 30, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-46, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-46, 1, 0]] 
 ![![137, 0, 0], ![91, 1, 0], ![76, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-46, 1, 0], ![0, -46, 1], ![-142, 30, -45]]]
  hmulB := by decide  
  f := ![![![231, -5, 0], ![685, 0, 0]], ![![185, -4, 0], ![549, 0, 0]], ![![200, -4, 0], ![594, 1, 0]]]
  g := ![![![1, 0, 0], ![-91, 137, 0], ![-76, 0, 137]], ![![-1, 1, 0], ![30, -46, 1], ![4, 30, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![12, 1, 0]] ![![137, 0, 0], ![33, 1, 0]]
  ![![137, 0, 0], ![-15, 45, 1]] where
 M := ![![![18769, 0, 0], ![4521, 137, 0]], ![![1644, 137, 0], ![396, 45, 1]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![33, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-15, 45, 1]] ![![137, 0, 0], ![-46, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6302, 137, 0]], ![![-2055, 6165, 137], ![548, -2055, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-46, 1, 0]]], ![![![-15, 45, 1]], ![![4, -15, 0]]]]
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


lemma PB170I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB170I2 : PrimesBelowBoundCertificateInterval O 79 137 170 where
  m := 11
  g := ![1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB170I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
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
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
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
      exact NI103N1
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
  β := ![I89N0, I89N1, I89N2, I97N1, I103N1, I107N1, I113N1, I127N1, I131N0, I131N1, I131N2, I137N0, I137N1, I137N2]
  Il := ![[], [I89N0, I89N1, I89N2], [I97N1], [], [I103N1], [I107N1], [], [I113N1], [I127N1], [I131N0, I131N1, I131N2], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
