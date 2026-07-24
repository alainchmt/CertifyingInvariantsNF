
import IdealArithmetic.Examples.NF3_1_172019_1.RI3_1_172019_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![19, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![19, 1, 0]] 
 ![![83, 0, 0], ![19, 1, 0], ![54, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![19, 1, 0], ![0, 19, 1], ![116, 41, 20]]]
  hmulB := by decide  
  f := ![![![514, 27, 0], ![-2241, 0, 0]], ![![114, 6, 0], ![-497, 0, 0]], ![![328, 17, 0], ![-1430, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 83, 0], ![-54, 0, 83]], ![![0, 1, 0], ![-5, 19, 1], ![-21, 41, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![23, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![23, 1, 0]] 
 ![![83, 0, 0], ![23, 1, 0], ![52, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![23, 1, 0], ![0, 23, 1], ![116, 41, 24]]]
  hmulB := by decide  
  f := ![![![852, 37, 0], ![-3071, 0, 0]], ![![230, 10, 0], ![-829, 0, 0]], ![![536, 23, 0], ![-1932, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 83, 0], ![-52, 0, 83]], ![![0, 1, 0], ![-7, 23, 1], ![-25, 41, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![40, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![40, 1, 0]] 
 ![![83, 0, 0], ![40, 1, 0], ![60, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![40, 1, 0], ![0, 40, 1], ![116, 41, 41]]]
  hmulB := by decide  
  f := ![![![761, 19, 0], ![-1577, 0, 0]], ![![360, 9, 0], ![-746, 0, 0]], ![![580, 14, 0], ![-1202, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 83, 0], ![-60, 0, 83]], ![![0, 1, 0], ![-20, 40, 1], ![-48, 41, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![19, 1, 0]] ![![83, 0, 0], ![23, 1, 0]]
  ![![83, 0, 0], ![-61, -41, 1]] where
 M := ![![![6889, 0, 0], ![1909, 83, 0]], ![![1577, 83, 0], ![437, 42, 1]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![23, 1, 0], ![0, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![6, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-61, -41, 1]] ![![83, 0, 0], ![40, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![3320, 83, 0]], ![![-5063, -3403, 83], ![-2324, -1660, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![40, 1, 0]]], ![![![-61, -41, 1]], ![![-28, -20, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [32, 40, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 19, 85], [49, 69, 4], [0, 1]]
 g := ![![[57, 15, 9], [85, 72], [0, 71], [56, 34, 87], [74, 5, 1], []], ![[72, 34, 77, 8], [], [2, 69], [39, 47, 14, 69], [32, 58, 66, 2], [17, 16]], ![[10, 10, 20, 47], [32, 72], [73, 55], [6, 74, 60, 73], [23, 88, 29, 20], [9, 16]]]
 h' := ![![[45, 19, 85], [38, 84, 3], [55, 51, 61], [77, 33, 58], [35, 84, 49], [0, 0, 1], [0, 1]], ![[49, 69, 4], [73, 35, 49], [42, 82], [62, 55, 43], [22, 11, 19], [57, 73, 69], [45, 19, 85]], ![[0, 1], [80, 59, 37], [83, 45, 28], [4, 1, 77], [87, 83, 21], [66, 16, 19], [49, 69, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 14], []]
 b := ![[], [79, 72, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [32, 40, 84, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8900, 979, 979]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-100, 11, 11]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23883, -11438, -1641]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-23883, -11438, -1641]] 
 ![![97, 0, 0], ![0, 97, 0], ![58, 1, 1]] where
  M :=![![![-23883, -11438, -1641], ![-190356, -91164, -13079], ![-1517164, -726595, -104243]]]
  hmulB := by decide  
  f := ![![![-751, -113, 26]], ![![3016, 315, -87]], ![![-522, -70, 17]]]
  g := ![![![735, -101, -1641], ![5858, -805, -13079], ![46690, -6416, -104243]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [63, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 96], [0, 1]]
 g := ![![[84, 62], [79], [11], [25], [48], [43, 1]], ![[34, 35], [79], [11], [25], [48], [86, 96]]]
 h' := ![![[43, 96], [14, 81], [74, 51], [31, 37], [32, 5], [7, 40], [0, 1]], ![[0, 1], [5, 16], [36, 46], [70, 60], [53, 92], [78, 57], [43, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [57, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [63, 54, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-338, 817, 526]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-318, 3, 526]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-751, -113, 26]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-751, -113, 26]] 
 ![![97, 0, 0], ![95, 1, 0], ![93, 0, 1]] where
  M :=![![![-751, -113, 26], ![3016, 315, -87], ![-10092, -551, 228]]]
  hmulB := by decide  
  f := ![![![-23883, -11438, -1641]], ![![-25353, -12142, -1742]], ![![-38539, -18457, -2648]]]
  g := ![![![78, -113, 26], ![-194, 315, -87], ![217, -551, 228]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-23883, -11438, -1641]] ![![-751, -113, 26]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [97, 38, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 59, 37], [93, 41, 64], [0, 1]]
 g := ![![[85, 53, 25], [9, 96], [66, 31, 96], [63, 68], [66, 33], [1]], ![[15, 16, 71, 25], [50, 16], [86, 36, 0, 9], [20, 76], [5, 23], [83, 65, 7, 52]], ![[99, 82, 5, 20], [98, 47], [83, 95, 91, 36], [85, 30], [33, 95], [78, 58, 27, 49]]]
 h' := ![![[37, 59, 37], [42, 54, 5], [62, 62, 55], [74, 59, 46], [78, 47, 13], [4, 63, 29], [0, 1]], ![[93, 41, 64], [11, 46, 82], [35, 24, 4], [33, 45, 29], [16, 63, 50], [81, 49, 86], [37, 59, 37]], ![[0, 1], [10, 1, 14], [27, 15, 42], [50, 98, 26], [35, 92, 38], [2, 90, 87], [93, 41, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51], []]
 b := ![[], [11, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [97, 38, 72, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35653, -13837, -9595]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![353, -137, -95]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![25, 16, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![25, 16, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![25, 16, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![25, 16, 1], ![116, 66, 17], ![1972, 813, 83]]]
  hmulB := by decide  
  f := ![![![-24, -16, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -16, 103]], ![![0, 0, 1], ![-3, -2, 17], ![-1, -5, 83]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [37, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 102], [0, 1]]
 g := ![![[31, 82], [4, 34], [27, 1], [1], [46], [89, 1]], ![[16, 21], [43, 69], [13, 102], [1], [46], [75, 102]]]
 h' := ![![[89, 102], [58, 59], [31, 31], [31, 102], [58, 1], [3, 56], [0, 1]], ![[0, 1], [56, 44], [9, 72], [45, 1], [44, 102], [43, 47], [89, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [4, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [37, 14, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![400, 1183, 325]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75, -39, 325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-17, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-17, 1, 0]] 
 ![![103, 0, 0], ![86, 1, 0], ![20, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-17, 1, 0], ![0, -17, 1], ![116, 41, -16]]]
  hmulB := by decide  
  f := ![![![1684, -99, 0], ![10197, 0, 0]], ![![1412, -83, 0], ![8550, 0, 0]], ![![360, -21, 0], ![2180, 1, 0]]]
  g := ![![![1, 0, 0], ![-86, 103, 0], ![-20, 0, 103]], ![![-1, 1, 0], ![14, -17, 1], ![-30, 41, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![25, 16, 1]] ![![103, 0, 0], ![-17, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1751, 103, 0]], ![![2575, 1648, 103], ![-309, -206, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-17, 1, 0]]], ![![![25, 16, 1]], ![![-3, -2, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [51, 56, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 8, 18], [82, 98, 89], [0, 1]]
 g := ![![[62, 105, 61], [77, 57, 57], [86, 89], [79, 106, 11], [68, 101], [1]], ![[102, 29, 20, 67], [61, 52, 61, 91], [33, 37], [99, 96, 31, 94], [103, 53], [104, 56, 30, 54]], ![[83, 18, 31, 23], [55, 38, 33, 34], [86, 34], [91, 76, 32, 75], [17, 11], [93, 96, 68, 53]]]
 h' := ![![[48, 8, 18], [32, 70, 32], [86, 100, 59], [37, 28, 93], [96, 70, 15], [56, 51, 23], [0, 1]], ![[82, 98, 89], [71, 26, 9], [77, 103, 92], [72, 43, 95], [97, 89, 55], [0, 71, 69], [48, 8, 18]], ![[0, 1], [74, 11, 66], [34, 11, 63], [51, 36, 26], [42, 55, 37], [69, 92, 15], [82, 98, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 96], []]
 b := ![[], [13, 57, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [51, 56, 84, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8881, 963, 963]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83, 9, 9]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 6, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![1, 6, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![1, 6, 1]] where
  M :=![![![1, 6, 1], ![116, 42, 7], ![812, 403, 49]]]
  hmulB := by decide  
  f := ![![![-7, 1, 0]], ![![0, -7, 1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![1, 0, 7], ![7, 1, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [60, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 108], [0, 1]]
 g := ![![[34, 20], [5], [50, 29], [42, 102], [78], [31, 1]], ![[0, 89], [5], [77, 80], [43, 7], [78], [62, 108]]]
 h' := ![![[31, 108], [6, 42], [52, 88], [96, 62], [56, 50], [102, 29], [0, 1]], ![[0, 1], [0, 67], [55, 21], [56, 47], [80, 59], [20, 80], [31, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [33, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [60, 78, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4663, 3235, 521]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 1, 521]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-7, 1, 0]] 
 ![![109, 0, 0], ![102, 1, 0], ![60, 0, 1]] where
  M :=![![![-7, 1, 0], ![0, -7, 1], ![116, 41, -6]]]
  hmulB := by decide  
  f := ![![![1, 6, 1]], ![![2, 6, 1]], ![![8, 7, 1]]]
  g := ![![![-1, 1, 0], ![6, -7, 1], ![-34, 41, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![1, 6, 1]] ![![-7, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![9, 37, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![9, 37, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![9, 37, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![9, 37, 1], ![116, 50, 38], ![4408, 1674, 88]]]
  hmulB := by decide  
  f := ![![![-8, -37, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -37, 113]], ![![0, 0, 1], ![-2, -12, 38], ![32, -14, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [25, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 112], [0, 1]]
 g := ![![[45, 104], [9], [91], [57], [], [5, 1]], ![[0, 9], [9], [91], [57], [], [10, 112]]]
 h' := ![![[5, 112], [1, 45], [0, 110], [44, 59], [0, 31], [101], [0, 1]], ![[0, 1], [0, 68], [98, 3], [0, 54], [42, 82], [101], [5, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [15, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [25, 108, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-662, 229, -61]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 22, -61]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-38, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-38, 1, 0]] 
 ![![113, 0, 0], ![75, 1, 0], ![25, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-38, 1, 0], ![0, -38, 1], ![116, 41, -37]]]
  hmulB := by decide  
  f := ![![![191, -5, 0], ![565, 0, 0]], ![![153, -4, 0], ![453, 0, 0]], ![![51, -1, 0], ![151, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 113, 0], ![-25, 0, 113]], ![![-1, 1, 0], ![25, -38, 1], ![-18, 41, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![9, 37, 1]] ![![113, 0, 0], ![-38, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-4294, 113, 0]], ![![1017, 4181, 113], ![-226, -1356, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-38, 1, 0]]], ![![![9, 37, 1]], ![![-2, -12, 0]]]]
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


lemma PB118I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 117 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 117 (by omega)

def PB118I2 : PrimesBelowBoundCertificateInterval O 79 117 118 where
  m := 8
  g := ![3, 1, 2, 1, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB118I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
  β := ![I83N0, I83N1, I83N2, I97N1, I103N1, I109N1, I113N1]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [], [I103N1], [], [I109N1], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
