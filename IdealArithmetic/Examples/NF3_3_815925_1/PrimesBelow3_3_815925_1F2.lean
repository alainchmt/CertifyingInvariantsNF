
import IdealArithmetic.Examples.NF3_3_815925_1.RI3_3_815925_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-984, -11, 27]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-984, -11, 27]] 
 ![![83, 0, 0], ![0, 83, 0], ![65, 58, 1]] where
  M :=![![![-984, -11, 27], ![-346, -1, 10], ![375, 9, -7]]]
  hmulB := by decide  
  f := ![![![1, -2, 1]], ![![-16, 39, -6]], ![![-10, 25, -3]]]
  g := ![![![-33, -19, 27], ![-12, -7, 10], ![10, 5, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [2, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 82], [0, 1]]
 g := ![![[58, 44], [43, 75], [17], [27], [51, 10], [1]], ![[17, 39], [58, 8], [17], [27], [53, 73], [1]]]
 h' := ![![[50, 82], [80, 25], [10, 18], [58, 10], [64, 44], [81, 50], [0, 1]], ![[0, 1], [2, 58], [80, 65], [60, 73], [23, 39], [8, 33], [50, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [25, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [2, 33, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![382, 134, 1150]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-896, -802, 1150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -1]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1, 2, -1]] 
 ![![83, 0, 0], ![15, 1, 0], ![31, 0, 1]] where
  M :=![![![-1, 2, -1], ![16, -39, 6], ![-33, 57, -34]]]
  hmulB := by decide  
  f := ![![![984, 11, -27]], ![![182, 2, -5]], ![![363, 4, -10]]]
  g := ![![![0, 2, -1], ![5, -39, 6], ![2, 57, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-984, -11, 27]] ![![-1, 2, -1]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-40, -18, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-40, -18, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![49, 71, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-40, -18, 1], ![-48, 14, -70], ![225, -633, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -71, 89]], ![![-1, -1, 1], ![38, 56, -70], ![24, 24, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [60, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 88], [0, 1]]
 g := ![![[69, 72], [8], [42], [66, 68], [32, 69], [1]], ![[50, 17], [8], [42], [53, 21], [62, 20], [1]]]
 h' := ![![[43, 88], [62, 61], [39, 50], [45, 24], [38, 35], [29, 43], [0, 1]], ![[0, 1], [15, 28], [53, 39], [9, 65], [30, 54], [9, 46], [43, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [57, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [60, 46, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1170, -942, 2129]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1159, -1709, 2129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-19, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-19, 1, 0]] 
 ![![89, 0, 0], ![70, 1, 0], ![39, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-19, 1, 0], ![2, -20, 4], ![-12, 36, -17]]]
  hmulB := by decide  
  f := ![![![-325, 3638, -728], ![178, 16198, 0]], ![![-266, 2859, -572], ![90, 12727, 0]], ![![-139, 1594, -319], ![94, 7098, 0]]]
  g := ![![![1, 0, 0], ![-70, 89, 0], ![-39, 0, 89]], ![![-1, 1, 0], ![14, -20, 4], ![-21, 36, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-40, -18, 1]] ![![89, 0, 0], ![-19, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1691, 89, 0]], ![![-3560, -1602, 89], ![712, 356, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-19, 1, 0]]], ![![![-40, -18, 1]], ![![8, 4, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 11, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-4, 11, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![93, 11, 1]] where
  M :=![![![-4, 11, 1], ![10, 21, 46], ![-123, 411, 55]]]
  hmulB := by decide  
  f := ![![![-183, -2, 5]], ![![-64, -1, 2]], ![![-182, -2, 5]]]
  g := ![![![-1, 0, 1], ![-44, -5, 46], ![-54, -2, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [51, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 96], [0, 1]]
 g := ![![[2, 33], [64], [44], [93], [94], [92, 1]], ![[31, 64], [64], [44], [93], [94], [87, 96]]]
 h' := ![![[92, 96], [25, 79], [66, 89], [46, 74], [91, 44], [61, 71], [0, 1]], ![[0, 1], [18, 18], [9, 8], [64, 23], [65, 53], [94, 26], [92, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [32, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [51, 5, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44741, 60462, 169162]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-161725, -18560, 169162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-183, -2, 5]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-183, -2, 5]] 
 ![![97, 0, 0], ![51, 1, 0], ![42, 0, 1]] where
  M :=![![![-183, -2, 5], ![-64, -1, 2], ![69, 3, -2]]]
  hmulB := by decide  
  f := ![![![-4, 11, 1]], ![![-2, 6, 1]], ![![-3, 9, 1]]]
  g := ![![![-3, -2, 5], ![-1, -1, 2], ![0, 3, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-4, 11, 1]] ![![-183, -2, 5]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [78, 57, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 93, 5], [72, 7, 96], [0, 1]]
 g := ![![[25, 10, 81], [69, 33], [19], [2, 30], [11, 65], [1]], ![[70, 23, 55, 37], [74, 88], [43, 98, 24, 52], [87, 88], [78, 4], [4, 83, 81, 24]], ![[90, 17, 18, 4], [1, 21], [73, 7, 66, 49], [84, 54], [75, 31], [92, 41, 46, 77]]]
 h' := ![![[70, 93, 5], [50, 91, 9], [33, 51, 29], [15, 76], [75, 64, 63], [23, 44, 41], [0, 1]], ![[72, 7, 96], [99, 38, 13], [35, 29, 54], [83, 99, 77], [1, 2, 54], [96, 29, 2], [70, 93, 5]], ![[0, 1], [59, 73, 79], [95, 21, 18], [33, 27, 24], [90, 35, 85], [48, 28, 58], [72, 7, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 90], []]
 b := ![[], [52, 46, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [78, 57, 60, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-358651, 129987, -820827]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3551, 1287, -8127]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![12, 44, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![12, 44, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![12, 44, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![12, 44, 1], ![76, 4, 178], ![-519, 1599, 137]]]
  hmulB := by decide  
  f := ![![![-11, -44, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -44, 103]], ![![0, 0, 1], ![-20, -76, 178], ![-21, -43, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 102], [0, 1]]
 g := ![![[1, 1], [20, 98], [6, 92], [76], [91], [98, 1]], ![[99, 102], [45, 5], [61, 11], [76], [91], [93, 102]]]
 h' := ![![[98, 102], [3, 1], [73, 43], [92, 35], [67, 30], [25, 20], [0, 1]], ![[0, 1], [101, 102], [64, 60], [20, 68], [20, 73], [28, 83], [98, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [102, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![469, 106, 1318]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-149, -562, 1318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![28, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![28, 1, 0]] 
 ![![103, 0, 0], ![28, 1, 0], ![69, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![28, 1, 0], ![2, 27, 4], ![-12, 36, 30]]]
  hmulB := by decide  
  f := ![![![13549, 203633, 30176], ![5665, -777032, 0]], ![![3680, 55335, 8200], ![1546, -211150, 0]], ![![9067, 136414, 20215], ![3830, -520536, 0]]]
  g := ![![![1, 0, 0], ![-28, 103, 0], ![-69, 0, 103]], ![![0, 1, 0], ![-10, 27, 4], ![-30, 36, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![12, 44, 1]] ![![103, 0, 0], ![28, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![2884, 103, 0]], ![![1236, 4532, 103], ![412, 1236, 206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![28, 1, 0]]], ![![![12, 44, 1]], ![![4, 12, 2]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 166, -49]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-77, 166, -49]] 
 ![![107, 0, 0], ![0, 107, 0], ![78, 25, 1]] where
  M :=![![![-77, 166, -49], ![920, -2007, 566], ![-2433, 5241, -1558]]]
  hmulB := by decide  
  f := ![![![-1500, -17, 41]], ![![-526, -7, 14]], ![![-1211, -14, 33]]]
  g := ![![![35, 13, -49], ![-404, -151, 566], ![1113, 413, -1558]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [48, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 106], [0, 1]]
 g := ![![[95, 29], [18, 10], [11], [3, 83], [35], [41, 1]], ![[0, 78], [0, 97], [11], [89, 24], [35], [82, 106]]]
 h' := ![![[41, 106], [99, 55], [92, 63], [70, 92], [84, 46], [65, 28], [0, 1]], ![[0, 1], [0, 52], [0, 44], [97, 15], [44, 61], [36, 79], [41, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [43, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [48, 66, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19659, 24528, 72975]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53013, -16821, 72975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1500, 17, -41]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1500, 17, -41]] 
 ![![107, 0, 0], ![5, 1, 0], ![49, 0, 1]] where
  M :=![![![1500, 17, -41], ![526, 7, -14], ![-573, -3, 17]]]
  hmulB := by decide  
  f := ![![![77, -166, 49]], ![![-5, 11, -3]], ![![58, -125, 37]]]
  g := ![![![32, 17, -41], ![11, 7, -14], ![-13, -3, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-77, 166, -49]] ![![1500, 17, -41]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [33, 91, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 50, 66], [67, 58, 43], [0, 1]]
 g := ![![[13, 73, 81], [95, 20], [78, 29, 71], [28, 52, 75], [10, 26], [1]], ![[31, 68, 65, 87], [19, 43], [21, 37, 96, 48], [36, 19, 32, 71], [29, 28], [95, 66, 29, 63]], ![[29, 50, 65, 60], [17, 26], [106, 41, 96, 97], [17, 34, 76, 31], [103, 25], [99, 101, 92, 46]]]
 h' := ![![[7, 50, 66], [46, 101, 9], [42, 99, 42], [57, 3, 92], [105, 96, 27], [76, 18, 74], [0, 1]], ![[67, 58, 43], [0, 30, 103], [55, 17, 32], [47, 16, 84], [44, 95, 54], [42, 15, 30], [7, 50, 66]], ![[0, 1], [58, 87, 106], [40, 102, 35], [107, 90, 42], [6, 27, 28], [35, 76, 5], [67, 58, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 60], []]
 b := ![[], [17, 66, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [33, 91, 35, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1417, 8393, 3924]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, 77, 36]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![28, -15, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![28, -15, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![28, 98, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![28, -15, 1], ![-42, 79, -58], ![189, -525, 35]]]
  hmulB := by decide  
  f := ![![![-27, 15, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -98, 113]], ![![0, -1, 1], ![14, 51, -58], ![-7, -35, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [32, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 112], [0, 1]]
 g := ![![[48, 53], [95], [85], [63], [5, 14], [46, 1]], ![[0, 60], [95], [85], [63], [84, 99], [92, 112]]]
 h' := ![![[46, 112], [39, 36], [64, 35], [80, 57], [66, 17], [110, 50], [0, 1]], ![[0, 1], [0, 77], [92, 78], [103, 56], [57, 96], [37, 63], [46, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [112, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [32, 67, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1780, -98, 4406]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1076, -3822, 4406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-55, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-55, 1, 0]] 
 ![![113, 0, 0], ![58, 1, 0], ![78, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-55, 1, 0], ![2, -56, 4], ![-12, 36, -53]]]
  hmulB := by decide  
  f := ![![![4764, -187229, 13376], ![-3955, -377872, 0]], ![![2443, -96078, 6864], ![-2033, -193908, 0]], ![![3304, -129238, 9233], ![-2698, -260832, 0]]]
  g := ![![![1, 0, 0], ![-58, 113, 0], ![-78, 0, 113]], ![![-1, 1, 0], ![26, -56, 4], ![18, 36, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![28, -15, 1]] ![![113, 0, 0], ![-55, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-6215, 113, 0]], ![![3164, -1695, 113], ![-1582, 904, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-55, 1, 0]]], ![![![28, -15, 1]], ![![-14, 8, -1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 32, -9]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-21, 32, -9]] 
 ![![127, 0, 0], ![0, 127, 0], ![87, 67, 1]] where
  M :=![![![-21, 32, -9], ![172, -377, 110], ![-465, 1017, -290]]]
  hmulB := by decide  
  f := ![![![-20, 1, 1]], ![![-10, 15, 6]], ![![-19, 9, 4]]]
  g := ![![![6, 5, -9], ![-74, -61, 110], ![195, 161, -290]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [124, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 126], [0, 1]]
 g := ![![[51, 42], [99, 100], [7, 21], [78, 2], [50, 31], [26, 1]], ![[0, 85], [32, 27], [45, 106], [3, 125], [94, 96], [52, 126]]]
 h' := ![![[26, 126], [43, 13], [21, 10], [107, 23], [23, 111], [78, 44], [0, 1]], ![[0, 1], [0, 114], [27, 117], [70, 104], [115, 16], [79, 83], [26, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [58, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [124, 101, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-131, 375, 470]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-323, -245, 470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 1, 1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-20, 1, 1]] 
 ![![127, 0, 0], ![111, 1, 0], ![123, 0, 1]] where
  M :=![![![-20, 1, 1], ![-10, 15, 6], ![-3, 51, 19]]]
  hmulB := by decide  
  f := ![![![-21, 32, -9]], ![![-17, 25, -7]], ![![-24, 39, -11]]]
  g := ![![![-2, 1, 1], ![-19, 15, 6], ![-63, 51, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-21, 32, -9]] ![![-20, 1, 1]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![3, -28, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![3, -28, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![3, 103, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![3, -28, 1], ![-68, 67, -110], ![345, -993, -16]]]
  hmulB := by decide  
  f := ![![![-2, 28, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -103, 131]], ![![0, -1, 1], ![2, 87, -110], ![3, 5, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [11, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 130], [0, 1]]
 g := ![![[78, 12], [33, 102], [60], [125], [27], [75], [1]], ![[0, 119], [25, 29], [60], [125], [27], [75], [1]]]
 h' := ![![[59, 130], [30, 55], [127, 44], [130, 45], [8, 115], [82, 114], [120, 59], [0, 1]], ![[0, 1], [0, 76], [103, 87], [34, 86], [112, 16], [127, 17], [64, 72], [59, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [116, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [11, 72, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![167, 2808, 3156]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-71, -2460, 3156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-21, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-21, 1, 0]] 
 ![![131, 0, 0], ![110, 1, 0], ![16, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-21, 1, 0], ![2, -22, 4], ![-12, 36, -19]]]
  hmulB := by decide  
  f := ![![![23860, -272799, 49608], ![-5895, -1624662, 0]], ![![20050, -229049, 41652], ![-4846, -1364103, 0]], ![![2915, -33319, 6059], ![-715, -198432, 0]]]
  g := ![![![1, 0, 0], ![-110, 131, 0], ![-16, 0, 131]], ![![-1, 1, 0], ![18, -22, 4], ![-28, 36, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![3, -28, 1]] ![![131, 0, 0], ![-21, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-2751, 131, 0]], ![![393, -3668, 131], ![-131, 655, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-21, 1, 0]]], ![![![3, -28, 1]], ![![-1, 5, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1319, 6418, 2444]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-1319, 6418, 2444]] 
 ![![137, 0, 0], ![0, 137, 0], ![116, 57, 1]] where
  M :=![![![-1319, 6418, 2444], ![-16492, 80247, 30560], ![-55020, 267708, 101945]]]
  hmulB := by decide  
  f := ![![![2745, 34, -76]], ![![980, -25, -16]], ![![2724, 19, -71]]]
  g := ![![![-2079, -970, 2444], ![-25996, -12129, 30560], ![-86720, -40461, 101945]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [25, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 136], [0, 1]]
 g := ![![[2, 11], [87], [50], [121, 101], [73], [34], [1]], ![[0, 126], [87], [50], [3, 36], [73], [34], [1]]]
 h' := ![![[87, 136], [10, 55], [104, 118], [126, 18], [28, 85], [49, 115], [112, 87], [0, 1]], ![[0, 1], [0, 82], [95, 19], [48, 119], [25, 52], [53, 22], [9, 50], [87, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [117, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [25, 50, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3308, 2216, 9439]
  a := ![14, -1, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7968, -3911, 9439]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2745, 34, -76]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![2745, 34, -76]] 
 ![![137, 0, 0], ![44, 1, 0], ![7, 0, 1]] where
  M :=![![![2745, 34, -76], ![980, -25, -16], ![-1092, 84, 1]]]
  hmulB := by decide  
  f := ![![![-1319, 6418, 2444]], ![![-544, 2647, 1008]], ![![-469, 2282, 869]]]
  g := ![![![13, 34, -76], ![16, -25, -16], ![-35, 84, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-1319, 6418, 2444]] ![![2745, 34, -76]]
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


lemma PB201I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB201I2 : PrimesBelowBoundCertificateInterval O 79 137 201 where
  m := 11
  g := ![2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB201I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
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
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I103N1, I107N1, I113N1, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [], [I103N1], [I107N1], [], [I113N1], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
