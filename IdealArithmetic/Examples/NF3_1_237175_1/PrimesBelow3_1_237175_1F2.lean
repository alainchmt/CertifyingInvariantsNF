
import IdealArithmetic.Examples.NF3_1_237175_1.RI3_1_237175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![48, -33, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![48, -33, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![48, 50, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![48, -33, 1], ![-98, 57, -130], ![1020, 772, -41]]]
  hmulB := by decide  
  f := ![![![-47, 33, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -50, 83]], ![![0, -1, 1], ![74, 79, -130], ![36, 34, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [8, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 82], [0, 1]]
 g := ![![[11, 4], [12, 33], [17], [36], [38, 25], [1]], ![[74, 79], [13, 50], [17], [36], [79, 58], [1]]]
 h' := ![![[78, 82], [70, 2], [34, 38], [81, 73], [28, 6], [75, 78], [0, 1]], ![[0, 1], [60, 81], [10, 45], [48, 10], [81, 77], [17, 5], [78, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [60, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [8, 5, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-908, -434, -842]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![476, 502, -842]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-36, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-36, 1, 0]] 
 ![![83, 0, 0], ![47, 1, 0], ![41, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-36, 1, 0], ![2, -37, 4], ![-32, -24, -34]]]
  hmulB := by decide  
  f := ![![![5271, -127420, 13780], ![-3735, -285935, 0]], ![![3001, -72125, 7800], ![-2074, -161850, 0]], ![![2589, -62942, 6807], ![-1879, -141245, 0]]]
  g := ![![![1, 0, 0], ![-47, 83, 0], ![-41, 0, 83]], ![![-1, 1, 0], ![19, -37, 4], ![30, -24, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![48, -33, 1]] ![![83, 0, 0], ![-36, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2988, 83, 0]], ![![3984, -2739, 83], ![-1826, 1245, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-36, 1, 0]]], ![![![48, -33, 1]], ![![-22, 15, -2]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [41, 51, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 21, 85], [5, 67, 4], [0, 1]]
 g := ![![[8, 1, 81], [36, 87], [49, 1], [78, 74, 67], [59, 33, 1], []], ![[55, 36, 75, 2], [13, 16], [79, 68], [6, 85, 8, 71], [4, 56, 23, 22], [4, 16]], ![[30, 74, 47, 71], [40, 50], [50, 50], [10, 6, 23, 80], [77, 78, 50, 73], [85, 16]]]
 h' := ![![[28, 21, 85], [84, 10, 80], [74, 48, 40], [6, 8, 1], [73, 88, 45], [0, 0, 1], [0, 1]], ![[5, 67, 4], [35, 36, 69], [52, 31, 85], [49, 39, 35], [88, 48, 82], [86, 49, 67], [28, 21, 85]], ![[0, 1], [35, 43, 29], [42, 10, 53], [57, 42, 53], [29, 42, 51], [11, 40, 21], [5, 67, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 81], []]
 b := ![[], [56, 9, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [41, 51, 56, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153525, 77964, 119972]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1725, 876, 1348]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![30, -9, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![30, -9, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![30, 88, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![30, -9, 1], ![-50, 15, -34], ![252, 196, -11]]]
  hmulB := by decide  
  f := ![![![-29, 9, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -88, 97]], ![![0, -1, 1], ![10, 31, -34], ![6, 12, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [84, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 96], [0, 1]]
 g := ![![[71, 11], [62], [53], [72], [81], [50, 1]], ![[39, 86], [62], [53], [72], [81], [3, 96]]]
 h' := ![![[50, 96], [34, 60], [95, 81], [45, 76], [51, 13], [68, 88], [0, 1]], ![[0, 1], [27, 37], [71, 16], [62, 21], [22, 84], [6, 9], [50, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [34, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [84, 47, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-151336, -84036, -94970]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27812, 85292, -94970]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![34, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![34, 1, 0]] 
 ![![97, 0, 0], ![34, 1, 0], ![11, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![34, 1, 0], ![2, 33, 4], ![-32, -24, 36]]]
  hmulB := by decide  
  f := ![![![-491, -9238, -1120], ![-194, 27160, 0]], ![![-196, -3234, -392], ![1, 9506, 0]], ![![-69, -1048, -127], ![16, 3080, 0]]]
  g := ![![![1, 0, 0], ![-34, 97, 0], ![-11, 0, 97]], ![![0, 1, 0], ![-12, 33, 4], ![4, -24, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![30, -9, 1]] ![![97, 0, 0], ![34, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3298, 97, 0]], ![![2910, -873, 97], ![970, -291, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![34, 1, 0]]], ![![![30, -9, 1]], ![![10, -3, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![33, 21, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![33, 21, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![33, 21, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![33, 21, 1], ![10, -12, 86], ![-708, -524, 52]]]
  hmulB := by decide  
  f := ![![![-32, -21, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -21, 101]], ![![0, 0, 1], ![-28, -18, 86], ![-24, -16, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [55, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 100], [0, 1]]
 g := ![![[40, 64], [47], [46, 87], [68], [19], [22, 1]], ![[34, 37], [47], [41, 14], [68], [19], [44, 100]]]
 h' := ![![[22, 100], [66, 8], [96, 42], [49, 84], [70, 13], [2, 25], [0, 1]], ![[0, 1], [40, 93], [10, 59], [79, 17], [53, 88], [47, 76], [22, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [59, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [55, 79, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1415, -120, -2574]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![827, 534, -2574]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![15, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![15, 1, 0]] 
 ![![101, 0, 0], ![15, 1, 0], ![49, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![15, 1, 0], ![2, 14, 4], ![-32, -24, 17]]]
  hmulB := by decide  
  f := ![![![-2516, -18139, -5184], ![-505, 130896, 0]], ![![-384, -2688, -768], ![1, 19392, 0]], ![![-1219, -8800, -2515], ![-256, 63504, 0]]]
  g := ![![![1, 0, 0], ![-15, 101, 0], ![-49, 0, 101]], ![![0, 1, 0], ![-4, 14, 4], ![-5, -24, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![33, 21, 1]] ![![101, 0, 0], ![15, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1515, 101, 0]], ![![3333, 2121, 101], ![505, 303, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![15, 1, 0]]], ![![![33, 21, 1]], ![![5, 3, 1]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [67, 45, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 67, 99], [85, 35, 4], [0, 1]]
 g := ![![[31, 51, 23], [33, 77, 16], [63, 39, 28], [15, 72], [33, 92], [1]], ![[67, 42, 6, 20], [41, 0, 84, 65], [53, 16, 25, 94], [18, 33], [94, 19], [102, 7, 100, 39]], ![[13, 36, 13, 26], [12, 44, 54, 55], [72, 7], [14, 52], [76, 28], [40, 68, 58, 64]]]
 h' := ![![[86, 67, 99], [55, 55, 34], [2, 41, 4], [66, 38, 50], [12, 29, 81], [36, 58, 68], [0, 1]], ![[85, 35, 4], [56, 35, 43], [21, 94, 79], [27, 26, 53], [10, 3, 41], [98, 88, 88], [86, 67, 99]], ![[0, 1], [51, 13, 26], [101, 71, 20], [8, 39], [88, 71, 84], [37, 60, 50], [85, 35, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 39], []]
 b := ![[], [69, 102, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [67, 45, 35, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-263474, -155633, -131016]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2558, -1511, -1272]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![17, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![17, 1, 0]] 
 ![![107, 0, 0], ![17, 1, 0], ![93, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![17, 1, 0], ![2, 16, 4], ![-32, -24, 19]]]
  hmulB := by decide  
  f := ![![![8607, 71548, 17892], ![2140, -478611, 0]], ![![1352, 11356, 2840], ![429, -75970, 0]], ![![7488, 62187, 15551], ![1815, -415989, 0]]]
  g := ![![![1, 0, 0], ![-17, 107, 0], ![-93, 0, 107]], ![![0, 1, 0], ![-6, 16, 4], ![-13, -24, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-11, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-11, 1, 0]] 
 ![![107, 0, 0], ![96, 1, 0], ![21, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-11, 1, 0], ![2, -12, 4], ![-32, -24, -9]]]
  hmulB := by decide  
  f := ![![![8040, -48949, 16320], ![-1177, -436560, 0]], ![![7211, -43910, 14640], ![-1069, -391620, 0]], ![![1580, -9607, 3203], ![-211, -85680, 0]]]
  g := ![![![1, 0, 0], ![-96, 107, 0], ![-21, 0, 107]], ![![-1, 1, 0], ![10, -12, 4], ![23, -24, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-7, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-7, 1, 0]] 
 ![![107, 0, 0], ![100, 1, 0], ![40, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-7, 1, 0], ![2, -8, 4], ![-32, -24, -5]]]
  hmulB := by decide  
  f := ![![![11277, -45374, 22692], ![-1070, -607011, 0]], ![![10533, -42398, 21204], ![-1069, -567207, 0]], ![![4214, -16962, 8483], ![-426, -226920, 0]]]
  g := ![![![1, 0, 0], ![-100, 107, 0], ![-40, 0, 107]], ![![-1, 1, 0], ![6, -8, 4], ![24, -24, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![17, 1, 0]] ![![107, 0, 0], ![-11, 1, 0]]
  ![![107, 0, 0], ![34, 28, 1]] where
 M := ![![![11449, 0, 0], ![-1177, 107, 0]], ![![1819, 107, 0], ![-185, 5, 4]]]
 hmul := by decide  
 g := ![![![![73, -28, -1], ![107, 0, 0]], ![![-11, 1, 0], ![0, 0, 0]]], ![![![-17, -27, -1], ![107, 0, 0]], ![![-3, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![34, 28, 1]] ![![107, 0, 0], ![-7, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-749, 107, 0]], ![![3638, 2996, 107], ![-214, -214, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-7, 1, 0]]], ![![![34, 28, 1]], ![![-2, -2, 1]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [58, 2, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 106, 48], [74, 2, 61], [0, 1]]
 g := ![![[35, 107, 81], [49, 46], [89, 14, 4], [91, 73, 15], [83, 36], [1]], ![[38, 14, 35, 66], [3, 12], [44, 68, 74, 63], [60, 83, 41, 61], [55, 80], [75, 106, 43, 66]], ![[67, 21, 54, 22], [69, 28], [105, 52, 15, 108], [44, 46, 1, 82], [101, 89], [61, 69, 21, 43]]]
 h' := ![![[41, 106, 48], [96, 94, 9], [70, 36, 68], [63, 52, 2], [76, 49, 61], [51, 107, 6], [0, 1]], ![[74, 2, 61], [28, 105, 61], [23, 91, 11], [76, 39, 102], [76, 78, 76], [43, 46, 25], [41, 106, 48]], ![[0, 1], [35, 19, 39], [2, 91, 30], [99, 18, 5], [33, 91, 81], [21, 65, 78], [74, 2, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 11], []]
 b := ![[], [37, 5, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [58, 2, 103, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![102117958, 65849298, 29745664]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![936862, 604122, 272896]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-19, 26, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-19, 26, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![94, 26, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-19, 26, 1], ![20, -69, 106], ![-868, -644, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-94, -26, 113]], ![![-1, 0, 1], ![-88, -25, 106], ![-16, -8, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [17, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 112], [0, 1]]
 g := ![![[76, 99], [97], [111], [7], [80, 8], [64, 1]], ![[84, 14], [97], [111], [7], [27, 105], [15, 112]]]
 h' := ![![[64, 112], [35, 72], [21, 53], [10, 26], [109, 81], [42, 11], [0, 1]], ![[0, 1], [10, 41], [23, 60], [92, 87], [95, 32], [68, 102], [64, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [21, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [17, 49, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81, -20, 34]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -8, 34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![7, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![7, 1, 0]] 
 ![![113, 0, 0], ![7, 1, 0], ![103, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![7, 1, 0], ![2, 6, 4], ![-32, -24, 9]]]
  hmulB := by decide  
  f := ![![![576, 1745, 1164], ![113, -32883, 0]], ![![29, 107, 72], ![114, -2034, 0]], ![![528, 1591, 1061], ![55, -29973, 0]]]
  g := ![![![1, 0, 0], ![-7, 113, 0], ![-103, 0, 113]], ![![0, 1, 0], ![-4, 6, 4], ![-7, -24, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-19, 26, 1]] ![![113, 0, 0], ![7, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![791, 113, 0]], ![![-2147, 2938, 113], ![-113, 113, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![7, 1, 0]]], ![![![-19, 26, 1]], ![![-1, 1, 1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3866742749377, -134518587898, 158956098232]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![3866742749377, -134518587898, 158956098232]] 
 ![![127, 0, 0], ![76, 1, 0], ![36, 0, 1]] where
  M :=![![![3866742749377, -134518587898, 158956098232], ![-5355632319220, 186314979707, -220162155128], ![-1417824723616, 49324144912, -58284685755]]]
  hmulB := by decide  
  f := ![![![-1065049, -997406, 862920]], ![![-870488, -760477, 498568]], ![![-295196, -230136, 64237]]]
  g := ![![![65887684199, -134518587898, 158956098232], ![-91257741672, 186314979707, -220162155128], ![-24159142124, 49324144912, -58284685755]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-49, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-49, 1, 0]] 
 ![![127, 0, 0], ![78, 1, 0], ![23, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-49, 1, 0], ![2, -50, 4], ![-32, -24, -47]]]
  hmulB := by decide  
  f := ![![![2247, -68390, 5472], ![-1270, -173736, 0]], ![![1387, -41994, 3360], ![-761, -106680, 0]], ![![427, -12386, 991], ![-178, -31464, 0]]]
  g := ![![![1, 0, 0], ![-78, 127, 0], ![-23, 0, 127]], ![![-1, 1, 0], ![30, -50, 4], ![23, -24, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-28, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-28, 1, 0]] 
 ![![127, 0, 0], ![99, 1, 0], ![115, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-28, 1, 0], ![2, -29, 4], ![-32, -24, -26]]]
  hmulB := by decide  
  f := ![![![1277, -19717, 2720], ![-381, -86360, 0]], ![![1005, -15368, 2120], ![-253, -67310, 0]], ![![1157, -17854, 2463], ![-342, -78200, 0]]]
  g := ![![![1, 0, 0], ![-99, 127, 0], ![-115, 0, 127]], ![![-1, 1, 0], ![19, -29, 4], ![42, -24, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![3866742749377, -134518587898, 158956098232]] ![![127, 0, 0], ![-49, 1, 0]]
  ![![127, 0, 0], ![22, -57, 1]] where
 M := ![![![491076329170879, -17083860663046, 20187424475464], ![-194826027038693, 6777725786709, -8009010968496]]]
 hmul := by decide  
 g := ![![![![3763853617097, 132057800282, 154279319492], ![593950899980, 0, 0]], ![![-1493243724083, -52391644689, -61207647540], ![-235639730916, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![22, -57, 1]] ![![127, 0, 0], ![-28, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3556, 127, 0]], ![![2794, -7239, 127], ![-762, 1651, -254]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-28, 1, 0]]], ![![![22, -57, 1]], ![![-6, 13, -2]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![19, 38, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![19, 38, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![19, 38, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![19, 38, 1], ![44, -43, 154], ![-1252, -932, 72]]]
  hmulB := by decide  
  f := ![![![-18, -38, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -38, 131]], ![![0, 0, 1], ![-22, -45, 154], ![-20, -28, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [48, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 130], [0, 1]]
 g := ![![[111, 101], [107, 63], [64], [49], [34], [15], [1]], ![[0, 30], [65, 68], [64], [49], [34], [15], [1]]]
 h' := ![![[43, 130], [104, 25], [85, 71], [119, 8], [84, 7], [12, 54], [83, 43], [0, 1]], ![[0, 1], [0, 106], [125, 60], [70, 123], [123, 124], [107, 77], [98, 88], [43, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [19, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [48, 88, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1799, -1240, -1384]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![187, 392, -1384]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-23, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-23, 1, 0]] 
 ![![131, 0, 0], ![108, 1, 0], ![59, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-23, 1, 0], ![2, -24, 4], ![-32, -24, -21]]]
  hmulB := by decide  
  f := ![![![16262, -204207, 34040], ![-4323, -1114810, 0]], ![![13410, -168333, 28060], ![-3536, -918965, 0]], ![![7322, -91971, 15331], ![-1959, -502090, 0]]]
  g := ![![![1, 0, 0], ![-108, 131, 0], ![-59, 0, 131]], ![![-1, 1, 0], ![18, -24, 4], ![29, -24, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![19, 38, 1]] ![![131, 0, 0], ![-23, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3013, 131, 0]], ![![2489, 4978, 131], ![-393, -917, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-23, 1, 0]]], ![![![19, 38, 1]], ![![-3, -7, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139579415809, -4855773226, 5737904166]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![139579415809, -4855773226, 5737904166]] 
 ![![137, 0, 0], ![69, 1, 0], ![129, 0, 1]] where
  M :=![![![139579415809, -4855773226, 5737904166], ![-193324479764, 6725489051, -7947284572], ![-51179806744, 1780474104, -2103926461]]]
  hmulB := by decide  
  f := ![![![44977, -15922, 182806]], ![![-20279, -39599, 94274]], ![![-1967, -38890, 141537]]]
  g := ![![![-1938407803, -4855773226, 5737904166], ![2684791865, 6725489051, -7947284572], ![710759077, 1780474104, -2103926461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-66, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-66, 1, 0]] 
 ![![137, 0, 0], ![71, 1, 0], ![128, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-66, 1, 0], ![2, -67, 4], ![-32, -24, -64]]]
  hmulB := by decide  
  f := ![![![3367, -154751, 9240], ![-2603, -316470, 0]], ![![1735, -80189, 4788], ![-1369, -163989, 0]], ![![3154, -144585, 8633], ![-2415, -295680, 0]]]
  g := ![![![1, 0, 0], ![-71, 137, 0], ![-128, 0, 137]], ![![-1, 1, 0], ![31, -67, 4], ![72, -24, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-4, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-4, 1, 0]] 
 ![![137, 0, 0], ![133, 1, 0], ![64, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-4, 1, 0], ![2, -5, 4], ![-32, -24, -2]]]
  hmulB := by decide  
  f := ![![![-8283, 20737, -16592], ![411, 568276, 0]], ![![-8039, 20127, -16104], ![412, 551562, 0]], ![![-3868, 9687, -7751], ![241, 265472, 0]]]
  g := ![![![1, 0, 0], ![-133, 137, 0], ![-64, 0, 137]], ![![-1, 1, 0], ![3, -5, 4], ![24, -24, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![139579415809, -4855773226, 5737904166]] ![![137, 0, 0], ![-66, 1, 0]]
  ![![137, 0, 0], ![-42, -68, 1]] where
 M := ![![![19122379965833, -665240931962, 786092870742], ![-9405565923158, 327206521967, -386648959528]]]
 hmul := by decide  
 g := ![![![![130353364093, -19793190290, 5957572064], ![-30094502026, 0, 0]], ![![-64115824540, 9735511867, -2930301401], ![14802332409, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-42, -68, 1]] ![![137, 0, 0], ![-4, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-548, 137, 0]], ![![-5754, -9316, 137], ![0, 274, -274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-4, 1, 0]]], ![![![-42, -68, 1]], ![![0, 2, -2]]]]
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


lemma PB138I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB138I2 : PrimesBelowBoundCertificateInterval O 79 137 138 where
  m := 11
  g := ![2, 1, 2, 2, 1, 3, 1, 2, 3, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB138I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![1295029]
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
  β := ![I83N1, I97N1, I101N1, I107N0, I107N1, I107N2, I113N1, I127N0, I127N1, I127N2, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [], [I97N1], [I101N1], [], [I107N0, I107N1, I107N2], [], [I113N1], [I127N0, I127N1, I127N2], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
