
import IdealArithmetic.Examples.NF3_1_406700_2.RI3_1_406700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-37, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-37, 1, 0]] 
 ![![83, 0, 0], ![46, 1, 0], ![51, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-37, 1, 0], ![1, -38, 5], ![-67, -24, -35]]]
  hmulB := by decide  
  f := ![![![1000, -56227, 7400], ![-1079, -122840, 0]], ![![562, -31153, 4100], ![-580, -68060, 0]], ![![610, -34549, 4547], ![-673, -75480, 0]]]
  g := ![![![1, 0, 0], ![-46, 83, 0], ![-51, 0, 83]], ![![-1, 1, 0], ![18, -38, 5], ![34, -24, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-10, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-10, 1, 0]] 
 ![![83, 0, 0], ![73, 1, 0], ![28, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-10, 1, 0], ![1, -11, 5], ![-67, -24, -8]]]
  hmulB := by decide  
  f := ![![![-4325, 49112, -22330], ![1162, 370678, 0]], ![![-3806, 43185, -19635], ![997, 325941, 0]], ![![-1460, 16568, -7533], ![384, 125048, 0]]]
  g := ![![![1, 0, 0], ![-73, 83, 0], ![-28, 0, 83]], ![![-1, 1, 0], ![8, -11, 5], ![23, -24, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-37, 1, 0]] ![![83, 0, 0], ![-37, 1, 0]]
  ![![83, 0, 0], ![25, -15, 1]] where
 M := ![![![6889, 0, 0], ![-3071, 83, 0]], ![![-3071, 83, 0], ![1370, -75, 5]]]
 hmul := by decide  
 g := ![![![![58, 15, -1], ![83, 0, 0]], ![![-37, 1, 0], ![0, 0, 0]]], ![![![-37, 1, 0], ![0, 0, 0]], ![![15, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![25, -15, 1]] ![![83, 0, 0], ![-10, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-830, 83, 0]], ![![2075, -1245, 83], ![-332, 166, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-10, 1, 0]]], ![![![25, -15, 1]], ![![-4, 2, -1]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![46, -45, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![46, -45, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![46, 44, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![46, -45, 1], ![-112, 67, -223], ![2970, 1057, -67]]]
  hmulB := by decide  
  f := ![![![-45, 45, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -44, 89]], ![![0, -1, 1], ![114, 111, -223], ![68, 45, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [14, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 88], [0, 1]]
 g := ![![[20, 85], [72], [9], [0, 45], [36, 80], [1]], ![[72, 4], [72], [9], [38, 44], [64, 9], [1]]]
 h' := ![![[76, 88], [5, 68], [52, 61], [0, 3], [30, 32], [75, 76], [0, 1]], ![[0, 1], [11, 21], [60, 28], [50, 86], [59, 57], [66, 13], [76, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [18, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [14, 13, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1123, -575, -630]
  a := ![-1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![313, 305, -630]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-44, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-44, 1, 0]] 
 ![![89, 0, 0], ![45, 1, 0], ![67, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-44, 1, 0], ![1, -45, 5], ![-67, -24, -42]]]
  hmulB := by decide  
  f := ![![![-27, 3239, -360], ![89, 6408, 0]], ![![9, 1619, -180], ![90, 3204, 0]], ![![-5, 2438, -271], ![98, 4824, 0]]]
  g := ![![![1, 0, 0], ![-45, 89, 0], ![-67, 0, 89]], ![![-1, 1, 0], ![19, -45, 5], ![43, -24, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![46, -45, 1]] ![![89, 0, 0], ![-44, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3916, 89, 0]], ![![4094, -4005, 89], ![-2136, 2047, -267]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-44, 1, 0]]], ![![![46, -45, 1]], ![![-24, 23, -3]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![37, -15, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![37, -15, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![37, 82, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![37, -15, 1], ![-82, 28, -73], ![960, 337, -16]]]
  hmulB := by decide  
  f := ![![![-36, 15, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -82, 97]], ![![0, -1, 1], ![27, 62, -73], ![16, 17, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [73, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 96], [0, 1]]
 g := ![![[15, 4], [61], [66], [9], [54], [69, 1]], ![[0, 93], [61], [66], [9], [54], [41, 96]]]
 h' := ![![[69, 96], [41, 95], [41, 35], [94, 58], [84, 3], [7, 32], [0, 1]], ![[0, 1], [0, 2], [31, 62], [22, 39], [0, 94], [81, 65], [69, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [93, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [73, 28, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2083, -328, -2526]
  a := ![2, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![985, 2132, -2526]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-24, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-24, 1, 0]] 
 ![![97, 0, 0], ![73, 1, 0], ![16, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-24, 1, 0], ![1, -25, 5], ![-67, -24, -22]]]
  hmulB := by decide  
  f := ![![![-299, 8698, -1740], ![194, 33756, 0]], ![![-212, 6523, -1305], ![195, 25317, 0]], ![![-32, 1434, -287], ![102, 5568, 0]]]
  g := ![![![1, 0, 0], ![-73, 97, 0], ![-16, 0, 97]], ![![-1, 1, 0], ![18, -25, 5], ![21, -24, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![37, -15, 1]] ![![97, 0, 0], ![-24, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2328, 97, 0]], ![![3589, -1455, 97], ![-970, 388, -97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-24, 1, 0]]], ![![![37, -15, 1]], ![![-10, 4, -1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![47, 36, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![47, 36, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![47, 36, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![47, 36, 1], ![-31, -13, 182], ![-2457, -887, 96]]]
  hmulB := by decide  
  f := ![![![-46, -36, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -36, 101]], ![![0, 0, 1], ![-85, -65, 182], ![-69, -43, 96]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [75, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 100], [0, 1]]
 g := ![![[22, 24], [77], [79, 92], [21], [92], [67, 1]], ![[14, 77], [77], [82, 9], [21], [92], [33, 100]]]
 h' := ![![[67, 100], [27, 23], [34, 73], [8, 30], [88, 18], [25, 71], [0, 1]], ![[0, 1], [53, 78], [77, 28], [99, 71], [82, 83], [35, 30], [67, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [54, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [75, 34, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2993403, -1541923, -1543795]
  a := ![-65, 2, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![688762, 534997, -1543795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![20, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![20, 1, 0]] 
 ![![101, 0, 0], ![20, 1, 0], ![5, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![20, 1, 0], ![1, 19, 5], ![-67, -24, 22]]]
  hmulB := by decide  
  f := ![![![-1875, -38297, -10080], ![-707, 203616, 0]], ![![-379, -7580, -1995], ![-100, 40299, 0]], ![![-95, -1896, -499], ![-24, 10080, 0]]]
  g := ![![![1, 0, 0], ![-20, 101, 0], ![-5, 0, 101]], ![![0, 1, 0], ![-4, 19, 5], ![3, -24, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![47, 36, 1]] ![![101, 0, 0], ![20, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![2020, 101, 0]], ![![4747, 3636, 101], ![909, 707, 202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![20, 1, 0]]], ![![![47, 36, 1]], ![![9, 7, 2]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-16, -25, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-16, -25, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![87, 78, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-16, -25, 1], ![-92, -15, -123], ![1630, 577, -89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -78, 103]], ![![-1, -1, 1], ![103, 93, -123], ![91, 73, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [100, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 102], [0, 1]]
 g := ![![[10, 34], [1, 2], [101, 92], [15], [61], [30, 1]], ![[0, 69], [61, 101], [80, 11], [15], [61], [60, 102]]]
 h' := ![![[30, 102], [3, 72], [97, 65], [40, 35], [43, 85], [90, 79], [0, 1]], ![[0, 1], [0, 31], [90, 38], [60, 68], [18, 18], [91, 24], [30, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [101, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [100, 73, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![425, -411, -3638]
  a := ![-2, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3077, 2751, -3638]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![20, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![20, 1, 0]] 
 ![![103, 0, 0], ![20, 1, 0], ![89, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![20, 1, 0], ![1, 19, 5], ![-67, -24, 22]]]
  hmulB := by decide  
  f := ![![![-5495, -112004, -29480], ![-2060, 607288, 0]], ![![-1064, -21732, -5720], ![-411, 117832, 0]], ![![-4745, -96780, -25473], ![-1796, 524744, 0]]]
  g := ![![![1, 0, 0], ![-20, 103, 0], ![-89, 0, 103]], ![![0, 1, 0], ![-8, 19, 5], ![-15, -24, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-16, -25, 1]] ![![103, 0, 0], ![20, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![2060, 103, 0]], ![![-1648, -2575, 103], ![-412, -515, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![20, 1, 0]]], ![![![-16, -25, 1]], ![![-4, -5, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![47, 8, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![47, 8, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![47, 8, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![47, 8, 1], ![-59, 15, 42], ![-581, -215, 40]]]
  hmulB := by decide  
  f := ![![![-46, -8, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -8, 107]], ![![0, 0, 1], ![-19, -3, 42], ![-23, -5, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [28, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 106], [0, 1]]
 g := ![![[103, 1], [82, 42], [61], [0, 92], [9], [5, 1]], ![[1, 106], [78, 65], [61], [32, 15], [9], [10, 106]]]
 h' := ![![[5, 106], [58, 106], [4, 91], [0, 32], [88, 29], [74, 104], [0, 1]], ![[0, 1], [53, 1], [31, 16], [53, 75], [19, 78], [59, 3], [5, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [27, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [28, 102, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1198, -575, -1075]
  a := ![-1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![461, 75, -1075]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-42, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-42, 1, 0]] 
 ![![107, 0, 0], ![65, 1, 0], ![67, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-42, 1, 0], ![1, -43, 5], ![-67, -24, -40]]]
  hmulB := by decide  
  f := ![![![-2113, 125197, -14560], ![2033, 311584, 0]], ![![-1263, 76012, -8840], ![1285, 189176, 0]], ![![-1307, 78394, -9117], ![1314, 195104, 0]]]
  g := ![![![1, 0, 0], ![-65, 107, 0], ![-67, 0, 107]], ![![-1, 1, 0], ![23, -43, 5], ![39, -24, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![47, 8, 1]] ![![107, 0, 0], ![-42, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4494, 107, 0]], ![![5029, 856, 107], ![-2033, -321, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-42, 1, 0]]], ![![![47, 8, 1]], ![![-19, -3, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![1, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![1, 1, 0]] 
 ![![109, 0, 0], ![1, 1, 0], ![22, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![1, 1, 0], ![1, 0, 5], ![-67, -24, 3]]]
  hmulB := by decide  
  f := ![![![0, 0, -5], ![0, 109, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 22, 0]]]
  g := ![![![1, 0, 0], ![-1, 109, 0], ![-22, 0, 109]], ![![0, 1, 0], ![-1, 0, 5], ![-1, -24, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![9, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![9, 1, 0]] 
 ![![109, 0, 0], ![9, 1, 0], ![73, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![9, 1, 0], ![1, 8, 5], ![-67, -24, 11]]]
  hmulB := by decide  
  f := ![![![-4698, -38018, -23765], ![-654, 518077, 0]], ![![-392, -3136, -1960], ![1, 42728, 0]], ![![-3150, -25462, -15916], ![-394, 346969, 0]]]
  g := ![![![1, 0, 0], ![-9, 109, 0], ![-73, 0, 109]], ![![0, 1, 0], ![-4, 8, 5], ![-6, -24, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-11, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-11, 1, 0]] 
 ![![109, 0, 0], ![98, 1, 0], ![61, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-11, 1, 0], ![1, -12, 5], ![-67, -24, -9]]]
  hmulB := by decide  
  f := ![![![5237, -64142, 26730], ![-1090, -582714, 0]], ![![4708, -57663, 24030], ![-980, -523854, 0]], ![![2931, -35896, 14959], ![-608, -326106, 0]]]
  g := ![![![1, 0, 0], ![-98, 109, 0], ![-61, 0, 109]], ![![-1, 1, 0], ![8, -12, 5], ![26, -24, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![1, 1, 0]] ![![109, 0, 0], ![9, 1, 0]]
  ![![109, 0, 0], ![2, -20, 1]] where
 M := ![![![11881, 0, 0], ![981, 109, 0]], ![![109, 109, 0], ![10, 9, 5]]]
 hmul := by decide  
 g := ![![![![107, 20, -1], ![109, 0, 0]], ![![9, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![2, -20, 1]] ![![109, 0, 0], ![-11, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1199, 109, 0]], ![![218, -2180, 109], ![-109, 218, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-11, 1, 0]]], ![![![2, -20, 1]], ![![-1, 2, -1]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [101, 11, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 13, 85], [17, 99, 28], [0, 1]]
 g := ![![[3, 77, 99], [74, 49], [84, 61], [52, 100], [30, 20, 97], [1]], ![[63, 23, 76, 105], [20, 11], [28, 64], [59, 41], [79, 25, 105, 81], [57, 91, 58, 83]], ![[14, 2, 106, 53], [47, 63], [31, 31], [13, 97], [33, 7, 13, 11], [83, 30, 76, 30]]]
 h' := ![![[36, 13, 85], [79, 41, 72], [35, 70, 7], [48, 71, 20], [21, 54, 10], [12, 102, 53], [0, 1]], ![[17, 99, 28], [63, 35, 104], [106, 80, 89], [30, 69, 105], [0, 49, 43], [106, 46, 18], [36, 13, 85]], ![[0, 1], [97, 37, 50], [18, 76, 17], [18, 86, 101], [38, 10, 60], [33, 78, 42], [17, 99, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 82], []]
 b := ![[], [106, 28, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [101, 11, 60, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3524357, 969201, -1341423]
  a := ![2, 18, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31189, 8577, -11871]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [47, 49, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 34, 91], [109, 92, 36], [0, 1]]
 g := ![![[42, 91, 1], [32, 31, 44], [34, 104, 42], [22, 98, 69], [103, 9, 76], [1]], ![[34, 69, 111, 118], [11, 45, 66, 3], [5, 55, 34, 110], [27, 47, 13, 29], [84, 62, 123, 10], [10, 108, 10, 80]], ![[58, 3, 49, 9], [125, 22, 93, 44], [103, 66, 23, 38], [116, 75, 29, 22], [77, 65, 30, 121], [67, 105, 39, 47]]]
 h' := ![![[58, 34, 91], [20, 38, 126], [53, 120, 60], [109, 2, 114], [112, 41, 14], [80, 78, 40], [0, 1]], ![[109, 92, 36], [121, 63, 64], [97, 96, 57], [64, 93, 2], [55, 58, 66], [78, 123, 110], [58, 34, 91]], ![[0, 1], [64, 26, 64], [60, 38, 10], [12, 32, 11], [104, 28, 47], [36, 53, 104], [109, 92, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 80], []]
 b := ![[], [34, 92, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [47, 49, 87, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-258572, -254508, -578866]
  a := ![-2, 4, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2036, -2004, -4558]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [19, 89, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 74, 112], [51, 56, 19], [0, 1]]
 g := ![![[103, 51, 62], [65, 67, 34], [31, 25], [85, 7], [90, 65], [59, 1], []], ![[53, 67, 67, 9], [16, 3, 118, 89], [24, 39], [27, 64], [39, 77], [3, 123], [16, 99]], ![[107, 126, 46, 127], [27, 56, 72, 119], [57, 39], [76, 13], [50, 108], [70, 105], [109, 99]]]
 h' := ![![[8, 74, 112], [75, 49, 18], [66, 41, 77], [0, 92, 126], [82, 113, 111], [58, 101, 117], [0, 0, 1], [0, 1]], ![[51, 56, 19], [77, 32, 77], [123, 61, 127], [102, 121, 68], [22, 85, 8], [34, 95, 48], [22, 106, 56], [8, 74, 112]], ![[0, 1], [62, 50, 36], [130, 29, 58], [77, 49, 68], [92, 64, 12], [16, 66, 97], [6, 25, 74], [51, 56, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 100], []]
 b := ![[], [78, 130, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [19, 89, 72, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1870287, 776961, 304575]
  a := ![2, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14277, 5931, 2325]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![48, -11, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![48, -11, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![48, 126, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![48, -11, 1], ![-78, 35, -53], ![692, 241, 3]]]
  hmulB := by decide  
  f := ![![![-47, 11, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -126, 137]], ![![0, -1, 1], ![18, 49, -53], ![4, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [2, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 136], [0, 1]]
 g := ![![[53, 69], [68], [50], [5, 128], [8], [2], [1]], ![[0, 68], [68], [50], [0, 9], [8], [2], [1]]]
 h' := ![![[31, 136], [1, 53], [0, 94], [127, 18], [121, 111], [0, 75], [135, 31], [0, 1]], ![[0, 1], [0, 84], [37, 43], [0, 119], [0, 26], [133, 62], [0, 106], [31, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [109, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [2, 106, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18503, -9200, -11120]
  a := ![-5, 0, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3761, 10160, -11120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![53, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![53, 1, 0]] 
 ![![137, 0, 0], ![53, 1, 0], ![134, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![53, 1, 0], ![1, 52, 5], ![-67, -24, 55]]]
  hmulB := by decide  
  f := ![![![-2596, -181879, -17490], ![-2329, 479226, 0]], ![![-1035, -70350, -6765], ![-821, 185361, 0]], ![![-2579, -177897, -17107], ![-2175, 468732, 0]]]
  g := ![![![1, 0, 0], ![-53, 137, 0], ![-134, 0, 137]], ![![0, 1, 0], ![-25, 52, 5], ![-45, -24, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![48, -11, 1]] ![![137, 0, 0], ![53, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![7261, 137, 0]], ![![6576, -1507, 137], ![2466, -548, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![53, 1, 0]]], ![![![48, -11, 1]], ![![18, -4, 0]]]]
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


lemma PB181I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB181I2 : PrimesBelowBoundCertificateInterval O 79 137 181 where
  m := 11
  g := ![3, 2, 2, 2, 2, 2, 3, 1, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB181I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0]
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
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![2048383]
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I89N1, I97N1, I101N1, I103N1, I107N1, I109N0, I109N1, I109N2, I137N1]
  Il := ![[I83N0, I83N0, I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
