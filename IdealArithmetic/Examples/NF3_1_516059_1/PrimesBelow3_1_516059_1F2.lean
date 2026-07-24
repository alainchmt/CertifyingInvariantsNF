
import IdealArithmetic.Examples.NF3_1_516059_1.RI3_1_516059_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![18, 36, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![18, 36, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![18, 36, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![18, 36, 1], ![-58, -116, 255], ![1854, -940, 103]]]
  hmulB := by decide  
  f := ![![![-17, -36, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -36, 83]], ![![0, 0, 1], ![-56, -112, 255], ![0, -56, 103]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [60, 21, 1] where
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
 g := ![![[46, 11], [60, 29], [11], [38], [65, 26], [1]], ![[64, 72], [32, 54], [11], [38], [17, 57], [1]]]
 h' := ![![[62, 82], [52, 29], [37, 64], [45, 54], [1, 11], [23, 62], [0, 1]], ![[0, 1], [24, 54], [21, 19], [73, 29], [19, 72], [49, 21], [62, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [16, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [60, 21, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1366, 574, -1372]
  a := ![3, 2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![314, 602, -1372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-6, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-6, 1, 0]] 
 ![![83, 0, 0], ![77, 1, 0], ![63, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-6, 1, 0], ![-3, -9, 7], ![50, -26, -3]]]
  hmulB := by decide  
  f := ![![![14455, 43476, -33810], ![-498, 400890, 0]], ![![13411, 40325, -31360], ![-414, 371840, 0]], ![![10971, 33000, -25663], ![-390, 304290, 0]]]
  g := ![![![1, 0, 0], ![-77, 83, 0], ![-63, 0, 83]], ![![-1, 1, 0], ![3, -9, 7], ![27, -26, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![18, 36, 1]] ![![83, 0, 0], ![-6, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-498, 83, 0]], ![![1494, 2988, 83], ![-166, -332, 249]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-6, 1, 0]]], ![![![18, 36, 1]], ![![-2, -4, 3]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-16, 4, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-16, 4, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![73, 4, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-16, 4, 1], ![38, -54, 31], ![254, -108, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -4, 89]], ![![-1, 0, 1], ![-25, -2, 31], ![25, 0, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [38, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 88], [0, 1]]
 g := ![![[14, 5], [80], [40], [18, 2], [34, 4], [1]], ![[24, 84], [80], [40], [22, 87], [42, 85], [1]]]
 h' := ![![[2, 88], [28, 70], [65, 13], [28, 29], [43, 25], [51, 2], [0, 1]], ![[0, 1], [79, 19], [2, 76], [86, 60], [4, 64], [55, 87], [2, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [6, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [38, 87, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1341, 5564, -5017]
  a := ![-7, -9, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4100, 288, -5017]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-31, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-31, 1, 0]] 
 ![![89, 0, 0], ![58, 1, 0], ![27, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-31, 1, 0], ![-3, -34, 7], ![50, -26, -28]]]
  hmulB := by decide  
  f := ![![![12931, 157110, -32340], ![-2670, 411180, 0]], ![![8411, 102360, -21070], ![-1779, 267890, 0]], ![![3941, 47662, -9811], ![-758, 124740, 0]]]
  g := ![![![1, 0, 0], ![-58, 89, 0], ![-27, 0, 89]], ![![-1, 1, 0], ![20, -34, 7], ![26, -26, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-16, 4, 1]] ![![89, 0, 0], ![-31, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2759, 89, 0]], ![![-1424, 356, 89], ![534, -178, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-31, 1, 0]]], ![![![-16, 4, 1]], ![![6, -2, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![48, -6, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![48, -6, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![48, 91, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![48, -6, 1], ![68, 40, -39], ![-246, 152, 7]]]
  hmulB := by decide  
  f := ![![![-47, 6, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -91, 97]], ![![0, -1, 1], ![20, 37, -39], ![-6, -5, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [87, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 96], [0, 1]]
 g := ![![[83, 8], [2], [2], [22], [62], [54, 1]], ![[30, 89], [2], [2], [22], [62], [11, 96]]]
 h' := ![![[54, 96], [44, 28], [86, 83], [58, 14], [56, 64], [55, 16], [0, 1]], ![[0, 1], [4, 69], [9, 14], [38, 83], [20, 33], [46, 81], [54, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [56, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [87, 43, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1428375, 1804800, -2696118]
  a := ![131, 132, -327]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1348887, 2547954, -2696118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![39, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![39, 1, 0]] 
 ![![97, 0, 0], ![39, 1, 0], ![90, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![39, 1, 0], ![-3, 36, 7], ![50, -26, 42]]]
  hmulB := by decide  
  f := ![![![-1091, 14042, 2730], ![-194, -37830, 0]], ![![-429, 5617, 1092], ![-96, -15132, 0]], ![![-999, 13029, 2533], ![-213, -35100, 0]]]
  g := ![![![1, 0, 0], ![-39, 97, 0], ![-90, 0, 97]], ![![0, 1, 0], ![-21, 36, 7], ![-28, -26, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![48, -6, 1]] ![![97, 0, 0], ![39, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3783, 97, 0]], ![![4656, -582, 97], ![1940, -194, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![39, 1, 0]]], ![![![48, -6, 1]], ![![20, -2, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![28, 45, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![28, 45, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![28, 45, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![28, 45, 1], ![-85, -133, 318], ![2304, -1174, 140]]]
  hmulB := by decide  
  f := ![![![-27, -45, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -45, 101]], ![![0, 0, 1], ![-89, -143, 318], ![-16, -74, 140]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [60, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 100], [0, 1]]
 g := ![![[49, 43], [1], [65, 71], [9], [85], [90, 1]], ![[81, 58], [1], [92, 30], [9], [85], [79, 100]]]
 h' := ![![[90, 100], [47, 12], [39, 100], [96, 77], [38, 98], [54, 61], [0, 1]], ![[0, 1], [16, 89], [50, 1], [57, 24], [71, 3], [90, 40], [90, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [96, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [60, 11, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1018, 5640, -6608]
  a := ![7, 8, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1842, 3000, -6608]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-15, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-15, 1, 0]] 
 ![![101, 0, 0], ![86, 1, 0], ![62, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-15, 1, 0], ![-3, -18, 7], ![50, -26, -12]]]
  hmulB := by decide  
  f := ![![![10966, 66609, -25900], ![-909, 373700, 0]], ![![9331, 56708, -22050], ![-807, 318150, 0]], ![![6727, 40889, -15899], ![-589, 229400, 0]]]
  g := ![![![1, 0, 0], ![-86, 101, 0], ![-62, 0, 101]], ![![-1, 1, 0], ![11, -18, 7], ![30, -26, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![28, 45, 1]] ![![101, 0, 0], ![-15, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1515, 101, 0]], ![![2828, 4545, 101], ![-505, -808, 303]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-15, 1, 0]]], ![![![28, 45, 1]], ![![-5, -8, 3]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![48, -10, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![48, -10, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![48, 93, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![48, -10, 1], ![80, 52, -67], ![-446, 256, -5]]]
  hmulB := by decide  
  f := ![![![-47, 10, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -93, 103]], ![![0, -1, 1], ![32, 61, -67], ![-2, 7, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [56, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 102], [0, 1]]
 g := ![![[95, 46], [67, 1], [95, 46], [1], [16], [36, 1]], ![[0, 57], [0, 102], [0, 57], [1], [16], [72, 102]]]
 h' := ![![[36, 102], [59, 47], [36, 102], [44, 56], [10, 1], [44, 4], [0, 1]], ![[0, 1], [0, 56], [0, 1], [0, 47], [46, 102], [85, 99], [36, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [45, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [56, 67, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1500, 666, -1694]
  a := ![3, 2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![804, 1536, -1694]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-36, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-36, 1, 0]] 
 ![![103, 0, 0], ![67, 1, 0], ![5, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-36, 1, 0], ![-3, -39, 7], ![50, -26, -33]]]
  hmulB := by decide  
  f := ![![![-2987, -42127, 7560], ![721, -111240, 0]], ![![-1925, -27383, 4914], ![516, -72306, 0]], ![![-145, -2045, 367], ![35, -5400, 0]]]
  g := ![![![1, 0, 0], ![-67, 103, 0], ![-5, 0, 103]], ![![-1, 1, 0], ![25, -39, 7], ![19, -26, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![48, -10, 1]] ![![103, 0, 0], ![-36, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3708, 103, 0]], ![![4944, -1030, 103], ![-1648, 412, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-36, 1, 0]]], ![![![48, -10, 1]], ![![-16, 4, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![61, -13, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![61, -13, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![61, 94, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![61, -13, 1], ![89, 74, -88], ![-596, 334, -1]]]
  hmulB := by decide  
  f := ![![![-60, 13, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -94, 107]], ![![0, -1, 1], ![51, 78, -88], ![-5, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [31, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 106], [0, 1]]
 g := ![![[62, 34], [20, 12], [56], [3, 40], [11], [4, 1]], ![[91, 73], [68, 95], [56], [56, 67], [11], [8, 106]]]
 h' := ![![[4, 106], [22, 81], [65, 36], [14, 85], [55, 19], [90, 92], [0, 1]], ![[0, 1], [25, 26], [102, 71], [33, 22], [24, 88], [30, 15], [4, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [103, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [31, 103, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23529, -8598, 184]
  a := ![-5, 14, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![115, -242, 184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-19, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-19, 1, 0]] 
 ![![107, 0, 0], ![88, 1, 0], ![1, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-19, 1, 0], ![-3, -22, 7], ![50, -26, -16]]]
  hmulB := by decide  
  f := ![![![11807, 88121, -28035], ![-1177, 428535, 0]], ![![9709, 72455, -23051], ![-962, 352351, 0]], ![![121, 823, -262], ![49, 4005, 0]]]
  g := ![![![1, 0, 0], ![-88, 107, 0], ![-1, 0, 107]], ![![-1, 1, 0], ![18, -22, 7], ![22, -26, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![61, -13, 1]] ![![107, 0, 0], ![-19, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-2033, 107, 0]], ![![6527, -1391, 107], ![-1070, 321, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-19, 1, 0]]], ![![![61, -13, 1]], ![![-10, 3, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![62, -27, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![62, -27, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![62, 82, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![62, -27, 1], ![131, 117, -186], ![-1296, 698, -42]]]
  hmulB := by decide  
  f := ![![![-61, 27, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -82, 109]], ![![0, -1, 1], ![107, 141, -186], ![12, 38, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [13, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 108], [0, 1]]
 g := ![![[46, 83], [84], [58, 64], [18, 94], [27], [56, 1]], ![[7, 26], [84], [45, 45], [50, 15], [27], [3, 108]]]
 h' := ![![[56, 108], [79, 44], [9, 56], [93, 8], [2, 51], [35, 71], [0, 1]], ![[0, 1], [36, 65], [93, 53], [105, 101], [24, 58], [87, 38], [56, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [29, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [13, 53, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1713, 4728, -4196]
  a := ![5, 8, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2371, 3200, -4196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-32, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-32, 1, 0]] 
 ![![109, 0, 0], ![77, 1, 0], ![42, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-32, 1, 0], ![-3, -35, 7], ![50, -26, -29]]]
  hmulB := by decide  
  f := ![![![-3600, -44632, 8925], ![763, -138975, 0]], ![![-2539, -31505, 6300], ![546, -98100, 0]], ![![-1376, -17198, 3439], ![332, -53550, 0]]]
  g := ![![![1, 0, 0], ![-77, 109, 0], ![-42, 0, 109]], ![![-1, 1, 0], ![22, -35, 7], ![30, -26, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![62, -27, 1]] ![![109, 0, 0], ![-32, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3488, 109, 0]], ![![6758, -2943, 109], ![-1853, 981, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-32, 1, 0]]], ![![![62, -27, 1]], ![![-17, 9, -2]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![58, -5, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![58, -5, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![58, 108, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![58, -5, 1], ![65, 47, -32], ![-196, 126, 20]]]
  hmulB := by decide  
  f := ![![![-57, 5, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -108, 113]], ![![0, -1, 1], ![17, 31, -32], ![-12, -18, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [81, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 112], [0, 1]]
 g := ![![[28, 60], [99], [18], [57], [64, 63], [105, 1]], ![[0, 53], [99], [18], [57], [12, 50], [97, 112]]]
 h' := ![![[105, 112], [26, 88], [94, 72], [99, 73], [14, 31], [83, 96], [0, 1]], ![[0, 1], [0, 25], [83, 41], [80, 40], [105, 82], [106, 17], [105, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [80, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [81, 8, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3578, 2801, -4809]
  a := ![-6, -5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2500, 4621, -4809]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![32, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![32, 1, 0]] 
 ![![113, 0, 0], ![32, 1, 0], ![93, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![32, 1, 0], ![-3, 29, 7], ![50, -26, 35]]]
  hmulB := by decide  
  f := ![![![446, -4612, -1113], ![113, 17967, 0]], ![![103, -1306, -315], ![114, 5085, 0]], ![![358, -3796, -916], ![125, 14787, 0]]]
  g := ![![![1, 0, 0], ![-32, 113, 0], ![-93, 0, 113]], ![![0, 1, 0], ![-14, 29, 7], ![-21, -26, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![58, -5, 1]] ![![113, 0, 0], ![32, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![3616, 113, 0]], ![![6554, -565, 113], ![1921, -113, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![32, 1, 0]]], ![![![58, -5, 1]], ![![17, -1, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![30, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![30, 1, 0]] 
 ![![127, 0, 0], ![30, 1, 0], ![29, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![30, 1, 0], ![-3, 27, 7], ![50, -26, 33]]]
  hmulB := by decide  
  f := ![![![21625, -202204, -52416], ![3556, 950976, 0]], ![![5094, -47743, -12376], ![890, 224536, 0]], ![![4925, -46173, -11969], ![867, 217152, 0]]]
  g := ![![![1, 0, 0], ![-30, 127, 0], ![-29, 0, 127]], ![![0, 1, 0], ![-8, 27, 7], ![-1, -26, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![46, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![46, 1, 0]] 
 ![![127, 0, 0], ![46, 1, 0], ![98, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![46, 1, 0], ![-3, 43, 7], ![50, -26, 49]]]
  hmulB := by decide  
  f := ![![![16451, -256914, -41818], ![4064, 758698, 0]], ![![5937, -93021, -15141], ![1525, 274701, 0]], ![![12722, -198248, -32269], ![3060, 585452, 0]]]
  g := ![![![1, 0, 0], ![-46, 127, 0], ![-98, 0, 127]], ![![0, 1, 0], ![-21, 43, 7], ![-28, -26, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![51, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![51, 1, 0]] 
 ![![127, 0, 0], ![51, 1, 0], ![49, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![51, 1, 0], ![-3, 48, 7], ![50, -26, 54]]]
  hmulB := by decide  
  f := ![![![-1721, 30003, 4375], ![-381, -79375, 0]], ![![-699, 12001, 1750], ![-126, -31750, 0]], ![![-662, 11576, 1688], ![-152, -30625, 0]]]
  g := ![![![1, 0, 0], ![-51, 127, 0], ![-49, 0, 127]], ![![0, 1, 0], ![-22, 48, 7], ![-10, -26, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![30, 1, 0]] ![![127, 0, 0], ![46, 1, 0]]
  ![![127, 0, 0], ![-21, -44, 1]] where
 M := ![![![16129, 0, 0], ![5842, 127, 0]], ![![3810, 127, 0], ![1377, 73, 7]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![46, 1, 0], ![0, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![12, 3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-21, -44, 1]] ![![127, 0, 0], ![51, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![6477, 127, 0]], ![![-2667, -5588, 127], ![-889, -2159, -254]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![51, 1, 0]]], ![![![-21, -44, 1]], ![![-7, -17, -2]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [43, 8, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 86, 8], [79, 44, 123], [0, 1]]
 g := ![![[61, 118, 15], [1, 63, 4], [72, 4], [92, 84], [69, 16], [76, 1], []], ![[90, 116, 49, 66], [108, 115, 84, 8], [4, 27], [108, 114], [94, 34], [109, 102], [83, 64]], ![[119, 57, 38, 35], [10, 117, 52, 123], [72, 99], [127, 91], [110, 11], [57, 60], [99, 64]]]
 h' := ![![[128, 86, 8], [88, 46, 43], [76, 93, 129], [91, 73, 2], [95, 126, 79], [7, 4, 4], [0, 0, 1], [0, 1]], ![[79, 44, 123], [9, 71, 33], [105, 11, 1], [88, 117, 17], [127, 67, 30], [34, 74, 77], [108, 129, 44], [128, 86, 8]], ![[0, 1], [85, 14, 55], [49, 27, 1], [1, 72, 112], [22, 69, 22], [6, 53, 50], [19, 2, 86], [79, 44, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 86], []]
 b := ![[], [29, 43, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [43, 8, 55, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![567623, 9717580, -10768200]
  a := ![10, 10, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4333, 74180, -82200]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![75, 43, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![75, 43, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![75, 43, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![75, 43, 1], ![-79, -80, 304], ![2204, -1122, 181]]]
  hmulB := by decide  
  f := ![![![-74, -43, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -43, 137]], ![![0, 0, 1], ![-167, -96, 304], ![-83, -65, 181]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [127, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 136], [0, 1]]
 g := ![![[54, 99], [49], [74], [87, 56], [32], [64], [1]], ![[84, 38], [49], [74], [50, 81], [32], [64], [1]]]
 h' := ![![[129, 136], [20, 28], [30, 7], [48, 99], [57, 78], [55, 13], [10, 129], [0, 1]], ![[0, 1], [70, 109], [111, 130], [78, 38], [118, 59], [88, 124], [74, 8], [129, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [21, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [127, 8, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17949, 21696, -13616]
  a := ![-10, -20, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7323, 4432, -13616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-30, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-30, 1, 0]] 
 ![![137, 0, 0], ![107, 1, 0], ![93, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-30, 1, 0], ![-3, -33, 7], ![50, -26, -27]]]
  hmulB := by decide  
  f := ![![![5206, 58910, -12495], ![-685, 244545, 0]], ![![4063, 46006, -9758], ![-547, 190978, 0]], ![![3534, 39990, -8482], ![-465, 166005, 0]]]
  g := ![![![1, 0, 0], ![-107, 137, 0], ![-93, 0, 137]], ![![-1, 1, 0], ![21, -33, 7], ![39, -26, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![75, 43, 1]] ![![137, 0, 0], ![-30, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-4110, 137, 0]], ![![10275, 5891, 137], ![-2329, -1370, 274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-30, 1, 0]]], ![![![75, 43, 1]], ![![-17, -10, 2]]]]
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


lemma PB204I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB204I2 : PrimesBelowBoundCertificateInterval O 79 137 204 where
  m := 11
  g := ![2, 2, 2, 2, 2, 2, 2, 2, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB204I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N1, I103N1, I107N1, I109N1, I113N1, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
