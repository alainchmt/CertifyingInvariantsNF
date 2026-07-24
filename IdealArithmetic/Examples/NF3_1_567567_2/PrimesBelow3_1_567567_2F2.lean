
import IdealArithmetic.Examples.NF3_1_567567_2.RI3_1_567567_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [8, 15, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 13, 42], [55, 69, 41], [0, 1]]
 g := ![![[9, 69, 11], [63, 50, 21], [31, 51], [51, 61], [25, 66, 1], []], ![[42, 28, 48, 6], [67, 10, 8, 19], [64, 36], [59, 49], [64, 49, 30, 15], [71, 21]], ![[4, 49, 80, 37], [52, 59, 0, 59], [0, 21], [71, 25], [8, 43, 81, 40], [72, 21]]]
 h' := ![![[11, 13, 42], [77, 70, 54], [2, 75, 42], [1, 59, 47], [49, 10, 71], [0, 0, 1], [0, 1]], ![[55, 69, 41], [32, 70, 26], [64, 45, 72], [59, 82, 77], [45, 40, 7], [51, 49, 69], [11, 13, 42]], ![[0, 1], [53, 26, 3], [81, 46, 52], [74, 25, 42], [12, 33, 5], [42, 34, 13], [55, 69, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 57], []]
 b := ![[], [60, 29, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [8, 15, 17, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-487127, 220448, -169984]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5869, 2656, -2048]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![53, -23, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![53, -23, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![53, 66, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![53, -23, 1], ![55, 3, -93], ![-2387, 653, 49]]]
  hmulB := by decide  
  f := ![![![-52, 23, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -66, 89]], ![![0, -1, 1], ![56, 69, -93], ![-56, -29, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [81, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 88], [0, 1]]
 g := ![![[14, 11], [87], [80], [33, 71], [75, 84], [1]], ![[0, 78], [87], [80], [64, 18], [49, 5], [1]]]
 h' := ![![[23, 88], [37, 10], [26, 49], [86, 76], [66, 58], [8, 23], [0, 1]], ![[0, 1], [0, 79], [85, 40], [54, 13], [65, 31], [3, 66], [23, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [47, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [81, 66, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1383, 800, -325]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![178, 250, -325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![4, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![4, 1, 0]] 
 ![![89, 0, 0], ![4, 1, 0], ![40, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![4, 1, 0], ![2, 5, 4], ![101, -27, 3]]]
  hmulB := by decide  
  f := ![![![2669, 6697, 5360], ![267, -119260, 0]], ![![116, 299, 240], ![90, -5340, 0]], ![![1200, 3010, 2409], ![110, -53600, 0]]]
  g := ![![![1, 0, 0], ![-4, 89, 0], ![-40, 0, 89]], ![![0, 1, 0], ![-2, 5, 4], ![1, -27, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![53, -23, 1]] ![![89, 0, 0], ![4, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![356, 89, 0]], ![![4717, -2047, 89], ![267, -89, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![4, 1, 0]]], ![![![53, -23, 1]], ![![3, -1, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![50, -35, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![50, -35, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![50, 62, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![50, -35, 1], ![31, -12, -141], ![-3599, 977, 58]]]
  hmulB := by decide  
  f := ![![![-49, 35, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -62, 97]], ![![0, -1, 1], ![73, 90, -141], ![-67, -27, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [44, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 96], [0, 1]]
 g := ![![[39, 86], [48], [22], [36], [95], [30, 1]], ![[0, 11], [48], [22], [36], [95], [60, 96]]]
 h' := ![![[30, 96], [24, 38], [14, 40], [77, 64], [77, 6], [38, 80], [0, 1]], ![[0, 1], [0, 59], [50, 57], [57, 33], [63, 91], [13, 17], [30, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [33, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [44, 67, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![115562, 550208, -987566]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![510246, 636900, -987566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![44, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![44, 1, 0]] 
 ![![97, 0, 0], ![44, 1, 0], ![39, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![44, 1, 0], ![2, 45, 4], ![101, -27, 43]]]
  hmulB := by decide  
  f := ![![![5333, 162497, 14448], ![4171, -350364, 0]], ![![2396, 73690, 6552], ![1941, -158886, 0]], ![![2151, 65334, 5809], ![1662, -140868, 0]]]
  g := ![![![1, 0, 0], ![-44, 97, 0], ![-39, 0, 97]], ![![0, 1, 0], ![-22, 45, 4], ![-4, -27, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![50, -35, 1]] ![![97, 0, 0], ![44, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4268, 97, 0]], ![![4850, -3395, 97], ![2231, -1552, -97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![44, 1, 0]]], ![![![50, -35, 1]], ![![23, -16, -1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![66, -9, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![66, -9, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![66, 92, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![66, -9, 1], ![83, 30, -37], ![-973, 275, 48]]]
  hmulB := by decide  
  f := ![![![-65, 9, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -92, 101]], ![![0, -1, 1], ![25, 34, -37], ![-41, -41, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [72, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 100], [0, 1]]
 g := ![![[51, 92], [95], [97, 43], [65], [43], [65, 1]], ![[72, 9], [95], [64, 58], [65], [43], [29, 100]]]
 h' := ![![[65, 100], [51, 30], [86, 87], [3, 89], [80, 60], [67, 12], [0, 1]], ![[0, 1], [82, 71], [85, 14], [31, 12], [41, 41], [39, 89], [65, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [18, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [72, 36, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1747, 1161, -1543]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![991, 1417, -1543]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![37, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![37, 1, 0]] 
 ![![101, 0, 0], ![37, 1, 0], ![53, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![37, 1, 0], ![2, 38, 4], ![101, -27, 36]]]
  hmulB := by decide  
  f := ![![![7776, 180719, 19028], ![4747, -480457, 0]], ![![2855, 66179, 6968], ![1718, -175942, 0]], ![![4090, 94833, 9985], ![2465, -252121, 0]]]
  g := ![![![1, 0, 0], ![-37, 101, 0], ![-53, 0, 101]], ![![0, 1, 0], ![-16, 38, 4], ![-8, -27, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![66, -9, 1]] ![![101, 0, 0], ![37, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![3737, 101, 0]], ![![6666, -909, 101], ![2525, -303, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![37, 1, 0]]], ![![![66, -9, 1]], ![![25, -3, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![15, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![15, 1, 0]] 
 ![![103, 0, 0], ![15, 1, 0], ![95, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![15, 1, 0], ![2, 16, 4], ![101, -27, 14]]]
  hmulB := by decide  
  f := ![![![-8529, -70382, -17600], ![-1854, 453200, 0]], ![![-1250, -10238, -2560], ![-205, 65920, 0]], ![![-7860, -64915, -16233], ![-1755, 418000, 0]]]
  g := ![![![1, 0, 0], ![-15, 103, 0], ![-95, 0, 103]], ![![0, 1, 0], ![-6, 16, 4], ![-8, -27, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![20, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![20, 1, 0]] 
 ![![103, 0, 0], ![20, 1, 0], ![50, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![20, 1, 0], ![2, 21, 4], ![101, -27, 19]]]
  hmulB := by decide  
  f := ![![![9109, 101277, 19296], ![2781, -496872, 0]], ![![1752, 19650, 3744], ![619, -96408, 0]], ![![4410, 49163, 9367], ![1411, -241200, 0]]]
  g := ![![![1, 0, 0], ![-20, 103, 0], ![-50, 0, 103]], ![![0, 1, 0], ![-6, 21, 4], ![-3, -27, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-35, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-35, 1, 0]] 
 ![![103, 0, 0], ![68, 1, 0], ![12, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-35, 1, 0], ![2, -34, 4], ![101, -27, -36]]]
  hmulB := by decide  
  f := ![![![7901, -158060, 18600], ![-4120, -478950, 0]], ![![5229, -104320, 12276], ![-2677, -316107, 0]], ![![929, -18415, 2167], ![-455, -55800, 0]]]
  g := ![![![1, 0, 0], ![-68, 103, 0], ![-12, 0, 103]], ![![-1, 1, 0], ![22, -34, 4], ![23, -27, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![15, 1, 0]] ![![103, 0, 0], ![20, 1, 0]]
  ![![103, 0, 0], ![24, 9, 1]] where
 M := ![![![10609, 0, 0], ![2060, 103, 0]], ![![1545, 103, 0], ![302, 36, 4]]]
 hmul := by decide  
 g := ![![![![79, -9, -1], ![103, 0, 0]], ![![-4, -8, -1], ![103, 0, 0]]], ![![![-9, -8, -1], ![103, 0, 0]], ![![2, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![24, 9, 1]] ![![103, 0, 0], ![-35, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3605, 103, 0]], ![![2472, 927, 103], ![-721, -309, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-35, 1, 0]]], ![![![24, 9, 1]], ![![-7, -3, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-2, -42, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-2, -42, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![105, 65, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-2, -42, 1], ![17, -71, -169], ![-4306, 1166, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -65, 107]], ![![-1, -1, 1], ![166, 102, -169], ![-53, 3, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [25, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 106], [0, 1]]
 g := ![![[79, 30], [27, 101], [39], [19, 100], [56], [58, 1]], ![[0, 77], [0, 6], [39], [41, 7], [56], [9, 106]]]
 h' := ![![[58, 106], [74, 43], [57, 23], [60, 50], [48, 10], [48, 22], [0, 1]], ![[0, 1], [0, 64], [0, 84], [71, 57], [93, 97], [40, 85], [58, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [9, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [25, 49, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15, 422, -1238]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1215, 756, -1238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-45, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-45, 1, 0]] 
 ![![107, 0, 0], ![62, 1, 0], ![94, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-45, 1, 0], ![2, -44, 4], ![101, -27, -46]]]
  hmulB := by decide  
  f := ![![![-2250, 64357, -5852], ![1605, 156541, 0]], ![![-1288, 37259, -3388], ![964, 90629, 0]], ![![-1980, 56538, -5141], ![1402, 137522, 0]]]
  g := ![![![1, 0, 0], ![-62, 107, 0], ![-94, 0, 107]], ![![-1, 1, 0], ![22, -44, 4], ![57, -27, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-2, -42, 1]] ![![107, 0, 0], ![-45, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4815, 107, 0]], ![![-214, -4494, 107], ![107, 1819, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-45, 1, 0]]], ![![![-2, -42, 1]], ![![1, 17, -2]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [15, 67, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 24, 75], [58, 84, 34], [0, 1]]
 g := ![![[45, 68, 49], [103, 25], [96, 24, 73], [54, 93, 27], [24, 61], [1]], ![[72, 44, 104, 35], [65, 43], [46, 22, 9, 15], [73, 17, 9, 73], [51, 63], [50, 47, 95, 45]], ![[32, 49, 107, 38], [11, 61], [28, 41, 30, 4], [5, 0, 85, 26], [22, 75], [87, 46, 34, 64]]]
 h' := ![![[88, 24, 75], [74, 39, 102], [86, 104, 104], [62, 23, 20], [83, 32, 71], [94, 42, 37], [0, 1]], ![[58, 84, 34], [13, 14, 48], [94, 0, 77], [76, 72, 26], [69, 45, 80], [17, 11, 45], [88, 24, 75]], ![[0, 1], [18, 56, 68], [40, 5, 37], [93, 14, 63], [22, 32, 67], [5, 56, 27], [58, 84, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 3], []]
 b := ![[], [99, 72, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [15, 67, 72, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![115597879, -61395558, 63582534]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1060531, -563262, 583326]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [73, 52, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 47, 84], [11, 65, 29], [0, 1]]
 g := ![![[1, 102, 44], [17, 49], [94, 63], [27, 97], [35, 109, 2], [1]], ![[78, 24, 84, 42], [103, 51], [99, 72], [91, 16], [26, 33, 106, 45], [1, 92, 109, 19]], ![[40, 27, 32, 76], [64, 26], [21, 14], [61, 28], [107, 61, 82, 84], [50, 37, 80, 94]]]
 h' := ![![[40, 47, 84], [58, 100, 65], [13, 32, 106], [78, 111, 17], [44, 72, 60], [40, 61, 51], [0, 1]], ![[11, 65, 29], [80, 33, 82], [49, 63, 86], [65, 64, 33], [43, 93, 4], [82, 64, 77], [40, 47, 84]], ![[0, 1], [88, 93, 79], [63, 18, 34], [63, 51, 63], [83, 61, 49], [54, 101, 98], [11, 65, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 106], []]
 b := ![[], [5, 37, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [73, 52, 62, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27572, 8475, -1017]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-244, 75, -9]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1113374513, 41800880, 37413534]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![1113374513, 41800880, 37413534]] 
 ![![127, 0, 0], ![0, 127, 0], ![76, 91, 1]] where
  M :=![![![1113374513, 41800880, 37413534], ![3862368694, 145009975, 129789986], ![1827422704, 68609328, 61408215]]]
  hmulB := by decide  
  f := ![![![10671, -3024, -110]], ![![-17158, 10617, -11986]], ![![-8258, 6413, -8523]]]
  g := ![![![-13622473, -26478982, 37413534], ![-47257246, -91857313, 129789986], ![-22359068, -43460931, 61408215]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [125, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 126], [0, 1]]
 g := ![![[99, 26], [43, 88], [26, 104], [60, 18], [77, 99], [71, 1]], ![[40, 101], [68, 39], [44, 23], [68, 109], [121, 28], [15, 126]]]
 h' := ![![[71, 126], [86, 91], [52, 71], [120, 72], [27, 48], [15, 90], [0, 1]], ![[0, 1], [70, 36], [13, 56], [25, 55], [6, 79], [55, 37], [71, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [10, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [125, 56, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![108, 1787, -2064]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1236, 1493, -2064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10671, -3024, -110]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![10671, -3024, -110]] 
 ![![127, 0, 0], ![18, 1, 0], ![42, 0, 1]] where
  M :=![![![10671, -3024, -110], ![-17158, 10617, -11986], ![-298384, 78128, 16665]]]
  hmulB := by decide  
  f := ![![![1113374513, 41800880, 37413534]], ![![188213464, 7066345, 6324674]], ![![382591750, 14364144, 12856509]]]
  g := ![![![549, -3024, -110], ![2324, 10617, -11986], ![-18934, 78128, 16665]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![1113374513, 41800880, 37413534]] ![![10671, -3024, -110]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-37, 38, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-37, 38, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![94, 38, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-37, 38, 1], ![177, -26, 151], ![3774, -994, -102]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-94, -38, 131]], ![![-1, 0, 1], ![-107, -44, 151], ![102, 22, -102]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [87, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 130], [0, 1]]
 g := ![![[45, 63], [88, 7], [89], [41], [48], [94], [1]], ![[73, 68], [62, 124], [89], [41], [48], [94], [1]]]
 h' := ![![[15, 130], [73, 71], [88, 20], [87, 73], [36, 98], [46, 110], [44, 15], [0, 1]], ![[0, 1], [90, 60], [126, 111], [3, 58], [65, 33], [124, 21], [7, 116], [15, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [51, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [87, 116, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-173, 2695, -7565]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5427, 2215, -7565]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-20, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-20, 1, 0]] 
 ![![131, 0, 0], ![111, 1, 0], ![102, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-20, 1, 0], ![2, -19, 4], ![101, -27, -21]]]
  hmulB := by decide  
  f := ![![![6281, -61550, 12960], ![-1310, -424440, 0]], ![![5311, -52146, 10980], ![-1178, -359595, 0]], ![![4882, -47924, 10091], ![-1076, -330480, 0]]]
  g := ![![![1, 0, 0], ![-111, 131, 0], ![-102, 0, 131]], ![![-1, 1, 0], ![13, -19, 4], ![40, -27, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-37, 38, 1]] ![![131, 0, 0], ![-20, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-2620, 131, 0]], ![![-4847, 4978, 131], ![917, -786, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-20, 1, 0]]], ![![![-37, 38, 1]], ![![7, -6, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![86, 37, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![86, 37, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![86, 37, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![86, 37, 1], ![175, 96, 147], ![3673, -967, 22]]]
  hmulB := by decide  
  f := ![![![-85, -37, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -37, 137]], ![![0, 0, 1], ![-91, -39, 147], ![13, -13, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [30, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 136], [0, 1]]
 g := ![![[56, 32], [25], [122], [55, 119], [19], [63], [1]], ![[0, 105], [25], [122], [18, 18], [19], [63], [1]]]
 h' := ![![[101, 136], [80, 124], [75, 5], [131, 56], [117, 121], [106, 29], [107, 101], [0, 1]], ![[0, 1], [0, 13], [32, 132], [33, 81], [8, 16], [21, 108], [33, 36], [101, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [116, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [30, 36, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5002, -948, -1092]
  a := ![-2, -6, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![722, 288, -1092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-10, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-10, 1, 0]] 
 ![![137, 0, 0], ![127, 1, 0], ![115, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-10, 1, 0], ![2, -9, 4], ![101, -27, -11]]]
  hmulB := by decide  
  f := ![![![-10897, 49437, -21976], ![1233, 752678, 0]], ![![-10103, 45820, -20368], ![1097, 697604, 0]], ![![-9145, 41498, -18447], ![1064, 631810, 0]]]
  g := ![![![1, 0, 0], ![-127, 137, 0], ![-115, 0, 137]], ![![-1, 1, 0], ![5, -9, 4], ![35, -27, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![86, 37, 1]] ![![137, 0, 0], ![-10, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-1370, 137, 0]], ![![11782, 5069, 137], ![-685, -274, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-10, 1, 0]]], ![![![86, 37, 1]], ![![-5, -2, 1]]]]
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


lemma PB214I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB214I2 : PrimesBelowBoundCertificateInterval O 79 137 214 where
  m := 11
  g := ![1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB214I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
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
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![1295029]
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
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
  β := ![I89N1, I97N1, I101N1, I103N0, I103N1, I103N2, I107N1, I127N1, I131N1, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
