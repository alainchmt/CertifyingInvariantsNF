
import IdealArithmetic.Examples.NF3_1_981215_1.RI3_1_981215_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [58, 23, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 82, 16], [41, 0, 67], [0, 1]]
 g := ![![[39, 15, 37], [68, 13, 9], [47, 29], [69, 10], [45, 20, 1], []], ![[60, 9, 9, 41], [80, 40, 20, 40], [45, 36], [77, 38], [36, 26], [25, 7]], ![[53, 68, 41, 43], [38, 4, 31, 72], [81, 3], [68, 27], [34, 40, 14, 67], [57, 7]]]
 h' := ![![[62, 82, 16], [40, 33, 28], [44, 14, 80], [23, 73, 64], [46, 46, 50], [0, 0, 1], [0, 1]], ![[41, 0, 67], [62, 69, 30], [38, 64, 58], [65, 6, 6], [7, 65, 72], [70, 57], [62, 82, 16]], ![[0, 1], [49, 64, 25], [15, 5, 28], [27, 4, 13], [30, 55, 44], [35, 26, 82], [41, 0, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 23], []]
 b := ![[], [44, 3, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [58, 23, 63, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3015390, 379227, -262944]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36330, 4569, -3168]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [67, 85, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 57, 80], [44, 31, 9], [0, 1]]
 g := ![![[50, 2, 17], [77, 53], [74, 36], [46, 35, 68], [84, 76, 1], []], ![[59, 2, 10, 10], [79, 73], [78, 4], [74, 85, 48, 39], [51, 77, 5, 73], [57, 81]], ![[53, 5, 4, 21], [44, 78], [25, 64], [49, 59, 25, 34], [43, 23, 52, 49], [39, 81]]]
 h' := ![![[32, 57, 80], [76, 14, 62], [47, 64, 63], [33, 60, 6], [68, 50, 35], [0, 0, 1], [0, 1]], ![[44, 31, 9], [72, 44, 16], [5, 8, 42], [46, 77, 2], [52, 7, 12], [53, 51, 31], [32, 57, 80]], ![[0, 1], [14, 31, 11], [84, 17, 73], [35, 41, 81], [22, 32, 42], [35, 38, 57], [44, 31, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 77], []]
 b := ![[], [86, 1, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [67, 85, 13, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112050110, -9117516, 1822008]
  a := ![-3, 6, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1258990, -102444, 20472]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1415, -801, 1325]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-1415, -801, 1325]] 
 ![![97, 0, 0], ![0, 97, 0], ![37, 86, 1]] where
  M :=![![![-1415, -801, 1325], ![253876, -15743, -11461], ![-266941, 32384, -10413]]]
  hmulB := by decide  
  f := ![![![-5516339, -356371, -309688]], ![![-58794037, -3798260, -3300705]], ![![-54657994, -3531060, -3068507]]]
  g := ![![![-520, -1183, 1325], ![6989, 9999, -11461], ![1220, 9566, -10413]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [29, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 96], [0, 1]]
 g := ![![[26, 48], [48], [47], [44], [27], [22, 1]], ![[15, 49], [48], [47], [44], [27], [44, 96]]]
 h' := ![![[22, 96], [72, 40], [3, 57], [28, 12], [25, 74], [41, 67], [0, 1]], ![[0, 1], [79, 57], [93, 40], [1, 85], [4, 23], [60, 30], [22, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [28, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [29, 75, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1402899, 25761, -22659]
  a := ![1, -66, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23106, 20355, -22659]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5516339, -356371, -309688]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-5516339, -356371, -309688]] 
 ![![97, 0, 0], ![26, 1, 0], ![46, 0, 1]] where
  M :=![![![-5516339, -356371, -309688], ![-58794037, -3798260, -3300705], ![-41433693, -2676733, -2326093]]]
  hmulB := by decide  
  f := ![![![-1415, -801, 1325]], ![![2238, -377, 237]], ![![-3423, -46, 521]]]
  g := ![![![185515, -356371, -309688], ![1977249, -3798260, -3300705], ![1393419, -2676733, -2326093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-1415, -801, 1325]] ![![-5516339, -356371, -309688]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106822, 6901, 5997]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![106822, 6901, 5997]] 
 ![![101, 0, 0], ![49, 1, 0], ![7, 0, 1]] where
  M :=![![![106822, 6901, 5997], ![1138526, 73552, 63917], ![802349, 51834, 45044]]]
  hmulB := by decide  
  f := ![![![2510, -146, -127]], ![![979, -39, -75]], ![![6, -21, 29]]]
  g := ![![![-2706, 6901, 5997], ![-28841, 73552, 63917], ![-20325, 51834, 45044]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18847273647893676, 1217586838155932, 1058088431784391]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![18847273647893676, 1217586838155932, 1058088431784391]] 
 ![![101, 0, 0], ![76, 1, 0], ![5, 0, 1]] where
  M :=![![![18847273647893676, 1217586838155932, 1058088431784391], ![200877303632662749, 12977238276301953, 11277278356146470], ![141563480954325386, 9145398660500041, 7947392517306684]]]
  hmulB := by decide  
  f := ![![![-947851418, 100810543, -16855583]], ![![-746108264, 70969126, -1370269]], ![![158070661, -7163349, -10880255]]]
  g := ![![![-781977903078011, 1217586838155932, 1058088431784391], ![-8334447496505129, 12977238276301953, 11277278356146470], ![-5873502770596150, 9145398660500041, 7947392517306684]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![106822, 6901, 5997]] ![![18847273647893676, 1217586838155932, 1058088431784391]]
  ![![4248513933267393228363, 274465938337271491634, 238512133322127188820]] where
 M := ![![![4248513933267393228363, 274465938337271491634, 238512133322127188820]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![4248513933267393228363, 274465938337271491634, 238512133322127188820]] ![![18847273647893676, 1217586838155932, 1058088431784391]]
  ![![101, 0, 0]] where
 M := ![![![168971490172301898158985333330849858774, 10916033071997228002825005751601202138, 9486081774626502169822455954041586793]]]
 hmul := by decide  
 g := ![![![![1672985051210909882762231023077721374, 108079535366309188146782235164368338, 93921601728975269008143128257837493]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N1
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [66, 38, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 72, 79], [2, 30, 24], [0, 1]]
 g := ![![[101, 73, 36], [37, 20, 49], [25, 96, 32], [5, 41], [37, 34], [1]], ![[16, 50], [16, 99, 89, 36], [6, 43, 42, 46], [27, 72], [67, 41], [62, 21, 31, 81]], ![[38, 81, 20, 40], [75, 91, 66, 90], [66, 45, 31, 3], [44, 100], [83, 52], [71, 16, 95, 22]]]
 h' := ![![[29, 72, 79], [30, 59, 6], [101, 85, 96], [77, 35, 49], [60, 27, 91], [37, 65, 31], [0, 1]], ![[2, 30, 24], [81, 26], [5, 59, 16], [67, 39, 12], [43, 88, 22], [6, 33, 91], [29, 72, 79]], ![[0, 1], [11, 18, 97], [36, 62, 94], [41, 29, 42], [79, 91, 93], [60, 5, 84], [2, 30, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 12], []]
 b := ![[], [0, 38, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [66, 38, 72, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-107363080, 10092249, -3137586]
  a := ![3, -7, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1042360, 97983, -30462]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-859146251, -55503262, -48232584]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-859146251, -55503262, -48232584]] 
 ![![107, 0, 0], ![0, 107, 0], ![47, 21, 1]] where
  M :=![![![-859146251, -55503262, -48232584], ![-9156920282, -591562781, -514070714], ![-6453120818, -416889738, -362279055]]]
  hmulB := by decide  
  f := ![![![-8589, -426, 1748]], ![![334294, -25599, -8182]], ![![59671, -4865, -1041]]]
  g := ![![![13156871, 8947486, -48232584], ![140228068, 95363759, -514070714], ![98822381, 67205331, -362279055]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [82, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 106], [0, 1]]
 g := ![![[47, 40], [18, 79], [30], [99, 40], [92], [105, 1]], ![[74, 67], [74, 28], [30], [19, 67], [92], [103, 106]]]
 h' := ![![[105, 106], [22, 88], [90, 20], [14, 64], [92, 19], [57, 29], [0, 1]], ![[0, 1], [60, 19], [50, 87], [100, 43], [54, 88], [106, 78], [105, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [72, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [82, 2, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6471, 1539, -1012]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![505, 213, -1012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8589, -426, 1748]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-8589, -426, 1748]] 
 ![![107, 0, 0], ![92, 1, 0], ![3, 0, 1]] where
  M :=![![![-8589, -426, 1748], ![334294, -25599, -8182], ![-231694, 37046, -21721]]]
  hmulB := by decide  
  f := ![![![-859146251, -55503262, -48232584]], ![![-824283882, -53251055, -46275406]], ![![-84397753, -5452332, -4738101]]]
  g := ![![![237, -426, 1748], ![25364, -25599, -8182], ![-33409, 37046, -21721]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-859146251, -55503262, -48232584]] ![![-8589, -426, 1748]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [14, 26, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 69, 86], [7, 39, 23], [0, 1]]
 g := ![![[37, 49, 4], [3, 36], [13, 0, 27], [46, 4, 48], [40, 66], [1]], ![[78, 24, 95, 44], [74, 74], [10, 38, 49, 98], [66, 38, 106, 56], [56, 27], [65, 23, 44, 41]], ![[19, 44, 16, 55], [10, 45], [21, 107, 79, 47], [73, 40, 67, 72], [13, 16], [73, 85, 4, 68]]]
 h' := ![![[27, 69, 86], [55, 49, 107], [36, 89, 6], [10, 8, 38], [72, 72, 22], [95, 83, 34], [0, 1]], ![[7, 39, 23], [20, 89, 103], [82, 103, 40], [86, 98, 99], [59, 87, 74], [25, 106, 71], [27, 69, 86]], ![[0, 1], [93, 80, 8], [48, 26, 63], [84, 3, 81], [7, 59, 13], [84, 29, 4], [7, 39, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 80], []]
 b := ![[], [81, 105, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [14, 26, 75, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17173168, 2178692, 711661]
  a := ![-1, 23, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![157552, 19988, 6529]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [110, 103, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 78, 10], [38, 34, 103], [0, 1]]
 g := ![![[56, 84, 28], [60, 22], [24, 1], [56, 63], [107, 75, 61], [1]], ![[99, 77, 76, 37], [41, 105], [93, 106], [78, 7], [99, 50, 44, 103], [67, 109, 10, 96]], ![[25, 59, 17, 89], [28, 69], [78, 50], [10, 112], [6, 107, 32, 67], [84, 40, 29, 17]]]
 h' := ![![[55, 78, 10], [31, 58, 64], [90, 82, 94], [40, 22, 1], [95, 61, 96], [3, 10, 93], [0, 1]], ![[38, 34, 103], [19, 43, 44], [3, 37, 61], [17, 94, 28], [3, 14, 32], [14, 111, 98], [55, 78, 10]], ![[0, 1], [112, 12, 5], [49, 107, 71], [43, 110, 84], [76, 38, 98], [93, 105, 35], [38, 34, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 56], []]
 b := ![[], [23, 5, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [110, 103, 20, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6959331, 590990, -19210]
  a := ![1, -1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61587, 5230, -170]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-74814, 8882, -2643]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-74814, 8882, -2643]] 
 ![![127, 0, 0], ![0, 127, 0], ![26, 42, 1]] where
  M :=![![![-74814, 8882, -2643], ![-513695, -24381, 102988], ![1923760, -130155, -71434]]]
  hmulB := by decide  
  f := ![![![119260122, 7704539, 6695279]], ![![1271093750, 82116228, 71359371]], ![![451830501, 29189520, 25365824]]]
  g := ![![![-48, 944, -2643], ![-25129, -34251, 102988], ![29772, 22599, -71434]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [3, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 126], [0, 1]]
 g := ![![[78, 13], [90, 9], [5, 4], [38, 11], [25, 2], [20, 1]], ![[84, 114], [16, 118], [85, 123], [4, 116], [65, 125], [40, 126]]]
 h' := ![![[20, 126], [111, 93], [112, 3], [13, 2], [52, 30], [67, 16], [0, 1]], ![[0, 1], [66, 34], [45, 124], [53, 125], [17, 97], [6, 111], [20, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [21, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [3, 107, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16948, 7292, -1683]
  a := ![-2, 7, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![478, 614, -1683]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119260122, 7704539, 6695279]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![119260122, 7704539, 6695279]] 
 ![![127, 0, 0], ![48, 1, 0], ![66, 0, 1]] where
  M :=![![![119260122, 7704539, 6695279], ![1271093750, 82116228, 71359371], ![895772955, 57869450, 50288812]]]
  hmulB := by decide  
  f := ![![![-74814, 8882, -2643]], ![![-32321, 3165, -188]], ![![-23732, 3591, -1936]]]
  g := ![![![-5452332, 7704539, 6695279], ![-58111840, 82116228, 71359371], ![-40952931, 57869450, 50288812]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-74814, 8882, -2643]] ![![119260122, 7704539, 6695279]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1412774626, 151059470, -26260085]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-1412774626, 151059470, -26260085]] 
 ![![131, 0, 0], ![0, 131, 0], ![80, 23, 1]] where
  M :=![![![-1412774626, 151059470, -26260085], ![-5166735705, -723255451, 1714174340], ![31110726080, -1858476845, -1504812886]]]
  hmulB := by decide  
  f := ![![![-32626850700135106, -2107786236095895, -1831675707389515]], ![![-347742273875301470, -22465128041917156, -19522297182275815]], ![![-82849491720622595, -5352309970742778, -4651181407269711]]]
  g := ![![![5252154, 5763675, -26260085], ![-1086264755, -306482941, 1714174340], ![1156456160, 250016943, -1504812886]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [94, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 130], [0, 1]]
 g := ![![[75, 46], [126, 53], [49], [101], [121], [52], [1]], ![[0, 85], [88, 78], [49], [101], [121], [52], [1]]]
 h' := ![![[24, 130], [77, 35], [40, 61], [89, 124], [85, 25], [18, 11], [37, 24], [0, 1]], ![[0, 1], [0, 96], [63, 70], [52, 7], [30, 106], [20, 120], [89, 107], [24, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [63, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [94, 107, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7469, -435, -560]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![399, 95, -560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32626850700135106, 2107786236095895, 1831675707389515]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![32626850700135106, 2107786236095895, 1831675707389515]] 
 ![![131, 0, 0], ![11, 1, 0], ![105, 0, 1]] where
  M :=![![![32626850700135106, 2107786236095895, 1831675707389515], ![347742273875301470, 22465128041917156, 19522297182275815], ![245063060258817655, 15831762315537730, 13757872568827196]]]
  hmulB := by decide  
  f := ![![![1412774626, -151059470, 26260085]], ![![158070661, -7163349, -10880255]], ![![894890150, -106891355, 32535281]]]
  g := ![![![-1396066772311594, 2107786236095895, 1831675707389515], ![-14879506402478991, 22465128041917156, 19522297182275815], ![-10485976678923305, 15831762315537730, 13757872568827196]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-1412774626, 151059470, -26260085]] ![![32626850700135106, 2107786236095895, 1831675707389515]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6678146, 431427, 374912]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![6678146, 431427, 374912]] 
 ![![137, 0, 0], ![0, 137, 0], ![13, 31, 1]] where
  M :=![![![6678146, 431427, 374912], ![71176765, 4598219, 3995873], ![50160125, 3240485, 2815996]]]
  hmulB := by decide  
  f := ![![![-1513, 44, 139]], ![![26505, -2632, 206]], ![![5828, -575, 40]]]
  g := ![![![13170, -81685, 374912], ![140368, -870612, 3995873], ![98921, -613543, 2815996]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [130, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 136], [0, 1]]
 g := ![![[57, 39], [136], [8], [97, 121], [73], [7], [1]], ![[0, 98], [136], [8], [15, 16], [73], [7], [1]]]
 h' := ![![[125, 136], [100, 54], [92, 100], [131, 75], [114, 11], [98, 22], [7, 125], [0, 1]], ![[0, 1], [0, 83], [125, 37], [53, 62], [119, 126], [108, 115], [14, 12], [125, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [121, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [130, 12, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67766, 11804, -4180]
  a := ![-2, -2, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98, 1032, -4180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1513, -44, -139]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![1513, -44, -139]] 
 ![![137, 0, 0], ![72, 1, 0], ![57, 0, 1]] where
  M :=![![![1513, -44, -139], ![-26505, 2632, -206], ![3550, -2245, 2713]]]
  hmulB := by decide  
  f := ![![![-6678146, -431427, -374912]], ![![-4029221, -260299, -226201]], ![![-3144631, -203152, -176540]]]
  g := ![![![92, -44, -139], ![-1491, 2632, -206], ![77, -2245, 2713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![6678146, 431427, 374912]] ![![1513, -44, -139]]
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


lemma PB281I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB281I2 : PrimesBelowBoundCertificateInterval O 79 137 281 where
  m := 11
  g := ![1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB281I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N1]
    · exact ![I103N0]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N1
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
  β := ![I97N1, I101N0, I101N1, I107N1, I127N1, I131N1, I137N1]
  Il := ![[], [], [I97N1], [I101N0, I101N1, I101N1], [], [I107N1], [], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
