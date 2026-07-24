
import IdealArithmetic.Examples.NF3_3_268380_1.RI3_3_268380_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7697, 491, -113]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![7697, 491, -113]] 
 ![![83, 0, 0], ![31, 1, 0], ![35, 0, 1]] where
  M :=![![![7697, 491, -113], ![-33448, -2134, 491], ![145336, 9269, -2134]]]
  hmulB := by decide  
  f := ![![![-2877, -397, 61]], ![![-857, -119, 18]], ![![-2629, -366, 55]]]
  g := ![![![-43, 491, -113], ![187, -2134, 491], ![-811, 9269, -2134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 22, -4]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![223, 22, -4]] 
 ![![83, 0, 0], ![62, 1, 0], ![57, 0, 1]] where
  M :=![![![223, 22, -4], ![-1184, -125, 22], ![6512, 730, -125]]]
  hmulB := by decide  
  f := ![![![-435, -170, -16]], ![![-382, -149, -14]], ![![-905, -352, -33]]]
  g := ![![![-11, 22, -4], ![64, -125, 22], ![-381, 730, -125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![749, 281, 25]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![749, 281, 25]] 
 ![![83, 0, 0], ![73, 1, 0], ![66, 0, 1]] where
  M :=![![![749, 281, 25], ![7400, 2924, 281], ![83176, 31847, 2924]]]
  hmulB := by decide  
  f := ![![![399231, 25469, -5861]], ![![330229, 21067, -4848]], ![![408290, 26047, -5994]]]
  g := ![![![-258, 281, 25], ![-2706, 2924, 281], ![-29333, 31847, 2924]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![7697, 491, -113]] ![![223, 22, -4]]
  ![![399231, 25469, -5861]] where
 M := ![![![399231, 25469, -5861]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![399231, 25469, -5861]] ![![749, 281, 25]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [38, 8, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 8, 83], [43, 80, 6], [0, 1]]
 g := ![![[83, 1, 71], [64, 72], [69, 36], [37, 31, 20], [8, 4, 1], []], ![[63, 50, 25, 15], [78, 8], [63, 72], [6, 52, 66, 56], [55, 43, 18, 48], [48, 36]], ![[49, 17, 31, 83], [71, 39], [67, 88], [67, 56, 51, 24], [78, 64, 59, 28], [36, 36]]]
 h' := ![![[50, 8, 83], [49, 6, 58], [16, 85, 28], [18, 73, 83], [52, 51, 51], [0, 0, 1], [0, 1]], ![[43, 80, 6], [41, 12, 65], [54, 12, 39], [57, 66, 61], [54, 5, 36], [53, 27, 80], [50, 8, 83]], ![[0, 1], [81, 71, 55], [51, 81, 22], [4, 39, 34], [76, 33, 2], [36, 62, 8], [43, 80, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 19], []]
 b := ![[], [82, 29, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [38, 8, 85, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-114810, -35244, -1246]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1290, -396, -14]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20731, -8030, -750]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-20731, -8030, -750]] 
 ![![97, 0, 0], ![0, 97, 0], ![57, 12, 1]] where
  M :=![![![-20731, -8030, -750], ![-222000, -85981, -8030], ![-2376880, -920610, -85981]]]
  hmulB := by decide  
  f := ![![![2413, 310, -50]], ![![-14800, -1937, 310]], ![![533, 68, -11]]]
  g := ![![![227, 10, -750], ![2430, 107, -8030], ![26021, 1146, -85981]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [92, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 96], [0, 1]]
 g := ![![[3, 79], [44], [66], [64], [35], [15, 1]], ![[24, 18], [44], [66], [64], [35], [30, 96]]]
 h' := ![![[15, 96], [23, 46], [71, 23], [41, 58], [77, 8], [75, 36], [0, 1]], ![[0, 1], [34, 51], [28, 74], [38, 39], [3, 89], [33, 61], [15, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [6, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [92, 82, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3541, 1460, 1027]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-640, -112, 1027]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2413, 310, -50]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![2413, 310, -50]] 
 ![![97, 0, 0], ![85, 1, 0], ![50, 0, 1]] where
  M :=![![![2413, 310, -50], ![-14800, -1937, 310], ![91760, 12170, -1937]]]
  hmulB := by decide  
  f := ![![![-20731, -8030, -750]], ![![-20455, -7923, -740]], ![![-35190, -13630, -1273]]]
  g := ![![![-221, 310, -50], ![1385, -1937, 310], ![-8720, 12170, -1937]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-20731, -8030, -750]] ![![2413, 310, -50]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -7, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-49, -7, 1]] 
 ![![101, 0, 0], ![41, 1, 0], ![36, 0, 1]] where
  M :=![![![-49, -7, 1], ![296, 38, -7], ![-2072, -313, 38]]]
  hmulB := by decide  
  f := ![![![747, 47, -11]], ![![271, 17, -4]], ![![404, 25, -6]]]
  g := ![![![2, -7, 1], ![-10, 38, -7], ![93, -313, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-140815, -9034, 2072]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-140815, -9034, 2072]] 
 ![![101, 0, 0], ![65, 1, 0], ![17, 0, 1]] where
  M :=![![![-140815, -9034, 2072], ![613312, 39449, -9034], ![-2674064, -172646, 39449]]]
  hmulB := by decide  
  f := ![![![-3460363, -1340246, -125172]], ![![-2593807, -1004617, -93826]], ![![-4510287, -1746896, -163151]]]
  g := ![![![4071, -9034, 2072], ![-17795, 39449, -9034], ![77993, -172646, 39449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20705, 2831, -445]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![20705, 2831, -445]] 
 ![![101, 0, 0], ![96, 1, 0], ![76, 0, 1]] where
  M :=![![![20705, 2831, -445], ![-131720, -18010, 2831], ![837976, 114577, -18010]]]
  hmulB := by decide  
  f := ![![![-7387, -455, 111]], ![![-6696, -410, 101]], ![![-6892, -409, 106]]]
  g := ![![![-2151, 2831, -445], ![13684, -18010, 2831], ![-87056, 114577, -18010]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-49, -7, 1]] ![![-140815, -9034, 2072]]
  ![![-67313, -6123, 1159]] where
 M := ![![![-67313, -6123, 1159]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-67313, -6123, 1159]] ![![20705, 2831, -445]]
  ![![101, 0, 0]] where
 M := ![![![384020079, 52506870, -8253518]]]
 hmul := by decide  
 g := ![![![![3802179, 519870, -81718]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9017, -1232, 194]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-9017, -1232, 194]] 
 ![![103, 0, 0], ![0, 103, 0], ![39, 34, 1]] where
  M :=![![![-9017, -1232, 194], ![57424, 7861, -1232], ![-364672, -49760, 7861]]]
  hmulB := by decide  
  f := ![![![-4767, -304, 70]], ![![20720, 1323, -304]], ![![4161, 266, -61]]]
  g := ![![![-161, -76, 194], ![1024, 483, -1232], ![-6517, -3078, 7861]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [76, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 102], [0, 1]]
 g := ![![[38, 61], [15, 81], [70, 82], [4], [98], [99, 1]], ![[0, 42], [0, 22], [51, 21], [4], [98], [95, 102]]]
 h' := ![![[99, 102], [96, 24], [36, 9], [54, 59], [96, 2], [98, 43], [0, 1]], ![[0, 1], [0, 79], [0, 94], [24, 44], [88, 101], [29, 60], [99, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [93, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [76, 4, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3324, -2, 212]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -70, 212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4767, -304, 70]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-4767, -304, 70]] 
 ![![103, 0, 0], ![69, 1, 0], ![80, 0, 1]] where
  M :=![![![-4767, -304, 70], ![20720, 1323, -304], ![-89984, -5728, 1323]]]
  hmulB := by decide  
  f := ![![![-9017, -1232, 194]], ![![-5483, -749, 118]], ![![-10544, -1440, 227]]]
  g := ![![![103, -304, 70], ![-449, 1323, -304], ![1936, -5728, 1323]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-9017, -1232, 194]] ![![-4767, -304, 70]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49871, -3180, 732]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-49871, -3180, 732]] 
 ![![107, 0, 0], ![0, 107, 0], ![32, 36, 1]] where
  M :=![![![-49871, -3180, 732], ![216672, 13813, -3180], ![-941280, -59988, 13813]]]
  hmulB := by decide  
  f := ![![![347, 132, 12]], ![![3552, 1391, 132]], ![![1664, 648, 61]]]
  g := ![![![-685, -276, 732], ![2976, 1199, -3180], ![-12928, -5208, 13813]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [92, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 106], [0, 1]]
 g := ![![[1, 57], [59, 87], [37], [77, 37], [34], [15, 1]], ![[0, 50], [80, 20], [37], [97, 70], [34], [30, 106]]]
 h' := ![![[15, 106], [29, 48], [76, 27], [85, 12], [96, 12], [11, 26], [0, 1]], ![[0, 1], [0, 59], [53, 80], [51, 95], [62, 95], [80, 81], [15, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [62, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [92, 92, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1591, 2236, 502]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-165, -148, 502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 132, 12]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![347, 132, 12]] 
 ![![107, 0, 0], ![71, 1, 0], ![95, 0, 1]] where
  M :=![![![347, 132, 12], ![3552, 1391, 132], ![39072, 15036, 1391]]]
  hmulB := by decide  
  f := ![![![-49871, -3180, 732]], ![![-31067, -1981, 456]], ![![-53075, -3384, 779]]]
  g := ![![![-95, 132, 12], ![-1007, 1391, 132], ![-10847, 15036, 1391]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-49871, -3180, 732]] ![![347, 132, 12]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [30, 54, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 71, 61], [90, 37, 48], [0, 1]]
 g := ![![[96, 2, 21], [70, 27], [72, 64, 4], [16, 3, 46], [99, 83], [1]], ![[50, 81, 100, 93], [64, 48], [74, 72, 59, 61], [97, 29, 90, 80], [67, 89], [24, 55, 73, 43]], ![[94, 88, 63, 66], [21, 38], [24, 53, 72, 105], [32, 6, 31, 71], [104, 60], [76, 45, 100, 66]]]
 h' := ![![[63, 71, 61], [44, 106, 81], [20, 52, 71], [65, 28, 107], [1, 91, 41], [79, 55, 44], [0, 1]], ![[90, 37, 48], [41, 29, 89], [76, 3, 22], [36, 90, 108], [35, 26, 92], [44, 99, 78], [63, 71, 61]], ![[0, 1], [70, 83, 48], [41, 54, 16], [68, 100, 3], [3, 101, 85], [17, 64, 96], [90, 37, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 11], []]
 b := ![[], [17, 67, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [30, 54, 65, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-126658, -44690, -3052]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1162, -410, -28]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6340571, -2455790, -229358]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-6340571, -2455790, -229358]] 
 ![![113, 0, 0], ![0, 113, 0], ![98, 33, 1]] where
  M :=![![![-6340571, -2455790, -229358], ![-67889968, -26294717, -2455790], ![-726913840, -281543698, -26294717]]]
  hmulB := by decide  
  f := ![![![-495587, -31642, 7278]], ![![2154288, 137599, -31642]], ![![116442, 7445, -1711]]]
  g := ![![![142801, 45248, -229358], ![1529004, 484481, -2455790], ![16371402, 5187451, -26294717]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [75, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 112], [0, 1]]
 g := ![![[13, 64], [60], [32], [41], [101, 36], [42, 1]], ![[102, 49], [60], [32], [41], [31, 77], [84, 112]]]
 h' := ![![[42, 112], [33, 105], [37, 88], [105, 22], [109, 43], [14, 107], [0, 1]], ![[0, 1], [36, 8], [4, 25], [12, 91], [107, 70], [101, 6], [42, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [82, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [75, 71, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11395, 4989, 521]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-351, -108, 521]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![495587, 31642, -7278]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![495587, 31642, -7278]] 
 ![![113, 0, 0], ![80, 1, 0], ![41, 0, 1]] where
  M :=![![![495587, 31642, -7278], ![-2154288, -137599, 31642], ![9366032, 598566, -137599]]]
  hmulB := by decide  
  f := ![![![6340571, 2455790, 229358]], ![![5089696, 1971309, 184110]], ![![8733427, 3382576, 315915]]]
  g := ![![![-15375, 31642, -7278], ![66870, -137599, 31642], ![-290953, 598566, -137599]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-6340571, -2455790, -229358]] ![![495587, 31642, -7278]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB116I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 115 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 115 (by omega)

def PB116I2 : PrimesBelowBoundCertificateInterval O 79 115 116 where
  m := 8
  g := ![3, 1, 2, 3, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB116I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
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
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
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
      exact NI101N1
      exact NI101N2
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
  β := ![I83N0, I83N1, I83N2, I97N1, I101N0, I101N1, I101N2, I103N1, I107N1, I113N1]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
