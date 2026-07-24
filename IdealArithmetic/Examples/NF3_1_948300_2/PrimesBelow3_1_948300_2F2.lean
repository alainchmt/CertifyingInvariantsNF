
import IdealArithmetic.Examples.NF3_1_948300_2.RI3_1_948300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21781827, -738042, 846148]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-21781827, -738042, 846148]] 
 ![![83, 0, 0], ![0, 83, 0], ![71, 54, 1]] where
  M :=![![![-21781827, -738042, 846148], ![167429198, -5596909, -3060274], ![-262162698, 35161892, -3274677]]]
  hmulB := by decide  
  f := ![![![1517266181347, 329341149754, 84270169880]], ![![16271882316606, 3532010728701, 903753279382]], ![![12526005626873, 2718922457836, 695704310207]]]
  g := ![![![-986245, -559398, 846148], ![4635044, 1923589, -3060274], ![-357357, 2554150, -3274677]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [19, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 82], [0, 1]]
 g := ![![[14, 81], [2, 51], [26], [3], [49, 40], [1]], ![[48, 2], [48, 32], [26], [3], [33, 43], [1]]]
 h' := ![![[66, 82], [45, 9], [79, 47], [18, 62], [65, 13], [64, 66], [0, 1]], ![[0, 1], [58, 74], [27, 36], [43, 21], [10, 70], [21, 17], [66, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [12, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [19, 17, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1155, 737, 132]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-99, -77, 132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1517266181347, -329341149754, -84270169880]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1517266181347, -329341149754, -84270169880]] 
 ![![83, 0, 0], ![5, 1, 0], ![45, 0, 1]] where
  M :=![![![-1517266181347, -329341149754, -84270169880], ![-16271882316606, -3532010728701, -903753279382], ![-53250923058098, -11558763018000, -2957598599073]]]
  hmulB := by decide  
  f := ![![![21781827, 738042, -846148]], ![![-705061, 111893, -14102]], ![![14968011, -23494, -419301]]]
  g := ![![![47248159181, -329341149754, -84270169880], ![506711673483, -3532010728701, -903753279382], ![1658250951689, -11558763018000, -2957598599073]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-21781827, -738042, 846148]] ![![-1517266181347, -329341149754, -84270169880]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [48, 78, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 51, 4], [44, 37, 85], [0, 1]]
 g := ![![[74, 52, 36], [59, 25], [56, 49], [56, 10, 78], [45, 52, 1], []], ![[77, 25, 82, 4], [25, 81], [4, 64], [18, 43, 9, 8], [71, 83, 7, 47], [83, 16]], ![[65, 66, 48, 71], [34, 18], [37, 1], [13, 85, 43, 32], [64, 52, 5, 9], [2, 16]]]
 h' := ![![[8, 51, 4], [24, 33, 83], [39, 44, 84], [71, 0, 7], [65, 46, 16], [0, 0, 1], [0, 1]], ![[44, 37, 85], [45, 11, 88], [55, 20, 80], [43, 52, 81], [13, 11, 64], [85, 71, 37], [8, 51, 4]], ![[0, 1], [48, 45, 7], [73, 25, 14], [46, 37, 1], [23, 32, 9], [60, 18, 51], [44, 37, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 15], []]
 b := ![[], [24, 6, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [48, 78, 37, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4220024, 1344256, 161624]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![47416, 15104, 1816]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![20, 29, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![20, 29, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![20, 29, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![20, 29, 1], ![168, 69, 86], ![5575, 639, 12]]]
  hmulB := by decide  
  f := ![![![-19, -29, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -29, 97]], ![![0, 0, 1], ![-16, -25, 86], ![55, 3, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [57, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 96], [0, 1]]
 g := ![![[43, 93], [85], [61], [89], [11], [71, 1]], ![[50, 4], [85], [61], [89], [11], [45, 96]]]
 h' := ![![[71, 96], [93, 44], [31, 52], [93, 62], [5, 63], [27, 37], [0, 1]], ![[0, 1], [16, 53], [37, 45], [33, 35], [16, 34], [35, 60], [71, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [61, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [57, 26, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1065978, 438675, 96105]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8826, -24210, 96105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![11, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![11, 1, 0]] 
 ![![97, 0, 0], ![11, 1, 0], ![85, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![11, 1, 0], ![-1, 12, 3], ![197, 20, 10]]]
  hmulB := by decide  
  f := ![![![-169, 1907, 477], ![97, -15423, 0]], ![![-18, 216, 54], ![1, -1746, 0]], ![![-149, 1671, 418], ![93, -13515, 0]]]
  g := ![![![1, 0, 0], ![-11, 97, 0], ![-85, 0, 97]], ![![0, 1, 0], ![-4, 12, 3], ![-9, 20, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![20, 29, 1]] ![![97, 0, 0], ![11, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![1067, 97, 0]], ![![1940, 2813, 97], ![388, 388, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![11, 1, 0]]], ![![![20, 29, 1]], ![![4, 4, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1093, 259, -48]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1093, 259, -48]] 
 ![![101, 0, 0], ![0, 101, 0], ![88, 43, 1]] where
  M :=![![![-1093, 259, -48], ![-9715, -1794, 825], ![57647, 2348, -2360]]]
  hmulB := by decide  
  f := ![![![22740, 4936, 1263]], ![![243875, 52936, 13545]], ![![131543, 28553, 7306]]]
  g := ![![![31, 23, -48], ![-815, -369, 825], ![2627, 1028, -2360]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [2, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 100], [0, 1]]
 g := ![![[35, 97], [30], [2, 85], [36], [76], [31, 1]], ![[12, 4], [30], [11, 16], [36], [76], [62, 100]]]
 h' := ![![[31, 100], [57, 20], [97, 38], [34, 40], [56, 95], [39, 50], [0, 1]], ![[0, 1], [71, 81], [63, 63], [62, 61], [72, 6], [74, 51], [31, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [3, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [2, 70, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5460, 4021, 723]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-684, -268, 723]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22740, -4936, -1263]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-22740, -4936, -1263]] 
 ![![101, 0, 0], ![74, 1, 0], ![35, 0, 1]] where
  M :=![![![-22740, -4936, -1263], ![-243875, -52936, -13545], ![-798098, -173237, -44327]]]
  hmulB := by decide  
  f := ![![![1093, -259, 48]], ![![897, -172, 27]], ![![-192, -113, 40]]]
  g := ![![![3829, -4936, -1263], ![41064, -52936, -13545], ![134385, -173237, -44327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1093, 259, -48]] ![![-22740, -4936, -1263]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-50, 8, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-50, 8, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![53, 8, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-50, 8, 1], ![189, -22, 23], ![1438, 219, -37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -8, 103]], ![![-1, 0, 1], ![-10, -2, 23], ![33, 5, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [38, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 102], [0, 1]]
 g := ![![[32, 19], [35, 52], [39, 97], [34], [28], [20, 1]], ![[0, 84], [45, 51], [22, 6], [34], [28], [40, 102]]]
 h' := ![![[20, 102], [9, 15], [63, 19], [12, 71], [45, 31], [64, 53], [0, 1]], ![[0, 1], [0, 88], [31, 84], [93, 32], [47, 72], [94, 50], [20, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [25, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [38, 83, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1240, 605, -66]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, 11, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-23, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-23, 1, 0]] 
 ![![103, 0, 0], ![80, 1, 0], ![37, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-23, 1, 0], ![-1, -22, 3], ![197, 20, -24]]]
  hmulB := by decide  
  f := ![![![-8718, -192325, 26226], ![103, -900426, 0]], ![![-6765, -149359, 20367], ![104, -699267, 0]], ![![-3123, -69088, 9421], ![76, -323454, 0]]]
  g := ![![![1, 0, 0], ![-80, 103, 0], ![-37, 0, 103]], ![![-1, 1, 0], ![16, -22, 3], ![-5, 20, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-50, 8, 1]] ![![103, 0, 0], ![-23, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2369, 103, 0]], ![![-5150, 824, 103], ![1339, -206, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-23, 1, 0]]], ![![![-50, 8, 1]], ![![13, -2, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-39, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-39, 1, 0]] 
 ![![107, 0, 0], ![68, 1, 0], ![5, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-39, 1, 0], ![-1, -38, 3], ![197, 20, -40]]]
  hmulB := by decide  
  f := ![![![-2264, -87553, 6912], ![107, -246528, 0]], ![![-1424, -55633, 4392], ![108, -156648, 0]], ![![-77, -4092, 323], ![84, -11520, 0]]]
  g := ![![![1, 0, 0], ![-68, 107, 0], ![-5, 0, 107]], ![![-1, 1, 0], ![24, -38, 3], ![-9, 20, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-38, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-38, 1, 0]] 
 ![![107, 0, 0], ![69, 1, 0], ![66, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-38, 1, 0], ![-1, -37, 3], ![197, 20, -39]]]
  hmulB := by decide  
  f := ![![![-797, -30933, 2508], ![107, -89452, 0]], ![![-500, -19944, 1617], ![108, -57673, 0]], ![![-498, -19080, 1547], ![48, -55176, 0]]]
  g := ![![![1, 0, 0], ![-69, 107, 0], ![-66, 0, 107]], ![![-1, 1, 0], ![22, -37, 3], ![13, 20, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19175409926, 4162256847, 1065017511]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![19175409926, 4162256847, 1065017511]] 
 ![![107, 0, 0], ![77, 1, 0], ![102, 0, 1]] where
  M :=![![![19175409926, 4162256847, 1065017511], ![205646192820, 44638016993, 11421753030], ![672992182341, 146081170089, 37378520810]]]
  hmulB := by decide  
  f := ![![![3004660, -57591, -68013]], ![![2037550, -26614, -49923]], ![![2845941, -103167, -49564]]]
  g := ![![![-3831309845, 4162256847, 1065017511], ![-41088784343, 44638016993, 11421753030], ![-134466047076, 146081170089, 37378520810]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-39, 1, 0]] ![![107, 0, 0], ![-38, 1, 0]]
  ![![3004660, -57591, -68013]] where
 M := ![![![11449, 0, 0], ![-4066, 107, 0]], ![![-4173, 107, 0], ![1481, -76, 3]]]
 hmul := by decide  
 g := ![![![![2051768862082, 445361482629, 113956873677]], ![![-523019384368, -113527743193, -29048912388]]], ![![![-542194794294, -117690000040, -30113929899]], ![![138211663487, 30000529058, 7676385663]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![3004660, -57591, -68013]] ![![19175409926, 4162256847, 1065017511]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![338362417, 10364737, -12808034]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![338362417, 10364737, -12808034]] 
 ![![109, 0, 0], ![25, 1, 0], ![1, 0, 1]] where
  M :=![![![338362417, 10364737, -12808034], ![-2533547435, 92566474, 43902245], ![3809361881, -548379266, 59028966]]]
  hmulB := by decide  
  f := ![![![29539184135338054, 6411840575851102, 1640629769386681]], ![![9681392911713545, 2101464536653214, 537712258649850]], ![![9782246508281130, 2123356041162269, 543313747577926]]]
  g := ![![![844514, 10364737, -12808034], ![-44877170, 92566474, 43902245], ![160181785, -548379266, 59028966]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103330, -35340, 13743]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-103330, -35340, 13743]] 
 ![![109, 0, 0], ![42, 1, 0], ![88, 0, 1]] where
  M :=![![![-103330, -35340, 13743], ![2742711, 136190, -119763], ![-8858514, 104037, 220613]]]
  hmulB := by decide  
  f := ![![![-42505067701, -9226243911, -2360765250]], ![![-20560159209, -4462833586, -1141927587]], ![![-48002113795, -10419444882, -2666075560]]]
  g := ![![![1574, -35340, 13743], ![69375, 136190, -119763], ![-299468, 104037, 220613]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![338362417, 10364737, -12808034]] ![![-103330, -35340, 13743]]
  ![![106924638134873, -11878663718008, 583183894658]] where
 M := ![![![106924638134873, -11878663718008, 583183894658]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![106924638134873, -11878663718008, 583183894658]] ![![-103330, -35340, 13743]]
  ![![109, 0, 0]] where
 M := ![![![-48794407198560284990, -5335799220593386994, 3020747653299537097]]]
 hmul := by decide  
 g := ![![![![-447655111913397110, -48952286427462266, 27713281222931533]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N1
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [34, 54, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 77, 74], [62, 35, 39], [0, 1]]
 g := ![![[27, 56, 57], [46, 49], [1, 31], [71, 4], [110, 92, 44], [1]], ![[68, 66, 88, 78], [15, 98], [58, 57], [77, 95], [83, 34, 22, 75], [83, 80, 96, 6]], ![[70, 78, 45, 38], [21, 60], [61, 22], [5, 13], [34, 43, 104, 10], [75, 88, 87, 107]]]
 h' := ![![[99, 77, 74], [106, 88, 31], [38, 29, 7], [80, 29, 101], [102, 111, 2], [79, 59, 48], [0, 1]], ![[62, 35, 39], [11, 19, 26], [71, 11, 18], [3, 37, 31], [94, 99, 35], [84, 106, 57], [99, 77, 74]], ![[0, 1], [68, 6, 56], [45, 73, 88], [57, 47, 94], [112, 16, 76], [60, 61, 8], [62, 35, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 104], []]
 b := ![[], [5, 48, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [34, 54, 65, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10872408, 2389385, 587826]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![96216, 21145, 5202]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [105, 3, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 60, 19], [19, 66, 108], [0, 1]]
 g := ![![[38, 122, 30], [100, 88, 30], [120, 90, 13], [70, 88, 1], [89, 16, 13], [1]], ![[52, 5, 27, 11], [46, 83, 94, 121], [11, 102, 60, 30], [100, 0, 50, 121], [99, 90, 48, 84], [46, 82, 49, 1]], ![[93, 20, 52, 105], [31, 55, 95, 77], [126, 64, 88, 111], [124, 97, 41, 46], [76, 106, 62, 101], [9, 6, 11, 126]]]
 h' := ![![[74, 60, 19], [41, 79, 86], [100, 98, 86], [16, 90, 34], [53, 61, 1], [22, 124, 93], [0, 1]], ![[19, 66, 108], [66, 47, 65], [7, 44, 45], [36, 92, 17], [106, 45, 82], [90, 48, 112], [74, 60, 19]], ![[0, 1], [91, 1, 103], [3, 112, 123], [95, 72, 76], [92, 21, 44], [72, 82, 49], [19, 66, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 99], []]
 b := ![[], [125, 98, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [105, 3, 34, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-499364, -111633, 3683]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3932, -879, 29]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [52, 58, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 88, 25], [5, 42, 106], [0, 1]]
 g := ![![[129, 24, 62], [114, 111, 33], [11, 20], [34, 43], [103, 41], [109, 1], []], ![[102, 109, 91, 107], [29, 78, 26, 53], [86, 9], [0, 11], [53, 91], [43, 61], [82, 101]], ![[64, 62, 26, 42], [22, 9, 113, 127], [43, 15], [10, 1], [64, 12], [93, 15], [1, 101]]]
 h' := ![![[104, 88, 25], [98, 107, 113], [96, 80, 65], [119, 25, 85], [61, 10, 49], [96, 45, 33], [0, 0, 1], [0, 1]], ![[5, 42, 106], [55, 127, 85], [31, 10, 14], [7, 91, 3], [20, 105, 81], [126, 8, 22], [2, 43, 42], [104, 88, 25]], ![[0, 1], [71, 28, 64], [51, 41, 52], [45, 15, 43], [98, 16, 1], [85, 78, 76], [104, 88, 88], [5, 42, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 64], []]
 b := ![[], [113, 79, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [52, 58, 22, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3220504, 712116, 124974]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24584, 5436, 954]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [39, 38, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 13, 51], [119, 123, 86], [0, 1]]
 g := ![![[61, 21, 87], [79, 135], [117, 49], [22, 85, 32], [121, 115], [69, 1], []], ![[131, 79, 115, 58], [29, 121], [35, 81], [28, 2, 36, 108], [119, 65], [134, 59], [92, 135]], ![[81, 18, 109, 95], [59, 8], [60, 119], [48, 52, 122, 117], [63, 130], [69, 32], [57, 135]]]
 h' := ![![[87, 13, 51], [100, 131, 19], [21, 76, 51], [101, 80, 7], [11, 29, 13], [49, 79, 65], [0, 0, 1], [0, 1]], ![[119, 123, 86], [4, 15, 113], [54, 120, 11], [130, 72, 9], [35, 8, 64], [44, 4, 105], [8, 77, 123], [87, 13, 51]], ![[0, 1], [21, 128, 5], [33, 78, 75], [27, 122, 121], [10, 100, 60], [136, 54, 104], [19, 60, 13], [119, 123, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 116], []]
 b := ![[], [88, 65, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [39, 38, 68, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2178711, -341815, -74665]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15903, -2495, -545]
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



lemma PB276I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB276I2 : PrimesBelowBoundCertificateInterval O 79 137 276 where
  m := 11
  g := ![2, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB276I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N1]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![2571353]
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
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N1
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
  β := ![I83N1, I97N1, I101N1, I103N1, I107N0, I107N1, I107N2, I109N0, I109N1]
  Il := ![[I83N1], [], [I97N1], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N0, I109N1, I109N1], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
