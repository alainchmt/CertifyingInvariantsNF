
import IdealArithmetic.Examples.NF3_1_393835_1.RI3_1_393835_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-36, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-36, 1, 0]] 
 ![![83, 0, 0], ![47, 1, 0], ![32, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-36, 1, 0], ![0, -36, 1], ![280, 81, -35]]]
  hmulB := by decide  
  f := ![![![1585, -44, 0], ![3652, 0, 0]], ![![901, -25, 0], ![2076, 0, 0]], ![![664, -18, 0], ![1530, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 83, 0], ![-32, 0, 83]], ![![-1, 1, 0], ![20, -36, 1], ![-29, 81, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 20, 2]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![53, 20, 2]] 
 ![![83, 0, 0], ![71, 1, 0], ![22, 0, 1]] where
  M :=![![![53, 20, 2], ![560, 215, 22], ![6160, 2342, 237]]]
  hmulB := by decide  
  f := ![![![-569, -56, 10]], ![![-453, -45, 8]], ![![-306, -26, 5]]]
  g := ![![![-17, 20, 2], ![-183, 215, 22], ![-1992, 2342, 237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-36, 1, 0]] ![![83, 0, 0], ![-36, 1, 0]]
  ![![-569, -56, 10]] where
 M := ![![![6889, 0, 0], ![-2988, 83, 0]], ![![-2988, 83, 0], ![1296, -72, 1]]]
 hmul := by decide  
 g := ![![![![4399, 1660, 166]], ![![-1348, -505, -50]]], ![![![-1348, -505, -50]], ![![416, 154, 15]]]]
 hle2 := by decide  
def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-569, -56, 10]] ![![53, 20, 2]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [32, 15, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 26, 77], [60, 62, 12], [0, 1]]
 g := ![![[7, 63, 49], [39, 81], [38, 4], [79, 77, 39], [3, 14, 1], []], ![[50, 52, 33, 61], [27, 73], [], [76, 76, 47, 19], [54, 84, 37, 63], [57, 55]], ![[52, 58, 1, 14], [44, 20], [9, 4], [23, 78, 56, 82], [59, 68, 20, 13], [33, 55]]]
 h' := ![![[43, 26, 77], [79, 0, 7], [80, 46, 80], [53, 49, 87], [82, 41, 67], [0, 0, 1], [0, 1]], ![[60, 62, 12], [76, 17, 78], [53, 68, 47], [63, 74], [49, 59, 13], [25, 66, 62], [43, 26, 77]], ![[0, 1], [87, 72, 4], [58, 64, 51], [41, 55, 2], [63, 78, 9], [52, 23, 26], [60, 62, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 41], []]
 b := ![[], [18, 19, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [32, 15, 75, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-131008, -41563, -2581]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1472, -467, -29]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-26, 33, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-26, 33, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![71, 33, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-26, 33, 1], ![280, 55, 34], ![9520, 3034, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -33, 97]], ![![-1, 0, 1], ![-22, -11, 34], ![33, 1, 89]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [60, 5, 1] where
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
 g := ![![[89, 25], [22], [49], [61], [61], [92, 1]], ![[61, 72], [22], [49], [61], [61], [87, 96]]]
 h' := ![![[92, 96], [2, 5], [35, 64], [29, 7], [10, 35], [9, 62], [0, 1]], ![[0, 1], [74, 92], [6, 33], [91, 90], [29, 62], [87, 35], [92, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [88, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [60, 5, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-784, 2271, 739]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-549, -228, 739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-34, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-34, 1, 0]] 
 ![![97, 0, 0], ![63, 1, 0], ![8, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-34, 1, 0], ![0, -34, 1], ![280, 81, -33]]]
  hmulB := by decide  
  f := ![![![1021, -30, 0], ![2910, 0, 0]], ![![715, -21, 0], ![2038, 0, 0]], ![![148, -4, 0], ![422, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 97, 0], ![-8, 0, 97]], ![![-1, 1, 0], ![22, -34, 1], ![-47, 81, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-26, 33, 1]] ![![97, 0, 0], ![-34, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3298, 97, 0]], ![![-2522, 3201, 97], ![1164, -1067, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-34, 1, 0]]], ![![![-26, 33, 1]], ![![12, -11, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-50, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-50, 1, 0]] 
 ![![101, 0, 0], ![51, 1, 0], ![25, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-50, 1, 0], ![0, -50, 1], ![280, 81, -49]]]
  hmulB := by decide  
  f := ![![![5051, -101, 0], ![10201, 0, 0]], ![![2601, -52, 0], ![5253, 0, 0]], ![![1275, -25, 0], ![2575, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 101, 0], ![-25, 0, 101]], ![![-1, 1, 0], ![25, -50, 1], ![-26, 81, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10039, 1168, -193]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![10039, 1168, -193]] 
 ![![101, 0, 0], ![52, 1, 0], ![23, 0, 1]] where
  M :=![![![10039, 1168, -193], ![-54040, -5594, 975], ![273000, 24935, -4619]]]
  hmulB := by decide  
  f := ![![![-1527061, -582537, -59158]], ![![-950212, -362483, -36811]], ![![-2126703, -811286, -82388]]]
  g := ![![![-458, 1168, -193], ![2123, -5594, 975], ![-9083, 24935, -4619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-3, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-3, 1, 0]] 
 ![![101, 0, 0], ![98, 1, 0], ![92, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-3, 1, 0], ![0, -3, 1], ![280, 81, -2]]]
  hmulB := by decide  
  f := ![![![109, -36, 0], ![3636, 0, 0]], ![![106, -35, 0], ![3536, 0, 0]], ![![100, -33, 0], ![3336, 1, 0]]]
  g := ![![![1, 0, 0], ![-98, 101, 0], ![-92, 0, 101]], ![![-1, 1, 0], ![2, -3, 1], ![-74, 81, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-50, 1, 0]] ![![10039, 1168, -193]]
  ![![101, 0, 0], ![-75, 2, 1]] where
 M := ![![![1013939, 117968, -19493]], ![![-555990, -63994, 10625]]]
 hmul := by decide  
 g := ![![![![6514, 1262, -146], ![-4747, 0, 0]]], ![![![-3540, -686, 79], ![2646, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-75, 2, 1]] ![![101, 0, 0], ![-3, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-303, 101, 0]], ![![-7575, 202, 101], ![505, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-3, 1, 0]]], ![![![-75, 2, 1]], ![![5, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-78, -31, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-78, -31, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![25, 72, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-78, -31, 1], ![280, 3, -30], ![-8400, -2150, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -72, 103]], ![![-1, -1, 1], ![10, 21, -30], ![-75, -2, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [36, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 102], [0, 1]]
 g := ![![[28, 83], [39, 72], [], [52], [60], [22, 1]], ![[0, 20], [78, 31], [], [52], [60], [44, 102]]]
 h' := ![![[22, 102], [38, 17], [0, 81], [94], [100, 19], [32, 36], [0, 1]], ![[0, 1], [0, 86], [31, 22], [94], [3, 84], [0, 67], [22, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [14, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [36, 81, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1332, 152, 128]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44, -88, 128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![30, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![30, 1, 0]] 
 ![![103, 0, 0], ![30, 1, 0], ![27, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![30, 1, 0], ![0, 30, 1], ![280, 81, 31]]]
  hmulB := by decide  
  f := ![![![1351, 45, 0], ![-4635, 0, 0]], ![![390, 13, 0], ![-1338, 0, 0]], ![![339, 11, 0], ![-1163, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 103, 0], ![-27, 0, 103]], ![![0, 1, 0], ![-9, 30, 1], ![-29, 81, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-78, -31, 1]] ![![103, 0, 0], ![30, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3090, 103, 0]], ![![-8034, -3193, 103], ![-2060, -927, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![30, 1, 0]]], ![![![-78, -31, 1]], ![![-20, -9, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-3, -23, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-3, -23, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![104, 84, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-3, -23, 1], ![280, 78, -22], ![-6160, -1502, 56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -84, 107]], ![![-1, -1, 1], ![24, 18, -22], ![-112, -58, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [95, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 106], [0, 1]]
 g := ![![[11, 36], [2, 40], [27], [19, 13], [25], [25, 1]], ![[55, 71], [39, 67], [27], [23, 94], [25], [50, 106]]]
 h' := ![![[25, 106], [24, 6], [92, 19], [14, 53], [99, 86], [86, 102], [0, 1]], ![[0, 1], [67, 101], [32, 88], [55, 54], [2, 21], [68, 5], [25, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [94, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [95, 82, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1018, 2847, 481]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-458, -351, 481]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![22, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![22, 1, 0]] 
 ![![107, 0, 0], ![22, 1, 0], ![51, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![22, 1, 0], ![0, 22, 1], ![280, 81, 23]]]
  hmulB := by decide  
  f := ![![![1167, 53, 0], ![-5671, 0, 0]], ![![198, 9, 0], ![-962, 0, 0]], ![![555, 25, 0], ![-2697, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 107, 0], ![-51, 0, 107]], ![![0, 1, 0], ![-5, 22, 1], ![-25, 81, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-3, -23, 1]] ![![107, 0, 0], ![22, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2354, 107, 0]], ![![-321, -2461, 107], ![214, -428, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![22, 1, 0]]], ![![![-3, -23, 1]], ![![2, -4, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31167809, 11889769, 1207434]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![31167809, 11889769, 1207434]] 
 ![![109, 0, 0], ![0, 109, 0], ![67, 65, 1]] where
  M :=![![![31167809, 11889769, 1207434], ![338081520, 128969963, 13097203], ![3667216840, 1398954963, 142067166]]]
  hmulB := by decide  
  f := ![![![39141, 5232, -815]], ![![-228200, -26874, 4417]], ![![-100677, -11621, 1927]]]
  g := ![![![-456241, -610949, 1207434], ![-4948909, -6627048, 13097203], ![-53681498, -71884503, 142067166]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [92, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 108], [0, 1]]
 g := ![![[103, 87], [88], [93, 104], [5, 38], [105], [7, 1]], ![[58, 22], [88], [58, 5], [53, 71], [105], [14, 108]]]
 h' := ![![[7, 108], [52, 14], [55, 52], [85, 70], [32, 93], [10, 66], [0, 1]], ![[0, 1], [41, 95], [92, 57], [30, 39], [29, 16], [36, 43], [7, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [69, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [92, 102, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![932, 421, -17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 14, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39141, 5232, -815]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![39141, 5232, -815]] 
 ![![109, 0, 0], ![43, 1, 0], ![4, 0, 1]] where
  M :=![![![39141, 5232, -815], ![-228200, -26874, 4417], ![1236760, 129577, -22457]]]
  hmulB := by decide  
  f := ![![![31167809, 11889769, 1207434]], ![![15397223, 5873670, 596485]], ![![34787964, 13270771, 1347678]]]
  g := ![![![-1675, 5232, -815], ![8346, -26874, 4417], ![-38947, 129577, -22457]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![31167809, 11889769, 1207434]] ![![39141, 5232, -815]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [32, 82, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 82, 19], [60, 30, 94], [0, 1]]
 g := ![![[42, 16, 9], [1, 52], [1, 22], [40, 36], [106, 66, 99], [1]], ![[49, 49, 57, 93], [19, 60], [18, 105], [55, 22], [43, 29, 60, 21], [94, 0, 26, 79]], ![[109, 7, 10, 103], [65, 28], [9, 72], [17, 60], [51, 52, 107, 35], [65, 87, 21, 34]]]
 h' := ![![[12, 82, 19], [99, 30, 110], [40, 90, 74], [80, 110, 19], [111, 51, 6], [81, 31, 72], [0, 1]], ![[60, 30, 94], [18, 8, 28], [20, 25, 88], [12, 66, 61], [23, 46, 19], [76, 31, 37], [12, 82, 19]], ![[0, 1], [49, 75, 88], [35, 111, 64], [53, 50, 33], [91, 16, 88], [11, 51, 4], [60, 30, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 38], []]
 b := ![[], [7, 51, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [32, 82, 41, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4137156, 1554428, 149612]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36612, 13756, 1324]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-91, 35, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-91, 35, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![36, 35, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-91, 35, 1], ![280, -10, 36], ![10080, 3196, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -35, 127]], ![![-1, 0, 1], ![-8, -10, 36], ![72, 18, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [55, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 126], [0, 1]]
 g := ![![[46, 25], [104, 25], [57, 4], [63, 79], [87, 120], [10, 1]], ![[42, 102], [100, 102], [97, 123], [91, 48], [17, 7], [20, 126]]]
 h' := ![![[10, 126], [122, 122], [40, 122], [91, 125], [41, 98], [85, 45], [0, 1]], ![[0, 1], [72, 5], [117, 5], [71, 2], [5, 29], [27, 82], [10, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [74, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [55, 117, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1461, 220, -30]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 10, -30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-36, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-36, 1, 0]] 
 ![![127, 0, 0], ![91, 1, 0], ![101, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-36, 1, 0], ![0, -36, 1], ![280, 81, -35]]]
  hmulB := by decide  
  f := ![![![2809, -78, 0], ![9906, 0, 0]], ![![1981, -55, 0], ![6986, 0, 0]], ![![2243, -62, 0], ![7910, 1, 0]]]
  g := ![![![1, 0, 0], ![-91, 127, 0], ![-101, 0, 127]], ![![-1, 1, 0], ![25, -36, 1], ![-28, 81, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-91, 35, 1]] ![![127, 0, 0], ![-36, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-4572, 127, 0]], ![![-11557, 4445, 127], ![3556, -1270, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-36, 1, 0]]], ![![![-91, 35, 1]], ![![28, -10, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-1, -19, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-1, -19, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![130, 112, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-1, -19, 1], ![280, 80, -18], ![-5040, -1178, 62]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-130, -112, 131]], ![![-1, -1, 1], ![20, 16, -18], ![-100, -62, 62]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [96, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 130], [0, 1]]
 g := ![![[40, 25], [91, 1], [75], [60], [9], [109], [1]], ![[63, 106], [50, 130], [75], [60], [9], [109], [1]]]
 h' := ![![[90, 130], [41, 5], [65, 130], [45, 72], [98, 45], [62, 128], [35, 90], [0, 1]], ![[0, 1], [98, 126], [106, 1], [106, 59], [87, 86], [54, 3], [13, 41], [90, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [114, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [96, 41, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2336, 1809, 415]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-394, -341, 415]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![18, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![18, 1, 0]] 
 ![![131, 0, 0], ![18, 1, 0], ![69, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![18, 1, 0], ![0, 18, 1], ![280, 81, 19]]]
  hmulB := by decide  
  f := ![![![811, 45, 0], ![-5895, 0, 0]], ![![90, 5, 0], ![-654, 0, 0]], ![![417, 23, 0], ![-3031, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 131, 0], ![-69, 0, 131]], ![![0, 1, 0], ![-3, 18, 1], ![-19, 81, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-1, -19, 1]] ![![131, 0, 0], ![18, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![2358, 131, 0]], ![![-131, -2489, 131], ![262, -262, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![18, 1, 0]]], ![![![-1, -19, 1]], ![![2, -2, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-17, 47, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-17, 47, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![120, 47, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-17, 47, 1], ![280, 64, 48], ![13440, 4168, 112]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -47, 137]], ![![-1, 0, 1], ![-40, -16, 48], ![0, -8, 112]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [105, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 136], [0, 1]]
 g := ![![[18, 107], [81], [25], [119, 135], [68], [99], [1]], ![[0, 30], [81], [25], [63, 2], [68], [99], [1]]]
 h' := ![![[28, 136], [27, 92], [77, 9], [109, 5], [132, 51], [82, 43], [32, 28], [0, 1]], ![[0, 1], [0, 45], [55, 128], [112, 132], [53, 86], [53, 94], [131, 109], [28, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [116, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [105, 109, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9753, -2926, 614]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-609, -232, 614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-48, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-48, 1, 0]] 
 ![![137, 0, 0], ![89, 1, 0], ![25, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-48, 1, 0], ![0, -48, 1], ![280, 81, -47]]]
  hmulB := by decide  
  f := ![![![1537, -32, 0], ![4384, 0, 0]], ![![1009, -21, 0], ![2878, 0, 0]], ![![305, -6, 0], ![870, 1, 0]]]
  g := ![![![1, 0, 0], ![-89, 137, 0], ![-25, 0, 137]], ![![-1, 1, 0], ![31, -48, 1], ![-42, 81, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-17, 47, 1]] ![![137, 0, 0], ![-48, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6576, 137, 0]], ![![-2329, 6439, 137], ![1096, -2192, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-48, 1, 0]]], ![![![-17, 47, 1]], ![![8, -16, 0]]]]
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


lemma PB178I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB178I2 : PrimesBelowBoundCertificateInterval O 79 137 178 where
  m := 11
  g := ![3, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB178I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
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
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
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
      exact NI109N1
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
  β := ![I83N0, I83N1, I97N1, I101N0, I101N1, I101N2, I103N1, I107N1, I109N1, I127N1, I131N1, I137N1]
  Il := ![[I83N0, I83N0, I83N1], [], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N1], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
