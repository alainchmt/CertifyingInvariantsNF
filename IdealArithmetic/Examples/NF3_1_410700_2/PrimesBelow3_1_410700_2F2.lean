
import IdealArithmetic.Examples.NF3_1_410700_2.RI3_1_410700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-18, -36, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-18, -36, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![65, 47, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-18, -36, 1], ![201, -13, -108], ![-7303, -1409, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -47, 83]], ![![-1, -1, 1], ![87, 61, -108], ![-106, -30, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [10, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 82], [0, 1]]
 g := ![![[43, 25], [34, 41], [17], [59], [79, 59], [1]], ![[0, 58], [0, 42], [17], [59], [24, 24], [1]]]
 h' := ![![[68, 82], [75, 5], [26, 46], [14, 73], [40, 68], [73, 68], [0, 1]], ![[0, 1], [0, 78], [0, 37], [81, 10], [16, 15], [49, 15], [68, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [56, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [10, 15, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2355, 2469, 962]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-725, -515, 962]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![25, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![25, 1, 0]] 
 ![![83, 0, 0], ![25, 1, 0], ![60, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![25, 1, 0], ![0, 26, 3], ![201, 41, 25]]]
  hmulB := by decide  
  f := ![![![201, 8, 0], ![-664, 0, 0]], ![![25, 1, 0], ![-82, 0, 0]], ![![120, -4, -1], ![-396, 28, 0]]]
  g := ![![![1, 0, 0], ![-25, 83, 0], ![-60, 0, 83]], ![![0, 1, 0], ![-10, 26, 3], ![-28, 41, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-18, -36, 1]] ![![83, 0, 0], ![25, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2075, 83, 0]], ![![-1494, -2988, 83], ![-249, -913, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![25, 1, 0]]], ![![![-18, -36, 1]], ![![-3, -11, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-62, -14, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-62, -14, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![27, 75, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-62, -14, 1], ![201, -35, -42], ![-2881, -507, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -75, 89]], ![![-1, -1, 1], ![15, 35, -42], ![-26, 12, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [39, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 88], [0, 1]]
 g := ![![[4, 16], [16], [16], [16, 64], [32, 39], [1]], ![[0, 73], [16], [16], [0, 25], [0, 50], [1]]]
 h' := ![![[22, 88], [88, 85], [0, 4], [88, 85], [87, 81], [50, 22], [0, 1]], ![[0, 1], [0, 4], [88, 85], [0, 4], [0, 8], [0, 67], [22, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [31, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [39, 67, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![308, 2151, 1353]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-407, -1116, 1353]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![42, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![42, 1, 0]] 
 ![![89, 0, 0], ![42, 1, 0], ![21, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![42, 1, 0], ![0, 43, 3], ![201, 41, 42]]]
  hmulB := by decide  
  f := ![![![1639, 39, 0], ![-3471, 0, 0]], ![![714, 17, 0], ![-1512, 0, 0]], ![![315, -7, -1], ![-667, 30, 0]]]
  g := ![![![1, 0, 0], ![-42, 89, 0], ![-21, 0, 89]], ![![0, 1, 0], ![-21, 43, 3], ![-27, 41, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-62, -14, 1]] ![![89, 0, 0], ![42, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3738, 89, 0]], ![![-5518, -1246, 89], ![-2403, -623, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![42, 1, 0]]], ![![![-62, -14, 1]], ![![-27, -7, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [57, 88, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 77, 1], [65, 19, 96], [0, 1]]
 g := ![![[57, 36, 33], [35, 27], [90, 65], [94, 22], [78, 95], [1]], ![[96, 44, 38, 16], [96, 54], [], [83, 65], [4, 32], [84, 43, 54, 1]], ![[29, 16, 2, 95], [36, 4], [57, 65], [59, 61], [37, 66], [57, 74, 40, 96]]]
 h' := ![![[49, 77, 1], [89, 42, 18], [12, 77, 30], [96, 66, 68], [64, 81, 33], [40, 9, 17], [0, 1]], ![[65, 19, 96], [93, 62, 93], [6, 28, 65], [54, 29], [41, 66, 29], [50, 36, 41], [49, 77, 1]], ![[0, 1], [20, 90, 83], [61, 89, 2], [20, 2, 29], [52, 47, 35], [67, 52, 39], [65, 19, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 30], []]
 b := ![[], [24, 81, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [57, 88, 80, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56745, -12998, -8342]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![585, -134, -86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-28, -6, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-28, -6, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![73, 95, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-28, -6, 1], ![201, 7, -18], ![-1273, -179, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -95, 101]], ![![-1, -1, 1], ![15, 17, -18], ![-22, -14, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [41, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 100], [0, 1]]
 g := ![![[57, 6], [22], [56, 5], [47], [88], [87, 1]], ![[74, 95], [22], [87, 96], [47], [88], [73, 100]]]
 h' := ![![[87, 100], [29, 39], [27, 27], [39, 56], [42, 59], [69, 54], [0, 1]], ![[0, 1], [89, 62], [53, 74], [63, 45], [24, 42], [20, 47], [87, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [69, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [41, 14, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2401, 4403, 1909]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1356, -1752, 1909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![18, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![18, 1, 0]] 
 ![![101, 0, 0], ![18, 1, 0], ![88, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![18, 1, 0], ![0, 19, 3], ![201, 41, 18]]]
  hmulB := by decide  
  f := ![![![1207, 67, 0], ![-6767, 0, 0]], ![![198, 11, 0], ![-1110, 0, 0]], ![![1052, 52, -1], ![-5898, 34, 0]]]
  g := ![![![1, 0, 0], ![-18, 101, 0], ![-88, 0, 101]], ![![0, 1, 0], ![-6, 19, 3], ![-21, 41, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-28, -6, 1]] ![![101, 0, 0], ![18, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1818, 101, 0]], ![![-2828, -606, 101], ![-303, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![18, 1, 0]]], ![![![-28, -6, 1]], ![![-3, -1, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![16, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![16, 1, 0]] 
 ![![103, 0, 0], ![16, 1, 0], ![81, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![16, 1, 0], ![0, 17, 3], ![201, 41, 16]]]
  hmulB := by decide  
  f := ![![![641, 40, 0], ![-4120, 0, 0]], ![![80, 5, 0], ![-514, 0, 0]], ![![487, 19, -2], ![-3130, 69, 0]]]
  g := ![![![1, 0, 0], ![-16, 103, 0], ![-81, 0, 103]], ![![0, 1, 0], ![-5, 17, 3], ![-17, 41, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![24, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![24, 1, 0]] 
 ![![103, 0, 0], ![24, 1, 0], ![6, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![24, 1, 0], ![0, 25, 3], ![201, 41, 24]]]
  hmulB := by decide  
  f := ![![![1465, 61, 0], ![-6283, 0, 0]], ![![312, 13, 0], ![-1338, 0, 0]], ![![42, -15, -2], ![-180, 69, 0]]]
  g := ![![![1, 0, 0], ![-24, 103, 0], ![-6, 0, 103]], ![![0, 1, 0], ![-6, 25, 3], ![-9, 41, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-41, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-41, 1, 0]] 
 ![![103, 0, 0], ![62, 1, 0], ![37, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-41, 1, 0], ![0, -40, 3], ![201, 41, -41]]]
  hmulB := by decide  
  f := ![![![4183, -102, 0], ![10506, 0, 0]], ![![2502, -61, 0], ![6284, 0, 0]], ![![1509, -10, -2], ![3790, 69, 0]]]
  g := ![![![1, 0, 0], ![-62, 103, 0], ![-37, 0, 103]], ![![-1, 1, 0], ![23, -40, 3], ![-8, 41, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![16, 1, 0]] ![![103, 0, 0], ![24, 1, 0]]
  ![![103, 0, 0], ![-78, 48, 1]] where
 M := ![![![10609, 0, 0], ![2472, 103, 0]], ![![1648, 103, 0], ![384, 41, 3]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![24, 1, 0], ![0, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![6, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-78, 48, 1]] ![![103, 0, 0], ![-41, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4223, 103, 0]], ![![-8034, 4944, 103], ![3399, -1957, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-41, 1, 0]]], ![![![-78, 48, 1]], ![![33, -19, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![2, -20, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![2, -20, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![2, 87, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![2, -20, 1], ![201, 23, -60], ![-4087, -753, 43]]]
  hmulB := by decide  
  f := ![![![-1, 20, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -87, 107]], ![![0, -1, 1], ![3, 49, -60], ![-39, -42, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [90, 103, 1] where
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
 g := ![![[38, 44], [37, 39], [14], [95, 85], [19], [4, 1]], ![[0, 63], [86, 68], [14], [7, 22], [19], [8, 106]]]
 h' := ![![[4, 106], [94, 30], [17, 50], [10, 96], [25, 70], [68, 33], [0, 1]], ![[0, 1], [0, 77], [3, 57], [73, 11], [91, 37], [93, 74], [4, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [51, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [90, 103, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2435, 2293, 522]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, -403, 522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-47, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-47, 1, 0]] 
 ![![107, 0, 0], ![60, 1, 0], ![64, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-47, 1, 0], ![0, -46, 3], ![201, 41, -47]]]
  hmulB := by decide  
  f := ![![![2116, -45, 0], ![4815, 0, 0]], ![![1176, -25, 0], ![2676, 0, 0]], ![![1292, -12, -1], ![2940, 36, 0]]]
  g := ![![![1, 0, 0], ![-60, 107, 0], ![-64, 0, 107]], ![![-1, 1, 0], ![24, -46, 3], ![7, 41, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![2, -20, 1]] ![![107, 0, 0], ![-47, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-5029, 107, 0]], ![![214, -2140, 107], ![107, 963, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-47, 1, 0]]], ![![![2, -20, 1]], ![![1, 9, -1]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [87, 55, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 72, 93], [34, 36, 16], [0, 1]]
 g := ![![[78, 30, 7], [42, 60], [50, 6, 12], [57, 12, 29], [101, 36], [1]], ![[45, 86, 106, 82], [34, 3], [94, 79, 92, 66], [60, 102, 84, 106], [60, 36], [14, 71, 91, 46]], ![[38, 14, 14, 48], [88, 97], [92, 3, 51, 108], [40, 103, 81, 28], [104, 35], [46, 22, 13, 63]]]
 h' := ![![[81, 72, 93], [43, 65, 15], [10, 80, 13], [55, 106, 11], [90, 11, 62], [22, 54, 6], [0, 1]], ![[34, 36, 16], [49, 105, 45], [101, 51, 60], [32, 26, 8], [41, 85, 94], [47, 96, 6], [81, 72, 93]], ![[0, 1], [80, 48, 49], [91, 87, 36], [9, 86, 90], [86, 13, 62], [95, 68, 97], [34, 36, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 107], []]
 b := ![[], [72, 6, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [87, 55, 103, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1597848004, 580209616, 145030604]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14659156, 5323024, 1330556]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![9, 20, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![9, 20, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![9, 20, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![9, 20, 1], ![201, 70, 60], ![3953, 887, 50]]]
  hmulB := by decide  
  f := ![![![-8, -20, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -20, 113]], ![![0, 0, 1], ![-3, -10, 60], ![31, -1, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [90, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 112], [0, 1]]
 g := ![![[53, 31], [53], [30], [28], [34, 26], [89, 1]], ![[100, 82], [53], [30], [28], [88, 87], [65, 112]]]
 h' := ![![[89, 112], [28, 101], [74, 36], [47, 97], [104, 64], [13, 34], [0, 1]], ![[0, 1], [90, 12], [1, 77], [92, 16], [37, 49], [101, 79], [89, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [25, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [90, 24, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1876, 1143, 447]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19, -69, 447]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![53, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![53, 1, 0]] 
 ![![113, 0, 0], ![53, 1, 0], ![63, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![53, 1, 0], ![0, 54, 3], ![201, 41, 53]]]
  hmulB := by decide  
  f := ![![![637, 12, 0], ![-1356, 0, 0]], ![![265, 5, 0], ![-564, 0, 0]], ![![327, -12, -1], ![-696, 38, 0]]]
  g := ![![![1, 0, 0], ![-53, 113, 0], ![-63, 0, 113]], ![![0, 1, 0], ![-27, 54, 3], ![-47, 41, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![9, 20, 1]] ![![113, 0, 0], ![53, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![5989, 113, 0]], ![![1017, 2260, 113], ![678, 1130, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![53, 1, 0]]], ![![![9, 20, 1]], ![![6, 10, 1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [73, 122, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 71, 25], [91, 55, 102], [0, 1]]
 g := ![![[114, 79, 72], [8, 76, 64], [46, 75, 34], [60], [6, 94, 68], [1]], ![[28, 63, 12, 38], [26, 36, 23, 73], [119, 92, 11, 84], [103, 126, 7, 113], [47, 14, 11, 69], [14, 73, 125, 4]], ![[118, 120, 108, 80], [117, 43, 92, 5], [21, 64, 62, 10], [67, 11, 15, 14], [104, 64, 126, 67], [78, 124, 32, 123]]]
 h' := ![![[60, 71, 25], [51, 41, 31], [71, 123, 119], [65, 120, 62], [70, 21], [54, 5, 24], [0, 1]], ![[91, 55, 102], [122, 71, 63], [87, 72, 95], [74, 46, 60], [60, 94, 17], [94, 49, 48], [60, 71, 25]], ![[0, 1], [80, 15, 33], [97, 59, 40], [25, 88, 5], [76, 12, 110], [101, 73, 55], [91, 55, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 96], []]
 b := ![[], [61, 58, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [73, 122, 103, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10803890, 4482465, 1242822]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85070, 35295, 9786]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-92, -5, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-92, -5, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![39, 126, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-92, -5, 1], ![201, -56, -15], ![-1072, -138, -51]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -126, 131]], ![![-1, -1, 1], ![6, 14, -15], ![7, 48, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [73, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 130], [0, 1]]
 g := ![![[29, 12], [107, 41], [61], [108], [3], [48], [1]], ![[39, 119], [32, 90], [61], [108], [3], [48], [1]]]
 h' := ![![[110, 130], [49, 55], [102, 33], [25, 42], [124, 97], [122, 93], [58, 110], [0, 1]], ![[0, 1], [73, 76], [64, 98], [60, 89], [52, 34], [3, 38], [106, 21], [110, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [108, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [73, 21, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32011, 22180, 7878]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2101, -7408, 7878]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![15, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![15, 1, 0]] 
 ![![131, 0, 0], ![15, 1, 0], ![51, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![15, 1, 0], ![0, 16, 3], ![201, 41, 15]]]
  hmulB := by decide  
  f := ![![![466, 31, 0], ![-4061, 0, 0]], ![![30, 2, 0], ![-261, 0, 0]], ![![186, 7, -1], ![-1621, 44, 0]]]
  g := ![![![1, 0, 0], ![-15, 131, 0], ![-51, 0, 131]], ![![0, 1, 0], ![-3, 16, 3], ![-9, 41, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-92, -5, 1]] ![![131, 0, 0], ![15, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![1965, 131, 0]], ![![-12052, -655, 131], ![-1179, -131, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![15, 1, 0]]], ![![![-92, -5, 1]], ![![-9, -1, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-26, -50, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-26, -50, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![111, 87, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-26, -50, 1], ![201, -35, -150], ![-10117, -1983, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-111, -87, 137]], ![![-1, -1, 1], ![123, 95, -150], ![-86, -24, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [2, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 136], [0, 1]]
 g := ![![[22, 69], [69], [76], [92, 68], [103], [18], [1]], ![[0, 68], [69], [76], [114, 69], [103], [18], [1]]]
 h' := ![![[93, 136], [3, 53], [2, 53], [90, 79], [133, 94], [105, 69], [135, 93], [0, 1]], ![[0, 1], [0, 84], [136, 84], [39, 58], [107, 43], [83, 68], [16, 44], [93, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [23, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [2, 44, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![676, 67, 111]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-85, -70, 111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![13, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![13, 1, 0]] 
 ![![137, 0, 0], ![13, 1, 0], ![122, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![13, 1, 0], ![0, 14, 3], ![201, 41, 13]]]
  hmulB := by decide  
  f := ![![![1379, 106, 0], ![-14522, 0, 0]], ![![117, 9, 0], ![-1232, 0, 0]], ![![1232, 90, -1], ![-12974, 46, 0]]]
  g := ![![![1, 0, 0], ![-13, 137, 0], ![-122, 0, 137]], ![![0, 1, 0], ![-4, 14, 3], ![-14, 41, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-26, -50, 1]] ![![137, 0, 0], ![13, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![1781, 137, 0]], ![![-3562, -6850, 137], ![-137, -685, -137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![13, 1, 0]]], ![![![-26, -50, 1]], ![![-1, -5, -1]]]]
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


lemma PB182I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB182I2 : PrimesBelowBoundCertificateInterval O 79 137 182 where
  m := 11
  g := ![2, 2, 1, 2, 3, 2, 1, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB182I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I101N1, I103N0, I103N1, I103N2, I107N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
