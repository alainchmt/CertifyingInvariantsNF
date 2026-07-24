
import IdealArithmetic.Examples.NF3_1_933907_1.RI3_1_933907_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [24, 14, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 4, 46], [37, 78, 37], [0, 1]]
 g := ![![[62, 9, 9], [31, 79, 3], [21, 51], [64, 17], [9, 43, 1], []], ![[46, 28, 3, 39], [20, 47, 0, 55], [45, 41], [68, 28], [72, 30, 43, 71], [56, 41]], ![[20, 44, 28, 12], [28, 27], [25, 17], [18, 69], [5, 49, 59, 11], [65, 41]]]
 h' := ![![[6, 4, 46], [3, 63, 80], [22, 53, 70], [51, 39, 36], [33, 4, 10], [0, 0, 1], [0, 1]], ![[37, 78, 37], [72, 17, 8], [80, 79, 13], [9, 71, 37], [8, 80, 51], [20, 23, 78], [6, 4, 46]], ![[0, 1], [2, 3, 78], [67, 34], [13, 56, 10], [14, 82, 22], [58, 60, 4], [37, 78, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 52], []]
 b := ![[], [51, 44, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [24, 14, 40, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4316249, 1584304, -305108]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52003, 19088, -3676]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-124, -35, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-124, -35, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![54, 54, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-124, -35, 1], ![-754, -42, -70], ![26767, -4472, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -54, 89]], ![![-2, -1, 1], ![34, 42, -70], ![305, -46, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [45, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 88], [0, 1]]
 g := ![![[70, 2], [42], [9], [24, 8], [58, 68], [1]], ![[0, 87], [42], [9], [11, 81], [81, 21], [1]]]
 h' := ![![[54, 88], [15, 64], [6, 24], [77, 86], [60, 50], [44, 54], [0, 1]], ![[0, 1], [0, 25], [56, 65], [4, 3], [1, 39], [23, 35], [54, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [17, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [45, 35, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11, -5062, 2006]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1217, -1274, 2006]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-19, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-19, 1, 0]] 
 ![![89, 0, 0], ![70, 1, 0], ![7, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-19, 1, 0], ![0, -18, 2], ![-754, 117, -19]]]
  hmulB := by decide  
  f := ![![![20, 1259, -140], ![89, 6230, 0]], ![![20, 989, -110], ![90, 4895, 0]], ![![2, 99, -11], ![9, 490, 0]]]
  g := ![![![1, 0, 0], ![-70, 89, 0], ![-7, 0, 89]], ![![-1, 1, 0], ![14, -18, 2], ![-99, 117, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-124, -35, 1]] ![![89, 0, 0], ![-19, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1691, 89, 0]], ![![-11036, -3115, 89], ![1602, 623, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-19, 1, 0]]], ![![![-124, -35, 1]], ![![18, 7, -1]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [51, 68, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 50, 80], [45, 46, 17], [0, 1]]
 g := ![![[72, 19, 18], [9, 54], [62, 61], [26, 1], [57, 86], [1]], ![[82, 14, 33, 80], [24, 75], [32, 61], [0, 72], [50, 3], [36, 52, 57, 34]], ![[47, 72, 79, 5], [95, 33], [], [76, 47], [21, 73], [24, 55, 46, 63]]]
 h' := ![![[14, 50, 80], [17, 28, 42], [31, 61, 32], [63, 34, 35], [82, 32, 1], [46, 29, 59], [0, 1]], ![[45, 46, 17], [2, 68, 1], [16, 12, 47], [22, 8, 62], [33, 44, 84], [35, 50, 87], [14, 50, 80]], ![[0, 1], [69, 1, 54], [8, 24, 18], [69, 55], [29, 21, 12], [79, 18, 48], [45, 46, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 8], []]
 b := ![[], [17, 24, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [51, 68, 38, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-497222, 146276, -39576]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5126, 1508, -408]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-100, 27, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-100, 27, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![1, 27, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-100, 27, 1], ![-754, 44, 54], ![-19981, 2782, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -27, 101]], ![![-1, 0, 1], ![-8, -14, 54], ![-198, 23, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [89, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 100], [0, 1]]
 g := ![![[28, 81], [71], [3, 84], [70], [100], [33, 1]], ![[75, 20], [71], [48, 17], [70], [100], [66, 100]]]
 h' := ![![[33, 100], [27, 9], [36, 77], [9, 65], [52, 26], [93, 91], [0, 1]], ![[0, 1], [21, 92], [52, 24], [33, 36], [1, 75], [66, 10], [33, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [44, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [89, 68, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5497, -7221, 2583]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-80, -762, 2583]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![47, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![47, 1, 0]] 
 ![![101, 0, 0], ![47, 1, 0], ![84, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![47, 1, 0], ![0, 48, 2], ![-754, 117, 47]]]
  hmulB := by decide  
  f := ![![![1364, 29, 0], ![-2929, 0, 0]], ![![564, 12, 0], ![-1211, 0, 0]], ![![1140, 0, -1], ![-2448, 51, 0]]]
  g := ![![![1, 0, 0], ![-47, 101, 0], ![-84, 0, 101]], ![![0, 1, 0], ![-24, 48, 2], ![-101, 117, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-100, 27, 1]] ![![101, 0, 0], ![47, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4747, 101, 0]], ![![-10100, 2727, 101], ![-5454, 1313, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![47, 1, 0]]], ![![![-100, 27, 1]], ![![-54, 13, 1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![35, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![35, 1, 0]] 
 ![![103, 0, 0], ![35, 1, 0], ![91, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![35, 1, 0], ![0, 36, 2], ![-754, 117, 35]]]
  hmulB := by decide  
  f := ![![![876, 25, 0], ![-2575, 0, 0]], ![![280, 8, 0], ![-823, 0, 0]], ![![812, 5, -1], ![-2387, 52, 0]]]
  g := ![![![1, 0, 0], ![-35, 103, 0], ![-91, 0, 103]], ![![0, 1, 0], ![-14, 36, 2], ![-78, 117, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-33, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-33, 1, 0]] 
 ![![103, 0, 0], ![70, 1, 0], ![90, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-33, 1, 0], ![0, -32, 2], ![-754, 117, -33]]]
  hmulB := by decide  
  f := ![![![1288, -39, 0], ![4017, 0, 0]], ![![892, -27, 0], ![2782, 0, 0]], ![![1128, -18, -1], ![3518, 52, 0]]]
  g := ![![![1, 0, 0], ![-70, 103, 0], ![-90, 0, 103]], ![![-1, 1, 0], ![20, -32, 2], ![-58, 117, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93482695, 18795255, -2158833]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-93482695, 18795255, -2158833]] 
 ![![103, 0, 0], ![100, 1, 0], ![100, 0, 1]] where
  M :=![![![-93482695, 18795255, -2158833], ![1627760082, -327270901, 37590510], ![-14985502311, 3012924876, -346066156]]]
  hmulB := by decide  
  f := ![![![800204, -60072, -11517]], ![![861206, -64219, -12348]], ![![1174493, -84405, -16495]]]
  g := ![![![-17059465, 18795255, -2158833], ![297046594, -327270901, 37590510], ![-2734673537, 3012924876, -346066156]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![35, 1, 0]] ![![103, 0, 0], ![-33, 1, 0]]
  ![![800204, -60072, -11517]] where
 M := ![![![10609, 0, 0], ![-3399, 103, 0]], ![![3605, 103, 0], ![-1155, 3, 2]]]
 hmul := by decide  
 g := ![![![![-9628717585, 1935911265, -222359799]], ![![4712689017, -947514316, 108831999]]], ![![![-1644134243, 330563024, -37968645]], ![![804706683, -161791092, 18583411]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![800204, -60072, -11517]] ![![-93482695, 18795255, -2158833]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![76, -12, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![76, -12, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![76, 95, 1]] where
  M :=![![![76, -12, 1], ![-754, 181, -24], ![9425, -1781, 193]]]
  hmulB := by decide  
  f := ![![![-73, 5, 1]], ![![-754, 49, 10]], ![![-753, 49, 10]]]
  g := ![![![0, -1, 1], ![10, 23, -24], ![-49, -188, 193]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [88, 66, 1] where
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
 g := ![![[81, 76], [6, 92], [64], [5, 57], [37], [41, 1]], ![[94, 31], [33, 15], [64], [95, 50], [37], [82, 106]]]
 h' := ![![[41, 106], [7, 66], [76, 78], [95, 8], [105, 48], [30, 95], [0, 1]], ![[0, 1], [38, 41], [64, 29], [102, 99], [40, 59], [73, 12], [41, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [77, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [88, 66, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5567, -2117, 863]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-665, -786, 863]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 5, 1]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-73, 5, 1]] 
 ![![107, 0, 0], ![24, 1, 0], ![21, 0, 1]] where
  M :=![![![-73, 5, 1], ![-754, 49, 10], ![-3393, 208, 44]]]
  hmulB := by decide  
  f := ![![![76, -12, 1]], ![![10, -1, 0]], ![![103, -19, 2]]]
  g := ![![![-2, 5, 1], ![-20, 49, 10], ![-87, 208, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![76, -12, 1]] ![![-73, 5, 1]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![18, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![18, 1, 0]] 
 ![![109, 0, 0], ![18, 1, 0], ![47, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![18, 1, 0], ![0, 19, 2], ![-754, 117, 18]]]
  hmulB := by decide  
  f := ![![![1711, 95, 0], ![-10355, 0, 0]], ![![270, 15, 0], ![-1634, 0, 0]], ![![713, 30, -1], ![-4315, 55, 0]]]
  g := ![![![1, 0, 0], ![-18, 109, 0], ![-47, 0, 109]], ![![0, 1, 0], ![-4, 19, 2], ![-34, 117, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![37, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![37, 1, 0]] 
 ![![109, 0, 0], ![37, 1, 0], ![60, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![37, 1, 0], ![0, 38, 2], ![-754, 117, 37]]]
  hmulB := by decide  
  f := ![![![1259, 34, 0], ![-3706, 0, 0]], ![![407, 11, 0], ![-1198, 0, 0]], ![![636, -2, -1], ![-1872, 55, 0]]]
  g := ![![![1, 0, 0], ![-37, 109, 0], ![-60, 0, 109]], ![![0, 1, 0], ![-14, 38, 2], ![-67, 117, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![53, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![53, 1, 0]] 
 ![![109, 0, 0], ![53, 1, 0], ![95, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![53, 1, 0], ![0, 54, 2], ![-754, 117, 53]]]
  hmulB := by decide  
  f := ![![![743, 14, 0], ![-1526, 0, 0]], ![![371, 7, 0], ![-762, 0, 0]], ![![703, -14, -1], ![-1444, 55, 0]]]
  g := ![![![1, 0, 0], ![-53, 109, 0], ![-95, 0, 109]], ![![0, 1, 0], ![-28, 54, 2], ![-110, 117, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![18, 1, 0]] ![![109, 0, 0], ![37, 1, 0]]
  ![![109, 0, 0], ![-103, 28, 1]] where
 M := ![![![11881, 0, 0], ![4033, 109, 0]], ![![1962, 109, 0], ![666, 56, 2]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![37, 1, 0], ![0, 0, 0]]], ![![![18, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-103, 28, 1]] ![![109, 0, 0], ![53, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![5777, 109, 0]], ![![-11227, 3052, 109], ![-6213, 1526, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![53, 1, 0]]], ![![![-103, 28, 1]], ![![-57, 14, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-73, 16, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-73, 16, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![40, 16, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-73, 16, 1], ![-754, 60, 32], ![-11687, 1495, 44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -16, 113]], ![![-1, 0, 1], ![-18, -4, 32], ![-119, 7, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [87, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 112], [0, 1]]
 g := ![![[8, 13], [104], [30], [56], [69, 8], [95, 1]], ![[0, 100], [104], [30], [56], [38, 105], [77, 112]]]
 h' := ![![[95, 112], [101, 37], [30, 45], [70, 97], [99, 13], [97, 11], [0, 1]], ![[0, 1], [0, 76], [11, 68], [19, 16], [91, 100], [12, 102], [95, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [29, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [87, 18, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-466997, -67177, 52817]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22829, -8073, 52817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-32, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-32, 1, 0]] 
 ![![113, 0, 0], ![81, 1, 0], ![69, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-32, 1, 0], ![0, -31, 2], ![-754, 117, -32]]]
  hmulB := by decide  
  f := ![![![2273, -71, 0], ![8023, 0, 0]], ![![1601, -50, 0], ![5651, 0, 0]], ![![1397, -28, -1], ![4931, 57, 0]]]
  g := ![![![1, 0, 0], ![-81, 113, 0], ![-69, 0, 113]], ![![-1, 1, 0], ![21, -31, 2], ![-71, 117, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-73, 16, 1]] ![![113, 0, 0], ![-32, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-3616, 113, 0]], ![![-8249, 1808, 113], ![1582, -452, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-32, 1, 0]]], ![![![-73, 16, 1]], ![![14, -4, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-103, -21, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-103, -21, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![24, 106, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-103, -21, 1], ![-754, -7, -42], ![16211, -2834, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -106, 127]], ![![-1, -1, 1], ![2, 35, -42], ![125, -34, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [22, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 126], [0, 1]]
 g := ![![[67, 52], [111, 107], [124, 104], [72, 8], [51, 34], [50, 1]], ![[0, 75], [0, 20], [117, 23], [91, 119], [100, 93], [100, 126]]]
 h' := ![![[50, 126], [98, 59], [66, 19], [67, 55], [21, 95], [43, 65], [0, 1]], ![[0, 1], [0, 68], [0, 108], [23, 72], [72, 32], [118, 62], [50, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [77, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [22, 77, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2693, 245, 200]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-59, -165, 200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![42, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![42, 1, 0]] 
 ![![127, 0, 0], ![42, 1, 0], ![113, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![42, 1, 0], ![0, 43, 2], ![-754, 117, 42]]]
  hmulB := by decide  
  f := ![![![3529, 84, 0], ![-10668, 0, 0]], ![![1134, 27, 0], ![-3428, 0, 0]], ![![3179, 54, -1], ![-9610, 64, 0]]]
  g := ![![![1, 0, 0], ![-42, 127, 0], ![-113, 0, 127]], ![![0, 1, 0], ![-16, 43, 2], ![-82, 117, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-103, -21, 1]] ![![127, 0, 0], ![42, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![5334, 127, 0]], ![![-13081, -2667, 127], ![-5080, -889, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![42, 1, 0]]], ![![![-103, -21, 1]], ![![-40, -7, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [44, 103, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 2, 96], [54, 128, 35], [0, 1]]
 g := ![![[49, 23, 7], [70, 17, 75], [130, 45], [79, 1], [33, 35], [125, 1], []], ![[114, 25, 70, 93], [44, 76, 96, 118], [66, 7], [90, 125], [76, 5], [102, 9], [108, 46]], ![[56, 84, 36, 15], [9, 1, 92, 121], [83, 61], [14, 27], [48, 102], [80, 4], [38, 46]]]
 h' := ![![[71, 2, 96], [64, 113, 111], [92, 46, 72], [110, 1, 69], [124, 108, 1], [2, 50, 64], [0, 0, 1], [0, 1]], ![[54, 128, 35], [80, 91, 35], [62, 54, 8], [79, 42, 20], [90, 59, 16], [40, 8, 23], [27, 105, 128], [71, 2, 96]], ![[0, 1], [19, 58, 116], [51, 31, 51], [64, 88, 42], [126, 95, 114], [50, 73, 44], [65, 26, 2], [54, 128, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 124], []]
 b := ![[], [3, 45, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [44, 103, 6, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21076983, -8062002, 1638417]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![160893, -61542, 12507]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [37, 15, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 29, 44], [112, 107, 93], [0, 1]]
 g := ![![[4, 133, 19], [33, 99], [8, 7], [76, 76, 76], [5, 112], [101, 1], []], ![[98, 119, 32, 130], [26, 56], [73, 109], [101, 133, 92, 34], [25, 25], [86, 78], [123, 18]], ![[118, 72, 0, 101], [20, 2], [86, 39], [71, 80, 22, 56], [85, 69], [22, 19], [74, 18]]]
 h' := ![![[126, 29, 44], [30, 7, 29], [93, 85, 109], [65, 12, 125], [26, 23, 79], [99, 92, 48], [0, 0, 1], [0, 1]], ![[112, 107, 93], [126, 124, 123], [35, 80, 59], [74, 50, 66], [112, 3, 12], [30, 24, 5], [91, 2, 107], [126, 29, 44]], ![[0, 1], [91, 6, 122], [3, 109, 106], [50, 75, 83], [75, 111, 46], [84, 21, 84], [79, 135, 29], [112, 107, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 70], []]
 b := ![[], [85, 43, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [37, 15, 36, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3595291, 7744336, -2476138]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26243, 56528, -18074]
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



lemma PB274I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB274I2 : PrimesBelowBoundCertificateInterval O 79 137 274 where
  m := 11
  g := ![1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB274I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
      exact NI109N1
      exact NI109N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N1, I101N1, I103N0, I103N1, I103N2, I107N1, I109N0, I109N1, I109N2, I113N1, I127N1]
  Il := ![[], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [I109N0, I109N1, I109N2], [I113N1], [I127N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
