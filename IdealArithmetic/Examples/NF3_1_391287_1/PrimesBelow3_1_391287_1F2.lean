
import IdealArithmetic.Examples.NF3_1_391287_1.RI3_1_391287_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2975, 949, -193]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2975, 949, -193]] 
 ![![83, 0, 0], ![0, 83, 0], ![61, 54, 1]] where
  M :=![![![-2975, 949, -193], ![-24109, -3345, 2654], ![98247, -10374, -1640]]]
  hmulB := by decide  
  f := ![![![397812, 42874, 22567]], ![![2665166, 287237, 151189]], ![![2110341, 227441, 119715]]]
  g := ![![![106, 137, -193], ![-2241, -1767, 2654], ![2389, 942, -1640]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [64, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 82], [0, 1]]
 g := ![![[10, 48], [22, 44], [27], [75], [45, 78], [1]], ![[0, 35], [82, 39], [27], [75], [8, 5], [1]]]
 h' := ![![[24, 82], [3, 31], [59, 25], [58, 44], [25, 18], [19, 24], [0, 1]], ![[0, 1], [0, 52], [78, 58], [35, 39], [42, 65], [14, 59], [24, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [81, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [64, 59, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![853, 351, -201]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![158, 135, -201]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397812, 42874, 22567]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![397812, 42874, 22567]] 
 ![![83, 0, 0], ![3, 1, 0], ![53, 0, 1]] where
  M :=![![![397812, 42874, 22567], ![2665166, 287237, 151189], ![6972807, 751491, 395552]]]
  hmulB := by decide  
  f := ![![![-2975, 949, -193]], ![![-398, -6, 25]], ![![-716, 481, -143]]]
  g := ![![![-11167, 42874, 22567], ![-74814, 287237, 151189], ![-195734, 751491, 395552]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2975, 949, -193]] ![![397812, 42874, 22567]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1288356, 68021, 47504]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-1288356, 68021, 47504]] 
 ![![89, 0, 0], ![0, 89, 0], ![32, 11, 1]] where
  M :=![![![-1288356, 68021, 47504], ![5632459, -1498889, 251567], ![12010344, 1648593, -1315343]]]
  hmulB := by decide  
  f := ![![![17492377064, 1885232675, 992304067]], ![![117191255365, 12630232188, 6648002092]], ![![24218701410, 2610159104, 1373873649]]]
  g := ![![![-31556, -5107, 47504], ![-27165, -47934, 251567], ![607880, 181094, -1315343]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [34, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 88], [0, 1]]
 g := ![![[6, 55], [67], [45], [17, 22], [34, 53], [1]], ![[0, 34], [67], [45], [68, 67], [80, 36], [1]]]
 h' := ![![[63, 88], [44, 77], [50, 44], [45, 57], [1, 72], [55, 63], [0, 1]], ![[0, 1], [0, 12], [63, 45], [76, 32], [87, 17], [19, 26], [63, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [55, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [34, 26, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4476, 2611, 27]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, 26, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17492377064, 1885232675, 992304067]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![17492377064, 1885232675, 992304067]] 
 ![![89, 0, 0], ![55, 1, 0], ![48, 0, 1]] where
  M :=![![![17492377064, 1885232675, 992304067], ![117191255365, 12630232188, 6648002092], ![306604550427, 33044160588, 17393001605]]]
  hmulB := by decide  
  f := ![![![-1288356, 68021, 47504]], ![![-732889, 25194, 32183]], ![![-559896, 55209, 10841]]]
  g := ![![![-1503663093, 1885232675, 992304067], ![-10073883319, 12630232188, 6648002092], ![-26356048977, 33044160588, 17393001605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-1288356, 68021, 47504]] ![![17492377064, 1885232675, 992304067]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [71, 96, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 10, 25], [86, 86, 72], [0, 1]]
 g := ![![[47, 83, 12], [85, 75], [86, 53], [18, 75], [30, 75], [1]], ![[28, 7, 84, 8], [3, 85], [51, 4], [31, 16], [25, 49], [85, 75, 17, 8]], ![[39, 10, 0, 9], [87, 4], [76, 70], [48, 6], [41, 48], [3, 96, 48, 89]]]
 h' := ![![[58, 10, 25], [6, 68, 20], [67, 15, 47], [81, 18, 76], [1, 92, 50], [26, 1, 47], [0, 1]], ![[86, 86, 72], [94, 48, 25], [4, 81, 52], [91, 87, 2], [62, 19, 4], [24, 38, 90], [58, 10, 25]], ![[0, 1], [95, 78, 52], [89, 1, 95], [76, 89, 19], [63, 83, 43], [8, 58, 57], [86, 86, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 61], []]
 b := ![[], [86, 66, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [71, 96, 50, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1348891021, 69166626, -34693505]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13906093, 713058, -357665]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [86, 31, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 59, 44], [19, 41, 57], [0, 1]]
 g := ![![[2, 73, 77], [0, 78], [43, 30, 54], [62, 78], [77, 78], [1]], ![[69, 8, 48, 8], [67, 100], [90, 62, 6, 74], [63, 17], [35, 6], [71, 47, 69, 41]], ![[42, 41, 17, 50], [72, 6], [3, 78, 21, 3], [93, 25], [16, 68], [42, 1, 82, 60]]]
 h' := ![![[30, 59, 44], [6, 71, 28], [39, 39, 52], [66, 6, 85], [67, 75, 49], [15, 70, 49], [0, 1]], ![[19, 41, 57], [11, 35, 30], [4, 26, 10], [3, 44, 12], [88, 34, 57], [88, 42, 39], [30, 59, 44]], ![[0, 1], [90, 96, 43], [90, 36, 39], [66, 51, 4], [61, 93, 96], [15, 90, 13], [19, 41, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 50], []]
 b := ![[], [1, 59, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [86, 31, 52, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2704174, 254520, 16160]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26774, 2520, 160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2961, -319, -168]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-2961, -319, -168]] 
 ![![103, 0, 0], ![0, 103, 0], ![82, 16, 1]] where
  M :=![![![-2961, -319, -168], ![-19841, -2138, -1125], ![-51888, -5595, -2944]]]
  hmulB := by decide  
  f := ![![![1, -8, 3]], ![![368, 0, -21]], ![![51, -5, -1]]]
  g := ![![![105, 23, -168], ![703, 154, -1125], ![1840, 403, -2944]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [22, 4, 1] where
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
 g := ![![[47, 26], [49, 41], [56, 59], [60], [36], [99, 1]], ![[46, 77], [91, 62], [26, 44], [60], [36], [95, 102]]]
 h' := ![![[99, 102], [55, 51], [4, 91], [45, 33], [51, 36], [88, 97], [0, 1]], ![[0, 1], [57, 52], [52, 12], [16, 70], [10, 67], [9, 6], [99, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [63, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [22, 4, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![756, 351, -36]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 9, -36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 8, -3]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-1, 8, -3]] 
 ![![103, 0, 0], ![54, 1, 0], ![7, 0, 1]] where
  M :=![![![-1, 8, -3], ![-368, 0, 21], ![717, -141, 13]]]
  hmulB := by decide  
  f := ![![![2961, 319, 168]], ![![1745, 188, 99]], ![![705, 76, 40]]]
  g := ![![![-4, 8, -3], ![-5, 0, 21], ![80, -141, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-2961, -319, -168]] ![![-1, 8, -3]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90011004607, 9700893502, 5106126264]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![90011004607, 9700893502, 5106126264]] 
 ![![107, 0, 0], ![13, 1, 0], ![19, 0, 1]] where
  M :=![![![90011004607, 9700893502, 5106126264], ![603034258178, 64991732313, 34208806770], ![1577703447624, 170036243790, 89499645581]]]
  hmulB := by decide  
  f := ![![![2900553, -14102, -160092]], ![![172993, 30015, -21342]], ![![378045, -60460, 1541]]]
  g := ![![![-1244084205, 9700893502, 5106126264], ![-8334818603, 64991732313, 34208806770], ![-21806177455, 170036243790, 89499645581]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43537443268207, 4692227381955, 2469783372709]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![43537443268207, 4692227381955, 2469783372709]] 
 ![![107, 0, 0], ![16, 1, 0], ![98, 0, 1]] where
  M :=![![![43537443268207, 4692227381955, 2469783372709], ![291681777343125, 31435865768125, 16546465518574], ![763119739024029, 82244869389786, 43290103904744]]]
  hmulB := by decide  
  f := ![![![-37400164, 11255754, -2168455]], ![![-8129654, 1289173, -28939]], ![![-23272621, 9203055, -2189870]]]
  g := ![![![-2556794068865, 4692227381955, 2469783372709], ![-17129399025861, 31435865768125, 16546465518574], ![-44815218260537, 82244869389786, 43290103904744]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![268674355177205, 28956251712470, 15241305076234]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![268674355177205, 28956251712470, 15241305076234]] 
 ![![107, 0, 0], ![78, 1, 0], ![102, 0, 1]] where
  M :=![![![268674355177205, 28956251712470, 15241305076234], ![1800000357435610, 193994188236033, 102110060213644], ![4709295916671354, 507542142835716, 267147996737207]]]
  hmulB := by decide  
  f := ![![![-164529273, 3102254, 8200958]], ![![-110768884, 464873, 6141892]], ![![-147153624, 5859444, 6155783]]]
  g := ![![![-33126414917489, 28956251712470, 15241305076234], ![-221932452960436, 193994188236033, 102110060213644], ![-580636326090744, 507542142835716, 267147996737207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![90011004607, 9700893502, 5106126264]] ![![43537443268207, 4692227381955, 2469783372709]]
  ![![10645008607078733754501055, 1147260774124427052829939, 603867918888705666572927]] where
 M := ![![![10645008607078733754501055, 1147260774124427052829939, 603867918888705666572927]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![10645008607078733754501055, 1147260774124427052829939, 603867918888705666572927]] ![![268674355177205, 28956251712470, 15241305076234]]
  ![![107, 0, 0]] where
 M := ![![![7768903351489909296190926984024890012223, 837289888821810528342733089004606908569, 440712795271204723714300899720067709475]]]
 hmul := by decide  
 g := ![![![![72606573378410367254120812934812056189, 7825139147867388115352645691631840267, 4118811170758922651535522427290352425]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1415763781, 70862484, 53686778]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-1415763781, 70862484, 53686778]] 
 ![![109, 0, 0], ![0, 109, 0], ![18, 95, 1]] where
  M :=![![![-1415763781, 70862484, 53686778], ![6371550876, -1647686599, 266274230], ![12852127098, 1881196890, -1452274853]]]
  hmulB := by decide  
  f := ![![![17357610642106883, 1870708287541608, 984659064376838]], ![![116288379437678952, 12532925161434761, 6596783927001662]], ![![107009866209696708, 11532937781285533, 6070434284631521]]]
  g := ![![![-21854365, -46141114, 53686778], ![14482704, -247190261, 266274230], ![357734628, 1283002825, -1452274853]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [7, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 108], [0, 1]]
 g := ![![[39, 78], [84], [7, 89], [53, 84], [66], [54, 1]], ![[0, 31], [84], [17, 20], [11, 25], [66], [108, 108]]]
 h' := ![![[54, 108], [69, 29], [60, 56], [65, 31], [68, 56], [58, 75], [0, 1]], ![[0, 1], [0, 80], [32, 53], [104, 78], [40, 53], [75, 34], [54, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [7, 55, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18205, 822, 1296]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -1122, 1296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17357610642106883, -1870708287541608, -984659064376838]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-17357610642106883, -1870708287541608, -984659064376838]] 
 ![![109, 0, 0], ![41, 1, 0], ![107, 0, 1]] where
  M :=![![![-17357610642106883, -1870708287541608, -984659064376838], ![-116288379437678952, -12532925161434761, -6596783927001662], ![-304242378719516838, -32789578648071858, -17259000800894815]]]
  hmulB := by decide  
  f := ![![![1415763781, -70862484, -53686778]], ![![474080405, -11538305, -22636992]], ![![1271877041, -86820942, -39378077]]]
  g := ![![![1511008706746979, -1870708287541608, -984659064376838], ![10123095709819487, -12532925161434761, -6596783927001662], ![26484802124286005, -32789578648071858, -17259000800894815]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-1415763781, 70862484, 53686778]] ![![-17357610642106883, -1870708287541608, -984659064376838]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [87, 88, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 103, 44], [31, 9, 69], [0, 1]]
 g := ![![[104, 48, 91], [0, 91], [101, 112], [90, 88], [78, 96, 77], [1]], ![[27, 61, 51, 51], [12, 85], [102, 64], [33, 28], [55, 98, 31, 102], [99, 89, 40, 95]], ![[7, 86, 40, 87], [72, 9], [111, 77], [10, 111], [103, 72, 96, 88], [37, 46, 28, 18]]]
 h' := ![![[105, 103, 44], [53, 70, 54], [36, 56, 59], [3, 26, 98], [107, 37, 38], [26, 25, 23], [0, 1]], ![[31, 9, 69], [95, 5, 63], [3, 91, 57], [17, 15, 105], [17, 101, 49], [28, 44, 64], [105, 103, 44]], ![[0, 1], [4, 38, 109], [36, 79, 110], [38, 72, 23], [111, 88, 26], [17, 44, 26], [31, 9, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 2], []]
 b := ![[], [103, 95, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [87, 88, 90, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-581046, 64636, 13108]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5142, 572, 116]
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


def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 3, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-20, 3, 0]] 
 ![![127, 0, 0], ![78, 1, 0], ![72, 0, 1]] where
  M :=![![![-20, 3, 0], ![-3, -23, 9], ![360, -9, -17]]]
  hmulB := by decide  
  f := ![![![472, 51, 27]], ![![315, 34, 18]], ![![333, 36, 19]]]
  g := ![![![-2, 3, 0], ![9, -23, 9], ![18, -9, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-709918677, 668205391, -214901127]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-709918677, 668205391, -214901127]] 
 ![![127, 0, 0], ![88, 1, 0], ![30, 0, 1]] where
  M :=![![![-709918677, 668205391, -214901127], ![-26456340631, -733420687, 1789715046], ![62777655633, -10385760126, 388088968]]]
  hmulB := by decide  
  f := ![![![18302918684121374780, 1972588415223835514, 1038284309889598737]], ![![13647861204521330658, 1470891794322254081, 774213140360990505]], ![![6849599995681566951, 738212403911322123, 388562738395700590]]]
  g := ![![![-417834325, 668205391, -214901127], ![-122887965, -733420687, 1789715046], ![7599069903, -10385760126, 388088968]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-20, 3, 0]] ![![-709918677, 668205391, -214901127]]
  ![![-65170648353, -15564369881, 9667167678]] where
 M := ![![![-65170648353, -15564369881, 9667167678]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-65170648353, -15564369881, 9667167678]] ![![-709918677, 668205391, -214901127]]
  ![![127, 0, 0]] where
 M := ![![![1064924255172559154066, -132533032315123150204, -10098820051516559391]]]
 hmul := by decide  
 g := ![![![![8385230355689442158, -1043567183583646852, -79518268122177633]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3678421113791924881, 396440097921411450, 208668737130441963]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![3678421113791924881, 396440097921411450, 208668737130441963]] 
 ![![131, 0, 0], ![0, 131, 0], ![67, 93, 1]] where
  M :=![![![3678421113791924881, 396440097921411450, 208668737130441963], ![24643808357731624110, 2655974804479187542, 1397989030894676313], ![64474979458135173003, 6948760454323002207, 3657523737452452405]]]
  hmulB := by decide  
  f := ![![![-807829651, 315934161, -74669016]], ![![-9276216081, -899756764, 873133467]], ![![-6755334146, -506638812, 579053671]]]
  g := ![![![-78644154762959440, -145112614161906039, 208668737130441963], ![-526881348948180831, -972190878387219157, 1397989030894676313], ![-1378466495810527772, -2543518680372176118, 3657523737452452405]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [125, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 130], [0, 1]]
 g := ![![[14, 109], [81, 45], [49], [33], [7], [113], [1]], ![[0, 22], [62, 86], [49], [33], [7], [113], [1]]]
 h' := ![![[84, 130], [93, 41], [33, 69], [1, 7], [117, 66], [59, 20], [6, 84], [0, 1]], ![[0, 1], [0, 90], [65, 62], [65, 124], [28, 65], [36, 111], [119, 47], [84, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [14, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [125, 47, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1510, 1396, 177]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-79, -115, 177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-807829651, 315934161, -74669016]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-807829651, 315934161, -74669016]] 
 ![![131, 0, 0], ![113, 1, 0], ![104, 0, 1]] where
  M :=![![![-807829651, 315934161, -74669016], ![-9276216081, -899756764, 873133467], ![31863909024, -3859894107, -342557458]]]
  hmulB := by decide  
  f := ![![![3678421113791924881, 396440097921411450, 208668737130441963]], ![![3361109879513123173, 362242029538921232, 190668368905607772]], ![![3412448666354926417, 367775043039311397, 193580705336018447]]]
  g := ![![![-219410780, 315934161, -74669016], ![12140593, -899756764, 873133467], ![3844716937, -3859894107, -342557458]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![3678421113791924881, 396440097921411450, 208668737130441963]] ![![-807829651, 315934161, -74669016]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [108, 27, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 12, 40], [58, 124, 97], [0, 1]]
 g := ![![[65, 127, 8], [39, 34], [23, 88], [57, 78, 69], [92, 34], [25, 1], []], ![[20, 21, 64, 79], [67, 7], [46, 74], [74, 128, 64, 46], [34, 72], [128, 32], [134, 93]], ![[109, 94, 4, 51], [105, 8], [119, 118], [57, 21, 101, 48], [30, 1], [50, 7], [77, 93]]]
 h' := ![![[104, 12, 40], [31, 26, 75], [63, 4, 87], [9, 68, 122], [21, 115, 53], [40, 39, 50], [0, 0, 1], [0, 1]], ![[58, 124, 97], [69, 69, 65], [110, 73, 125], [134, 70, 38], [12, 52, 75], [81, 32, 88], [43, 68, 124], [104, 12, 40]], ![[0, 1], [39, 42, 134], [62, 60, 62], [6, 136, 114], [14, 107, 9], [69, 66, 136], [117, 69, 12], [58, 124, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 65], []]
 b := ![[], [125, 76, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [108, 27, 112, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-337842, 133575, -21235]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2466, 975, -155]
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



lemma PB177I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB177I2 : PrimesBelowBoundCertificateInterval O 79 137 177 where
  m := 11
  g := ![2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB177I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
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
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N1, I103N1, I107N0, I107N1, I107N2, I109N1, I127N0, I127N1, I131N1]
  Il := ![[I83N1], [I89N1], [], [], [I103N1], [I107N0, I107N1, I107N2], [I109N1], [], [I127N0, I127N1, I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
