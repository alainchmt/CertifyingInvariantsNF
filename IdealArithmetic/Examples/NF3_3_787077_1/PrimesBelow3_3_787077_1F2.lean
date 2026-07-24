
import IdealArithmetic.Examples.NF3_3_787077_1.RI3_3_787077_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-811, 2, 28]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-811, 2, 28]] 
 ![![83, 0, 0], ![0, 83, 0], ![57, 6, 1]] where
  M :=![![![-811, 2, 28], ![1768, 7, -68], ![-994, -26, 51]]]
  hmulB := by decide  
  f := ![![![-17, -10, -4]], ![![-272, -163, -68]], ![![-37, -22, -9]]]
  g := ![![![-29, -2, 28], ![68, 5, -68], ![-47, -4, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [20, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 82], [0, 1]]
 g := ![![[37, 3], [46, 10], [31], [65], [63, 49], [1]], ![[58, 80], [33, 73], [31], [65], [74, 34], [1]]]
 h' := ![![[7, 82], [76, 70], [60, 33], [4, 60], [68, 27], [63, 7], [0, 1]], ![[0, 1], [68, 13], [42, 50], [9, 23], [8, 56], [29, 76], [7, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [56, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [20, 76, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1651, 2773, 3464]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2359, -217, 3464]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 10, 4]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![17, 10, 4]] 
 ![![83, 0, 0], ![38, 1, 0], ![13, 0, 1]] where
  M :=![![![17, 10, 4], ![272, 163, 68], ![470, 278, 111]]]
  hmulB := by decide  
  f := ![![![811, -2, -28]], ![![350, -1, -12]], ![![139, 0, -5]]]
  g := ![![![-5, 10, 4], ![-82, 163, 68], ![-139, 278, 111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-811, 2, 28]] ![![17, 10, 4]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [42, 6, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 71, 82], [73, 17, 7], [0, 1]]
 g := ![![[29, 51, 8], [80, 50], [6, 2], [37, 31, 40], [49, 12, 1], []], ![[18, 76, 54, 28], [], [55, 32], [85, 64, 4, 59], [47, 34, 45, 24], [39, 49]], ![[57, 21, 21, 43], [18, 50], [32, 50], [73, 36, 31, 58], [33, 12, 77, 43], [25, 49]]]
 h' := ![![[28, 71, 82], [47, 4, 50], [5, 27, 53], [48, 21, 25], [78, 3, 29], [0, 0, 1], [0, 1]], ![[73, 17, 7], [1, 23, 21], [88, 33], [23, 70, 11], [49, 10, 27], [36, 82, 17], [28, 71, 82]], ![[0, 1], [66, 62, 18], [33, 29, 36], [65, 87, 53], [55, 76, 33], [7, 7, 71], [73, 17, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 62], []]
 b := ![[], [8, 23, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [42, 6, 77, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-185209, 358759, 852175]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2081, 4031, 9575]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1752, -1052, -431]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-1752, -1052, -431]] 
 ![![97, 0, 0], ![0, 97, 0], ![43, 38, 1]] where
  M :=![![![-1752, -1052, -431], ![-29257, -17407, -7123], ![-49036, -29215, -11957]]]
  hmulB := by decide  
  f := ![![![-382, -133, 93]], ![![5593, 1916, -1343]], ![![1897, 649, -455]]]
  g := ![![![173, 158, -431], ![2856, 2611, -7123], ![4795, 4383, -11957]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [50, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 96], [0, 1]]
 g := ![![[48, 33], [96], [16], [16], [49], [25, 1]], ![[0, 64], [96], [16], [16], [49], [50, 96]]]
 h' := ![![[25, 96], [62, 79], [20, 22], [74, 4], [96, 4], [11, 90], [0, 1]], ![[0, 1], [0, 18], [85, 75], [77, 93], [2, 93], [30, 7], [25, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [40, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [50, 72, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2901477, 4594421, 6192072]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2715027, -2378395, 6192072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-382, -133, 93]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-382, -133, 93]] 
 ![![97, 0, 0], ![87, 1, 0], ![40, 0, 1]] where
  M :=![![![-382, -133, 93], ![5593, 1916, -1343], ![-12099, -4136, 2900]]]
  hmulB := by decide  
  f := ![![![-1752, -1052, -431]], ![![-1873, -1123, -460]], ![![-1228, -735, -301]]]
  g := ![![![77, -133, 93], ![-1107, 1916, -1343], ![2389, -4136, 2900]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-1752, -1052, -431]] ![![-382, -133, 93]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4586, 17, 155]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-4586, 17, 155]] 
 ![![101, 0, 0], ![49, 1, 0], ![10, 0, 1]] where
  M :=![![![-4586, 17, 155], ![9799, -40, -329], ![-5129, 28, 168]]]
  hmulB := by decide  
  f := ![![![2492, 1484, 607]], ![![1617, 963, 394]], ![![932, 555, 227]]]
  g := ![![![-69, 17, 155], ![149, -40, -329], ![-81, 28, 168]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5080, -20, -171]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![5080, -20, -171]] 
 ![![101, 0, 0], ![55, 1, 0], ![56, 0, 1]] where
  M :=![![![5080, -20, -171], ![-10813, 61, 353], ![5580, -67, -161]]]
  hmulB := by decide  
  f := ![![![-13830, -8237, -3371]], ![![-9797, -5835, -2388]], ![![-11471, -6832, -2796]]]
  g := ![![![156, -20, -171], ![-336, 61, 353], ![181, -67, -161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7564, -38, 295]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-7564, -38, 295]] 
 ![![101, 0, 0], ![98, 1, 0], ![76, 0, 1]] where
  M :=![![![-7564, -38, 295], ![18509, 877, -1189], ![-14194, -1987, 1695]]]
  hmulB := by decide  
  f := ![![![876028, 521755, 213533]], ![![993533, 591740, 242175]], ![![900073, 536076, 219394]]]
  g := ![![![-260, -38, 295], ![227, 877, -1189], ![512, -1987, 1695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-4586, 17, 155]] ![![5080, -20, -171]]
  ![![-22615801, 82372, 765252]] where
 M := ![![![-22615801, 82372, 765252]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-22615801, 82372, 765252]] ![![-7564, -38, 295]]
  ![![101, 0, 0]] where
 M := ![![![161728555224, -588915042, -5472499463]]]
 hmul := by decide  
 g := ![![![![1601272824, -5830842, -54183163]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![64, 23, -13]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![64, 23, -13]] 
 ![![103, 0, 0], ![0, 103, 0], ![3, 22, 1]] where
  M :=![![![64, 23, -13], ![-773, -244, 223], ![1969, 706, -408]]]
  hmulB := by decide  
  f := ![![![562, -2, -19]], ![![-1201, 5, 41]], ![![-234, 1, 8]]]
  g := ![![![1, 3, -13], ![-14, -50, 223], ![31, 94, -408]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [90, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 102], [0, 1]]
 g := ![![[40, 79], [93, 13], [37, 1], [36], [2], [5, 1]], ![[23, 24], [55, 90], [42, 102], [36], [2], [10, 102]]]
 h' := ![![[5, 102], [76, 39], [69, 42], [16, 1], [28, 6], [65, 38], [0, 1]], ![[0, 1], [65, 64], [73, 61], [21, 102], [58, 97], [49, 65], [5, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [83, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [90, 98, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-371, 2189, 3859]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-116, -803, 3859]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-562, 2, 19]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-562, 2, 19]] 
 ![![103, 0, 0], ![33, 1, 0], ![32, 0, 1]] where
  M :=![![![-562, 2, 19], ![1201, -5, -41], ![-634, 1, 21]]]
  hmulB := by decide  
  f := ![![![-64, -23, 13]], ![![-13, -5, 2]], ![![-39, -14, 8]]]
  g := ![![![-12, 2, 19], ![26, -5, -41], ![-13, 1, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![64, 23, -13]] ![![-562, 2, 19]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [73, 42, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 65, 24], [50, 41, 83], [0, 1]]
 g := ![![[18, 12, 41], [103, 97, 13], [32, 47], [16, 41, 27], [7, 79], [1]], ![[3, 18, 37, 22], [98, 82, 46, 55], [32, 35], [95, 1, 106, 20], [54, 34], [6, 17, 69, 21]], ![[92, 8, 13, 12], [21, 94, 57, 99], [5, 13], [29, 33, 34, 39], [96, 83], [82, 74, 22, 86]]]
 h' := ![![[77, 65, 24], [78, 106, 83], [99, 37, 86], [9, 89, 49], [3, 71, 53], [34, 65, 20], [0, 1]], ![[50, 41, 83], [4, 53, 62], [75, 74, 27], [48, 96, 79], [100, 12, 25], [61, 25, 26], [77, 65, 24]], ![[0, 1], [38, 55, 69], [5, 103, 101], [7, 29, 86], [98, 24, 29], [30, 17, 61], [50, 41, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 67], []]
 b := ![[], [24, 83, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [73, 42, 87, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1537055, -1366176, -1230072]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14365, -12768, -11496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-563480, -335604, -137349]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-563480, -335604, -137349]] 
 ![![109, 0, 0], ![24, 1, 0], ![1, 0, 1]] where
  M :=![![![-563480, -335604, -137349], ![-9324195, -5553413, -2272785], ![-15649092, -9320469, -3814487]]]
  hmulB := by decide  
  f := ![![![-442034, 1533, 15003]], ![![-88629, 316, 3003]], ![![-8675, 9, 307]]]
  g := ![![![69985, -335604, -137349], ![1158078, -5553413, -2272785], ![1943639, -9320469, -3814487]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2454, -9, -83]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![2454, -9, -83]] 
 ![![109, 0, 0], ![35, 1, 0], ![52, 0, 1]] where
  M :=![![![2454, -9, -83], ![-5247, 20, 177], ![2753, -12, -92]]]
  hmulB := by decide  
  f := ![![![-284, -168, -67]], ![![-133, -79, -32]], ![![-208, -123, -49]]]
  g := ![![![65, -9, -83], ![-139, 20, 177], ![73, -12, -92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 36, -32]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![293, 36, -32]] 
 ![![109, 0, 0], ![50, 1, 0], ![105, 0, 1]] where
  M :=![![![293, 36, -32], ![-1944, -527, 384], ![3548, 1140, -807]]]
  hmulB := by decide  
  f := ![![![-12471, -7428, -3040]], ![![-7614, -4535, -1856]], ![![-15191, -9048, -3703]]]
  g := ![![![17, 36, -32], ![-146, -527, 384], ![287, 1140, -807]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-563480, -335604, -137349]] ![![2454, -9, -83]]
  ![![12471, 7428, 3040]] where
 M := ![![![12471, 7428, 3040]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![12471, 7428, 3040]] ![![293, 36, -32]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58, -35, -15]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-58, -35, -15]] 
 ![![113, 0, 0], ![12, 1, 0], ![6, 0, 1]] where
  M :=![![![-58, -35, -15], ![-1015, -598, -235], ![-1605, -970, -418]]]
  hmulB := by decide  
  f := ![![![22014, -80, -745]], ![![1921, -7, -65]], ![![1388, -5, -47]]]
  g := ![![![4, -35, -15], ![67, -598, -235], ![111, -970, -418]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-546, -325, -133]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-546, -325, -133]] 
 ![![113, 0, 0], ![13, 1, 0], ![59, 0, 1]] where
  M :=![![![-546, -325, -133], ![-9029, -5378, -2201], ![-15155, -9026, -3694]]]
  hmulB := by decide  
  f := ![![![-106, 92, -51]], ![![-39, -1, 2]], ![![14, 73, -44]]]
  g := ![![![102, -325, -133], ![1688, -5378, -2201], ![2833, -9026, -3694]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70168, 251, 2377]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-70168, 251, 2377]] 
 ![![113, 0, 0], ![88, 1, 0], ![101, 0, 1]] where
  M :=![![![-70168, 251, 2377], ![150253, -482, -5123], ![-79267, 148, 2766]]]
  hmulB := by decide  
  f := ![![![575008, 342470, 140159]], ![![531997, 316853, 129675]], ![![655266, 390271, 159722]]]
  g := ![![![-2941, 251, 2377], ![6284, -482, -5123], ![-3289, 148, 2766]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-58, -35, -15]] ![![-546, -325, -133]]
  ![![575008, 342470, 140159]] where
 M := ![![![575008, 342470, 140159]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![575008, 342470, 140159]] ![![-70168, 251, 2377]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -48, -20]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-79, -48, -20]] 
 ![![127, 0, 0], ![0, 127, 0], ![23, 104, 1]] where
  M :=![![![-79, -48, -20], ![-1356, -803, -324], ![-2224, -1332, -555]]]
  hmulB := by decide  
  f := ![![![111, 0, -4]], ![![-252, -5, 12]], ![![-185, -4, 9]]]
  g := ![![![3, 16, -20], ![48, 259, -324], ![83, 444, -555]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [119, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 126], [0, 1]]
 g := ![![[16, 38], [82, 21], [93, 26], [98, 18], [98, 81], [1, 1]], ![[54, 89], [103, 106], [119, 101], [116, 109], [52, 46], [2, 126]]]
 h' := ![![[1, 126], [21, 66], [109, 23], [22, 91], [22, 48], [8, 9], [0, 1]], ![[0, 1], [87, 61], [5, 104], [113, 36], [70, 79], [17, 118], [1, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [77, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [119, 126, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![180682, 220765, 263827]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46357, -214309, 263827]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![111, 0, -4]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![111, 0, -4]] 
 ![![127, 0, 0], ![60, 1, 0], ![4, 0, 1]] where
  M :=![![![111, 0, -4], ![-252, -5, 12], ![160, 12, -13]]]
  hmulB := by decide  
  f := ![![![-79, -48, -20]], ![![-48, -29, -12]], ![![-20, -12, -5]]]
  g := ![![![1, 0, -4], ![0, -5, 12], ![-4, 12, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-79, -48, -20]] ![![111, 0, -4]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2654, -902, 633]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-2654, -902, 633]] 
 ![![131, 0, 0], ![0, 131, 0], ![73, 41, 1]] where
  M :=![![![-2654, -902, 633], ![38075, 12997, -9115], ![-82146, -28057, 19675]]]
  hmulB := by decide  
  f := ![![![-180, -101, -41]], ![![-2785, -1672, -685]], ![![-1008, -601, -246]]]
  g := ![![![-373, -205, 633], ![5370, 2952, -9115], ![-11591, -6372, 19675]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [109, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 130], [0, 1]]
 g := ![![[7, 125], [112, 35], [58], [5], [84], [5], [1]], ![[0, 6], [0, 96], [58], [5], [84], [5], [1]]]
 h' := ![![[23, 130], [106, 115], [31, 67], [14, 53], [67, 23], [70, 79], [22, 23], [0, 1]], ![[0, 1], [0, 16], [0, 64], [54, 78], [72, 108], [53, 52], [27, 108], [23, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [58, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [109, 108, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-358, -27, -39]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 12, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![180, 101, 41]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![180, 101, 41]] 
 ![![131, 0, 0], ![68, 1, 0], ![19, 0, 1]] where
  M :=![![![180, 101, 41], ![2785, 1672, 685], ![4723, 2806, 1148]]]
  hmulB := by decide  
  f := ![![![2654, 902, -633]], ![![1087, 369, -259]], ![![1012, 345, -242]]]
  g := ![![![-57, 101, 41], ![-946, 1672, 685], ![-1587, 2806, 1148]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-2654, -902, 633]] ![![180, 101, 41]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2094, -8, -71]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![2094, -8, -71]] 
 ![![137, 0, 0], ![0, 137, 0], ![94, 58, 1]] where
  M :=![![![2094, -8, -71], ![-4489, 11, 149], ![2336, -19, -83]]]
  hmulB := by decide  
  f := ![![![-14, -5, 3]], ![![179, 58, -49]], ![![63, 20, -18]]]
  g := ![![![64, 30, -71], ![-135, -63, 149], ![74, 35, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [29, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 136], [0, 1]]
 g := ![![[80, 1], [129], [136], [59, 15], [105], [81], [1]], ![[89, 136], [129], [136], [57, 122], [105], [81], [1]]]
 h' := ![![[9, 136], [104, 1], [134, 102], [70, 37], [107, 120], [136, 70], [108, 9], [0, 1]], ![[0, 1], [113, 136], [93, 35], [129, 100], [91, 17], [81, 67], [52, 128], [9, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [125, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [29, 128, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4982, 9376, 14712]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10058, -6160, 14712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 5, -3]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![14, 5, -3]] 
 ![![137, 0, 0], ![87, 1, 0], ![49, 0, 1]] where
  M :=![![![14, 5, -3], ![-179, -58, 49], ![435, 154, -94]]]
  hmulB := by decide  
  f := ![![![-2094, 8, 71]], ![![-1297, 5, 44]], ![![-766, 3, 26]]]
  g := ![![![-2, 5, -3], ![18, -58, 49], ![-61, 154, -94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![2094, -8, -71]] ![![14, 5, -3]]
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


lemma PB198I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB198I2 : PrimesBelowBoundCertificateInterval O 79 137 198 where
  m := 11
  g := ![2, 1, 2, 3, 2, 1, 3, 3, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB198I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![113, 113, 113]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
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
  β := ![I83N1, I97N1, I101N0, I101N1, I101N2, I103N1, I109N0, I109N1, I109N2, I113N0, I113N1, I113N2, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [], [I109N0, I109N1, I109N2], [I113N0, I113N1, I113N2], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
