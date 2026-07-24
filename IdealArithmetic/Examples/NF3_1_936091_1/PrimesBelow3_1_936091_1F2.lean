
import IdealArithmetic.Examples.NF3_1_936091_1.RI3_1_936091_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![184495, -45006, 6084]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![184495, -45006, 6084]] 
 ![![83, 0, 0], ![0, 83, 0], ![26, 49, 1]] where
  M :=![![![184495, -45006, 6084], ![-1180296, 287923, -38922], ![7550868, -1841970, 249001]]]
  hmulB := by decide  
  f := ![![![-499, -78, 0]], ![![0, -499, -78]], ![![26, -335, -53]]]
  g := ![![![317, -4134, 6084], ![-2028, 26447, -38922], ![12974, -169193, 249001]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [9, 59, 1] where
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
 g := ![![[25, 37], [36, 40], [59], [64], [29, 78], [1]], ![[0, 46], [0, 43], [59], [64], [75, 5], [1]]]
 h' := ![![[24, 82], [8, 55], [7, 17], [66, 68], [71, 75], [74, 24], [0, 1]], ![[0, 1], [0, 28], [0, 66], [38, 15], [45, 8], [69, 59], [24, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [48, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [9, 59, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-573, -202, -38]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 20, -38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-499, -78, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-499, -78, 0]] 
 ![![83, 0, 0], ![33, 1, 0], ![73, 0, 1]] where
  M :=![![![-499, -78, 0], ![0, -499, -78], ![15132, -1326, -577]]]
  hmulB := by decide  
  f := ![![![184495, -45006, 6084]], ![![59133, -14425, 1950]], ![![253241, -61776, 8351]]]
  g := ![![![25, -78, 0], ![267, -499, -78], ![1217, -1326, -577]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![184495, -45006, 6084]] ![![-499, -78, 0]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [47, 29, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 20, 5], [67, 68, 84], [0, 1]]
 g := ![![[58, 4, 69], [13, 2], [9, 25], [3, 18, 84], [3, 11, 1], []], ![[28, 26, 59, 22], [70, 22], [79, 40], [26, 68, 61, 47], [43, 87, 27, 69], [30, 25]], ![[36, 61, 36, 68], [35, 73], [55, 88], [17, 37, 85, 40], [80, 4, 19, 47], [40, 25]]]
 h' := ![![[33, 20, 5], [33, 44, 43], [56, 34, 64], [37, 80, 84], [37, 19, 23], [0, 0, 1], [0, 1]], ![[67, 68, 84], [53, 54, 29], [36, 26, 72], [10, 63, 60], [45, 81, 57], [35, 76, 68], [33, 20, 5]], ![[0, 1], [2, 80, 17], [32, 29, 42], [6, 35, 34], [85, 78, 9], [28, 13, 20], [67, 68, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 36], []]
 b := ![[], [30, 86, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [47, 29, 78, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1059723, -314348, 19135]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11907, -3532, 215]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![0, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![0, 1, 0]] 
 ![![97, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![0, 1, 0], ![0, 0, 1], ![-194, 17, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![0, 1, 0], ![0, 0, 1], ![-2, 17, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-17, -1, 1]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-17, -1, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![80, 96, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-17, -1, 1], ![-194, 0, 0], ![0, -194, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -96, 97]], ![![-1, -1, 1], ![-2, 0, 0], ![0, -2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [10, 5, 1] where
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
 g := ![![[49, 16], [48], [50], [72], [31], [92, 1]], ![[66, 81], [48], [50], [72], [31], [87, 96]]]
 h' := ![![[92, 96], [93, 93], [66, 40], [88, 27], [56, 84], [50, 15], [0, 1]], ![[0, 1], [16, 4], [60, 57], [50, 70], [24, 13], [72, 82], [92, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [65, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [10, 5, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-566, -1688, 136]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-118, -152, 136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![0, 1, 0]] ![![97, 0, 0], ![-17, -1, 1]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1649, -97, 97]], ![![0, 97, 0], ![-194, 0, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-17, -1, 1]]], ![![![0, 1, 0]], ![![-2, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![18, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![18, 1, 0]] 
 ![![101, 0, 0], ![18, 1, 0], ![80, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![18, 1, 0], ![0, 18, 1], ![-194, 17, 19]]]
  hmulB := by decide  
  f := ![![![955, 53, 0], ![-5353, 0, 0]], ![![162, 9, 0], ![-908, 0, 0]], ![![760, 42, 0], ![-4260, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 101, 0], ![-80, 0, 101]], ![![0, 1, 0], ![-4, 18, 1], ![-20, 17, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![29, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![29, 1, 0]] 
 ![![101, 0, 0], ![29, 1, 0], ![68, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![29, 1, 0], ![0, 29, 1], ![-194, 17, 30]]]
  hmulB := by decide  
  f := ![![![146, 5, 0], ![-505, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![96, 3, 0], ![-332, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 101, 0], ![-68, 0, 101]], ![![0, 1, 0], ![-9, 29, 1], ![-27, 17, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-48, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-48, 1, 0]] 
 ![![101, 0, 0], ![53, 1, 0], ![19, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-48, 1, 0], ![0, -48, 1], ![-194, 17, -47]]]
  hmulB := by decide  
  f := ![![![2881, -60, 0], ![6060, 0, 0]], ![![1489, -31, 0], ![3132, 0, 0]], ![![599, -12, 0], ![1260, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 101, 0], ![-19, 0, 101]], ![![-1, 1, 0], ![25, -48, 1], ![-2, 17, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![18, 1, 0]] ![![101, 0, 0], ![29, 1, 0]]
  ![![101, 0, 0], ![17, 47, 1]] where
 M := ![![![10201, 0, 0], ![2929, 101, 0]], ![![1818, 101, 0], ![522, 47, 1]]]
 hmul := by decide  
 g := ![![![![84, -47, -1], ![101, 0, 0]], ![![12, -46, -1], ![101, 0, 0]]], ![![![1, -46, -1], ![101, 0, 0]], ![![5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![17, 47, 1]] ![![101, 0, 0], ![-48, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4848, 101, 0]], ![![1717, 4747, 101], ![-1010, -2222, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-48, 1, 0]]], ![![![17, 47, 1]], ![![-10, -22, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [67, 92, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 89, 94], [1, 13, 9], [0, 1]]
 g := ![![[19, 3, 82], [77, 14, 60], [56, 63, 55], [98, 52], [35, 60], [1]], ![[15, 83, 53, 69], [35, 47, 73, 65], [70, 70, 17, 87], [75, 52], [53, 26], [33, 89, 79, 95]], ![[75, 42, 30, 98], [9, 12, 42, 28], [25, 37, 88, 29], [], [52, 19], [47, 6, 90, 8]]]
 h' := ![![[66, 89, 94], [94, 94, 59], [59, 7, 67], [78, 53, 63], [84, 41, 19], [36, 11, 67], [0, 1]], ![[1, 13, 9], [3, 21, 24], [43, 97, 87], [35, 24, 33], [61, 87, 84], [78, 41, 51], [66, 89, 94]], ![[0, 1], [94, 91, 20], [64, 102, 52], [83, 26, 7], [86, 78], [45, 51, 88], [1, 13, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 56], []]
 b := ![[], [84, 88, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [67, 92, 36, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40479, 1133, 1133]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-393, 11, 11]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [31, 36, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 100, 18], [28, 6, 89], [0, 1]]
 g := ![![[75, 24, 102], [49, 5, 99], [69, 79], [51, 23, 49], [45, 39], [1]], ![[49, 24, 36, 50], [92, 30, 106, 106], [58, 102], [106, 66, 20, 78], [36, 11], [84, 13, 19, 54]], ![[35, 19, 36, 86], [94, 70, 102, 62], [80, 69], [41, 21, 93, 83], [1, 48], [59, 47, 79, 53]]]
 h' := ![![[29, 100, 18], [86, 59, 67], [42, 61, 45], [24, 55, 20], [101, 45, 100], [76, 71, 57], [0, 1]], ![[28, 6, 89], [76, 63, 73], [69, 54, 84], [72, 19, 40], [91, 100, 19], [64, 98, 15], [29, 100, 18]], ![[0, 1], [71, 92, 74], [81, 99, 85], [97, 33, 47], [18, 69, 95], [7, 45, 35], [28, 6, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 28], []]
 b := ![[], [26, 70, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [31, 36, 50, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2109826, -47401, 39483]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19718, -443, 369]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [12, 95, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 31, 34], [9, 77, 75], [0, 1]]
 g := ![![[40, 1, 102], [45, 49], [64, 66, 105], [41, 92, 28], [72, 26], [1]], ![[40, 3], [102, 63], [44, 22, 46, 25], [101, 52, 31, 81], [92, 104], [75, 101, 83, 64]], ![[94, 43, 67, 20], [64, 27], [21, 103, 47, 106], [24, 100, 77, 43], [83, 26], [18, 13, 46, 45]]]
 h' := ![![[65, 31, 34], [30, 15, 50], [104, 79, 7], [53, 11, 66], [43, 33, 79], [97, 14, 74], [0, 1]], ![[9, 77, 75], [24, 37], [7, 87, 64], [5, 42, 6], [8, 59, 11], [26, 36, 70], [65, 31, 34]], ![[0, 1], [31, 57, 59], [103, 52, 38], [10, 56, 37], [28, 17, 19], [77, 59, 74], [9, 77, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 34], []]
 b := ![[], [47, 100, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [12, 95, 35, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31283, 3597, -1199]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-287, 33, -11]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [103, 92, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 105, 94], [59, 7, 19], [0, 1]]
 g := ![![[69, 2, 81], [82, 8], [6, 36], [82, 105], [8, 84, 69], [1]], ![[72, 82, 81, 37], [93, 87], [3, 104], [1, 81], [81, 70, 0, 19], [67, 6, 78, 34]], ![[1, 68, 21, 27], [16, 62], [54, 52], [78, 41], [22, 104, 102, 33], [106, 43, 82, 79]]]
 h' := ![![[12, 105, 94], [61, 62, 104], [91, 19, 11], [101, 43, 107], [80, 91, 52], [10, 21, 71], [0, 1]], ![[59, 7, 19], [52, 42, 2], [34, 107, 55], [2, 90, 45], [61, 106, 104], [25, 45, 98], [12, 105, 94]], ![[0, 1], [83, 9, 7], [6, 100, 47], [101, 93, 74], [15, 29, 70], [101, 47, 57], [59, 7, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 36], []]
 b := ![[], [45, 14, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [103, 92, 42, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![138425, -76049, 1243]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1225, -673, 11]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [6, 120, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 33, 67], [111, 93, 60], [0, 1]]
 g := ![![[71], [10, 60, 25], [56, 65, 1], [99, 66, 26], [102, 3, 38], [1]], ![[26, 39, 61, 12], [53, 97, 47, 77], [86, 1, 81, 56], [112, 34, 11, 111], [107, 77, 34, 95], [83, 10, 42, 27]], ![[81, 42, 92, 115], [79, 1, 16, 117], [63, 106, 45, 32], [99, 49, 82, 100], [34, 2, 19, 37], [58, 112, 80, 100]]]
 h' := ![![[82, 33, 67], [67, 84], [45, 32, 122], [41, 64, 126], [23, 97, 91], [121, 7, 66], [0, 1]], ![[111, 93, 60], [97, 105, 40], [107, 84, 28], [103, 38, 4], [97, 38, 103], [71, 82, 3], [82, 33, 67]], ![[0, 1], [120, 65, 87], [57, 11, 104], [87, 25, 124], [34, 119, 60], [1, 38, 58], [111, 93, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 18], []]
 b := ![[], [86, 6, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [6, 120, 61, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1211834, -282956, 38100]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9542, -2228, 300]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [107, 45, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 114, 21], [21, 16, 110], [0, 1]]
 g := ![![[24, 125, 89], [89, 27, 5], [102, 27], [40, 74], [32, 102], [73, 1], []], ![[71, 80, 22, 100], [90, 125, 79, 59], [94, 34], [48, 5], [59, 11], [63, 125], [39, 48]], ![[4, 71, 125, 26], [127, 70, 44, 124], [85, 59], [129, 16], [128, 36], [88, 27], [81, 48]]]
 h' := ![![[52, 114, 21], [40, 58, 58], [128, 61, 23], [13, 28, 114], [25, 22, 27], [49, 14, 44], [0, 0, 1], [0, 1]], ![[21, 16, 110], [122, 94, 50], [36, 105, 77], [111, 7, 54], [20, 61, 108], [69, 107, 81], [103, 118, 16], [52, 114, 21]], ![[0, 1], [73, 110, 23], [65, 96, 31], [11, 96, 94], [37, 48, 127], [90, 10, 6], [27, 13, 114], [21, 16, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 15], []]
 b := ![[], [2, 25, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [107, 45, 58, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72443, -29606, 4192]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![553, -226, 32]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![15, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![15, 1, 0]] 
 ![![137, 0, 0], ![15, 1, 0], ![49, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![15, 1, 0], ![0, 15, 1], ![-194, 17, 16]]]
  hmulB := by decide  
  f := ![![![841, 56, 0], ![-7672, 0, 0]], ![![75, 5, 0], ![-684, 0, 0]], ![![287, 19, 0], ![-2618, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 137, 0], ![-49, 0, 137]], ![![0, 1, 0], ![-2, 15, 1], ![-9, 17, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![57, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![57, 1, 0]] 
 ![![137, 0, 0], ![57, 1, 0], ![39, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![57, 1, 0], ![0, 57, 1], ![-194, 17, 58]]]
  hmulB := by decide  
  f := ![![![2452, 43, 0], ![-5891, 0, 0]], ![![1026, 18, 0], ![-2465, 0, 0]], ![![708, 12, 0], ![-1701, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 137, 0], ![-39, 0, 137]], ![![0, 1, 0], ![-24, 57, 1], ![-25, 17, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![64, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![64, 1, 0]] 
 ![![137, 0, 0], ![64, 1, 0], ![14, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![64, 1, 0], ![0, 64, 1], ![-194, 17, 65]]]
  hmulB := by decide  
  f := ![![![833, 13, 0], ![-1781, 0, 0]], ![![320, 5, 0], ![-684, 0, 0]], ![![30, 0, 0], ![-64, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 137, 0], ![-14, 0, 137]], ![![0, 1, 0], ![-30, 64, 1], ![-16, 17, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![15, 1, 0]] ![![137, 0, 0], ![57, 1, 0]]
  ![![137, 0, 0], ![33, -65, 1]] where
 M := ![![![18769, 0, 0], ![7809, 137, 0]], ![![2055, 137, 0], ![855, 72, 1]]]
 hmul := by decide  
 g := ![![![![104, 65, -1], ![137, 0, 0]], ![![24, 66, -1], ![137, 0, 0]]], ![![![-18, 66, -1], ![137, 0, 0]], ![![6, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![33, -65, 1]] ![![137, 0, 0], ![64, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8768, 137, 0]], ![![4521, -8905, 137], ![1918, -4110, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![64, 1, 0]]], ![![![33, -65, 1]], ![![14, -30, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB274I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB274I2 : PrimesBelowBoundCertificateInterval O 79 137 274 where
  m := 11
  g := ![2, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB274I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![97, 9409]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![137, 137, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
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
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I97N0, I101N0, I101N1, I101N2, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [], [I97N0], [I101N0, I101N1, I101N2], [], [], [], [], [], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
