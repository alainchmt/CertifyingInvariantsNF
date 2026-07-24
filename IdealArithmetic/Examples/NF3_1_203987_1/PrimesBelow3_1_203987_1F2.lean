
import IdealArithmetic.Examples.NF3_1_203987_1.RI3_1_203987_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155, -26, -18]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-155, -26, -18]] 
 ![![83, 0, 0], ![48, 1, 0], ![73, 0, 1]] where
  M :=![![![-155, -26, -18], ![-1584, -265, -184], ![-3872, -648, -449]]]
  hmulB := by decide  
  f := ![![![247, 10, -14]], ![![128, 7, -8]], ![![213, 6, -11]]]
  g := ![![![29, -26, -18], ![296, -265, -184], ![723, -648, -449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-983, 277, -74]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-983, 277, -74]] 
 ![![83, 0, 0], ![52, 1, 0], ![61, 0, 1]] where
  M :=![![![-983, 277, -74], ![-6512, -2203, 1163], ![17864, 791, -1040]]]
  hmulB := by decide  
  f := ![![![1371187, 229546, 159129]], ![![1027772, 172056, 119275]], ![![1419829, 237689, 164774]]]
  g := ![![![-131, 277, -74], ![447, -2203, 1163], ![484, 791, -1040]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1577, -264, -183]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-1577, -264, -183]] 
 ![![83, 0, 0], ![65, 1, 0], ![11, 0, 1]] where
  M :=![![![-1577, -264, -183], ![-16104, -2696, -1869], ![-39336, -6585, -4565]]]
  hmulB := by decide  
  f := ![![![125, 105, -48]], ![![47, 76, -33]], ![![77, 12, -8]]]
  g := ![![![212, -264, -183], ![2165, -2696, -1869], ![5288, -6585, -4565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-155, -26, -18]] ![![-983, 277, -74]]
  ![![125, 105, -48]] where
 M := ![![![125, 105, -48]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![125, 105, -48]] ![![-1577, -264, -183]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [19, 49, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 52, 3], [38, 36, 86], [0, 1]]
 g := ![![[6, 67, 73], [32, 73], [81, 39], [38, 3, 18], [31, 13, 1], []], ![[68, 32, 16, 76], [77, 21], [6, 88], [65, 42, 65, 76], [57, 5, 66, 61], [73, 9]], ![[9, 69, 61, 63], [16, 18], [16, 55], [32, 77, 24, 19], [46, 52, 17, 76], [79, 9]]]
 h' := ![![[64, 52, 3], [62, 55, 47], [74, 48, 47], [79, 38, 67], [34, 14, 14], [0, 0, 1], [0, 1]], ![[38, 36, 86], [75, 73, 77], [84, 65, 56], [51, 33, 34], [52, 55, 12], [39, 60, 36], [64, 52, 3]], ![[0, 1], [7, 50, 54], [20, 65, 75], [18, 18, 77], [35, 20, 63], [32, 29, 52], [38, 36, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 31], []]
 b := ![[], [30, 47, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [19, 49, 76, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-906821, -102706, -28213]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10189, -1154, -317]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [87, 77, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 29, 4], [89, 67, 93], [0, 1]]
 g := ![![[19, 15, 36], [11, 8], [88, 61], [25, 73], [23, 47], [1]], ![[78, 69, 21, 61], [6, 36], [40, 75], [], [88, 85], [24, 6, 42, 64]], ![[60, 88, 28, 22], [82, 89], [60, 47], [37, 73], [93, 48], [43, 62, 7, 33]]]
 h' := ![![[93, 29, 4], [88, 13, 6], [50, 66, 28], [25, 16, 62], [39, 69, 48], [10, 20, 85], [0, 1]], ![[89, 67, 93], [10, 89, 66], [85, 85, 6], [48, 10, 47], [40, 85], [79, 89, 52], [93, 29, 4]], ![[0, 1], [47, 92, 25], [10, 43, 63], [63, 71, 85], [88, 40, 49], [15, 85, 57], [89, 67, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 5], []]
 b := ![[], [14, 17, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [87, 77, 12, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1311925, 255498, 103693]
  a := ![-1, -4, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13525, 2634, 1069]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [74, 42, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 31, 86], [21, 69, 15], [0, 1]]
 g := ![![[28, 72, 20], [71, 1], [10, 6, 95], [56, 37], [83, 52], [1]], ![[69, 60, 42, 18], [26, 20], [6, 91, 21, 55], [24, 52], [84, 36], [93, 63, 7, 59]], ![[40, 85, 28, 11], [54, 43], [36, 74, 17, 59], [41, 78], [46, 19], [78, 45, 25, 42]]]
 h' := ![![[49, 31, 86], [77, 42, 90], [68, 51, 1], [62, 93, 87], [41, 94, 80], [27, 59, 70], [0, 1]], ![[21, 69, 15], [4, 89, 25], [98, 11, 11], [98, 17, 63], [37, 29, 70], [71, 100, 6], [49, 31, 86]], ![[0, 1], [8, 71, 87], [41, 39, 89], [15, 92, 52], [25, 79, 52], [55, 43, 25], [21, 69, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 41], []]
 b := ![[], [95, 78, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [74, 42, 31, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-150894, -2929, -24240]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1494, -29, -240]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![10, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![10, 1, 0]] 
 ![![103, 0, 0], ![10, 1, 0], ![87, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![10, 1, 0], ![0, 8, 5], ![88, 9, 13]]]
  hmulB := by decide  
  f := ![![![291, 29, 0], ![-2987, 0, 0]], ![![10, 1, 0], ![-102, 0, 0]], ![![239, 19, -3], ![-2453, 62, 0]]]
  g := ![![![1, 0, 0], ![-10, 103, 0], ![-87, 0, 103]], ![![0, 1, 0], ![-5, 8, 5], ![-11, 9, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![36, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![36, 1, 0]] 
 ![![103, 0, 0], ![36, 1, 0], ![23, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![36, 1, 0], ![0, 34, 5], ![88, 9, 39]]]
  hmulB := by decide  
  f := ![![![1261, 35, 0], ![-3605, 0, 0]], ![![396, 11, 0], ![-1132, 0, 0]], ![![269, -13, -3], ![-769, 62, 0]]]
  g := ![![![1, 0, 0], ![-36, 103, 0], ![-23, 0, 103]], ![![0, 1, 0], ![-13, 34, 5], ![-11, 9, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-47, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-47, 1, 0]] 
 ![![103, 0, 0], ![56, 1, 0], ![75, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-47, 1, 0], ![0, -49, 5], ![88, 9, -44]]]
  hmulB := by decide  
  f := ![![![4090, -87, 0], ![8961, 0, 0]], ![![2210, -47, 0], ![4842, 0, 0]], ![![3032, -35, -3], ![6643, 62, 0]]]
  g := ![![![1, 0, 0], ![-56, 103, 0], ![-75, 0, 103]], ![![-1, 1, 0], ![23, -49, 5], ![28, 9, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![10, 1, 0]] ![![103, 0, 0], ![36, 1, 0]]
  ![![103, 0, 0], ![-31, 50, 1]] where
 M := ![![![10609, 0, 0], ![3708, 103, 0]], ![![1030, 103, 0], ![360, 44, 5]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![36, 1, 0], ![0, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![5, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-31, 50, 1]] ![![103, 0, 0], ![-47, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4841, 103, 0]], ![![-3193, 5150, 103], ![1545, -2472, 206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-47, 1, 0]]], ![![![-31, 50, 1]], ![![15, -24, 2]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-51, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-51, 1, 0]] 
 ![![107, 0, 0], ![56, 1, 0], ![80, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-51, 1, 0], ![0, -53, 5], ![88, 9, -48]]]
  hmulB := by decide  
  f := ![![![4642, -91, 0], ![9737, 0, 0]], ![![2398, -47, 0], ![5030, 0, 0]], ![![3484, -47, -2], ![7308, 43, 0]]]
  g := ![![![1, 0, 0], ![-56, 107, 0], ![-80, 0, 107]], ![![-1, 1, 0], ![24, -53, 5], ![32, 9, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-40, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-40, 1, 0]] 
 ![![107, 0, 0], ![67, 1, 0], ![92, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-40, 1, 0], ![0, -42, 5], ![88, 9, -37]]]
  hmulB := by decide  
  f := ![![![4201, -105, 0], ![11235, 0, 0]], ![![2641, -66, 0], ![7063, 0, 0]], ![![3556, -72, -2], ![9510, 43, 0]]]
  g := ![![![1, 0, 0], ![-67, 107, 0], ![-92, 0, 107]], ![![-1, 1, 0], ![22, -42, 5], ![27, 9, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-17, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-17, 1, 0]] 
 ![![107, 0, 0], ![90, 1, 0], ![21, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-17, 1, 0], ![0, -19, 5], ![88, 9, -14]]]
  hmulB := by decide  
  f := ![![![1242, -73, 0], ![7811, 0, 0]], ![![1038, -61, 0], ![6528, 0, 0]], ![![266, -8, -2], ![1673, 43, 0]]]
  g := ![![![1, 0, 0], ![-90, 107, 0], ![-21, 0, 107]], ![![-1, 1, 0], ![15, -19, 5], ![-4, 9, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-51, 1, 0]] ![![107, 0, 0], ![-40, 1, 0]]
  ![![107, 0, 0], ![-20, -40, 1]] where
 M := ![![![11449, 0, 0], ![-4280, 107, 0]], ![![-5457, 107, 0], ![2040, -93, 5]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![-20, 41, -1], ![107, 0, 0]]], ![![![-31, 41, -1], ![107, 0, 0]], ![![20, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-20, -40, 1]] ![![107, 0, 0], ![-17, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1819, 107, 0]], ![![-2140, -4280, 107], ![428, 749, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-17, 1, 0]]], ![![![-20, -40, 1]], ![![4, 7, -2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [29, 50, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 38, 103], [100, 70, 6], [0, 1]]
 g := ![![[72, 71, 35], [42, 15], [83, 85, 104], [75, 69, 49], [66, 22], [1]], ![[66, 24, 61, 69], [31, 45], [25, 7, 53, 98], [27, 44, 66, 30], [82, 36], [9, 27, 19, 2]], ![[104, 16, 83, 2], [94, 4], [5, 81, 40, 17], [101, 93, 22, 52], [15, 73], [37, 51, 91, 107]]]
 h' := ![![[92, 38, 103], [62, 0, 12], [100, 59, 48], [5, 97, 70], [17, 52, 102], [80, 59, 83], [0, 1]], ![[100, 70, 6], [62, 23, 77], [78, 45, 63], [100, 96, 67], [5, 46, 70], [58, 103, 6], [92, 38, 103]], ![[0, 1], [107, 86, 20], [76, 5, 107], [103, 25, 81], [95, 11, 46], [51, 56, 20], [100, 70, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 105], []]
 b := ![[], [51, 37, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [29, 50, 26, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3162526, -527996, -199906]
  a := ![1, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29014, -4844, -1834]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 6, -13]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![263, 6, -13]] 
 ![![113, 0, 0], ![9, 1, 0], ![10, 0, 1]] where
  M :=![![![263, 6, -13], ![-1144, 134, -9], ![-616, -245, 125]]]
  hmulB := by decide  
  f := ![![![-14545, -2435, -1688]], ![![-2473, -414, -287]], ![![-4498, -753, -522]]]
  g := ![![![3, 6, -13], ![-20, 134, -9], ![3, -245, 125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 8, -5]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![43, 8, -5]] 
 ![![113, 0, 0], ![36, 1, 0], ![49, 0, 1]] where
  M :=![![![43, 8, -5], ![-440, -18, 25], ![264, -43, 7]]]
  hmulB := by decide  
  f := ![![![-949, -159, -110]], ![![-388, -65, -45]], ![![-621, -104, -72]]]
  g := ![![![0, 8, -5], ![-9, -18, 25], ![13, -43, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2955, 28, 107]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-2955, 28, 107]] 
 ![![113, 0, 0], ![67, 1, 0], ![33, 0, 1]] where
  M :=![![![-2955, 28, 107], ![9416, -2048, 461], ![11880, 2713, -1587]]]
  hmulB := by decide  
  f := ![![![-1999483, -334727, -232044]], ![![-1366241, -228718, -158555]], ![![-1025299, -171642, -118988]]]
  g := ![![![-74, 28, 107], ![1163, -2048, 461], ![-1040, 2713, -1587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![263, 6, -13]] ![![43, 8, -5]]
  ![![5237, 2555, -1256]] where
 M := ![![![5237, 2555, -1256]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![5237, 2555, -1256]] ![![-2955, 28, 107]]
  ![![113, 0, 0]] where
 M := ![![![-6338735, -8493532, 3731486]]]
 hmul := by decide  
 g := ![![![![-56095, -75164, 33022]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -7, -6]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-43, -7, -6]] 
 ![![127, 0, 0], ![0, 127, 0], ![113, 107, 1]] where
  M :=![![![-43, -7, -6], ![-528, -83, -53], ![-1144, -201, -136]]]
  hmulB := by decide  
  f := ![![![-5, -2, 1]], ![![88, 8, -7]], ![![69, 5, -5]]]
  g := ![![![5, 5, -6], ![43, 44, -53], ![112, 113, -136]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [59, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 126], [0, 1]]
 g := ![![[73, 113], [118, 18], [108, 18], [58, 22], [35, 34], [11, 1]], ![[46, 14], [62, 109], [52, 109], [46, 105], [28, 93], [22, 126]]]
 h' := ![![[11, 126], [23, 85], [105, 48], [7, 48], [94, 99], [113, 62], [0, 1]], ![[0, 1], [69, 42], [125, 79], [27, 79], [40, 28], [33, 65], [11, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [75, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [59, 116, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1467, 1370, -259]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![242, 229, -259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -2, 1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-5, -2, 1]] 
 ![![127, 0, 0], ![97, 1, 0], ![62, 0, 1]] where
  M :=![![![-5, -2, 1], ![88, 8, -7], ![-88, 5, 1]]]
  hmulB := by decide  
  f := ![![![-43, -7, -6]], ![![-37, -6, -5]], ![![-30, -5, -4]]]
  g := ![![![1, -2, 1], ![-2, 8, -7], ![-5, 5, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-43, -7, -6]] ![![-5, -2, 1]]
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


lemma PB128I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 127 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 127 (by omega)

def PB128I2 : PrimesBelowBoundCertificateInterval O 79 127 128 where
  m := 9
  g := ![3, 1, 1, 1, 3, 3, 1, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127]
  hP := PB128I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![912673]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
  β := ![I83N0, I83N1, I83N2, I103N0, I103N1, I103N2, I107N0, I107N1, I107N2, I113N0, I113N1, I113N2, I127N1]
  Il := ![[I83N0, I83N1, I83N2], [], [], [], [I103N0, I103N1, I103N2], [I107N0, I107N1, I107N2], [], [I113N0, I113N1, I113N2], [I127N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
