
import IdealArithmetic.Examples.NF3_1_925444_2.RI3_1_925444_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-6, -14, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-6, -14, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![77, 69, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-6, -14, 1], ![260, -2, -71], ![-3400, -408, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -69, 83]], ![![-1, -1, 1], ![69, 59, -71], ![-79, -39, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [68, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 82], [0, 1]]
 g := ![![[0, 11], [], [], [78], [], [1]], ![[0, 72], [], [], [78], [], [1]]]
 h' := ![![[0, 82], [0, 29], [64], [8], [0, 59], [15], [0, 1]], ![[0, 1], [0, 54], [64], [8], [0, 24], [15], [0, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [0, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [68, 0, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3214, 1966, 820]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-722, -658, 820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-12, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-12, 1, 0]] 
 ![![83, 0, 0], ![71, 1, 0], ![42, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-12, 1, 0], ![-2, -10, 5], ![232, 32, -13]]]
  hmulB := by decide  
  f := ![![![6769, 34206, -17100], ![-498, 283860, 0]], ![![5791, 29255, -14625], ![-414, 242775, 0]], ![![3426, 17309, -8653], ![-247, 143640, 0]]]
  g := ![![![1, 0, 0], ![-71, 83, 0], ![-42, 0, 83]], ![![-1, 1, 0], ![6, -10, 5], ![-18, 32, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-6, -14, 1]] ![![83, 0, 0], ![-12, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-996, 83, 0]], ![![-498, -1162, 83], ![332, 166, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-12, 1, 0]]], ![![![-6, -14, 1]], ![![4, 2, -1]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [27, 68, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 30, 4], [48, 58, 85], [0, 1]]
 g := ![![[36, 14, 25], [], [55, 84], [75, 68, 9], [20, 55, 1], []], ![[50, 55, 15, 69], [7, 9], [8, 32], [26, 15, 34, 78], [79, 1, 0, 17], [52, 16]], ![[88, 8, 46, 39], [56, 9], [46, 55], [33, 13, 18, 50], [37, 38, 14, 49], [60, 16]]]
 h' := ![![[7, 30, 4], [39, 56, 84], [67, 23], [22, 42, 23], [83, 3, 3], [0, 0, 1], [0, 1]], ![[48, 58, 85], [86, 18, 23], [50, 67, 3], [34, 23, 78], [44, 37, 8], [69, 12, 58], [7, 30, 4]], ![[0, 1], [19, 15, 71], [14, 88, 86], [59, 24, 77], [54, 49, 78], [61, 77, 30], [48, 58, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 65], []]
 b := ![[], [23, 12, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [27, 68, 34, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13676452, 5520670, 1804920]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![153668, 62030, 20280]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [91, 68, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 48, 43], [51, 48, 54], [0, 1]]
 g := ![![[19, 13, 35], [28, 62], [30, 4], [1, 36], [22, 65], [1]], ![[43, 48, 90, 89], [13, 79], [96, 54], [66, 1], [25, 73], [38, 92, 75, 64]], ![[58, 37, 4, 48], [34, 27], [28, 27], [75, 25], [65, 12], [67, 5, 4, 33]]]
 h' := ![![[17, 48, 43], [96, 45, 61], [92, 46, 81], [3, 85, 2], [71, 18, 91], [6, 29, 68], [0, 1]], ![[51, 48, 54], [81, 74, 13], [10, 63, 46], [4, 68, 65], [53, 96, 1], [0, 8, 49], [17, 48, 43]], ![[0, 1], [4, 75, 23], [73, 85, 67], [14, 41, 30], [90, 80, 5], [66, 60, 77], [51, 48, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 17], []]
 b := ![[], [42, 46, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [91, 68, 29, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144624407675, -36873954032, -10665501334]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1490973275, -380143856, -109953622]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [6, 14, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 32, 34], [22, 68, 67], [0, 1]]
 g := ![![[98, 86, 96], [0, 47], [17, 75, 56], [53, 30], [58, 85], [1]], ![[18, 59, 6, 59], [33, 76], [79, 78, 9, 27], [11, 20], [49, 80], [32, 64, 72, 15]], ![[17, 43, 31, 59], [78, 64], [0, 51, 94, 69], [19, 78], [82, 6], [6, 73, 96, 86]]]
 h' := ![![[18, 32, 34], [1, 58, 46], [100, 32, 59], [66, 54, 37], [92, 58, 38], [95, 87, 40], [0, 1]], ![[22, 68, 67], [81, 16, 50], [28, 78, 50], [65, 46, 9], [63, 33, 11], [85, 73, 22], [18, 32, 34]], ![[0, 1], [15, 27, 5], [68, 92, 93], [94, 1, 55], [62, 10, 52], [7, 42, 39], [22, 68, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 72], []]
 b := ![[], [78, 89, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [6, 14, 61, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17515622, -5245839, -1468035]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-173422, -51939, -14535]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1090277, 256429, 76389]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![1090277, 256429, 76389]] 
 ![![103, 0, 0], ![0, 103, 0], ![69, 54, 1]] where
  M :=![![![1090277, 256429, 76389], ![17209390, 4047583, 1205756], ![47880400, 11261288, 3354685]]]
  hmulB := by decide  
  f := ![![![3909, 89, -121]], ![![-28250, 215, 566]], ![![-11813, 153, 214]]]
  g := ![![![-40588, -37559, 76389], ![-640658, -592847, 1205756], ![-1782455, -1649434, 3354685]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [53, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 102], [0, 1]]
 g := ![![[33, 33], [48, 52], [46, 28], [32], [32], [2, 1]], ![[99, 70], [49, 51], [102, 75], [32], [32], [4, 102]]]
 h' := ![![[2, 102], [31, 41], [34, 84], [31, 53], [64, 49], [100, 54], [0, 1]], ![[0, 1], [10, 62], [99, 19], [34, 50], [59, 54], [2, 49], [2, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [102, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [53, 101, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3401, 1663, 315]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-178, -149, 315]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3909, 89, -121]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![3909, 89, -121]] 
 ![![103, 0, 0], ![40, 1, 0], ![55, 0, 1]] where
  M :=![![![3909, 89, -121], ![-28250, 215, 566], ![39040, -1992, -173]]]
  hmulB := by decide  
  f := ![![![1090277, 256429, 76389]], ![![590490, 138881, 41372]], ![![1047045, 246261, 73360]]]
  g := ![![![68, 89, -121], ![-660, 215, 566], ![1245, -1992, -173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![1090277, 256429, 76389]] ![![3909, 89, -121]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-48, 28, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-48, 28, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![59, 28, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-48, 28, 1], ![176, 40, 139], ![6344, 936, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -28, 107]], ![![-1, 0, 1], ![-75, -36, 139], ![83, 20, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [81, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 106], [0, 1]]
 g := ![![[92, 37], [34, 16], [64], [83, 85], [35], [38, 1]], ![[0, 70], [0, 91], [64], [103, 22], [35], [76, 106]]]
 h' := ![![[38, 106], [28, 95], [62, 4], [18, 99], [37, 37], [25, 79], [0, 1]], ![[0, 1], [0, 12], [0, 103], [35, 8], [52, 70], [31, 28], [38, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [35, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [81, 69, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74473, 16843, 4893]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2002, -1123, 4893]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-32, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-32, 1, 0]] 
 ![![107, 0, 0], ![75, 1, 0], ![43, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-32, 1, 0], ![-2, -30, 5], ![232, 32, -33]]]
  hmulB := by decide  
  f := ![![![1437, 22502, -3750], ![-214, 80250, 0]], ![![1019, 15751, -2625], ![-106, 56175, 0]], ![![605, 9042, -1507], ![6, 32250, 0]]]
  g := ![![![1, 0, 0], ![-75, 107, 0], ![-43, 0, 107]], ![![-1, 1, 0], ![19, -30, 5], ![-7, 32, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-48, 28, 1]] ![![107, 0, 0], ![-32, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3424, 107, 0]], ![![-5136, 2996, 107], ![1712, -856, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-32, 1, 0]]], ![![![-48, 28, 1]], ![![16, -8, 1]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [92, 107, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 42, 30], [78, 66, 79], [0, 1]]
 g := ![![[23, 88, 7], [10, 61], [9, 82, 66], [23, 63, 89], [99, 108], [1]], ![[58, 76, 105, 2], [48, 15], [45, 29, 66, 40], [1, 47, 108, 79], [33, 94], [51, 71, 74, 77]], ![[67, 24, 70, 52], [52, 31], [60, 86, 74, 10], [84, 67, 70, 72], [41, 106], [91, 18, 60, 32]]]
 h' := ![![[64, 42, 30], [35, 57, 15], [44, 58, 72], [64, 18, 75], [10, 31, 31], [17, 2, 33], [0, 1]], ![[78, 66, 79], [57, 19, 84], [107, 83, 61], [90, 108, 40], [52, 27, 33], [103, 91, 58], [64, 42, 30]], ![[0, 1], [86, 33, 10], [40, 77, 85], [94, 92, 103], [103, 51, 45], [96, 16, 18], [78, 66, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 87], []]
 b := ![[], [95, 69, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [92, 107, 76, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4142218, -1265926, -321332]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38002, -11614, -2948]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [38, 54, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 7, 83], [25, 105, 30], [0, 1]]
 g := ![![[67, 12, 63], [21, 109], [92, 9], [23, 53], [2, 3, 95], [1]], ![[112, 53, 51, 41], [86, 8], [14, 60], [27, 9], [57, 76, 83, 104], [38, 102, 10, 7]], ![[59, 58, 110, 26], [100, 22], [94, 32], [84, 52], [0, 77, 92, 64], [83, 5, 2, 106]]]
 h' := ![![[53, 7, 83], [37, 22, 17], [48, 34, 83], [43, 49, 3], [37, 92, 36], [75, 59, 78], [0, 1]], ![[25, 105, 30], [107, 62, 108], [95, 68, 11], [47, 21, 88], [13, 57, 3], [81, 64, 92], [53, 7, 83]], ![[0, 1], [106, 29, 101], [105, 11, 19], [93, 43, 22], [102, 77, 74], [41, 103, 56], [25, 105, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 17], []]
 b := ![[], [27, 2, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [38, 54, 35, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15733668, 4460110, 1343570]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139236, 39470, 11890]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-1, 50, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-1, 50, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![126, 50, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-1, 50, 1], ![132, 131, 249], ![11448, 1640, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-126, -50, 127]], ![![-1, 0, 1], ![-246, -97, 249], ![108, 20, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [95, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 126], [0, 1]]
 g := ![![[27, 52], [110, 74], [56, 104], [25, 31], [71, 103], [102, 1]], ![[124, 75], [38, 53], [123, 23], [12, 96], [36, 24], [77, 126]]]
 h' := ![![[102, 126], [91, 68], [14, 70], [38, 55], [113, 44], [89, 22], [0, 1]], ![[0, 1], [42, 59], [42, 57], [60, 72], [29, 83], [47, 105], [102, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [31, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [95, 25, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35445, 18450, 7100]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6765, -2650, 7100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![5, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![5, 1, 0]] 
 ![![127, 0, 0], ![5, 1, 0], ![18, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![5, 1, 0], ![-2, 7, 5], ![232, 32, 4]]]
  hmulB := by decide  
  f := ![![![-713, 2499, 1785], ![0, -45339, 0]], ![![-28, 98, 70], ![1, -1778, 0]], ![![-102, 354, 253], ![24, -6426, 0]]]
  g := ![![![1, 0, 0], ![-5, 127, 0], ![-18, 0, 127]], ![![0, 1, 0], ![-1, 7, 5], ![0, 32, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-1, 50, 1]] ![![127, 0, 0], ![5, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![635, 127, 0]], ![![-127, 6350, 127], ![127, 381, 254]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![5, 1, 0]]], ![![![-1, 50, 1]], ![![1, 3, 2]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-63, -29, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-63, -29, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![68, 102, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-63, -29, 1], ![290, -89, -146], ![-6880, -888, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -102, 131]], ![![-1, -1, 1], ![78, 113, -146], ![-52, -6, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [127, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 130], [0, 1]]
 g := ![![[122, 100], [76, 3], [15], [58], [20], [117], [1]], ![[59, 31], [99, 128], [15], [58], [20], [117], [1]]]
 h' := ![![[95, 130], [42, 10], [30, 38], [106, 88], [108, 78], [91, 85], [4, 95], [0, 1]], ![[0, 1], [75, 121], [103, 93], [82, 43], [51, 53], [44, 46], [121, 36], [95, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [113, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [127, 36, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53821, 8152, 8916]
  a := ![-6, -2, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5039, -6880, 8916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![15, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![15, 1, 0]] 
 ![![131, 0, 0], ![15, 1, 0], ![1, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![15, 1, 0], ![-2, 17, 5], ![232, 32, 14]]]
  hmulB := by decide  
  f := ![![![-8914, 76163, 22400], ![-393, -586880, 0]], ![![-1024, 8704, 2560], ![1, -67072, 0]], ![![-74, 581, 171], ![49, -4480, 0]]]
  g := ![![![1, 0, 0], ![-15, 131, 0], ![-1, 0, 131]], ![![0, 1, 0], ![-2, 17, 5], ![-2, 32, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-63, -29, 1]] ![![131, 0, 0], ![15, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![1965, 131, 0]], ![![-8253, -3799, 131], ![-655, -524, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![15, 1, 0]]], ![![![-63, -29, 1]], ![![-5, -4, -1]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [119, 102, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 82, 124], [30, 54, 13], [0, 1]]
 g := ![![[4, 62, 22], [85, 32], [136, 8], [97, 113, 11], [1, 44], [102, 1], []], ![[68, 44, 115, 111], [30, 2], [13, 115], [115, 26, 16, 52], [10, 28], [122, 39], [36, 32]], ![[123, 6, 123, 55], [8, 18], [7, 100], [63, 30, 96, 10], [65, 135], [31, 11], [10, 32]]]
 h' := ![![[72, 82, 124], [14, 45, 61], [111, 20, 13], [102, 105, 62], [29, 125, 82], [55, 26, 27], [0, 0, 1], [0, 1]], ![[30, 54, 13], [66, 0, 106], [99, 90, 31], [31, 69, 65], [81, 41, 63], [60, 72, 24], [78, 81, 54], [72, 82, 124]], ![[0, 1], [114, 92, 107], [92, 27, 93], [68, 100, 10], [1, 108, 129], [129, 39, 86], [121, 56, 82], [30, 54, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 89], []]
 b := ![[], [74, 128, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [119, 102, 35, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1542980721, 402821511, 117525861]
  a := ![-15, 27, 44]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11262633, 2940303, 857853]
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



lemma PB273I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB273I2 : PrimesBelowBoundCertificateInterval O 79 137 273 where
  m := 11
  g := ![2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB273I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
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
    · exact ![704969]
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![16129, 127]
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
  β := ![I83N1, I103N1, I107N1, I127N1, I131N1]
  Il := ![[I83N1], [], [], [], [I103N1], [I107N1], [], [], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
