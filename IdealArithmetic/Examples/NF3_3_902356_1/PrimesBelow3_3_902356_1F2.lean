
import IdealArithmetic.Examples.NF3_3_902356_1.RI3_3_902356_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [65, 43, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 68, 40], [25, 14, 43], [0, 1]]
 g := ![![[48, 33, 23], [77, 25, 48], [53, 69], [42, 27], [35, 59, 1], []], ![[66, 12, 14, 81], [42, 6, 23, 65], [65, 3], [2, 36], [25, 59, 34, 38], [74, 23]], ![[33, 27, 10, 39], [66, 2, 37, 18], [82, 63], [6, 33], [79, 59, 52, 47], [71, 23]]]
 h' := ![![[34, 68, 40], [58, 54, 40], [50, 60, 52], [3, 3, 22], [49, 55, 44], [0, 0, 1], [0, 1]], ![[25, 14, 43], [71, 58, 64], [77, 79, 57], [61, 34, 13], [5, 80, 77], [81, 30, 14], [34, 68, 40]], ![[0, 1], [6, 54, 62], [76, 27, 57], [29, 46, 48], [81, 31, 45], [77, 53, 68], [25, 14, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 22], []]
 b := ![[], [25, 61, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [65, 43, 24, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56855, -115370, -139855]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-685, -1390, -1685]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6317, -283, -78]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![6317, -283, -78]] 
 ![![89, 0, 0], ![0, 89, 0], ![16, 39, 1]] where
  M :=![![![6317, -283, -78], ![-566, 3304, -1337], ![-1092, -9359, 3870]]]
  hmulB := by decide  
  f := ![![![3073, 20508, 7147]], ![![41016, 273726, 95393]], ![![19650, 131137, 45701]]]
  g := ![![![85, 31, -78], ![234, 623, -1337], ![-708, -1801, 3870]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [24, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 88], [0, 1]]
 g := ![![[72, 69], [88], [42], [74, 16], [73, 34], [1]], ![[11, 20], [88], [42], [16, 73], [61, 55], [1]]]
 h' := ![![[52, 88], [15, 43], [76, 34], [4, 65], [28, 85], [65, 52], [0, 1]], ![[0, 1], [26, 46], [64, 55], [2, 24], [87, 4], [10, 37], [52, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [25, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [24, 37, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2600, -1183, 6526]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1144, -2873, 6526]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3073, 20508, 7147]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![3073, 20508, 7147]] 
 ![![89, 0, 0], ![73, 1, 0], ![77, 0, 1]] where
  M :=![![![3073, 20508, 7147], ![41016, 273726, 95393], ![100058, 667751, 232710]]]
  hmulB := by decide  
  f := ![![![6317, -283, -78]], ![![5175, -195, -79]], ![![5453, -350, -24]]]
  g := ![![![-22970, 20508, 7147], ![-306587, 273726, 95393], ![-747915, 667751, 232710]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![6317, -283, -78]] ![![3073, 20508, 7147]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [76, 72, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 46, 30], [23, 50, 67], [0, 1]]
 g := ![![[45, 55, 85], [85, 11], [14, 16], [33, 62], [86, 4], [1]], ![[62, 95, 2, 76], [59, 93], [47, 22], [52, 32], [59, 65], [6, 74, 69, 34]], ![[18, 3, 91, 42], [34, 49], [22, 11], [56, 43], [18, 88], [70, 92, 44, 63]]]
 h' := ![![[72, 46, 30], [71, 51, 45], [56, 8, 37], [76, 30, 4], [16, 83, 81], [21, 25, 95], [0, 1]], ![[23, 50, 67], [11, 23, 94], [79, 38, 53], [16, 44, 33], [31, 44, 41], [21, 72, 68], [72, 46, 30]], ![[0, 1], [34, 23, 55], [75, 51, 7], [1, 23, 60], [38, 67, 72], [57, 0, 31], [23, 50, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 70], []]
 b := ![[], [85, 31, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [76, 72, 2, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1270597374, -3172238530, -3105019470]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13098942, -32703490, -32010510]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -153, 62]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![23, -153, 62]] 
 ![![101, 0, 0], ![3, 1, 0], ![99, 0, 1]] where
  M :=![![![23, -153, 62], ![-306, 2040, -827], ![868, -5789, 2346]]]
  hmulB := by decide  
  f := ![![![1663, -20, -51]], ![![49, -2, -2]], ![![1623, -23, -51]]]
  g := ![![![-56, -153, 62], ![747, 2040, -827], ![-2119, -5789, 2346]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 10, -4]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-3, 10, -4]] 
 ![![101, 0, 0], ![15, 1, 0], ![13, 0, 1]] where
  M :=![![![-3, 10, -4], ![20, -133, 54], ![-56, 378, -153]]]
  hmulB := by decide  
  f := ![![![-63, 18, 8]], ![![-9, 5, 2]], ![![-7, 8, 3]]]
  g := ![![![-1, 10, -4], ![13, -133, 54], ![-37, 378, -153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8221, 54864, 19120]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![8221, 54864, 19120]] 
 ![![101, 0, 0], ![83, 1, 0], ![20, 0, 1]] where
  M :=![![![8221, 54864, 19120], ![109728, 732285, 255200], ![267680, 1786400, 622557]]]
  hmulB := by decide  
  f := ![![![-127255, 752, 3600]], ![![-104561, 613, 2960]], ![![-24700, 160, 693]]]
  g := ![![![-48791, 54864, 19120], ![-651227, 732285, 255200], ![-1588660, 1786400, 622557]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![23, -153, 62]] ![![-3, 10, -4]]
  ![![-6601, 44015, -17840]] where
 M := ![![![-6601, 44015, -17840]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-6601, 44015, -17840]] ![![8221, 54864, 19120]]
  ![![101, 0, 0]] where
 M := ![![![-101, -8989, 0]]]
 hmul := by decide  
 g := ![![![![-1, -89, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [30, 70, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 46], [32, 56], [0, 1]]
 g := ![![[1, 86, 98], [45, 24, 25], [78, 67, 49], [41, 13], [37, 4], [1]], ![[28, 40, 29], [92, 84, 61], [41, 94, 66], [63, 83], [20, 81], [1]], ![[2, 80, 79], [45, 98, 17], [74, 45, 91], [45, 7], [62, 18], [1]]]
 h' := ![![[73, 46], [92, 61, 43], [29, 18, 5], [22, 64, 7], [99, 48, 42], [73, 33, 2], [0, 1]], ![[32, 56], [88, 1, 39], [75, 6, 74], [76, 1, 83], [100, 0, 86], [59, 15, 9], [73, 46]], ![[0, 1], [35, 41, 21], [60, 79, 24], [71, 38, 13], [44, 55, 78], [87, 55, 92], [32, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47], []]
 b := ![[], [71, 96, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [30, 70, 101, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-866436, 429201, -2190707]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8412, 4167, -21269]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [78, 42, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 93, 21], [102, 13, 86], [0, 1]]
 g := ![![[58, 2, 53], [79, 96, 40], [60, 13], [66, 56, 33], [83, 48], [1]], ![[106, 59, 25, 88], [57, 104, 85, 17], [49, 47], [42, 21, 16, 93], [55, 27], [77, 40, 64, 59]], ![[6, 35, 77, 76], [28, 27, 18, 13], [56, 85], [45, 97, 52, 14], [15, 40], [21, 56, 4, 48]]]
 h' := ![![[77, 93, 21], [44, 53, 69], [65, 62, 88], [95, 82, 86], [38, 71, 56], [29, 65, 72], [0, 1]], ![[102, 13, 86], [91, 63, 84], [40, 16, 92], [63, 105, 58], [29, 16, 79], [57, 37, 54], [77, 93, 21]], ![[0, 1], [45, 98, 61], [102, 29, 34], [46, 27, 70], [40, 20, 79], [56, 5, 88], [102, 13, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 38], []]
 b := ![[], [39, 1, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [78, 42, 35, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52858, -109461, -130005]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-494, -1023, -1215]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14237, 94943, -38482]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-14237, 94943, -38482]] 
 ![![109, 0, 0], ![0, 109, 0], ![57, 21, 1]] where
  M :=![![![-14237, 94943, -38482], ![189886, -1266164, 513197], ![-538748, 3592379, -1456050]]]
  hmulB := by decide  
  f := ![![![307, 1592, 553]], ![![3184, 21254, 7407]], ![![845, 5403, 1882]]]
  g := ![![![19993, 8285, -38482], ![-266627, -110489, 513197], ![756478, 313481, -1456050]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [90, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 108], [0, 1]]
 g := ![![[103, 31], [73], [57, 38], [106, 82], [83], [104, 1]], ![[57, 78], [73], [85, 71], [23, 27], [83], [99, 108]]]
 h' := ![![[104, 108], [19, 24], [102, 89], [52, 16], [29, 54], [14, 44], [0, 1]], ![[0, 1], [8, 85], [93, 20], [81, 93], [86, 55], [12, 65], [104, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [96, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [90, 5, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1682, 10619, 3703]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1921, -616, 3703]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-307, -1592, -553]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-307, -1592, -553]] 
 ![![109, 0, 0], ![5, 1, 0], ![38, 0, 1]] where
  M :=![![![-307, -1592, -553], ![-3184, -21254, -7407], ![-7742, -51849, -18070]]]
  hmulB := by decide  
  f := ![![![14237, -94943, 38482]], ![![-1089, 7261, -2943]], ![![9906, -66057, 26774]]]
  g := ![![![263, -1592, -553], ![3528, -21254, -7407], ![8607, -51849, -18070]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-14237, 94943, -38482]] ![![-307, -1592, -553]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [111, 49, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 37, 38], [63, 75, 75], [0, 1]]
 g := ![![[58, 78, 72], [50, 8], [30, 106], [30, 98], [107, 110, 62], [1]], ![[112, 63, 64, 76], [111, 105], [68, 53], [19, 30], [45, 88, 9, 42], [63, 4, 65, 67]], ![[104, 46, 100, 21], [59, 99], [46, 64], [17, 26], [23, 46, 109, 42], [13, 34, 10, 46]]]
 h' := ![![[3, 37, 38], [89, 40, 80], [92, 81, 11], [91, 80, 85], [101, 66, 18], [2, 64, 66], [0, 1]], ![[63, 75, 75], [60, 88, 62], [8, 71, 61], [95, 12, 36], [31, 27, 16], [40, 67, 37], [3, 37, 38]], ![[0, 1], [104, 98, 84], [41, 74, 41], [47, 21, 105], [37, 20, 79], [4, 95, 10], [63, 75, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 19], []]
 b := ![[], [105, 68, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [111, 49, 47, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145092, 317530, -374030]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1284, 2810, -3310]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1231, -7, -35]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![1231, -7, -35]] 
 ![![127, 0, 0], ![14, 1, 0], ![60, 0, 1]] where
  M :=![![![1231, -7, -35], ![-14, -1, 0], ![-490, 0, 13]]]
  hmulB := by decide  
  f := ![![![13, -91, 35]], ![![0, -1, 0]], ![![10, -70, 27]]]
  g := ![![![27, -7, -35], ![0, -1, 0], ![-10, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7489, -161, 296]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-7489, -161, 296]] 
 ![![127, 0, 0], ![37, 1, 0], ![24, 0, 1]] where
  M :=![![![-7489, -161, 296], ![-322, 2710, -1101], ![4144, -7707, 3032]]]
  hmulB := by decide  
  f := ![![![-268687, -1793120, -624899]], ![![-106517, -710856, -247732]], ![![-119662, -798581, -278304]]]
  g := ![![![-68, -161, 296], ![-584, 2710, -1101], ![1705, -7707, 3032]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129, -736, -256]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-129, -736, -256]] 
 ![![127, 0, 0], ![76, 1, 0], ![100, 0, 1]] where
  M :=![![![-129, -736, -256], ![-1472, -9825, -3424], ![-3584, -23968, -8353]]]
  hmulB := by decide  
  f := ![![![1793, -12000, 4864]], ![![884, -5921, 2400]], ![![1948, -13024, 5279]]]
  g := ![![![641, -736, -256], ![8564, -9825, -3424], ![20892, -23968, -8353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![1231, -7, -35]] ![![-7489, -161, 296]]
  ![![-9361745, 52584, 265963]] where
 M := ![![![-9361745, 52584, 265963]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-9361745, 52584, 265963]] ![![-129, -736, -256]]
  ![![127, 0, 0]] where
 M := ![![![177050065, -994664, -5029835]]]
 hmul := by decide  
 g := ![![![![1394095, -7832, -39605]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [80, 0, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 92, 76], [123, 38, 55], [0, 1]]
 g := ![![[122, 11, 27], [2, 111, 61], [46, 129], [125, 48], [117, 21], [57, 1], []], ![[22, 111, 5, 8], [10, 119, 8, 119], [10, 20], [80, 113], [130, 36], [129, 3], [127, 12]], ![[62, 43, 117, 101], [43, 4, 3, 59], [27, 105], [78, 39], [6, 7], [56, 80], [17, 12]]]
 h' := ![![[65, 92, 76], [102, 122, 114], [15, 119, 42], [17, 72, 103], [42, 84, 110], [25, 51, 105], [0, 0, 1], [0, 1]], ![[123, 38, 55], [66, 26, 111], [44, 38, 29], [53, 55, 85], [54, 83, 84], [57, 80, 6], [91, 127, 38], [65, 92, 76]], ![[0, 1], [67, 114, 37], [44, 105, 60], [97, 4, 74], [124, 95, 68], [39, 0, 20], [14, 4, 92], [123, 38, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 86], []]
 b := ![[], [88, 39, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [80, 0, 74, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![619630, 746700, 1536630]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4730, 5700, 11730]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [106, 74, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 91, 99], [48, 45, 38], [0, 1]]
 g := ![![[24, 90, 15], [24, 22], [0, 17], [27, 25, 19], [129, 16], [107, 1], []], ![[113, 111, 16, 28], [78, 14], [38, 88], [10, 40, 56, 126], [46, 49], [51, 107], [43, 74]], ![[74, 62, 92, 100], [17, 136], [129, 65], [96, 71, 47, 37], [104, 9], [33, 61], [104, 74]]]
 h' := ![![[59, 91, 99], [131, 32, 17], [88, 64, 61], [15, 117, 90], [45, 126, 29], [29, 59, 4], [0, 0, 1], [0, 1]], ![[48, 45, 38], [13, 71, 97], [91, 38, 39], [134, 71, 15], [84, 100, 79], [24, 107, 130], [19, 123, 45], [59, 91, 99]], ![[0, 1], [17, 34, 23], [60, 35, 37], [87, 86, 32], [87, 48, 29], [39, 108, 3], [48, 14, 91], [48, 45, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 98], []]
 b := ![[], [92, 87, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [106, 74, 30, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-499639, -1337120, -1218615]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3647, -9760, -8895]
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



lemma PB212I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB212I2 : PrimesBelowBoundCertificateInterval O 79 137 212 where
  m := 11
  g := ![1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB212I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![127, 127, 127]
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
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N1, I101N0, I101N1, I101N2, I109N1, I127N0, I127N1, I127N2]
  Il := ![[], [I89N1], [], [I101N0, I101N1, I101N2], [], [], [I109N1], [], [I127N0, I127N1, I127N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
