
import IdealArithmetic.Examples.NF3_1_692259_1.RI3_1_692259_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [8, 50, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 6, 8], [25, 76, 75], [0, 1]]
 g := ![![[43, 29, 51], [82, 17, 70], [26, 64], [27, 78], [36, 13, 1], []], ![[8, 28, 8, 47], [78, 81, 81, 74], [23, 27], [17, 21], [40, 20, 16, 60], [15, 64]], ![[82, 21, 70, 17], [54, 82, 12, 33], [15, 51], [73, 75], [51, 20, 53, 44], [31, 64]]]
 h' := ![![[71, 6, 8], [8, 35, 36], [72, 28, 30], [60, 43, 8], [44, 5, 59], [0, 0, 1], [0, 1]], ![[25, 76, 75], [37, 58, 28], [41, 69, 14], [68, 49, 39], [72, 76, 42], [24, 5, 76], [71, 6, 8]], ![[0, 1], [13, 73, 19], [47, 69, 39], [1, 74, 36], [2, 2, 65], [45, 78, 6], [25, 76, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 23], []]
 b := ![[], [56, 52, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [8, 50, 70, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76443, 68724, -20667]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-921, 828, -249]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [41, 5, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 19, 7], [13, 69, 82], [0, 1]]
 g := ![![[50, 26, 87], [31, 68], [5, 39], [54, 44, 71], [6, 10, 1], []], ![[13, 15, 49, 62], [37, 67], [33, 88], [19, 32, 45, 48], [35, 49, 21, 41], [44, 49]], ![[0, 13, 49, 75], [66, 81], [37, 55], [3, 2, 75, 82], [0, 70, 24, 54], [58, 49]]]
 h' := ![![[86, 19, 7], [0, 74, 40], [5, 8, 54], [11, 58, 22], [21, 5, 58], [0, 0, 1], [0, 1]], ![[13, 69, 82], [68, 68, 74], [61, 10, 44], [41, 19, 55], [26, 15, 32], [74, 60, 69], [86, 19, 7]], ![[0, 1], [0, 36, 64], [83, 71, 80], [49, 12, 12], [35, 69, 88], [16, 29, 19], [13, 69, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 12], []]
 b := ![[], [16, 29, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [41, 5, 79, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4723853, -625492, -23318]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![53077, -7028, -262]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-208047, 60549, -10531]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-208047, 60549, -10531]] 
 ![![97, 0, 0], ![0, 97, 0], ![42, 49, 1]] where
  M :=![![![-208047, 60549, -10531], ![-1682323, -100100, 171116], ![8187198, -1453210, 10467]]]
  hmulB := by decide  
  f := ![![![-2552780780, -151236991, -95945872]], ![![-14624427297, -866409837, -549656845]], ![![-8839859599, -523708803, -332244760]]]
  g := ![![![2415, 5944, -10531], ![-91435, -87472, 171116], ![79872, -20269, 10467]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [95, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 96], [0, 1]]
 g := ![![[91, 48], [16], [47], [50], [73], [85, 1]], ![[0, 49], [16], [47], [50], [73], [73, 96]]]
 h' := ![![[85, 96], [5, 57], [78, 93], [9, 85], [43, 70], [73, 49], [0, 1]], ![[0, 1], [0, 40], [29, 4], [56, 12], [76, 27], [67, 48], [85, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [28, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [95, 12, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![443644, 210806, -68529]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34246, 36791, -68529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2552780780, 151236991, 95945872]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![2552780780, 151236991, 95945872]] 
 ![![97, 0, 0], ![46, 1, 0], ![21, 0, 1]] where
  M :=![![![2552780780, 151236991, 95945872], ![14624427297, 866409837, 549656845], ![33652650790, 1993718256, 1264829691]]]
  hmulB := by decide  
  f := ![![![208047, -60549, 10531]], ![![116005, -27682, 3230]], ![![-39363, 1873, 2172]]]
  g := ![![![-66175094, 151236991, 95945872], ![-379105350, 866409837, 549656845], ![-872369201, 1993718256, 1264829691]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-208047, 60549, -10531]] ![![2552780780, 151236991, 95945872]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-46, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-46, 1, 0]] 
 ![![101, 0, 0], ![55, 1, 0], ![87, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-46, 1, 0], ![-1, -47, 3], ![154, -16, -45]]]
  hmulB := by decide  
  f := ![![![-4229, -198810, 12690], ![0, -427230, 0]], ![![-2302, -108241, 6909], ![1, -232603, 0]], ![![-3651, -171252, 10931], ![-18, -368010, 0]]]
  g := ![![![1, 0, 0], ![-55, 101, 0], ![-87, 0, 101]], ![![-1, 1, 0], ![23, -47, 3], ![49, -16, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-30, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-30, 1, 0]] 
 ![![101, 0, 0], ![71, 1, 0], ![60, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-30, 1, 0], ![-1, -31, 3], ![154, -16, -29]]]
  hmulB := by decide  
  f := ![![![-628, -19499, 1887], ![0, -63529, 0]], ![![-441, -13702, 1326], ![1, -44642, 0]], ![![-360, -11584, 1121], ![44, -37740, 0]]]
  g := ![![![1, 0, 0], ![-71, 101, 0], ![-60, 0, 101]], ![![-1, 1, 0], ![20, -31, 3], ![30, -16, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-561, 45, 23]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-561, 45, 23]] 
 ![![101, 0, 0], ![76, 1, 0], ![86, 0, 1]] where
  M :=![![![-561, 45, 23], ![3497, -974, 158], ![9414, 338, -861]]]
  hmulB := by decide  
  f := ![![![785210, 46519, 29512]], ![![635389, 37643, 23881]], ![![771082, 45682, 28981]]]
  g := ![![![-59, 45, 23], ![633, -974, 158], ![572, 338, -861]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-46, 1, 0]] ![![101, 0, 0], ![-30, 1, 0]]
  ![![-785210, -46519, -29512]] where
 M := ![![![10201, 0, 0], ![-3030, 101, 0]], ![![-4646, 101, 0], ![1379, -77, 3]]]
 hmul := by decide  
 g := ![![![![56661, -4545, -2323]], ![![-20327, 2324, 532]]], ![![![-29303, 3044, 900]], ![![10046, -1367, -168]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-785210, -46519, -29512]] ![![-561, 45, 23]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [73, 52, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 40, 90], [22, 62, 13], [0, 1]]
 g := ![![[25, 19, 98], [38, 14, 58], [20, 42, 30], [18, 19], [39, 26], [1]], ![[61, 34, 67, 6], [38, 42, 74, 35], [76, 96, 48, 48], [72, 23], [16, 8], [98, 6, 6, 69]], ![[2, 73, 40, 50], [39, 49, 61, 16], [0, 40, 66, 32], [22, 32], [85, 7], [91, 63, 2, 34]]]
 h' := ![![[29, 40, 90], [7, 4, 60], [85, 86, 26], [22, 30, 37], [10, 61, 15], [30, 51, 51], [0, 1]], ![[22, 62, 13], [66, 96, 63], [72, 27, 82], [38, 55, 50], [91, 55, 34], [34, 8, 27], [29, 40, 90]], ![[0, 1], [4, 3, 83], [87, 93, 98], [92, 18, 16], [16, 90, 54], [91, 44, 25], [22, 62, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 64], []]
 b := ![[], [77, 80, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [73, 52, 52, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4822460, 1142476, -144200]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46820, 11092, -1400]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9433, -1879, 101]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![9433, -1879, 101]] 
 ![![107, 0, 0], ![0, 107, 0], ![15, 10, 1]] where
  M :=![![![9433, -1879, 101], ![17433, 9696, -5536], ![-278458, 34710, 6039]]]
  hmulB := by decide  
  f := ![![![-2343072, -138813, -88064]], ![![-13423043, -795235, -504503]], ![![-1871632, -110883, -70345]]]
  g := ![![![74, -27, 101], ![939, 608, -5536], ![-3449, -240, 6039]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [94, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 106], [0, 1]]
 g := ![![[59, 41], [8, 4], [75], [66, 25], [42], [18, 1]], ![[48, 66], [80, 103], [75], [88, 82], [42], [36, 106]]]
 h' := ![![[18, 106], [104, 24], [16, 105], [2, 90], [90, 5], [20, 16], [0, 1]], ![[0, 1], [1, 83], [87, 2], [17, 17], [73, 102], [94, 91], [18, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [12, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [94, 89, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1156, 414, -408]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68, 42, -408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2343072, -138813, -88064]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-2343072, -138813, -88064]] 
 ![![107, 0, 0], ![76, 1, 0], ![97, 0, 1]] where
  M :=![![![-2343072, -138813, -88064], ![-13423043, -795235, -504503], ![-30888114, -1829936, -1160925]]]
  hmulB := by decide  
  f := ![![![9433, -1879, 101]], ![![6863, -1244, 20]], ![![5949, -1379, 148]]]
  g := ![![![156532, -138813, -88064], ![896744, -795235, -504503], ![2063521, -1829936, -1160925]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![9433, -1879, 101]] ![![-2343072, -138813, -88064]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-847, 661, -223]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-847, 661, -223]] 
 ![![109, 0, 0], ![23, 1, 0], ![49, 0, 1]] where
  M :=![![![-847, 661, -223], ![-35003, 2060, 1760], ![77710, -20834, 3159]]]
  hmulB := by decide  
  f := ![![![-43175380, -2557883, -1622740]], ![![-11379613, -674174, -427701]], ![![-24630858, -1459231, -925747]]]
  g := ![![![-47, 661, -223], ![-1547, 2060, 1760], ![3689, -20834, 3159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4468894, 169819, -412794]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![4468894, 169819, -412794]] 
 ![![109, 0, 0], ![63, 1, 0], ![42, 0, 1]] where
  M :=![![![4468894, 169819, -412794], ![-63740095, 10903779, 96663], ![-18429626, -21705628, 10830623]]]
  hmulB := by decide  
  f := ![![![-120192850743681, -7120707437395, -4517429762523]], ![![-75786358466450, -4489888400567, -2848418597373]], ![![-60849276063724, -3604955618792, -2287010658433]]]
  g := ![![![101905, 169819, -412794], ![-6924202, 10903779, 96663], ![8203108, -21705628, 10830623]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-847, 661, -223]] ![![-847, 661, -223]]
  ![![-39748904, 5447775, 647784]] where
 M := ![![![-39748904, 5447775, 647784]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-39748904, 5447775, 647784]] ![![4468894, 169819, -412794]]
  ![![109, 0, 0]] where
 M := ![![![-536813751479585, 38590656984997, 23950611642033]]]
 hmul := by decide  
 g := ![![![![-4924896802565, 354042724633, 219730382037]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![49, 3, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![49, 3, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![49, 3, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![49, 3, 1], ![151, 30, 10], ![570, -2, 37]]]
  hmulB := by decide  
  f := ![![![-48, -3, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -3, 113]], ![![0, 0, 1], ![-3, 0, 10], ![-11, -1, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [22, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 112], [0, 1]]
 g := ![![[72, 36], [62], [56], [14], [28, 98], [111, 1]], ![[0, 77], [62], [56], [14], [58, 15], [109, 112]]]
 h' := ![![[111, 112], [101, 107], [83, 47], [33, 100], [62, 63], [44, 95], [0, 1]], ![[0, 1], [0, 6], [102, 66], [59, 13], [49, 50], [80, 18], [111, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [35, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [22, 2, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23601, -1892, 876]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-171, -40, 876]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-10, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-10, 1, 0]] 
 ![![113, 0, 0], ![103, 1, 0], ![76, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-10, 1, 0], ![-1, -11, 3], ![154, -16, -9]]]
  hmulB := by decide  
  f := ![![![-394, -4345, 1185], ![0, -44635, 0]], ![![-359, -3960, 1080], ![1, -40680, 0]], ![![-258, -2923, 797], ![79, -30020, 0]]]
  g := ![![![1, 0, 0], ![-103, 113, 0], ![-76, 0, 113]], ![![-1, 1, 0], ![8, -11, 3], ![22, -16, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![49, 3, 1]] ![![113, 0, 0], ![-10, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1130, 113, 0]], ![![5537, 339, 113], ![-339, 0, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-10, 1, 0]]], ![![![49, 3, 1]], ![![-3, 0, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [105, 20, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [109, 103, 5], [18, 23, 122], [0, 1]]
 g := ![![[80, 95, 122], [63, 72, 19], [20, 44, 103], [83, 94, 81], [19], [1]], ![[107, 98, 72, 75], [89, 38, 125, 112], [124, 62, 109, 45], [41, 96, 60, 29], [124, 49, 90, 89], [40, 91, 105, 125]], ![[91, 43, 50, 122], [86, 22, 19, 100], [79, 30, 29, 50], [112, 120, 75, 49], [2, 80, 9, 38], [89, 106, 74, 2]]]
 h' := ![![[109, 103, 5], [116, 122, 54], [59, 78, 20], [48, 126, 105], [37, 104, 9], [22, 107], [0, 1]], ![[18, 23, 122], [44, 15, 74], [119, 107, 88], [5, 95, 124], [43, 90, 92], [1, 99, 27], [109, 103, 5]], ![[0, 1], [60, 117, 126], [88, 69, 19], [82, 33, 25], [52, 60, 26], [43, 48, 100], [18, 23, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 30], []]
 b := ![[], [3, 34, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [105, 20, 0, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-814578, 120396, 7620]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6414, 948, 60]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![72, 4, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![72, 4, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![72, 4, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![72, 4, 1], ![150, 52, 13], ![724, -18, 61]]]
  hmulB := by decide  
  f := ![![![-71, -4, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -4, 131]], ![![0, 0, 1], ![-6, 0, 13], ![-28, -2, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [55, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 130], [0, 1]]
 g := ![![[98, 81], [35, 1], [16], [107], [58], [99], [1]], ![[0, 50], [16, 130], [16], [107], [58], [99], [1]]]
 h' := ![![[112, 130], [40, 9], [27, 1], [11, 127], [130, 99], [69, 78], [76, 112], [0, 1]], ![[0, 1], [0, 122], [8, 130], [87, 4], [83, 32], [28, 53], [44, 19], [112, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [116, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [55, 19, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2060, 1832, -459]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![268, 28, -459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-13, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-13, 1, 0]] 
 ![![131, 0, 0], ![118, 1, 0], ![70, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-13, 1, 0], ![-1, -14, 3], ![154, -16, -12]]]
  hmulB := by decide  
  f := ![![![344, 4619, -990], ![131, 43230, 0]], ![![311, 4157, -891], ![132, 38907, 0]], ![![186, 2468, -529], ![92, 23100, 0]]]
  g := ![![![1, 0, 0], ![-118, 131, 0], ![-70, 0, 131]], ![![-1, 1, 0], ![11, -14, 3], ![22, -16, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![72, 4, 1]] ![![131, 0, 0], ![-13, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-1703, 131, 0]], ![![9432, 524, 131], ![-786, 0, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-13, 1, 0]]], ![![![72, 4, 1]], ![![-6, 0, 0]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [20, 95, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 102, 134], [79, 34, 3], [0, 1]]
 g := ![![[51, 99, 44], [116, 101], [125, 72], [49, 129, 136], [76, 107], [18, 1], []], ![[4, 113, 66, 84], [123, 18], [35, 17], [7, 53, 38, 79], [59, 14], [128, 60], [98, 9]], ![[135, 123, 21, 54], [129, 37], [91, 4], [95, 36, 76, 35], [120, 69], [109, 129], [92, 9]]]
 h' := ![![[76, 102, 134], [25, 127, 110], [133, 118, 52], [116, 114, 88], [122, 89, 37], [51, 51, 92], [0, 0, 1], [0, 1]], ![[79, 34, 3], [79, 43, 71], [115, 74, 44], [33, 121, 47], [118, 66, 32], [32, 78, 98], [117, 123, 34], [76, 102, 134]], ![[0, 1], [9, 104, 93], [64, 82, 41], [69, 39, 2], [110, 119, 68], [27, 8, 84], [17, 14, 102], [79, 34, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 130], []]
 b := ![[], [77, 25, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [20, 95, 119, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-361680, 315100, -92475]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2640, 2300, -675]
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



lemma PB236I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB236I2 : PrimesBelowBoundCertificateInterval O 79 137 236 where
  m := 11
  g := ![1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB236I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![571787]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N0
      exact NI109N1
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
  β := ![I97N1, I101N0, I101N1, I101N2, I107N1, I109N0, I109N1, I113N1, I131N1]
  Il := ![[], [], [I97N1], [I101N0, I101N1, I101N2], [], [I107N1], [I109N0, I109N0, I109N1], [I113N1], [], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
