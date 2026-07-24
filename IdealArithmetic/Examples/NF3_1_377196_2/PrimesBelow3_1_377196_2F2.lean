
import IdealArithmetic.Examples.NF3_1_377196_2.RI3_1_377196_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-26, -28, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-26, -28, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![57, 55, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-26, -28, 1], ![90, -18, -195], ![-3286, -206, -46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -55, 83]], ![![-1, -1, 1], ![135, 129, -195], ![-8, 28, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [11, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 82], [0, 1]]
 g := ![![[65, 68], [28, 51], [17], [29], [26, 28], [1]], ![[0, 15], [0, 32], [17], [29], [9, 55], [1]]]
 h' := ![![[32, 82], [24, 20], [73, 47], [54, 10], [46, 64], [72, 32], [0, 1]], ![[0, 1], [0, 63], [0, 36], [42, 73], [19, 19], [17, 51], [32, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [81, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [11, 51, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2496, 945, 70]
  a := ![-1, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -35, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![29, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![29, 1, 0]] 
 ![![83, 0, 0], ![29, 1, 0], ![46, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![29, 1, 0], ![1, 29, 7], ![118, 8, 30]]]
  hmulB := by decide  
  f := ![![![-1095, -40184, -9702], ![-830, 115038, 0]], ![![-397, -14033, -3388], ![-248, 40172, 0]], ![![-617, -22271, -5377], ![-431, 63756, 0]]]
  g := ![![![1, 0, 0], ![-29, 83, 0], ![-46, 0, 83]], ![![0, 1, 0], ![-14, 29, 7], ![-18, 8, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-26, -28, 1]] ![![83, 0, 0], ![29, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2407, 83, 0]], ![![-2158, -2324, 83], ![-664, -830, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![29, 1, 0]]], ![![![-26, -28, 1]], ![![-8, -10, -2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![17, -18, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![17, -18, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![17, 71, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![17, -18, 1], ![100, 25, -125], ![-2106, -126, 7]]]
  hmulB := by decide  
  f := ![![![-16, 18, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -71, 89]], ![![0, -1, 1], ![25, 100, -125], ![-25, -7, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [31, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 88], [0, 1]]
 g := ![![[18, 49], [1], [68], [75, 42], [35, 42], [1]], ![[88, 40], [1], [68], [46, 47], [6, 47], [1]]]
 h' := ![![[65, 88], [9, 7], [60, 1], [78, 35], [72, 65], [58, 65], [0, 1]], ![[0, 1], [19, 82], [36, 88], [39, 54], [25, 24], [11, 24], [65, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [22, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [31, 24, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2943, 3514, 2188]
  a := ![2, -2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-451, -1706, 2188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![36, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![36, 1, 0]] 
 ![![89, 0, 0], ![36, 1, 0], ![82, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![36, 1, 0], ![1, 36, 7], ![118, 8, 37]]]
  hmulB := by decide  
  f := ![![![-2762, -137023, -26649], ![-2581, 338823, 0]], ![![-1107, -55392, -10773], ![-1067, 136971, 0]], ![![-2548, -126246, -24553], ![-2370, 312174, 0]]]
  g := ![![![1, 0, 0], ![-36, 89, 0], ![-82, 0, 89]], ![![0, 1, 0], ![-21, 36, 7], ![-36, 8, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![17, -18, 1]] ![![89, 0, 0], ![36, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3204, 89, 0]], ![![1513, -1602, 89], ![712, -623, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![36, 1, 0]]], ![![![17, -18, 1]], ![![8, -7, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1273358846, 193297409, 125499193]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![1273358846, 193297409, 125499193]] 
 ![![97, 0, 0], ![0, 97, 0], ![51, 7, 1]] where
  M :=![![![1273358846, 193297409, 125499193], ![15002202183, 2277352390, 1478581056], ![25068079736, 3805364746, 2470649799]]]
  hmulB := by decide  
  f := ![![![-1878, 5971, -3478]], ![![-404433, -29702, 38319]], ![![-23555, 843, 692]]]
  g := ![![![-52856701, -7063886, 125499193], ![-622736409, -83223866, 1478581056], ![-1040567629, -139063751, 2470649799]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [18, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 96], [0, 1]]
 g := ![![[7, 27], [27], [49], [18], [75], [68, 1]], ![[0, 70], [27], [49], [18], [75], [39, 96]]]
 h' := ![![[68, 96], [3, 67], [2, 67], [37, 7], [19, 42], [37, 47], [0, 1]], ![[0, 1], [0, 30], [96, 30], [28, 90], [62, 55], [32, 50], [68, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [18, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [18, 29, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2661941, 2745501, 1261764]
  a := ![-65, 1, -391]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-635959, -62751, 1261764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1878, 5971, -3478]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-1878, 5971, -3478]] 
 ![![97, 0, 0], ![47, 1, 0], ![31, 0, 1]] where
  M :=![![![-1878, 5971, -3478], ![-404433, -29702, 38319], ![641974, -14836, -23731]]]
  hmulB := by decide  
  f := ![![![1273358846, 193297409, 125499193]], ![![771650185, 117137429, 76051991]], ![![665383546, 101006025, 65578606]]]
  g := ![![![-1801, 5971, -3478], ![-2024, -29702, 38319], ![21391, -14836, -23731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![1273358846, 193297409, 125499193]] ![![-1878, 5971, -3478]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-34, 15, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-34, 15, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![67, 15, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-34, 15, 1], ![133, -26, 106], ![1788, 138, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -15, 101]], ![![-1, 0, 1], ![-69, -16, 106], ![25, 3, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [13, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 100], [0, 1]]
 g := ![![[24, 70], [36], [89, 65], [76], [79], [92, 1]], ![[0, 31], [36], [9, 36], [76], [79], [83, 100]]]
 h' := ![![[92, 100], [32, 26], [55, 95], [78, 60], [37, 51], [16, 68], [0, 1]], ![[0, 1], [0, 75], [8, 6], [43, 41], [83, 50], [10, 33], [92, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [38, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [13, 9, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![510, 3815, 1702]
  a := ![-2, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1124, -215, 1702]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-5, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-5, 1, 0]] 
 ![![101, 0, 0], ![96, 1, 0], ![11, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-5, 1, 0], ![1, -5, 7], ![118, 8, -4]]]
  hmulB := by decide  
  f := ![![![-1929, 9698, -13580], ![202, 195940, 0]], ![![-1832, 9213, -12901], ![203, 186143, 0]], ![![-209, 1056, -1479], ![44, 21340, 0]]]
  g := ![![![1, 0, 0], ![-96, 101, 0], ![-11, 0, 101]], ![![-1, 1, 0], ![4, -5, 7], ![-6, 8, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-34, 15, 1]] ![![101, 0, 0], ![-5, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-505, 101, 0]], ![![-3434, 1515, 101], ![303, -101, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-5, 1, 0]]], ![![![-34, 15, 1]], ![![3, -1, 1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-46, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-46, 1, 0]] 
 ![![103, 0, 0], ![57, 1, 0], ![51, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-46, 1, 0], ![1, -46, 7], ![118, 8, -45]]]
  hmulB := by decide  
  f := ![![![-2233, 155639, -23688], ![2575, 348552, 0]], ![![-1227, 86098, -13104], ![1443, 192816, 0]], ![![-1107, 77064, -11729], ![1272, 172584, 0]]]
  g := ![![![1, 0, 0], ![-57, 103, 0], ![-51, 0, 103]], ![![-1, 1, 0], ![22, -46, 7], ![19, 8, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-37, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-37, 1, 0]] 
 ![![103, 0, 0], ![66, 1, 0], ![40, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-37, 1, 0], ![1, -37, 7], ![118, 8, -36]]]
  hmulB := by decide  
  f := ![![![-2486, 120747, -22848], ![2163, 336192, 0]], ![![-1609, 77354, -14637], ![1340, 215373, 0]], ![![-964, 46892, -8873], ![844, 130560, 0]]]
  g := ![![![1, 0, 0], ![-66, 103, 0], ![-40, 0, 103]], ![![-1, 1, 0], ![21, -37, 7], ![10, 8, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-21, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-21, 1, 0]] 
 ![![103, 0, 0], ![82, 1, 0], ![99, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-21, 1, 0], ![1, -21, 7], ![118, 8, -20]]]
  hmulB := by decide  
  f := ![![![-3506, 80247, -26754], ![1545, 393666, 0]], ![![-2789, 63870, -21294], ![1237, 313326, 0]], ![![-3378, 77131, -25715], ![1445, 378378, 0]]]
  g := ![![![1, 0, 0], ![-82, 103, 0], ![-99, 0, 103]], ![![-1, 1, 0], ![10, -21, 7], ![14, 8, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-46, 1, 0]] ![![103, 0, 0], ![-37, 1, 0]]
  ![![103, 0, 0], ![-51, 47, 1]] where
 M := ![![![10609, 0, 0], ![-3811, 103, 0]], ![![-4738, 103, 0], ![1703, -83, 7]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![14, -46, -1], ![103, 0, 0]]], ![![![5, -46, -1], ![103, 0, 0]], ![![20, -4, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-51, 47, 1]] ![![103, 0, 0], ![-21, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2163, 103, 0]], ![![-5253, 4841, 103], ![1236, -1030, 309]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-21, 1, 0]]], ![![![-51, 47, 1]], ![![12, -10, 3]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [98, 80, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 8, 91], [106, 98, 16], [0, 1]]
 g := ![![[11, 24, 36], [19, 52, 53], [64, 16], [1, 16, 49], [69, 81], [1]], ![[20, 70, 91, 84], [93, 73, 94, 32], [6, 41], [73, 73, 101, 88], [102, 44], [100, 86, 101, 77]], ![[34, 25, 18, 11], [74, 6, 71, 35], [6, 79], [94, 23, 43, 25], [25, 23], [11, 88, 94, 30]]]
 h' := ![![[99, 8, 91], [64, 29, 6], [15, 93, 69], [9, 26, 4], [60, 82, 100], [9, 27, 98], [0, 1]], ![[106, 98, 16], [6, 32, 17], [95, 49, 31], [24, 39, 83], [57, 69, 35], [67, 88, 77], [99, 8, 91]], ![[0, 1], [29, 46, 84], [67, 72, 7], [86, 42, 20], [92, 63, 79], [98, 99, 39], [106, 98, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 69], []]
 b := ![[], [23, 52, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [98, 80, 9, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-907574, -107642, -53179]
  a := ![-1, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8482, -1006, -497]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-19, -36, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-19, -36, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![90, 73, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-19, -36, 1], ![82, -11, -251], ![-4230, -270, -47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-90, -73, 109]], ![![-1, -1, 1], ![208, 168, -251], ![0, 29, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [45, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 108], [0, 1]]
 g := ![![[103, 63], [61], [26, 7], [75, 38], [105], [52, 1]], ![[0, 46], [61], [63, 102], [89, 71], [105], [104, 108]]]
 h' := ![![[52, 108], [58, 45], [29, 72], [4, 94], [56, 93], [58, 43], [0, 1]], ![[0, 1], [0, 64], [67, 37], [96, 15], [96, 16], [5, 66], [52, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [80, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [45, 57, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61858, 8153, 5166]
  a := ![2, 19, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3698, -3385, 5166]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![33, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![33, 1, 0]] 
 ![![109, 0, 0], ![33, 1, 0], ![47, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![33, 1, 0], ![1, 33, 7], ![118, 8, 34]]]
  hmulB := by decide  
  f := ![![![-4504, -178041, -37772], ![-2943, 588164, 0]], ![![-1369, -53881, -11431], ![-871, 177997, 0]], ![![-1943, -76770, -16287], ![-1266, 253612, 0]]]
  g := ![![![1, 0, 0], ![-33, 109, 0], ![-47, 0, 109]], ![![0, 1, 0], ![-13, 33, 7], ![-16, 8, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-19, -36, 1]] ![![109, 0, 0], ![33, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3597, 109, 0]], ![![-2071, -3924, 109], ![-545, -1199, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![33, 1, 0]]], ![![![-19, -36, 1]], ![![-5, -11, -2]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [30, 72, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 77, 6], [105, 35, 107], [0, 1]]
 g := ![![[3, 108, 97], [95, 52], [45, 11], [40, 102], [94, 85, 112], [1]], ![[95, 78, 71, 68], [62, 95], [32, 26], [8, 91], [18, 6, 67, 27], [62, 88, 30, 103]], ![[18, 106, 18, 96], [39, 16], [52, 87], [32, 88], [14, 27, 112, 76], [98, 60, 88, 10]]]
 h' := ![![[23, 77, 6], [97, 31, 53], [110, 45, 74], [68, 54, 24], [5, 57, 92], [83, 41, 15], [0, 1]], ![[105, 35, 107], [72, 81, 7], [89, 79, 35], [91, 18, 34], [52, 45, 59], [24, 61, 93], [23, 77, 6]], ![[0, 1], [21, 1, 53], [20, 102, 4], [87, 41, 55], [16, 11, 75], [51, 11, 5], [105, 35, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 62], []]
 b := ![[], [84, 16, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [30, 72, 98, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4107324, -329169, 91304]
  a := ![-2, 3, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36348, -2913, 808]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [76, 5, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 64, 69], [1, 62, 58], [0, 1]]
 g := ![![[7, 39, 73], [116, 48, 69], [43, 95, 61], [59, 78, 42], [91, 1, 21], [1]], ![[14, 107, 76, 1], [72, 7, 113, 71], [91, 126, 102, 19], [83, 90, 66, 68], [11, 49, 39, 79], [21, 16, 124, 87]], ![[94, 13, 48, 77], [18, 75, 31, 29], [50, 35, 30, 105], [17, 114, 35, 55], [13, 20, 91, 116], [80, 78, 71, 40]]]
 h' := ![![[103, 64, 69], [74, 103, 33], [34, 55, 113], [88, 62, 51], [69, 38, 114], [51, 122, 104], [0, 1]], ![[1, 62, 58], [110, 41, 9], [63, 107, 6], [63, 9, 74], [74, 52, 38], [74, 51, 7], [103, 64, 69]], ![[0, 1], [64, 110, 85], [110, 92, 8], [10, 56, 2], [63, 37, 102], [17, 81, 16], [1, 62, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 47], []]
 b := ![[], [5, 110, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [76, 5, 23, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6993509, 952754, 403606]
  a := ![2, 1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55067, 7502, 3178]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [130, 76, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 92, 76], [67, 38, 55], [0, 1]]
 g := ![![[93, 40, 89], [96, 70, 36], [6, 36], [58, 108], [122, 48], [29, 1], []], ![[101, 103, 5, 54], [42, 51, 119, 42], [96, 89], [120, 65], [41, 91], [45, 3], [53, 12]], ![[81, 57, 47, 74], [10, 93, 13, 94], [16, 84], [86, 77], [117, 15], [43, 80], [74, 12]]]
 h' := ![![[93, 92, 76], [96, 14, 73], [64, 103, 125], [78, 110, 6], [46, 28, 34], [29, 24, 110], [0, 0, 1], [0, 1]], ![[67, 38, 55], [115, 79, 39], [6, 68, 2], [33, 9, 73], [100, 82, 14], [37, 65, 109], [56, 127, 38], [93, 92, 76]], ![[0, 1], [83, 38, 19], [23, 91, 4], [111, 12, 52], [126, 21, 83], [3, 42, 43], [109, 4, 92], [67, 38, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 84], []]
 b := ![[], [79, 107, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [130, 76, 102, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59824425, -6366600, -2047530]
  a := ![-5, 0, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-456675, -48600, -15630]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41732, 6335, 4113]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![41732, 6335, 4113]] 
 ![![137, 0, 0], ![0, 137, 0], ![28, 11, 1]] where
  M :=![![![41732, 6335, 4113], ![491669, 74636, 48458], ![821564, 124714, 80971]]]
  hmulB := by decide  
  f := ![![![-288, -19, 26]], ![![3049, -80, -107]], ![![173, -8, -4]]]
  g := ![![![-536, -284, 4113], ![-6315, -3346, 48458], ![-10552, -5591, 80971]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [106, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 136], [0, 1]]
 g := ![![[114, 18], [88], [18], [75, 74], [32], [99], [1]], ![[21, 119], [88], [18], [58, 63], [32], [99], [1]]]
 h' := ![![[109, 136], [116, 44], [26, 122], [133, 93], [131, 38], [57, 13], [31, 109], [0, 1]], ![[0, 1], [117, 93], [35, 15], [132, 44], [26, 99], [104, 124], [130, 28], [109, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [108, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [106, 28, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-48858, 7648, 6524]
  a := ![4, -10, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1690, -468, 6524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![288, 19, -26]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![288, 19, -26]] 
 ![![137, 0, 0], ![59, 1, 0], ![90, 0, 1]] where
  M :=![![![288, 19, -26], ![-3049, 80, 107], ![1774, -316, 99]]]
  hmulB := by decide  
  f := ![![![-41732, -6335, -4113]], ![![-21561, -3273, -2125]], ![![-33412, -5072, -3293]]]
  g := ![![![11, 19, -26], ![-127, 80, 107], ![84, -316, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![41732, 6335, 4113]] ![![288, 19, -26]]
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


lemma PB174I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB174I2 : PrimesBelowBoundCertificateInterval O 79 137 174 where
  m := 11
  g := ![2, 2, 2, 2, 3, 1, 2, 1, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB174I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
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
      exact NI97N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N1, I103N0, I103N1, I103N2, I109N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [], [I109N1], [], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
