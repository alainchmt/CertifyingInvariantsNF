
import IdealArithmetic.Examples.NF3_1_649415_1.RI3_1_649415_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![21, 40, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![21, 40, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![21, 40, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![21, 40, 1], ![237, -11, 201], ![6346, 353, 69]]]
  hmulB := by decide  
  f := ![![![-20, -40, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -40, 83]], ![![0, 0, 1], ![-48, -97, 201], ![59, -29, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [52, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 82], [0, 1]]
 g := ![![[70, 65], [56, 48], [26], [68], [65, 61], [1]], ![[20, 18], [51, 35], [26], [68], [50, 22], [1]]]
 h' := ![![[12, 82], [76, 27], [5, 31], [64, 62], [23, 63], [31, 12], [0, 1]], ![[0, 1], [68, 56], [45, 52], [61, 21], [32, 20], [9, 71], [12, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [5, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [52, 71, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1564, 825, -135]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![53, 75, -135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-35, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-35, 1, 0]] 
 ![![83, 0, 0], ![48, 1, 0], ![14, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-35, 1, 0], ![2, -36, 5], ![157, 8, -34]]]
  hmulB := by decide  
  f := ![![![4152, -96733, 13440], ![-2905, -223104, 0]], ![![2409, -55924, 7770], ![-1659, -128982, 0]], ![![721, -16317, 2267], ![-441, -37632, 0]]]
  g := ![![![1, 0, 0], ![-48, 83, 0], ![-14, 0, 83]], ![![-1, 1, 0], ![20, -36, 5], ![3, 8, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![21, 40, 1]] ![![83, 0, 0], ![-35, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2905, 83, 0]], ![![1743, 3320, 83], ![-498, -1411, 166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-35, 1, 0]]], ![![![21, 40, 1]], ![![-6, -17, 2]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [58, 31, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 11, 28], [34, 77, 61], [0, 1]]
 g := ![![[75, 13, 39], [20, 22], [18, 49], [19, 19, 32], [36, 45, 1], []], ![[16, 70, 41, 6], [71, 8], [10, 64], [42, 76, 4, 38], [35, 37, 28, 27], [29, 72]], ![[75, 7, 46, 35], [5, 21], [40, 1], [44, 42, 12, 62], [76, 83, 69, 83], [85, 72]]]
 h' := ![![[11, 11, 28], [81, 76, 67], [23, 39, 72], [55, 79, 7], [48, 12, 78], [0, 0, 1], [0, 1]], ![[34, 77, 61], [15, 6, 78], [22, 87, 50], [54, 57, 81], [85, 73, 23], [41, 62, 77], [11, 11, 28]], ![[0, 1], [75, 7, 33], [3, 52, 56], [86, 42, 1], [51, 4, 77], [53, 27, 11], [34, 77, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 57], []]
 b := ![[], [79, 18, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [58, 31, 44, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8720487, 1325299, 46102]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![97983, 14891, 518]
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


def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2216, 257, -200]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![2216, 257, -200]] 
 ![![97, 0, 0], ![51, 1, 0], ![53, 0, 1]] where
  M :=![![![2216, 257, -200], ![-30886, 359, 1085], ![27149, -4544, 873]]]
  hmulB := by decide  
  f := ![![![-5243647, -684439, -350645]], ![![-3338620, -435781, -223255]], ![![-4211472, -549712, -281623]]]
  g := ![![![-3, 257, -200], ![-1100, 359, 1085], ![2192, -4544, 873]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 0, -1]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![25, 0, -1]] 
 ![![97, 0, 0], ![92, 1, 0], ![72, 0, 1]] where
  M :=![![![25, 0, -1], ![-157, 17, -1], ![-66, -33, 17]]]
  hmulB := by decide  
  f := ![![![256, 33, 17]], ![![271, 35, 18]], ![![255, 33, 17]]]
  g := ![![![1, 0, -1], ![-17, 17, -1], ![18, -33, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![2216, 257, -200]] ![![2216, 257, -200]]
  ![![-8456846, 1570575, -338955]] where
 M := ![![![-8456846, 1570575, -338955]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-8456846, 1570575, -338955]] ![![25, 0, -1]]
  ![![97, 0, 0]] where
 M := ![![![-435630395, 37885290, 1124036]]]
 hmul := by decide  
 g := ![![![![-4491035, 390570, 11588]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-21, 4, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-21, 4, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![80, 4, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-21, 4, 1], ![165, -17, 21], ![694, 65, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -4, 101]], ![![-1, 0, 1], ![-15, -1, 21], ![14, 1, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [48, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 100], [0, 1]]
 g := ![![[75, 25], [5], [71, 58], [100], [84], [36, 1]], ![[66, 76], [5], [38, 43], [100], [84], [72, 100]]]
 h' := ![![[36, 100], [32, 96], [26, 45], [24, 19], [28, 10], [90, 36], [0, 1]], ![[0, 1], [54, 5], [30, 56], [1, 82], [85, 91], [73, 65], [36, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [67, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [48, 65, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1084072, 579343, 149911]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108008, -201, 149911]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-21, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-21, 1, 0]] 
 ![![101, 0, 0], ![80, 1, 0], ![9, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-21, 1, 0], ![2, -22, 5], ![157, 8, -20]]]
  hmulB := by decide  
  f := ![![![-581, 6862, -1560], ![202, 31512, 0]], ![![-451, 5432, -1235], ![203, 24947, 0]], ![![-42, 611, -139], ![65, 2808, 0]]]
  g := ![![![1, 0, 0], ![-80, 101, 0], ![-9, 0, 101]], ![![-1, 1, 0], ![17, -22, 5], ![-3, 8, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-21, 4, 1]] ![![101, 0, 0], ![-21, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2121, 101, 0]], ![![-2121, 404, 101], ![606, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-21, 1, 0]]], ![![![-21, 4, 1]], ![![6, -1, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![34, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![34, 1, 0]] 
 ![![103, 0, 0], ![34, 1, 0], ![85, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![34, 1, 0], ![2, 33, 5], ![157, 8, 35]]]
  hmulB := by decide  
  f := ![![![6313, 122068, 18500], ![3296, -381100, 0]], ![![2068, 40282, 6105], ![1134, -125763, 0]], ![![5185, 100735, 15267], ![2795, -314500, 0]]]
  g := ![![![1, 0, 0], ![-34, 103, 0], ![-85, 0, 103]], ![![0, 1, 0], ![-15, 33, 5], ![-30, 8, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-17, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-17, 1, 0]] 
 ![![103, 0, 0], ![86, 1, 0], ![1, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-17, 1, 0], ![2, -18, 5], ![157, 8, -16]]]
  hmulB := by decide  
  f := ![![![-896, 8529, -2370], ![309, 48822, 0]], ![![-755, 7108, -1975], ![207, 40685, 0]], ![![5, 82, -23], ![86, 474, 0]]]
  g := ![![![1, 0, 0], ![-86, 103, 0], ![-1, 0, 103]], ![![-1, 1, 0], ![15, -18, 5], ![-5, 8, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![34, 1, 0]] ![![103, 0, 0], ![-17, 1, 0]]
  ![![103, 0, 0], ![29, -38, 1]] where
 M := ![![![10609, 0, 0], ![-1751, 103, 0]], ![![3502, 103, 0], ![-576, 16, 5]]]
 hmul := by decide  
 g := ![![![![74, 38, -1], ![103, 0, 0]], ![![-17, 1, 0], ![0, 0, 0]]], ![![![5, 39, -1], ![103, 0, 0]], ![![-7, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![29, -38, 1]] ![![103, 0, 0], ![-17, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1751, 103, 0]], ![![2987, -3914, 103], ![-412, 721, -206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-17, 1, 0]]], ![![![29, -38, 1]], ![![-4, 7, -2]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N1
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [88, 11, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 88, 37], [101, 18, 70], [0, 1]]
 g := ![![[28, 94, 85], [45, 12, 39], [74, 39], [40, 6, 92], [4, 81], [1]], ![[24, 53, 85, 11], [83, 47, 66, 16], [53, 89], [3, 42, 34, 10], [61, 86], [48, 37, 20, 42]], ![[80, 46, 20, 106], [90, 52, 42, 54], [5, 30], [66, 40, 28, 32], [105, 30], [6, 4, 46, 65]]]
 h' := ![![[104, 88, 37], [106, 39, 70], [29, 101, 50], [11, 76, 57], [9, 7, 29], [19, 96, 98], [0, 1]], ![[101, 18, 70], [49, 30, 28], [44, 38, 36], [0, 23, 93], [74, 84, 32], [29, 90, 73], [104, 88, 37]], ![[0, 1], [90, 38, 9], [22, 75, 21], [26, 8, 64], [94, 16, 46], [5, 28, 43], [101, 18, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 104], []]
 b := ![[], [104, 3, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [88, 11, 9, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9888512, -1086906, -40767]
  a := ![-5, 4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92416, -10158, -381]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [105, 2, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 3, 76], [4, 105, 33], [0, 1]]
 g := ![![[32, 9, 71], [91, 48], [49, 38, 45], [14, 23, 25], [85, 93], [1]], ![[45, 7, 89, 58], [31, 63], [21, 62, 61, 14], [55, 74, 10, 72], [76, 22], [11, 104, 96, 33]], ![[29, 51, 5, 11], [16, 20], [65, 74, 31, 39], [105, 54, 82, 32], [52, 9], [14, 44, 16, 76]]]
 h' := ![![[19, 3, 76], [85, 42, 17], [87, 29, 22], [56, 33, 46], [29, 77, 104], [4, 107, 23], [0, 1]], ![[4, 105, 33], [58, 27, 72], [32, 23, 45], [60, 94, 35], [74, 87, 95], [36, 46, 83], [19, 3, 76]], ![[0, 1], [84, 40, 20], [42, 57, 42], [0, 91, 28], [2, 54, 19], [11, 65, 3], [4, 105, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 85], []]
 b := ![[], [26, 28, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [105, 2, 86, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-581188, 0, -2725]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5332, 0, -25]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [5, 78, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 32, 89], [111, 80, 24], [0, 1]]
 g := ![![[111, 35, 14], [95, 100], [27, 69], [9, 8], [96, 55, 64], [1]], ![[105, 81, 53, 103], [52, 28], [41, 49], [52, 53], [19, 7, 2, 48], [26, 105, 74, 75]], ![[80, 59, 0, 35], [71, 52], [36, 28], [39, 62], [62, 21, 24, 59], [17, 55, 6, 38]]]
 h' := ![![[10, 32, 89], [86, 32, 50], [83, 7, 103], [61, 22, 42], [85, 59, 102], [108, 35, 8], [0, 1]], ![[111, 80, 24], [43, 15, 68], [90, 19, 49], [71, 96, 7], [52, 24, 77], [79, 41, 26], [10, 32, 89]], ![[0, 1], [79, 66, 108], [35, 87, 74], [92, 108, 64], [20, 30, 47], [20, 37, 79], [111, 80, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 8], []]
 b := ![[], [16, 95, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [5, 78, 105, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16153802, 2147226, 1055872]
  a := ![3, 18, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![142954, 19002, 9344]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![43, 22, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![43, 22, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![43, 22, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![43, 22, 1], ![201, 29, 111], ![3520, 209, 73]]]
  hmulB := by decide  
  f := ![![![-42, -22, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -22, 127]], ![![0, 0, 1], ![-36, -19, 111], ![3, -11, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [107, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 126], [0, 1]]
 g := ![![[80, 19], [76, 41], [42, 4], [89, 100], [21, 84], [76, 1]], ![[0, 108], [17, 86], [92, 123], [69, 27], [55, 43], [25, 126]]]
 h' := ![![[76, 126], [123, 107], [78, 101], [2, 125], [39, 117], [123, 81], [0, 1]], ![[0, 1], [0, 20], [7, 26], [104, 2], [41, 10], [56, 46], [76, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [78, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [107, 51, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5563, 1333, 101]
  a := ![-3, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-78, -7, 101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![16, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![16, 1, 0]] 
 ![![127, 0, 0], ![16, 1, 0], ![54, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![16, 1, 0], ![2, 15, 5], ![157, 8, 17]]]
  hmulB := by decide  
  f := ![![![-15, -120, -40], ![0, 1016, 0]], ![![-2, -15, -5], ![1, 127, 0]], ![![-22, -52, -17], ![124, 432, 0]]]
  g := ![![![1, 0, 0], ![-16, 127, 0], ![-54, 0, 127]], ![![0, 1, 0], ![-4, 15, 5], ![-7, 8, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![43, 22, 1]] ![![127, 0, 0], ![16, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![2032, 127, 0]], ![![5461, 2794, 127], ![889, 381, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![16, 1, 0]]], ![![![43, 22, 1]], ![![7, 3, 1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![39, -15, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![39, -15, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![39, 116, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![39, -15, 1], ![127, 62, -74], ![-2289, -87, 32]]]
  hmulB := by decide  
  f := ![![![-38, 15, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -116, 131]], ![![0, -1, 1], ![23, 66, -74], ![-27, -29, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [117, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 130], [0, 1]]
 g := ![![[40, 28], [103, 59], [39], [100], [7], [117], [1]], ![[0, 103], [0, 72], [39], [100], [7], [117], [1]]]
 h' := ![![[36, 130], [1, 40], [22, 94], [0, 68], [98, 121], [0, 111], [14, 36], [0, 1]], ![[0, 1], [0, 91], [0, 37], [90, 63], [0, 10], [66, 20], [0, 95], [36, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [57, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [117, 95, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3975, 3036, 1815]
  a := ![4, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-510, -1584, 1815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-57, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-57, 1, 0]] 
 ![![131, 0, 0], ![74, 1, 0], ![99, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-57, 1, 0], ![2, -58, 5], ![157, 8, -56]]]
  hmulB := by decide  
  f := ![![![19708, -751571, 64800], ![-14279, -1697760, 0]], ![![11164, -424499, 36600], ![-7990, -958920, 0]], ![![14886, -567981, 48971], ![-10809, -1283040, 0]]]
  g := ![![![1, 0, 0], ![-74, 131, 0], ![-99, 0, 131]], ![![-1, 1, 0], ![29, -58, 5], ![39, 8, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![39, -15, 1]] ![![131, 0, 0], ![-57, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-7467, 131, 0]], ![![5109, -1965, 131], ![-2096, 917, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-57, 1, 0]]], ![![![39, -15, 1]], ![![-16, 7, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![26, -45, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![26, -45, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![26, 92, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![26, -45, 1], ![67, 79, -224], ![-6999, -327, -11]]]
  hmulB := by decide  
  f := ![![![-25, 45, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -92, 137]], ![![0, -1, 1], ![43, 151, -224], ![-49, 5, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [38, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 136], [0, 1]]
 g := ![![[29, 119], [11], [107], [47, 112], [60], [36], [1]], ![[0, 18], [11], [107], [60, 25], [60], [36], [1]]]
 h' := ![![[131, 136], [96, 16], [69, 82], [132, 92], [71, 89], [76, 103], [99, 131], [0, 1]], ![[0, 1], [0, 121], [125, 55], [128, 45], [85, 48], [6, 34], [135, 6], [131, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [78, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [38, 6, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6633, 3300, 840]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-111, -540, 840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-50, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-50, 1, 0]] 
 ![![137, 0, 0], ![87, 1, 0], ![11, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-50, 1, 0], ![2, -51, 5], ![157, 8, -49]]]
  hmulB := by decide  
  f := ![![![11739, -363019, 35595], ![-6850, -975303, 0]], ![![7441, -230488, 22600], ![-4383, -619240, 0]], ![![967, -29148, 2858], ![-483, -78309, 0]]]
  g := ![![![1, 0, 0], ![-87, 137, 0], ![-11, 0, 137]], ![![-1, 1, 0], ![32, -51, 5], ![0, 8, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![26, -45, 1]] ![![137, 0, 0], ![-50, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6850, 137, 0]], ![![3562, -6165, 137], ![-1233, 2329, -274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-50, 1, 0]]], ![![![26, -45, 1]], ![![-9, 17, -2]]]]
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


lemma PB229I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB229I2 : PrimesBelowBoundCertificateInterval O 79 137 229 where
  m := 11
  g := ![2, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB229I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N1]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
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
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
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
      exact NI103N1
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
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I97N0, I97N1, I101N1, I103N0, I103N1, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [], [I97N0, I97N0, I97N1], [I101N1], [I103N0, I103N1, I103N1], [], [], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
