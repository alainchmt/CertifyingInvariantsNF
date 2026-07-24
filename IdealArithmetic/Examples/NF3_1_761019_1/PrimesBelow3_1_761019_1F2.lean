
import IdealArithmetic.Examples.NF3_1_761019_1.RI3_1_761019_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![29, 38, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![29, 38, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![29, 38, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![29, 38, 1], ![-16, -41, 154], ![-3581, -1255, 74]]]
  hmulB := by decide  
  f := ![![![-28, -38, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -38, 83]], ![![0, 0, 1], ![-54, -71, 154], ![-69, -49, 74]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 82], [0, 1]]
 g := ![![[28, 28], [66, 77], [48], [1], [5, 1], [1]], ![[0, 55], [72, 6], [48], [1], [4, 82], [1]]]
 h' := ![![[82, 82], [51, 51], [4, 49], [56, 52], [68, 1], [80, 82], [0, 1]], ![[0, 1], [0, 32], [38, 34], [4, 31], [67, 82], [81, 1], [82, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [68, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [3, 1, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1945, -1026, -1106]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![363, 494, -1106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![12, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![12, 1, 0]] 
 ![![83, 0, 0], ![12, 1, 0], ![9, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![12, 1, 0], ![2, 11, 4], ![-92, -32, 14]]]
  hmulB := by decide  
  f := ![![![-391, -2156, -784], ![0, 16268, 0]], ![![-56, -308, -112], ![1, 2324, 0]], ![![-45, -234, -85], ![18, 1764, 0]]]
  g := ![![![1, 0, 0], ![-12, 83, 0], ![-9, 0, 83]], ![![0, 1, 0], ![-2, 11, 4], ![2, -32, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![29, 38, 1]] ![![83, 0, 0], ![12, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![996, 83, 0]], ![![2407, 3154, 83], ![332, 415, 166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![12, 1, 0]]], ![![![29, 38, 1]], ![![4, 5, 2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![44, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![44, 1, 0]] 
 ![![89, 0, 0], ![44, 1, 0], ![17, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![44, 1, 0], ![2, 43, 4], ![-92, -32, 46]]]
  hmulB := by decide  
  f := ![![![4417, 134634, 12528], ![3738, -278748, 0]], ![![2172, 66543, 6192], ![1870, -137772, 0]], ![![817, 25716, 2393], ![768, -53244, 0]]]
  g := ![![![1, 0, 0], ![-44, 89, 0], ![-17, 0, 89]], ![![0, 1, 0], ![-22, 43, 4], ![6, -32, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-36, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-36, 1, 0]] 
 ![![89, 0, 0], ![53, 1, 0], ![68, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-36, 1, 0], ![2, -37, 4], ![-92, -32, -34]]]
  hmulB := by decide  
  f := ![![![1669, -38838, 4200], ![-1068, -93450, 0]], ![![999, -23118, 2500], ![-622, -55625, 0]], ![![1276, -29674, 3209], ![-814, -71400, 0]]]
  g := ![![![1, 0, 0], ![-53, 89, 0], ![-68, 0, 89]], ![![-1, 1, 0], ![19, -37, 4], ![44, -32, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-9, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-9, 1, 0]] 
 ![![89, 0, 0], ![80, 1, 0], ![67, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-9, 1, 0], ![2, -10, 4], ![-92, -32, -7]]]
  hmulB := by decide  
  f := ![![![1405, -7108, 2844], ![-178, -63279, 0]], ![![1261, -6388, 2556], ![-177, -56871, 0]], ![![1058, -5351, 2141], ![-131, -47637, 0]]]
  g := ![![![1, 0, 0], ![-80, 89, 0], ![-67, 0, 89]], ![![-1, 1, 0], ![6, -10, 4], ![33, -32, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![44, 1, 0]] ![![89, 0, 0], ![-36, 1, 0]]
  ![![89, 0, 0], ![5, 24, 1]] where
 M := ![![![7921, 0, 0], ![-3204, 89, 0]], ![![3916, 89, 0], ![-1582, 7, 4]]]
 hmul := by decide  
 g := ![![![![84, -24, -1], ![89, 0, 0]], ![![-36, 1, 0], ![0, 0, 0]]], ![![![39, -23, -1], ![89, 0, 0]], ![![-18, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![5, 24, 1]] ![![89, 0, 0], ![-9, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-801, 89, 0]], ![![445, 2136, 89], ![-89, -267, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-9, 1, 0]]], ![![![5, 24, 1]], ![![-1, -3, 1]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![45, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![45, 1, 0]] 
 ![![97, 0, 0], ![45, 1, 0], ![39, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![45, 1, 0], ![2, 44, 4], ![-92, -32, 47]]]
  hmulB := by decide  
  f := ![![![-3290, -97127, -8832], ![-2425, 214176, 0]], ![![-1508, -45044, -4096], ![-1163, 99328, 0]], ![![-1320, -39051, -3551], ![-981, 86112, 0]]]
  g := ![![![1, 0, 0], ![-45, 97, 0], ![-39, 0, 97]], ![![0, 1, 0], ![-22, 44, 4], ![-5, -32, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-32, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-32, 1, 0]] 
 ![![97, 0, 0], ![65, 1, 0], ![76, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-32, 1, 0], ![2, -33, 4], ![-92, -32, -30]]]
  hmulB := by decide  
  f := ![![![3, 494, -60], ![97, 1455, 0]], ![![13, 329, -40], ![98, 970, 0]], ![![4, 387, -47], ![81, 1140, 0]]]
  g := ![![![1, 0, 0], ![-65, 97, 0], ![-76, 0, 97]], ![![-1, 1, 0], ![19, -33, 4], ![44, -32, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-14, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-14, 1, 0]] 
 ![![97, 0, 0], ![83, 1, 0], ![45, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-14, 1, 0], ![2, -15, 4], ![-92, -32, -12]]]
  hmulB := by decide  
  f := ![![![16749, -129562, 34560], ![-3686, -838080, 0]], ![![14323, -110847, 29568], ![-3200, -717024, 0]], ![![7769, -60106, 16033], ![-1718, -388800, 0]]]
  g := ![![![1, 0, 0], ![-83, 97, 0], ![-45, 0, 97]], ![![-1, 1, 0], ![11, -15, 4], ![32, -32, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![45, 1, 0]] ![![97, 0, 0], ![-32, 1, 0]]
  ![![97, 0, 0], ![-20, 3, 1]] where
 M := ![![![9409, 0, 0], ![-3104, 97, 0]], ![![4365, 97, 0], ![-1438, 12, 4]]]
 hmul := by decide  
 g := ![![![![97, 0, 0], ![0, 0, 0]], ![![-12, -2, -1], ![97, 0, 0]]], ![![![45, 1, 0], ![0, 0, 0]], ![![-14, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-20, 3, 1]] ![![97, 0, 0], ![-14, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1358, 97, 0]], ![![-1940, 291, 97], ![194, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-14, 1, 0]]], ![![![-20, 3, 1]], ![![2, -1, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [44, 15, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 55, 50], [47, 45, 51], [0, 1]]
 g := ![![[89, 81, 17], [0, 71], [13, 26, 87], [94, 54], [25, 52], [1]], ![[49, 73, 28, 55], [59, 23], [24, 19, 54, 73], [80, 4], [2, 71], [37, 67, 83, 63]], ![[11, 95, 51, 11], [5, 81], [59, 89, 54, 99], [2, 95], [15, 96], [65, 49, 93, 38]]]
 h' := ![![[23, 55, 50], [45, 62, 44], [34, 32, 77], [82, 89, 17], [28, 71, 85], [57, 86, 70], [0, 1]], ![[47, 45, 51], [84, 20, 30], [85, 19, 15], [85, 64, 64], [26, 51, 2], [35, 53, 77], [23, 55, 50]], ![[0, 1], [62, 19, 27], [79, 50, 9], [17, 49, 20], [2, 80, 14], [64, 63, 55], [47, 45, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 7], []]
 b := ![[], [50, 62, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [44, 15, 31, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![863348, 381780, 285224]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8548, 3780, 2824]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-29, 16, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-29, 16, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![74, 16, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-29, 16, 1], ![-60, -77, 66], ![-1557, -551, -28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -16, 103]], ![![-1, 0, 1], ![-48, -11, 66], ![5, -1, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [40, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 102], [0, 1]]
 g := ![![[63, 36], [43, 7], [16, 19], [82], [4], [55, 1]], ![[86, 67], [16, 96], [31, 84], [82], [4], [7, 102]]]
 h' := ![![[55, 102], [31, 97], [81, 78], [24, 88], [76, 59], [66, 101], [0, 1]], ![[0, 1], [10, 6], [45, 25], [23, 15], [25, 44], [59, 2], [55, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [73, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [40, 48, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-356969, -165743, -129884]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![89849, 18567, -129884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![37, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![37, 1, 0]] 
 ![![103, 0, 0], ![37, 1, 0], ![28, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![37, 1, 0], ![2, 36, 4], ![-92, -32, 39]]]
  hmulB := by decide  
  f := ![![![-1772, -37899, -4212], ![-927, 108459, 0]], ![![-645, -13605, -1512], ![-308, 38934, 0]], ![![-495, -10303, -1145], ![-215, 29484, 0]]]
  g := ![![![1, 0, 0], ![-37, 103, 0], ![-28, 0, 103]], ![![0, 1, 0], ![-14, 36, 4], ![0, -32, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-29, 16, 1]] ![![103, 0, 0], ![37, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3811, 103, 0]], ![![-2987, 1648, 103], ![-1133, 515, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![37, 1, 0]]], ![![![-29, 16, 1]], ![![-11, 5, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![27, 39, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![27, 39, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![27, 39, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![27, 39, 1], ![-14, -44, 158], ![-3673, -1287, 74]]]
  hmulB := by decide  
  f := ![![![-26, -39, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -39, 107]], ![![0, 0, 1], ![-40, -58, 158], ![-53, -39, 74]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [16, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 106], [0, 1]]
 g := ![![[100, 87], [25, 102], [49], [33, 48], [81], [5, 1]], ![[0, 20], [0, 5], [49], [59, 59], [81], [10, 106]]]
 h' := ![![[5, 106], [28, 80], [14, 40], [7, 100], [75, 35], [27, 9], [0, 1]], ![[0, 1], [0, 27], [0, 67], [79, 7], [36, 72], [72, 98], [5, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [52, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [16, 102, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2275, -1158, -3429]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![844, 1239, -3429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-51, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-51, 1, 0]] 
 ![![107, 0, 0], ![56, 1, 0], ![33, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-51, 1, 0], ![2, -52, 4], ![-92, -32, -49]]]
  hmulB := by decide  
  f := ![![![3975, -143074, 11008], ![-3210, -294464, 0]], ![![2116, -74865, 5760], ![-1604, -154080, 0]], ![![1245, -44126, 3395], ![-950, -90816, 0]]]
  g := ![![![1, 0, 0], ![-56, 107, 0], ![-33, 0, 107]], ![![-1, 1, 0], ![26, -52, 4], ![31, -32, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![27, 39, 1]] ![![107, 0, 0], ![-51, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-5457, 107, 0]], ![![2889, 4173, 107], ![-1391, -2033, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-51, 1, 0]]], ![![![27, 39, 1]], ![![-13, -19, 1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![18, 48, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![18, 48, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![18, 48, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![18, 48, 1], ![4, -62, 194], ![-4501, -1575, 83]]]
  hmulB := by decide  
  f := ![![![-17, -48, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -48, 109]], ![![0, 0, 1], ![-32, -86, 194], ![-55, -51, 83]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [38, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 108], [0, 1]]
 g := ![![[8, 66], [81], [93, 4], [71, 89], [82], [23, 1]], ![[0, 43], [81], [76, 105], [47, 20], [82], [46, 108]]]
 h' := ![![[23, 108], [19, 75], [63, 100], [27, 107], [49, 31], [107, 55], [0, 1]], ![[0, 1], [0, 34], [74, 9], [90, 2], [108, 78], [64, 54], [23, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [7, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [38, 86, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2165, -941, -1616]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![247, 703, -1616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![24, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![24, 1, 0]] 
 ![![109, 0, 0], ![24, 1, 0], ![26, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![24, 1, 0], ![2, 23, 4], ![-92, -32, 26]]]
  hmulB := by decide  
  f := ![![![-1603, -19546, -3400], ![-436, 92650, 0]], ![![-350, -4300, -748], ![-108, 20383, 0]], ![![-398, -4663, -811], ![-33, 22100, 0]]]
  g := ![![![1, 0, 0], ![-24, 109, 0], ![-26, 0, 109]], ![![0, 1, 0], ![-6, 23, 4], ![0, -32, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![18, 48, 1]] ![![109, 0, 0], ![24, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![2616, 109, 0]], ![![1962, 5232, 109], ![436, 1090, 218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![24, 1, 0]]], ![![![18, 48, 1]], ![![4, 10, 2]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [34, 70, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 4, 107], [95, 108, 6], [0, 1]]
 g := ![![[44, 36, 91], [95, 22], [100, 9], [48, 97], [100, 38, 104], [1]], ![[7, 11, 61, 79], [84, 13], [10, 104], [50, 14], [83, 33, 45, 20], [27, 70, 95, 10]], ![[110, 45, 102, 84], [4, 85], [104, 44], [85, 9], [19, 77, 59, 5], [78, 92, 23, 103]]]
 h' := ![![[86, 4, 107], [63, 10, 54], [4, 22, 94], [50, 10, 110], [103, 96, 53], [79, 43, 68], [0, 1]], ![[95, 108, 6], [96, 3, 9], [63, 78, 76], [8, 86, 68], [37, 61, 63], [78, 71, 80], [86, 4, 107]], ![[0, 1], [9, 100, 50], [91, 13, 56], [89, 17, 48], [43, 69, 110], [104, 112, 78], [95, 108, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 30], []]
 b := ![[], [98, 25, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [34, 70, 45, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![462820202, 182382904, 58409361]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4095754, 1614008, 516897]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![33, 32, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![33, 32, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![33, 32, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![33, 32, 1], ![-28, -31, 130], ![-3029, -1063, 66]]]
  hmulB := by decide  
  f := ![![![-32, -32, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -32, 127]], ![![0, 0, 1], ![-34, -33, 130], ![-41, -25, 66]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [21, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 126], [0, 1]]
 g := ![![[103, 121], [10, 104], [113, 113], [122, 16], [76, 25], [123, 1]], ![[0, 6], [102, 23], [42, 14], [58, 111], [103, 102], [119, 126]]]
 h' := ![![[123, 126], [44, 11], [40, 72], [105, 42], [55, 4], [84, 122], [0, 1]], ![[0, 1], [0, 116], [6, 55], [64, 85], [39, 123], [104, 5], [123, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [15, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [21, 4, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-246, -100, -19]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 4, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-3, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-3, 1, 0]] 
 ![![127, 0, 0], ![124, 1, 0], ![61, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-3, 1, 0], ![2, -4, 4], ![-92, -32, -1]]]
  hmulB := by decide  
  f := ![![![-1088, 2183, -2184], ![127, 69342, 0]], ![![-1062, 2131, -2132], ![128, 67691, 0]], ![![-521, 1048, -1049], ![128, 33306, 0]]]
  g := ![![![1, 0, 0], ![-124, 127, 0], ![-61, 0, 127]], ![![-1, 1, 0], ![2, -4, 4], ![31, -32, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![33, 32, 1]] ![![127, 0, 0], ![-3, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-381, 127, 0]], ![![4191, 4064, 127], ![-127, -127, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-3, 1, 0]]], ![![![33, 32, 1]], ![![-1, -1, 1]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [103, 20, 93, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 50, 130], [16, 80, 1], [0, 1]]
 g := ![![[85, 90, 121], [75, 118, 41], [76, 5], [48, 9], [107, 27], [38, 1], []], ![[76, 31, 20, 30], [95, 26, 123, 69], [87, 7], [28, 74], [127, 74], [28, 112], [69, 1]], ![[90, 119, 44, 117], [130, 105, 49, 112], [86, 9], [89, 114], [72, 100], [113, 11], [67, 1]]]
 h' := ![![[22, 50, 130], [4, 69, 11], [112, 129, 98], [39, 105, 108], [108, 82, 3], [16, 54, 114], [0, 0, 1], [0, 1]], ![[16, 80, 1], [64, 71, 25], [119, 81, 113], [98, 25, 20], [121, 94, 27], [87, 74, 27], [58, 62, 80], [22, 50, 130]], ![[0, 1], [63, 122, 95], [71, 52, 51], [105, 1, 3], [87, 86, 101], [6, 3, 121], [36, 69, 50], [16, 80, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 1], []]
 b := ![[], [3, 18, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [103, 20, 93, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4014757, 1590078, 582426]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30647, 12138, 4446]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [32, 44, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 62, 125], [75, 74, 12], [0, 1]]
 g := ![![[100, 124, 101], [61, 112], [11, 11], [0, 127, 59], [136, 69], [26, 1], []], ![[93, 18, 2, 108], [90, 30], [105, 100], [54, 30, 4, 111], [27, 101], [41, 133], [64, 7]], ![[89, 97, 90, 29], [25, 103], [16, 107], [35, 4, 77, 13], [70, 1], [68, 8], [40, 7]]]
 h' := ![![[88, 62, 125], [22, 26, 52], [59, 123, 48], [0, 71, 82], [132, 121, 14], [127, 57, 84], [0, 0, 1], [0, 1]], ![[75, 74, 12], [116, 93, 111], [16, 101, 21], [122, 115, 10], [104, 27, 132], [134, 58, 52], [79, 63, 74], [88, 62, 125]], ![[0, 1], [81, 18, 111], [14, 50, 68], [72, 88, 45], [30, 126, 128], [30, 22, 1], [98, 74, 62], [75, 74, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 13], []]
 b := ![[], [0, 55, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [32, 44, 111, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-979413, -400725, -169195]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7149, -2925, -1235]
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



lemma PB247I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB247I2 : PrimesBelowBoundCertificateInterval O 79 137 247 where
  m := 11
  g := ![2, 3, 3, 1, 2, 2, 2, 1, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB247I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
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
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
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
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
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
      exact NI109N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N0, I89N1, I89N2, I97N0, I97N1, I97N2, I103N1, I107N1, I109N1, I127N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N0, I97N1, I97N2], [], [I103N1], [I107N1], [I109N1], [], [I127N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
