
import IdealArithmetic.Examples.NF3_1_797203_1.RI3_1_797203_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [58, 14, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 37, 77], [41, 45, 6], [0, 1]]
 g := ![![[80, 67, 29], [65, 5, 31], [2, 65], [13, 29], [63, 49, 1], []], ![[65, 15, 20, 41], [33, 54, 15, 51], [52, 51], [40, 21], [47, 52, 13, 51], [75, 36]], ![[5, 38, 54, 46], [63, 2, 37, 82], [40, 81], [16, 69], [28, 2, 2, 80], [63, 36]]]
 h' := ![![[8, 37, 77], [48, 40, 64], [59, 14, 23], [80, 1, 27], [81, 11, 19], [0, 0, 1], [0, 1]], ![[41, 45, 6], [47, 54, 67], [31, 60, 38], [68, 19, 47], [75, 7, 42], [30, 27, 45], [8, 37, 77]], ![[0, 1], [82, 72, 35], [74, 9, 22], [53, 63, 9], [63, 65, 22], [19, 56, 37], [41, 45, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 5], []]
 b := ![[], [68, 53, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [58, 14, 34, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-638685, 381551, -182434]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7695, 4597, -2198]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![48, -25, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![48, -25, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![48, 64, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![48, -25, 1], ![102, 47, -98], ![-3699, 675, -27]]]
  hmulB := by decide  
  f := ![![![-47, 25, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -64, 89]], ![![0, -1, 1], ![54, 71, -98], ![-27, 27, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [26, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 88], [0, 1]]
 g := ![![[69, 55], [32], [40], [86, 79], [31, 18], [1]], ![[11, 34], [32], [40], [48, 10], [46, 71], [1]]]
 h' := ![![[75, 88], [9, 12], [60, 78], [78, 60], [84, 41], [63, 75], [0, 1]], ![[0, 1], [19, 77], [36, 11], [39, 29], [44, 48], [81, 14], [75, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [25, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [26, 14, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1340, 2248, -1133]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![596, 840, -1133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![9, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![9, 1, 0]] 
 ![![89, 0, 0], ![9, 1, 0], ![27, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![9, 1, 0], ![2, 8, 4], ![152, -26, 11]]]
  hmulB := by decide  
  f := ![![![-1030, -4159, -2080], ![-89, 46280, 0]], ![![-104, -416, -208], ![1, 4628, 0]], ![![-315, -1262, -631], ![-2, 14040, 0]]]
  g := ![![![1, 0, 0], ![-9, 89, 0], ![-27, 0, 89]], ![![0, 1, 0], ![-2, 8, 4], ![1, -26, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![48, -25, 1]] ![![89, 0, 0], ![9, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![801, 89, 0]], ![![4272, -2225, 89], ![534, -178, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![9, 1, 0]]], ![![![48, -25, 1]], ![![6, -2, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11030, -273, -361]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-11030, -273, -361]] 
 ![![97, 0, 0], ![0, 97, 0], ![19, 33, 1]] where
  M :=![![![-11030, -273, -361], ![-55418, -1371, -1814], ![-77957, -1927, -2551]]]
  hmulB := by decide  
  f := ![![![-19, 8, -3]], ![![-440, 51, 26]], ![![-144, 16, 9]]]
  g := ![![![-43, 120, -361], ![-216, 603, -1814], ![-304, 848, -2551]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [74, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 96], [0, 1]]
 g := ![![[92, 73], [75], [75], [16], [32], [79, 1]], ![[39, 24], [75], [75], [16], [32], [61, 96]]]
 h' := ![![[79, 96], [49, 48], [78, 50], [83, 47], [54, 4], [71, 56], [0, 1]], ![[0, 1], [58, 49], [51, 47], [13, 50], [79, 93], [33, 41], [79, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [34, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [74, 18, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![423023, 112219, -101768]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24295, 35779, -101768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 8, -3]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-19, 8, -3]] 
 ![![97, 0, 0], ![60, 1, 0], ![37, 0, 1]] where
  M :=![![![-19, 8, -3], ![-440, 51, 26], ![913, -283, 72]]]
  hmulB := by decide  
  f := ![![![-11030, -273, -361]], ![![-7394, -183, -242]], ![![-5011, -124, -164]]]
  g := ![![![-4, 8, -3], ![-46, 51, 26], ![157, -283, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-11030, -273, -361]] ![![-19, 8, -3]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![21, -43, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![21, -43, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![21, 58, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![21, -43, 1], ![66, 38, -170], ![-6435, 1143, -90]]]
  hmulB := by decide  
  f := ![![![-20, 43, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -58, 101]], ![![0, -1, 1], ![36, 98, -170], ![-45, 63, -90]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [98, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 100], [0, 1]]
 g := ![![[85, 52], [54], [60, 20], [16], [54], [53, 1]], ![[13, 49], [54], [9, 81], [16], [54], [5, 100]]]
 h' := ![![[53, 100], [40, 31], [79, 85], [28, 11], [92, 97], [58, 85], [0, 1]], ![[0, 1], [67, 70], [39, 16], [5, 90], [82, 4], [18, 16], [53, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [79, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [98, 48, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-87, 3540, -2457]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![510, 1446, -2457]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-32, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-32, 1, 0]] 
 ![![101, 0, 0], ![69, 1, 0], ![90, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-32, 1, 0], ![2, -33, 4], ![152, -26, -30]]]
  hmulB := by decide  
  f := ![![![2569, -48696, 5904], ![-1212, -149076, 0]], ![![1761, -33256, 4032], ![-807, -101808, 0]], ![![2274, -43392, 5261], ![-1128, -132840, 0]]]
  g := ![![![1, 0, 0], ![-69, 101, 0], ![-90, 0, 101]], ![![-1, 1, 0], ![19, -33, 4], ![46, -26, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![21, -43, 1]] ![![101, 0, 0], ![-32, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3232, 101, 0]], ![![2121, -4343, 101], ![-606, 1414, -202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-32, 1, 0]]], ![![![21, -43, 1]], ![![-6, 14, -2]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![14, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![14, 1, 0]] 
 ![![103, 0, 0], ![14, 1, 0], ![58, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![14, 1, 0], ![2, 13, 4], ![152, -26, 16]]]
  hmulB := by decide  
  f := ![![![7405, 49476, 15228], ![1545, -392121, 0]], ![![1006, 6719, 2068], ![207, -53251, 0]], ![![4166, 27860, 8575], ![898, -220806, 0]]]
  g := ![![![1, 0, 0], ![-14, 103, 0], ![-58, 0, 103]], ![![0, 1, 0], ![-4, 13, 4], ![-4, -26, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![35, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![35, 1, 0]] 
 ![![103, 0, 0], ![35, 1, 0], ![12, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![35, 1, 0], ![2, 34, 4], ![152, -26, 37]]]
  hmulB := by decide  
  f := ![![![-8352, -167543, -19716], ![-4429, 507687, 0]], ![![-2858, -56902, -6696], ![-1441, 172422, 0]], ![![-988, -19520, -2297], ![-472, 59148, 0]]]
  g := ![![![1, 0, 0], ![-35, 103, 0], ![-12, 0, 103]], ![![0, 1, 0], ![-12, 34, 4], ![6, -26, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-50, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-50, 1, 0]] 
 ![![103, 0, 0], ![53, 1, 0], ![84, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-50, 1, 0], ![2, -51, 4], ![152, -26, -48]]]
  hmulB := by decide  
  f := ![![![2001, -71384, 5600], ![-1648, -144200, 0]], ![![1041, -36712, 2880], ![-823, -74160, 0]], ![![1628, -58216, 4567], ![-1352, -117600, 0]]]
  g := ![![![1, 0, 0], ![-53, 103, 0], ![-84, 0, 103]], ![![-1, 1, 0], ![23, -51, 4], ![54, -26, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![14, 1, 0]] ![![103, 0, 0], ![35, 1, 0]]
  ![![103, 0, 0], ![20, 12, 1]] where
 M := ![![![10609, 0, 0], ![3605, 103, 0]], ![![1442, 103, 0], ![492, 48, 4]]]
 hmul := by decide  
 g := ![![![![83, -12, -1], ![103, 0, 0]], ![![15, -11, -1], ![103, 0, 0]]], ![![![-6, -11, -1], ![103, 0, 0]], ![![4, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![20, 12, 1]] ![![103, 0, 0], ![-50, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-5150, 103, 0]], ![![2060, 1236, 103], ![-824, -618, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-50, 1, 0]]], ![![![20, 12, 1]], ![![-8, -6, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![4, -5, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![4, -5, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![4, 102, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![4, -5, 1], ![142, -17, -18], ![-659, 155, -31]]]
  hmulB := by decide  
  f := ![![![-3, 5, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -102, 107]], ![![0, -1, 1], ![2, 17, -18], ![-5, 31, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [2, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 106], [0, 1]]
 g := ![![[94, 13], [8, 13], [62], [90, 44], [61], [26, 1]], ![[4, 94], [25, 94], [62], [57, 63], [61], [52, 106]]]
 h' := ![![[26, 106], [91, 21], [69, 86], [34, 94], [14, 77], [55, 32], [0, 1]], ![[0, 1], [102, 86], [58, 21], [17, 13], [90, 30], [31, 75], [26, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [1, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [2, 81, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1582, 1286, -1370]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, 1318, -1370]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![18, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![18, 1, 0]] 
 ![![107, 0, 0], ![18, 1, 0], ![31, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![18, 1, 0], ![2, 17, 4], ![152, -26, 20]]]
  hmulB := by decide  
  f := ![![![481, 4384, 1032], ![214, -27606, 0]], ![![68, 730, 172], ![108, -4601, 0]], ![![137, 1270, 299], ![76, -7998, 0]]]
  g := ![![![1, 0, 0], ![-18, 107, 0], ![-31, 0, 107]], ![![0, 1, 0], ![-4, 17, 4], ![0, -26, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![4, -5, 1]] ![![107, 0, 0], ![18, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![1926, 107, 0]], ![![428, -535, 107], ![214, -107, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![18, 1, 0]]], ![![![4, -5, 1]], ![![2, -1, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![4, -52, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![4, -52, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![4, 57, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![4, -52, 1], ![48, 30, -206], ![-7803, 1377, -125]]]
  hmulB := by decide  
  f := ![![![-3, 52, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -57, 109]], ![![0, -1, 1], ![8, 108, -206], ![-67, 78, -125]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [57, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 108], [0, 1]]
 g := ![![[35, 4], [60], [40, 93], [64, 21], [94], [76, 1]], ![[12, 105], [60], [23, 16], [25, 88], [94], [43, 108]]]
 h' := ![![[76, 108], [40, 107], [9, 13], [58, 86], [4, 81], [28, 51], [0, 1]], ![[0, 1], [106, 2], [16, 96], [54, 23], [56, 28], [89, 58], [76, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [3, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [57, 33, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![174946, 48383, -43082]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3186, 22973, -43082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-12, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-12, 1, 0]] 
 ![![109, 0, 0], ![97, 1, 0], ![16, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-12, 1, 0], ![2, -13, 4], ![152, -26, -10]]]
  hmulB := by decide  
  f := ![![![-1799, 11931, -3672], ![327, 100062, 0]], ![![-1595, 10605, -3264], ![328, 88944, 0]], ![![-260, 1751, -539], ![85, 14688, 0]]]
  g := ![![![1, 0, 0], ![-97, 109, 0], ![-16, 0, 109]], ![![-1, 1, 0], ![11, -13, 4], ![26, -26, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![4, -52, 1]] ![![109, 0, 0], ![-12, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1308, 109, 0]], ![![436, -5668, 109], ![0, 654, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-12, 1, 0]]], ![![![4, -52, 1]], ![![0, 6, -2]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1560446317, 38611972, 51070783]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1560446317, 38611972, 51070783]] 
 ![![113, 0, 0], ![0, 113, 0], ![39, 90, 1]] where
  M :=![![![1560446317, 38611972, 51070783], ![7839982960, 193993987, 256589454], ![11027168827, 272858303, 360900686]]]
  hmulB := by decide  
  f := ![![![18040, -3111, -341]], ![![-58054, 30017, -13126]], ![![-44501, 23474, -10392]]]
  g := ![![![-3816940, -40334146, 51070783], ![-19177042, -202646521, 256589454], ![-26973079, -285028349, 360900686]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [77, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 112], [0, 1]]
 g := ![![[2, 91], [56], [91], [62], [75, 32], [72, 1]], ![[0, 22], [56], [91], [62], [6, 81], [31, 112]]]
 h' := ![![[72, 112], [46, 59], [8, 13], [3, 59], [101, 47], [106, 22], [0, 1]], ![[0, 1], [0, 54], [40, 100], [70, 54], [95, 66], [108, 91], [72, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [84, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [77, 41, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![484, 13, 24]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -19, 24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18040, -3111, -341]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![18040, -3111, -341]] 
 ![![113, 0, 0], ![90, 1, 0], ![32, 0, 1]] where
  M :=![![![18040, -3111, -341], ![-58054, 30017, -13126], ![-507313, 72361, 20343]]]
  hmulB := by decide  
  f := ![![![1560446317, 38611972, 51070783]], ![![1312213730, 32469659, 42946548]], ![![539481867, 13349039, 17656334]]]
  g := ![![![2734, -3111, -341], ![-20704, 30017, -13126], ![-67883, 72361, 20343]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1560446317, 38611972, 51070783]] ![![18040, -3111, -341]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [45, 3, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 37, 3], [4, 89, 124], [0, 1]]
 g := ![![[45, 92, 36], [107, 91, 94], [76, 49, 104], [39, 41, 117], [125, 122, 121], [1]], ![[55, 105, 47, 7], [106, 4, 19, 126], [49, 11, 8, 29], [21, 4, 70, 77], [30, 70, 27, 125], [85, 15, 26, 27]], ![[65, 98, 122, 34], [39, 12, 11, 47], [105, 12, 2, 79], [24, 113, 30, 124], [59, 52, 3, 8], [68, 72, 74, 100]]]
 h' := ![![[7, 37, 3], [11, 110, 121], [9, 1, 100], [23, 42, 55], [90, 97, 25], [82, 124, 11], [0, 1]], ![[4, 89, 124], [35, 26, 50], [88, 0, 13], [1, 16, 68], [25, 119, 103], [74, 64, 81], [7, 37, 3]], ![[0, 1], [126, 118, 83], [11, 126, 14], [101, 69, 4], [33, 38, 126], [52, 66, 35], [4, 89, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 97], []]
 b := ![[], [79, 93, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [45, 3, 116, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4081145, -1233932, 410464]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32135, -9716, 3232]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![20, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![20, 1, 0]] 
 ![![131, 0, 0], ![20, 1, 0], ![102, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![20, 1, 0], ![2, 19, 4], ![152, -26, 22]]]
  hmulB := by decide  
  f := ![![![-5149, -50437, -10620], ![-1048, 347805, 0]], ![![-790, -7694, -1620], ![-130, 53055, 0]], ![![-3998, -39271, -8269], ![-889, 270810, 0]]]
  g := ![![![1, 0, 0], ![-20, 131, 0], ![-102, 0, 131]], ![![0, 1, 0], ![-6, 19, 4], ![-12, -26, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![973367, -253446, 42452]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![973367, -253446, 42452]] 
 ![![131, 0, 0], ![51, 1, 0], ![18, 0, 1]] where
  M :=![![![973367, -253446, 42452], ![5945812, 123061, -928880], ![-34236140, 7650896, -594825]]]
  hmulB := by decide  
  f := ![![![-7033564517155, -174039820042, -230196734908]], ![![-3008013539855, -74430842837, -98447223132]], ![![-1345863238022, -33302288644, -44047839793]]]
  g := ![![![100267, -253446, 42452], ![125111, 123061, -928880], ![-3158206, 7650896, -594825]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![59, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![59, 1, 0]] 
 ![![131, 0, 0], ![59, 1, 0], ![62, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![59, 1, 0], ![2, 58, 4], ![152, -26, 61]]]
  hmulB := by decide  
  f := ![![![1510, 59151, 4080], ![1179, -133620, 0]], ![![682, 26618, 1836], ![525, -60129, 0]], ![![707, 27995, 1931], ![575, -63240, 0]]]
  g := ![![![1, 0, 0], ![-59, 131, 0], ![-62, 0, 131]], ![![0, 1, 0], ![-28, 58, 4], ![-16, -26, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![20, 1, 0]] ![![973367, -253446, 42452]]
  ![![131, 0, 0], ![59, -48, 1]] where
 M := ![![![127511077, -33201426, 5561212]], ![![25413152, -4945859, -79840]]]
 hmul := by decide  
 g := ![![![![794302, -107766, 39417], ![397585, 0, 0]]], ![![![159860, -9985, -1188], ![75788, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![59, -48, 1]] ![![131, 0, 0], ![59, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![7729, 131, 0]], ![![7729, -6288, 131], ![3537, -2751, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![59, 1, 0]]], ![![![59, -48, 1]], ![![27, -21, -1]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6023501, 858972, 241678]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-6023501, 858972, 241678]] 
 ![![137, 0, 0], ![59, 1, 0], ![104, 0, 1]] where
  M :=![![![-6023501, 858972, 241678], ![38453000, -13166101, 3919244], ![154973222, -16291322, -10347507]]]
  hmulB := by decide  
  f := ![![![200085988260775, 4950964664488, 6548477814646]], ![![93506159595189, 2313733690659, 3060299309134]], ![![162210844287606, 4013775103622, 5308888065305]]]
  g := ![![![-597353, 858972, 241678], ![2975559, -13166101, 3919244], ![16002204, -16291322, -10347507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-30, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-30, 1, 0]] 
 ![![137, 0, 0], ![107, 1, 0], ![42, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-30, 1, 0], ![2, -31, 4], ![152, -26, -28]]]
  hmulB := by decide  
  f := ![![![10561, -175744, 22680], ![-3562, -776790, 0]], ![![8257, -137248, 17712], ![-2739, -606636, 0]], ![![3246, -53878, 6953], ![-1054, -238140, 0]]]
  g := ![![![1, 0, 0], ![-107, 137, 0], ![-42, 0, 137]], ![![-1, 1, 0], ![23, -31, 4], ![30, -26, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-6023501, 858972, 241678]] ![![137, 0, 0], ![-30, 1, 0]]
  ![![137, 0, 0], ![-31, 7, 1]] where
 M := ![![![-825219637, 117679164, 33109886], ![219158030, -38935261, -3331096]]]
 hmul := by decide  
 g := ![![![![-5721034, 790673, 231921], ![1336709, 0, 0]], ![![1518828, -265939, -21706], ![-357374, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-31, 7, 1]] ![![137, 0, 0], ![-30, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-4110, 137, 0]], ![![-4247, 959, 137], ![1096, -274, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-30, 1, 0]]], ![![![-31, 7, 1]], ![![8, -2, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB253I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB253I2 : PrimesBelowBoundCertificateInterval O 79 137 253 where
  m := 11
  g := ![1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB253I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1, I137N1]
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
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![131, 131, 131]
    · exact ![137, 137, 137]
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
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
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N1
  β := ![I89N1, I97N1, I101N1, I103N0, I103N1, I103N2, I107N1, I109N1, I113N1, I131N0, I131N1, I131N2, I137N0, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [I109N1], [I113N1], [], [I131N0, I131N1, I131N2], [I137N0, I137N1, I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
