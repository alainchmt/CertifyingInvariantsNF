
import IdealArithmetic.Examples.NF3_1_884199_1.RI3_1_884199_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![24, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![24, 1, 0]] 
 ![![83, 0, 0], ![24, 1, 0], ![49, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![24, 1, 0], ![0, 25, 3], ![327, 58, 24]]]
  hmulB := by decide  
  f := ![![![985, 41, 0], ![-3403, 0, 0]], ![![264, 11, 0], ![-912, 0, 0]], ![![563, 15, -1], ![-1945, 28, 0]]]
  g := ![![![1, 0, 0], ![-24, 83, 0], ![-49, 0, 83]], ![![0, 1, 0], ![-9, 25, 3], ![-27, 58, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![29, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![29, 1, 0]] 
 ![![83, 0, 0], ![29, 1, 0], ![42, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![29, 1, 0], ![0, 30, 3], ![327, 58, 29]]]
  hmulB := by decide  
  f := ![![![1306, 45, 0], ![-3735, 0, 0]], ![![406, 14, 0], ![-1161, 0, 0]], ![![642, 12, -1], ![-1836, 28, 0]]]
  g := ![![![1, 0, 0], ![-29, 83, 0], ![-42, 0, 83]], ![![0, 1, 0], ![-12, 30, 3], ![-31, 58, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![24, 1, 0]] ![![83, 0, 0], ![29, 1, 0]]
  ![![83, 0, 0], ![-17, 18, 1]] where
 M := ![![![6889, 0, 0], ![2407, 83, 0]], ![![1992, 83, 0], ![696, 54, 3]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![29, 1, 0], ![0, 0, 0]]], ![![![24, 1, 0], ![0, 0, 0]], ![![9, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-17, 18, 1]] ![![83, 0, 0], ![29, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2407, 83, 0]], ![![-1411, 1494, 83], ![-166, 581, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![29, 1, 0]]], ![![![-17, 18, 1]], ![![-2, 7, 1]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![18, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![18, 1, 0]] 
 ![![89, 0, 0], ![18, 1, 0], ![64, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![18, 1, 0], ![0, 19, 3], ![327, 58, 18]]]
  hmulB := by decide  
  f := ![![![55, 3, 0], ![-267, 0, 0]], ![![-18, -1, 0], ![90, 0, 0]], ![![8, -6, -1], ![-36, 30, 0]]]
  g := ![![![1, 0, 0], ![-18, 89, 0], ![-64, 0, 89]], ![![0, 1, 0], ![-6, 19, 3], ![-21, 58, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![19, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![19, 1, 0]] 
 ![![89, 0, 0], ![19, 1, 0], ![81, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![19, 1, 0], ![0, 20, 3], ![327, 58, 19]]]
  hmulB := by decide  
  f := ![![![1084, 57, 0], ![-5073, 0, 0]], ![![228, 12, 0], ![-1067, 0, 0]], ![![984, 45, -1], ![-4605, 30, 0]]]
  g := ![![![1, 0, 0], ![-19, 89, 0], ![-81, 0, 89]], ![![0, 1, 0], ![-7, 20, 3], ![-26, 58, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-38, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-38, 1, 0]] 
 ![![89, 0, 0], ![51, 1, 0], ![6, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-38, 1, 0], ![0, -37, 3], ![327, 58, -38]]]
  hmulB := by decide  
  f := ![![![3345, -88, 0], ![7832, 0, 0]], ![![1939, -51, 0], ![4540, 0, 0]], ![![246, 6, -1], ![576, 30, 0]]]
  g := ![![![1, 0, 0], ![-51, 89, 0], ![-6, 0, 89]], ![![-1, 1, 0], ![21, -37, 3], ![-27, 58, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![18, 1, 0]] ![![89, 0, 0], ![19, 1, 0]]
  ![![89, 0, 0], ![-64, -17, 1]] where
 M := ![![![7921, 0, 0], ![1691, 89, 0]], ![![1602, 89, 0], ![342, 38, 3]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![19, 1, 0], ![0, 0, 0]]], ![![![18, 1, 0], ![0, 0, 0]], ![![6, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-64, -17, 1]] ![![89, 0, 0], ![-38, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3382, 89, 0]], ![![-5696, -1513, 89], ![2759, 623, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-38, 1, 0]]], ![![![-64, -17, 1]], ![![31, 7, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [55, 75, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 79, 60], [7, 17, 37], [0, 1]]
 g := ![![[16, 84, 31], [88, 8], [44, 24], [87, 1], [], [1]], ![[59, 28, 21, 71], [19, 62], [41, 62], [26, 64], [26, 86], [54, 53, 85, 78]], ![[64, 3, 87, 59], [0, 93], [62, 50], [12, 81], [3, 86], [45, 39, 76, 19]]]
 h' := ![![[90, 79, 60], [46, 36, 82], [6, 40, 69], [1, 2, 11], [18, 5, 96], [42, 22], [0, 1]], ![[7, 17, 37], [16, 35, 62], [24, 57, 81], [57, 71, 16], [56, 59, 89], [82, 89, 59], [90, 79, 60]], ![[0, 1], [95, 26, 50], [17, 0, 44], [41, 24, 70], [33, 33, 9], [2, 83, 38], [7, 17, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 88], []]
 b := ![[], [36, 61, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [55, 75, 0, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6517818, -2109750, -466764]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-67194, -21750, -4812]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [86, 77, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 79, 64], [59, 21, 37], [0, 1]]
 g := ![![[75, 97, 4], [18, 54], [35, 11, 47], [37, 4], [35, 77], [1]], ![[71, 73, 43, 97], [80, 30], [99, 38, 49, 16], [24, 4], [64, 6], [57, 0, 83, 49]], ![[45, 20, 35, 17], [92, 80], [91, 91, 80, 45], [21, 16], [93, 20], [33, 75, 52, 52]]]
 h' := ![![[14, 79, 64], [64, 74, 99], [20, 92, 16], [81, 17, 42], [43, 89, 99], [15, 24, 73], [0, 1]], ![[59, 21, 37], [19, 94, 48], [58, 57, 63], [93, 26, 51], [6, 67, 99], [64, 47, 39], [14, 79, 64]], ![[0, 1], [9, 34, 55], [12, 53, 22], [96, 58, 8], [65, 46, 4], [36, 30, 90], [59, 21, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 51], []]
 b := ![[], [83, 38, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [86, 77, 28, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5102217, 1921424, 470458]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50517, 19024, 4658]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![42, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![42, 1, 0]] 
 ![![103, 0, 0], ![42, 1, 0], ![16, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![42, 1, 0], ![0, 43, 3], ![327, 58, 42]]]
  hmulB := by decide  
  f := ![![![967, 23, 0], ![-2369, 0, 0]], ![![378, 9, 0], ![-926, 0, 0]], ![![160, -25, -2], ![-392, 69, 0]]]
  g := ![![![1, 0, 0], ![-42, 103, 0], ![-16, 0, 103]], ![![0, 1, 0], ![-18, 43, 3], ![-27, 58, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-38, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-38, 1, 0]] 
 ![![103, 0, 0], ![65, 1, 0], ![12, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-38, 1, 0], ![0, -37, 3], ![327, 58, -38]]]
  hmulB := by decide  
  f := ![![![1559, -41, 0], ![4223, 0, 0]], ![![989, -26, 0], ![2679, 0, 0]], ![![220, 19, -2], ![596, 69, 0]]]
  g := ![![![1, 0, 0], ![-65, 103, 0], ![-12, 0, 103]], ![![-1, 1, 0], ![23, -37, 3], ![-29, 58, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87351, 22412, 4238]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![87351, 22412, 4238]] 
 ![![103, 0, 0], ![98, 1, 0], ![62, 0, 1]] where
  M :=![![![87351, 22412, 4238], ![1385826, 355567, 67236], ![6866782, 1761838, 333155]]]
  hmulB := by decide  
  f := ![![![-15883, -416, 286]], ![![-14204, -393, 260]], ![![-11184, -182, 179]]]
  g := ![![![-23027, 22412, 4238], ![-365324, 355567, 67236], ![-1810184, 1761838, 333155]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![42, 1, 0]] ![![103, 0, 0], ![-38, 1, 0]]
  ![![-15883, -416, 286]] where
 M := ![![![10609, 0, 0], ![-3914, 103, 0]], ![![4326, 103, 0], ![-1596, 5, 3]]]
 hmul := by decide  
 g := ![![![![8997153, 2308436, 436514]], ![![-1933512, -496089, -93808]]], ![![![5054568, 1296871, 245232]], ![![-1086240, -278701, -52701]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-15883, -416, 286]] ![![87351, 22412, 4238]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [104, 7, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 86, 87], [97, 20, 20], [0, 1]]
 g := ![![[79, 30, 105], [75, 98, 1], [5, 25], [23, 10, 36], [89, 62], [1]], ![[27, 10, 75, 92], [30, 98, 94, 69], [63, 81], [103, 48, 80, 14], [32, 35], [92, 88, 56, 25]], ![[75, 44, 24, 50], [105, 17, 74, 28], [24, 16], [46, 4, 26, 97], [92, 11], [39, 20, 28, 82]]]
 h' := ![![[23, 86, 87], [11, 6, 76], [68, 11, 106], [69, 75, 5], [62, 56, 101], [3, 100, 13], [0, 1]], ![[97, 20, 20], [44, 40, 9], [76, 85, 81], [23, 55, 98], [94, 78, 44], [31, 105, 79], [23, 86, 87]], ![[0, 1], [66, 61, 22], [48, 11, 27], [46, 84, 4], [42, 80, 69], [80, 9, 15], [97, 20, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 38], []]
 b := ![[], [69, 0, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [104, 7, 94, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![103897, -23326, -9202]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![971, -218, -86]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![0, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![0, 1, 0]] 
 ![![109, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![0, 1, 0], ![0, 1, 3], ![327, 58, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -2], ![36, 73, 0]]]
  g := ![![![1, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![0, 1, 0], ![0, 1, 3], ![3, 58, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![38, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![38, 1, 0]] 
 ![![109, 0, 0], ![38, 1, 0], ![51, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![38, 1, 0], ![0, 39, 3], ![327, 58, 38]]]
  hmulB := by decide  
  f := ![![![2281, 60, 0], ![-6540, 0, 0]], ![![798, 21, 0], ![-2288, 0, 0]], ![![1031, 1, -2], ![-2956, 73, 0]]]
  g := ![![![1, 0, 0], ![-38, 109, 0], ![-51, 0, 109]], ![![0, 1, 0], ![-15, 39, 3], ![-35, 58, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-39, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-39, 1, 0]] 
 ![![109, 0, 0], ![70, 1, 0], ![51, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-39, 1, 0], ![0, -38, 3], ![327, 58, -39]]]
  hmulB := by decide  
  f := ![![![1951, -50, 0], ![5450, 0, 0]], ![![1288, -33, 0], ![3598, 0, 0]], ![![915, 2, -2], ![2556, 73, 0]]]
  g := ![![![1, 0, 0], ![-70, 109, 0], ![-51, 0, 109]], ![![-1, 1, 0], ![23, -38, 3], ![-16, 58, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![0, 1, 0]] ![![109, 0, 0], ![38, 1, 0]]
  ![![109, 0, 0], ![0, 13, 1]] where
 M := ![![![11881, 0, 0], ![4142, 109, 0]], ![![0, 109, 0], ![0, 39, 3]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![38, -12, -1], ![109, 0, 0]]], ![![![0, -12, -1], ![109, 0, 0]], ![![0, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![0, 13, 1]] ![![109, 0, 0], ![-39, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-4251, 109, 0]], ![![0, 1417, 109], ![327, -436, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-39, 1, 0]]], ![![![0, 13, 1]], ![![3, -4, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [84, 11, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 42, 23], [81, 70, 90], [0, 1]]
 g := ![![[16, 72, 64], [29, 61], [25, 32], [93, 97], [104, 11, 61], [1]], ![[99, 28, 93, 66], [73, 111], [], [62, 44], [35, 15, 104, 5], [79, 14, 46, 76]], ![[84, 39, 65, 45], [49, 36], [91, 32], [47, 25], [88, 48, 107, 55], [109, 110, 62, 37]]]
 h' := ![![[12, 42, 23], [86, 28, 8], [6, 51, 20], [80, 105, 22], [78, 16, 60], [29, 102, 93], [0, 1]], ![[81, 70, 90], [84, 66, 74], [112, 45, 87], [15, 58], [108, 31, 48], [64, 53, 42], [12, 42, 23]], ![[0, 1], [66, 19, 31], [112, 17, 6], [33, 63, 91], [34, 66, 5], [112, 71, 91], [81, 70, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 20], []]
 b := ![[], [32, 61, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [84, 11, 20, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15553094, -5199469, -1161979]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-137638, -46013, -10283]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-44, -40, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-44, -40, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![83, 87, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-44, -40, 1], ![327, -26, -120], ![-13189, -2211, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -87, 127]], ![![-1, -1, 1], ![81, 82, -120], ![-113, -27, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [15, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 126], [0, 1]]
 g := ![![[84, 17], [8, 50], [116, 98], [120, 100], [14, 113], [10, 1]], ![[0, 110], [0, 77], [80, 29], [104, 27], [1, 14], [20, 126]]]
 h' := ![![[10, 126], [7, 12], [38, 47], [105, 112], [44, 117], [104, 85], [0, 1]], ![[0, 1], [0, 115], [0, 80], [82, 15], [71, 10], [65, 42], [10, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [32, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [15, 117, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3830, 3655, 877]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-543, -572, 877]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-7, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-7, 1, 0]] 
 ![![127, 0, 0], ![120, 1, 0], ![113, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-7, 1, 0], ![0, -6, 3], ![327, 58, -7]]]
  hmulB := by decide  
  f := ![![![778, -111, 0], ![14097, 0, 0]], ![![736, -105, 0], ![13336, 0, 0]], ![![694, -95, -2], ![12575, 85, 0]]]
  g := ![![![1, 0, 0], ![-120, 127, 0], ![-113, 0, 127]], ![![-1, 1, 0], ![3, -6, 3], ![-46, 58, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-44, -40, 1]] ![![127, 0, 0], ![-7, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-889, 127, 0]], ![![-5588, -5080, 127], ![635, 254, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-7, 1, 0]]], ![![![-44, -40, 1]], ![![5, 2, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-21, 26, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-21, 26, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![110, 26, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-21, 26, 1], ![327, 63, 78], ![8393, 1617, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-110, -26, 131]], ![![-1, 0, 1], ![-63, -15, 78], ![33, 5, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [108, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 130], [0, 1]]
 g := ![![[17, 74], [65, 15], [58], [44], [44], [4], [1]], ![[0, 57], [35, 116], [58], [44], [44], [4], [1]]]
 h' := ![![[129, 130], [54, 27], [104, 88], [39, 53], [72, 31], [97, 31], [23, 129], [0, 1]], ![[0, 1], [0, 104], [59, 43], [64, 78], [10, 100], [35, 100], [27, 2], [129, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [30, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [108, 2, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![353162, 278829, 98862]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-80318, -17493, 98862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![53, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![53, 1, 0]] 
 ![![131, 0, 0], ![53, 1, 0], ![94, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![53, 1, 0], ![0, 54, 3], ![327, 58, 53]]]
  hmulB := by decide  
  f := ![![![4188, 79, 0], ![-10349, 0, 0]], ![![1696, 32, 0], ![-4191, 0, 0]], ![![2976, 38, -1], ![-7354, 44, 0]]]
  g := ![![![1, 0, 0], ![-53, 131, 0], ![-94, 0, 131]], ![![0, 1, 0], ![-24, 54, 3], ![-59, 58, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-21, 26, 1]] ![![131, 0, 0], ![53, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![6943, 131, 0]], ![![-2751, 3406, 131], ![-786, 1441, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![53, 1, 0]]], ![![![-21, 26, 1]], ![![-6, 11, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-61, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-61, 1, 0]] 
 ![![137, 0, 0], ![76, 1, 0], ![13, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-61, 1, 0], ![0, -60, 3], ![327, 58, -61]]]
  hmulB := by decide  
  f := ![![![1282, -21, 0], ![2877, 0, 0]], ![![794, -13, 0], ![1782, 0, 0]], ![![192, 17, -1], ![431, 46, 0]]]
  g := ![![![1, 0, 0], ![-76, 137, 0], ![-13, 0, 137]], ![![-1, 1, 0], ![33, -60, 3], ![-24, 58, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-60, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-60, 1, 0]] 
 ![![137, 0, 0], ![77, 1, 0], ![53, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-60, 1, 0], ![0, -59, 3], ![327, 58, -60]]]
  hmulB := by decide  
  f := ![![![3721, -62, 0], ![8494, 0, 0]], ![![2101, -35, 0], ![4796, 0, 0]], ![![1549, -6, -1], ![3536, 46, 0]]]
  g := ![![![1, 0, 0], ![-77, 137, 0], ![-53, 0, 137]], ![![-1, 1, 0], ![32, -59, 3], ![-7, 58, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-17, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-17, 1, 0]] 
 ![![137, 0, 0], ![120, 1, 0], ![92, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-17, 1, 0], ![0, -16, 3], ![327, 58, -17]]]
  hmulB := by decide  
  f := ![![![2228, -131, 0], ![17947, 0, 0]], ![![1956, -115, 0], ![15756, 0, 0]], ![![1486, -82, -1], ![11970, 46, 0]]]
  g := ![![![1, 0, 0], ![-120, 137, 0], ![-92, 0, 137]], ![![-1, 1, 0], ![12, -16, 3], ![-37, 58, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-61, 1, 0]] ![![137, 0, 0], ![-60, 1, 0]]
  ![![137, 0, 0], ![-13, -40, 1]] where
 M := ![![![18769, 0, 0], ![-8220, 137, 0]], ![![-8357, 137, 0], ![3660, -120, 3]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![-47, 41, -1], ![137, 0, 0]]], ![![![-48, 41, -1], ![137, 0, 0]], ![![27, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-13, -40, 1]] ![![137, 0, 0], ![-17, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-2329, 137, 0]], ![![-1781, -5480, 137], ![548, 685, -137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-17, 1, 0]]], ![![![-13, -40, 1]], ![![4, 5, -1]]]]
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


lemma PB267I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB267I2 : PrimesBelowBoundCertificateInterval O 79 137 267 where
  m := 11
  g := ![3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB267I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![83, 83, 83]
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
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
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
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
      exact NI137N2
  β := ![I83N0, I83N1, I89N0, I89N1, I89N2, I103N0, I103N1, I103N2, I109N0, I109N1, I109N2, I127N1, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N0, I83N1, I83N1], [I89N0, I89N1, I89N2], [], [], [I103N0, I103N1, I103N2], [], [I109N0, I109N1, I109N2], [], [I127N1], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
